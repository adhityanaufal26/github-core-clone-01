#!/usr/bin/env python3
"""forge: a single-process GitHub-compatible git forge.

Serves git smart HTTP (upload-pack v2/v0, receive-pack v0), REST v3 under
/api/v3, GraphQL at /api/graphql and MCP at /mcp, from one in-memory store.
Standard library only. Deterministic: no wall clock or unseeded randomness
reaches any response; commit timestamps come from a fixed base plus a
monotonic counter, and ids come from counters.
"""
import base64
import hashlib
import json
import os
import re
import sys
import threading
import time
import urllib.error
import urllib.request
import zlib
from collections import deque
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, unquote, urlparse

ZERO = "0" * 40
FIXED_TS = 1760000000
FIXED_ISO = "2026-11-14T06:00:00Z"
VERSION = "1.0.0"

# ---------------------------------------------------------------- utilities

def sha1_hex(data):
    return hashlib.sha1(data).hexdigest()


def git_hash(otype, content):
    h = hashlib.sha1()
    h.update(("%s %d\0" % (otype, len(content))).encode())
    h.update(content)
    return h.hexdigest()


def b64_node(kind, num):
    return base64.b64encode(("%s:%s" % (kind, num)).encode()).decode()


def pkt(data):
    if isinstance(data, str):
        data = data.encode()
    return ("%04x" % (len(data) + 4)).encode() + data


FLUSH = b"0000"


def parse_pkt_lines(buf):
    """Return (lines, rest_offset). lines are payload bytes; flush ends list."""
    lines = []
    pos = 0
    n = len(buf)
    while pos + 4 <= n:
        try:
            ln = int(buf[pos:pos + 4], 16)
        except ValueError:
            break
        if ln == 0:
            return lines, pos + 4
        if ln == 1:
            # delimiter packet: separates command/capabilities from args
            pos += 4
            continue
        if ln < 4 or pos + ln > n:
            break
        lines.append(buf[pos + 4:pos + ln])
        pos += ln
    return lines, pos


# ---------------------------------------------------------------- git objects

def parse_commit(content):
    """content bytes -> (tree_sha, [parent_shas], message str)."""
    text = content.decode("utf-8", "replace")
    head, _, msg = text.partition("\n\n")
    tree = None
    parents = []
    for line in head.split("\n"):
        if line.startswith("tree "):
            tree = line[5:].strip()
        elif line.startswith("parent "):
            parents.append(line[7:].strip())
    return tree, parents, msg


def parse_tree(data):
    """tree bytes -> [(mode_str, name, sha_hex)]."""
    out = []
    pos = 0
    n = len(data)
    while pos < n:
        sp = data.index(b" ", pos)
        mode = data[pos:sp].decode()
        nul = data.index(b"\0", sp)
        name = data[sp + 1:nul].decode("utf-8", "surrogateescape")
        sha = data[nul + 1:nul + 21].hex()
        out.append((mode, name, sha))
        pos = nul + 21
    return out


def build_tree(entries):
    """entries: [(mode, name, sha_hex)] -> (sha, bytes)."""
    def sort_key(e):
        return e[1] + ("/" if e[0] == "40000" else "")
    data = b""
    for mode, name, sha in sorted(entries, key=sort_key):
        data += mode.encode() + b" " + name.encode("utf-8", "surrogateescape")
        data += b"\0" + bytes.fromhex(sha)
    return git_hash("tree", data), data


def flatten_tree(objects, tree_sha, prefix=""):
    """tree sha -> {path: (blob_sha, mode)} for all files below it."""
    out = {}
    if tree_sha not in objects:
        return out
    for mode, name, sha in parse_tree(objects[tree_sha][1]):
        path = prefix + name
        if mode == "40000":
            out.update(flatten_tree(objects, sha, path + "/"))
        else:
            out[path] = (sha, mode)
    return out


def rebuild_tree(objects, files):
    """files: {path: (blob_sha, mode)} -> tree sha; stores new trees."""
    nested = {}

    def put(parts, sha, mode):
        node = nested
        for part in parts[:-1]:
            node = node.setdefault(part, {})
        node[parts[-1]] = (sha, mode)

    for path, (sha, mode) in files.items():
        put(path.split("/"), sha, mode)

    def build(node):
        entries = []
        for name, val in node.items():
            if isinstance(val, dict):
                sub, _ = build(val)
                entries.append(("40000", name, sub))
            else:
                entries.append((val[1], name, val[0]))
        sha, data = build_tree(entries)
        objects[sha] = ("tree", data)
        return sha, data

    sha, _ = build(nested)
    return sha


def make_commit(objects, tree_sha, parents, message, ts):
    lines = ["tree %s" % tree_sha]
    for p in parents:
        lines.append("parent %s" % p)
    who = "forge <forge@forge.local> %d +0000" % ts
    lines.append("author %s" % who)
    lines.append("committer %s" % who)
    body = "\n".join(lines) + "\n\n" + message
    if not body.endswith("\n"):
        body += "\n"
    content = body.encode()
    sha = git_hash("commit", content)
    objects[sha] = ("commit", content)
    return sha


# ---------------------------------------------------------------- git deltas

def _rd_varint(d, i):
    r = 0
    s = 0
    while True:
        b = d[i]
        i += 1
        r |= (b & 0x7F) << s
        s += 7
        if not (b & 0x80):
            return r, i


def apply_delta(base, delta):
    src_size, i = _rd_varint(delta, 0)
    tgt_size, i = _rd_varint(delta, i)
    if src_size != len(base):
        raise ValueError("delta source size mismatch")
    out = bytearray()
    while i < len(delta):
        op = delta[i]
        i += 1
        if op & 0x80:
            cp_off = 0
            cp_size = 0
            for j in range(4):
                if op & (1 << j):
                    cp_off |= delta[i] << (8 * j)
                    i += 1
            for j in range(3):
                if op & (0x10 << j):
                    cp_size |= delta[i] << (8 * j)
                    i += 1
            if cp_size == 0:
                cp_size = 0x10000
            out += base[cp_off:cp_off + cp_size]
        elif op:
            out += delta[i:i + op]
            i += op
        else:
            raise ValueError("delta opcode 0")
    if len(out) != tgt_size:
        raise ValueError("delta target size mismatch")
    return bytes(out)


# ---------------------------------------------------------------- packfiles

_TYPE_NUM = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}
_NUM_TYPE = {1: "commit", 2: "tree", 3: "blob", 4: "tag"}


def read_pack(data, objects):
    """Parse a packfile; return {sha: (type, content)} for its entries.

    Delta bases resolve against earlier pack entries first, then the
    repository object store passed in.
    """
    if len(data) < 12 or data[:4] != b"PACK":
        raise ValueError("bad pack magic")
    count = int.from_bytes(data[8:12], "big")
    pos = 12
    found = {}
    offmap = {}
    for _ in range(count):
        start = pos
        b = data[pos]
        pos += 1
        otype_num = (b >> 4) & 7
        size = b & 0x0F
        shift = 4
        while b & 0x80:
            b = data[pos]
            pos += 1
            size |= (b & 0x7F) << shift
            shift += 7
        base_type = None
        base_content = None
        if otype_num == 6:  # OFS_DELTA
            b = data[pos]
            pos += 1
            off = b & 0x7F
            while b & 0x80:
                b = data[pos]
                pos += 1
                off = ((off + 1) << 7) | (b & 0x7F)
            base_sha = offmap.get(start - off)
            if base_sha is None or base_sha not in found:
                raise ValueError("ofs-delta base not found")
            base_type, base_content = found[base_sha]
        elif otype_num == 7:  # REF_DELTA
            base_sha = data[pos:pos + 20].hex()
            pos += 20
            if base_sha in found:
                base_type, base_content = found[base_sha]
            elif base_sha in objects:
                base_type, base_content = objects[base_sha]
            else:
                raise ValueError("ref-delta base not found")
        dobj = zlib.decompressobj()
        raw = dobj.decompress(data[pos:])
        consumed = len(data[pos:]) - len(dobj.unused_data)
        pos += consumed
        if otype_num in (6, 7):
            # size is the delta data's length, not the result's
            if len(raw) != size:
                raise ValueError("pack entry size mismatch")
            content = apply_delta(base_content, raw)
            tname = base_type
        else:
            content = raw
            tname = _NUM_TYPE[otype_num]
            if len(content) != size:
                raise ValueError("pack entry size mismatch")
        sha = git_hash(tname, content)
        found[sha] = (tname, content)
        offmap[start] = sha
    return found


def write_pack(objs):
    """objs: iterable of (sha, (type, content)) -> packfile bytes."""
    items = sorted(objs, key=lambda kv: (_TYPE_NUM.get(kv[1][0], 9), kv[0]))
    out = bytearray(b"PACK")
    out += (2).to_bytes(4, "big")
    out += len(items).to_bytes(4, "big")
    for _sha, (tname, content) in items:
        tnum = _TYPE_NUM[tname]
        size = len(content)
        first = (tnum << 4) | (size & 0x0F)
        size >>= 4
        if size:
            first |= 0x80
        out.append(first)
        while size:
            b = size & 0x7F
            size >>= 7
            if size:
                b |= 0x80
            out.append(b)
        out += zlib.compress(content, 6)
    out += hashlib.sha1(bytes(out)).digest()
    return bytes(out)


def commit_closure(objects, start_shas, depth=None):
    """All object shas reachable from start commits.

    Returns (reachable_set, shallow_set). With depth N, parents at depth
    N are cut and the cut commits are reported as shallow.
    """
    reachable = set()
    shallow = set()
    seen = set()
    queue = deque()
    for s in start_shas:
        queue.append((s, 0))
    while queue:
        sha, d = queue.popleft()
        if sha in seen or sha not in objects:
            continue
        seen.add(sha)
        tname, content = objects[sha]
        reachable.add(sha)
        if tname == "tag":
            # tag object: first line is "object <sha>"
            for line in content.decode("utf-8", "replace").split("\n"):
                if line.startswith("object "):
                    queue.append((line[7:].strip(), d))
                    break
            continue
        if tname != "commit":
            continue
        tree, parents, _msg = parse_commit(content)
        if tree:
            _walk_tree(objects, tree, reachable)
        cut = depth is not None and d + 1 >= depth
        if cut:
            shallow.add(sha)
        else:
            for p in parents:
                queue.append((p, d + 1))
    return reachable, shallow


def _walk_tree(objects, tree_sha, out):
    if tree_sha in out or tree_sha not in objects:
        return
    out.add(tree_sha)
    for _mode, _name, sha in parse_tree(objects[tree_sha][1]):
        if sha in objects and objects[sha][0] == "tree":
            _walk_tree(objects, sha, out)
        else:
            out.add(sha)


def ancestors(objects, start_sha, limit=200000):
    """Set of commit shas reachable from start_sha via parents."""
    out = set()
    queue = deque([start_sha])
    while queue and len(out) < limit:
        sha = queue.popleft()
        if sha in out or sha not in objects:
            continue
        tname, content = objects[sha]
        if tname != "commit":
            continue
        out.add(sha)
        _tree, parents, _m = parse_commit(content)
        queue.extend(parents)
    return out

# ---------------------------------------------------------------- the store

class Repo:
    __slots__ = ("dbid", "name", "owner", "description", "private",
                 "default_branch", "labels", "issues", "pulls", "counter",
                 "objects", "refs")

    def __init__(self, dbid, name, owner, description, private, default_branch):
        self.dbid = dbid
        self.name = name
        self.owner = owner  # None until the token login is observed
        self.description = description or ""
        self.private = bool(private)
        self.default_branch = default_branch or "main"
        self.labels = {}    # name -> {name, color, description}
        self.issues = {}    # number -> issue dict
        self.pulls = {}     # number -> pr dict
        self.counter = 0    # shared issue/PR numbering
        self.objects = {}   # sha -> (type, content)
        self.refs = {}      # refname -> sha

    def head_sha(self, branch=None):
        ref = "refs/heads/" + (branch or self.default_branch)
        return self.refs.get(ref)

    def full_name(self, login):
        return "%s/%s" % (self.owner or login, self.name)


class Forge:
    def __init__(self):
        self.lock = threading.RLock()
        self.repos = {}          # name -> Repo (names unique in practice)
        self.login = None        # token login, learned from first owner seen
        self.next_id = 1
        self.req_seq = 0
        self.commit_seq = 0

    def next_dbid(self):
        n = self.next_id
        self.next_id += 1
        return n

    def next_req_id(self):
        self.req_seq += 1
        return "%016x" % self.req_seq

    def next_ts(self):
        self.commit_seq += 1
        return FIXED_TS + self.commit_seq

    def owner_login(self):
        return self.login or "octocat"

    def learn_login(self, owner):
        if owner and self.login is None:
            self.login = owner
            for r in self.repos.values():
                if r.owner is None:
                    r.owner = owner

    def find_repo(self, owner, name):
        """Resolve a repo by (owner, name); learns the login on first hit."""
        r = self.repos.get(name)
        if r is None:
            return None
        if r.owner is None:
            self.learn_login(owner)
        if r.owner is not None and r.owner != owner:
            return None
        return r

    def find_repo_any_owner(self, name):
        return self.repos.get(name)


FORGE = Forge()


def repo_json(r, base_url):
    login = r.owner or FORGE.owner_login()
    full = "%s/%s" % (login, r.name)
    return {
        "id": r.dbid,
        "node_id": b64_node("Repository", r.dbid),
        "name": r.name,
        "full_name": full,
        "owner": {"login": login, "id": r.dbid, "node_id": b64_node("User", r.dbid),
                  "type": "User", "site_admin": False},
        "private": r.private,
        "html_url": "%s/%s" % (base_url, full),
        "description": r.description,
        "fork": False,
        "url": "%s/api/v3/repos/%s" % (base_url, full),
        "created_at": FIXED_ISO,
        "updated_at": FIXED_ISO,
        "pushed_at": FIXED_ISO,
        "git_url": "git://example.invalid/%s.git" % full,
        "ssh_url": "git@example.invalid:%s.git" % full,
        "clone_url": "%s/%s.git" % (base_url, full),
        "homepage": None,
        "size": 0,
        "stargazers_count": 0,
        "watchers_count": 0,
        "language": None,
        "has_issues": True,
        "has_projects": True,
        "has_downloads": True,
        "has_wiki": True,
        "has_pages": False,
        "has_discussions": False,
        "forks_count": 0,
        "archived": False,
        "disabled": False,
        "open_issues_count": sum(1 for i in r.issues.values()
                                  if i["state"] == "open"),
        "license": None,
        "allow_forking": True,
        "is_template": False,
        "topics": [],
        "visibility": "public" if not r.private else "private",
        "forks": 0,
        "open_issues": sum(1 for i in r.issues.values()
                           if i["state"] == "open"),
        "watchers": 0,
        "default_branch": r.default_branch,
    }


def issue_json(r, iss, base_url):
    login = r.owner or FORGE.owner_login()
    full = "%s/%s" % (login, r.name)
    labels = [dict(r.labels[nm]) for nm in iss["labels"] if nm in r.labels]
    return {
        "id": iss["dbid"],
        "node_id": b64_node("Issue", iss["dbid"]),
        "url": "%s/api/v3/repos/%s/issues/%d" % (base_url, full, iss["number"]),
        "repository_url": "%s/api/v3/repos/%s" % (base_url, full),
        "labels_url": "%s/api/v3/repos/%s/issues/%d/labels" % (
            base_url, full, iss["number"]),
        "comments_url": "%s/api/v3/repos/%s/issues/%d/comments" % (
            base_url, full, iss["number"]),
        "events_url": "%s/api/v3/repos/%s/issues/%d/events" % (
            base_url, full, iss["number"]),
        "html_url": "%s/%s/issues/%d" % (base_url, full, iss["number"]),
        "number": iss["number"],
        "state": iss["state"],
        "title": iss["title"],
        "body": iss.get("body") or "",
        "user": {"login": login, "id": 1, "type": "User"},
        "labels": labels,
        "assignee": None,
        "assignees": [],
        "milestone": None,
        "locked": False,
        "active_lock_reason": None,
        "comments": len(iss.get("comments", [])),
        "closed_at": iss.get("closed_at"),
        "created_at": iss["created_at"],
        "updated_at": iss["updated_at"],
        "author_association": "OWNER",
        "state_reason": None,
    }


def pr_json(r, pr, base_url, mergeable=None):
    login = r.owner or FORGE.owner_login()
    full = "%s/%s" % (login, r.name)
    if mergeable is None:
        mergeable = compute_mergeable(r, pr)
    return {
        "id": pr["dbid"],
        "node_id": b64_node("PullRequest", pr["dbid"]),
        "url": "%s/api/v3/repos/%s/pulls/%d" % (base_url, full, pr["number"]),
        "html_url": "%s/%s/pull/%d" % (base_url, full, pr["number"]),
        "diff_url": "%s/%s/pull/%d.diff" % (base_url, full, pr["number"]),
        "patch_url": "%s/%s/pull/%d.patch" % (base_url, full, pr["number"]),
        "issue_url": "%s/api/v3/repos/%s/issues/%d" % (
            base_url, full, pr["number"]),
        "number": pr["number"],
        "state": pr["state"],
        "locked": False,
        "title": pr["title"],
        "body": pr.get("body") or "",
        "user": {"login": login, "id": 1, "type": "User"},
        "created_at": pr["created_at"],
        "updated_at": pr["updated_at"],
        "closed_at": pr.get("closed_at"),
        "merged_at": pr.get("merged_at"),
        "merge_commit_sha": pr.get("merge_commit_sha"),
        "merged": pr["merged"],
        "mergeable": mergeable,
        "mergeable_state": "clean" if mergeable else "dirty",
        "merged_by": None,
        "comments": 0,
        "review_comments": 0,
        "commits": 1,
        "additions": pr.get("additions", 0),
        "deletions": pr.get("deletions", 0),
        "changed_files": pr.get("changed_files", 0),
        "head": {"label": "%s:%s" % (login, pr["head_ref"]),
                 "ref": pr["head_ref"],
                 "sha": pr.get("head_sha") or ZERO,
                 "user": {"login": login, "id": 1, "type": "User"},
                 "repo": repo_json(r, base_url)},
        "base": {"label": "%s:%s" % (login, pr["base_ref"]),
                 "ref": pr["base_ref"],
                 "sha": pr.get("base_sha") or ZERO,
                 "user": {"login": login, "id": 1, "type": "User"},
                 "repo": repo_json(r, base_url)},
        "author_association": "OWNER",
        "auto_merge": None,
        "draft": False,
    }


def head_tree_files(r, pr):
    """{path: blob_sha} of the PR head tip, or {} if unknown."""
    sha = pr.get("head_sha")
    if not sha or sha not in r.objects:
        return {}
    tname, content = r.objects[sha]
    if tname != "commit":
        return {}
    tree, _p, _m = parse_commit(content)
    if not tree:
        return {}
    return {p: v[0] for p, v in flatten_tree(r.objects, tree).items()}


def tree_files_at(r, sha):
    if not sha or sha not in r.objects:
        return {}
    tname, content = r.objects[sha]
    if tname != "commit":
        return {}
    tree, _p, _m = parse_commit(content)
    if not tree:
        return {}
    return {p: v[0] for p, v in flatten_tree(r.objects, tree).items()}


def compute_mergeable(r, pr):
    if pr["state"] != "open":
        return False
    base_sha = pr.get("base_sha")
    head = head_tree_files(r, pr)
    if not head:
        return True  # nothing pushed yet: nothing to conflict with
    default_sha = r.head_sha(pr["base_ref"])
    if not base_sha or not default_sha or default_sha == base_sha:
        return True
    base = tree_files_at(r, base_sha)
    cur = tree_files_at(r, default_sha)
    paths = set(base) | set(head) | set(cur)
    for p in paths:
        b = base.get(p)
        h = head.get(p)
        c = cur.get(p)
        if h != b and c != b and h != c:
            return False
    return True


def make_squash_commit(r, pr):
    """Create the squash commit of pr onto its base branch; return sha."""
    head_files = head_tree_files(r, pr)
    if head_files:
        files = {p: (s, "100644") for p, s in head_files.items()}
        tree_sha = rebuild_tree(r.objects, files)
    else:
        base_sha = r.head_sha(pr["base_ref"])
        if base_sha and base_sha in r.objects:
            tree, _p, _m = parse_commit(r.objects[base_sha][1])
            tree_sha = tree
        else:
            tree_sha, _d = build_tree([])
            r.objects[tree_sha] = ("tree", _d)
    parent = r.head_sha(pr["base_ref"])
    parents = [parent] if parent else []
    msg = "%s (#%d)\n\n%s" % (pr["title"], pr["number"], pr.get("body") or "")
    sha = make_commit(r.objects, tree_sha, parents, msg, FORGE.next_ts())
    ref = "refs/heads/" + pr["base_ref"]
    r.refs[ref] = sha
    return sha

# ---------------------------------------------------------------- REST helpers

class ApiError(Exception):
    def __init__(self, status, message):
        super().__init__(message)
        self.status = status
        self.message = message


def parse_json_body(raw):
    """Return parsed object; {} for empty; raise ApiError 400 if malformed."""
    if raw is None or raw == b"":
        return {}
    try:
        val = json.loads(raw.decode("utf-8"))
    except Exception:
        raise ApiError(400, "Problems parsing JSON")
    if not isinstance(val, dict):
        raise ApiError(400, "Problems parsing JSON")
    return val


def page_link(base_url, path, query, page, per_page, total):
    """Link header value with rel=next when another page exists."""
    if page * per_page >= total:
        return None
    q = dict(query)
    q["page"] = [str(page + 1)]
    q["per_page"] = [str(per_page)]
    qs = "&".join("%s=%s" % (k, v[0]) for k, v in sorted(q.items()))
    return '<%s%s?%s>; rel="next"' % (base_url, path, qs)


def paginate(items, query):
    try:
        page = int(query.get("page", ["1"])[0])
    except ValueError:
        page = 1
    try:
        per_page = int(query.get("per_page", ["30"])[0])
    except ValueError:
        per_page = 30
    page = max(1, page)
    per_page = max(1, min(100, per_page))
    start = (page - 1) * per_page
    return items[start:start + per_page], page, per_page


def content_commit(r, branch, path, content_bytes, message, parent_sha=None):
    """Write one file into branch tip tree; return (blob_sha, commit_sha)."""
    blob_sha = git_hash("blob", content_bytes)
    r.objects[blob_sha] = ("blob", content_bytes)
    tip = r.head_sha(branch)
    files = {}
    if tip and tip in r.objects:
        tree, _p, _m = parse_commit(r.objects[tip][1])
        if tree:
            files = {p: v for p, v in flatten_tree(r.objects, tree).items()}
    files[path] = (blob_sha, "100644")
    tree_sha = rebuild_tree(r.objects, files)
    parents = [tip] if tip else []
    if parent_sha:
        parents = [parent_sha]
    commit_sha = make_commit(r.objects, tree_sha, parents, message,
                             FORGE.next_ts())
    r.refs["refs/heads/" + branch] = commit_sha
    return blob_sha, commit_sha


def delete_content_commit(r, branch, path, message):
    tip = r.head_sha(branch)
    files = {}
    if tip and tip in r.objects:
        tree, _p, _m = parse_commit(r.objects[tip][1])
        if tree:
            files = {p: v for p, v in flatten_tree(r.objects, tree).items()}
    if path not in files:
        return None
    del files[path]
    tree_sha = rebuild_tree(r.objects, files)
    parents = [tip] if tip else []
    commit_sha = make_commit(r.objects, tree_sha, parents, message,
                             FORGE.next_ts())
    r.refs["refs/heads/" + branch] = commit_sha
    return commit_sha


def resolve_ref_commit(r, ref):
    """ref may be a branch name, a full ref, or a sha -> commit sha or None."""
    if not ref:
        return r.head_sha()
    if ref in r.objects and r.objects[ref][0] == "commit":
        return ref
    if ref.startswith("refs/"):
        return r.refs.get(ref)
    return r.refs.get("refs/heads/" + ref)


# ---------------------------------------------------------------- REST routes

def handle_rest(method, seg, query, raw_body, base_url):
    """Return (status, extra_headers, json_obj). Raises ApiError."""
    # GET /api/v3/
    if not seg:
        if method != "GET":
            raise ApiError(404, "Not Found")
        return 200, {"X-OAuth-Scopes": "repo, user, gist"}, {}
    if seg == ["meta"]:
        if method != "GET":
            raise ApiError(404, "Not Found")
        return 200, {}, {"installed_version": VERSION,
                         "version": VERSION,
                         "git_hash": "forge-" + VERSION}
    if seg == ["user"]:
        if method == "GET":
            login = FORGE.owner_login()
            return 200, {}, {"login": login, "id": 1, "node_id": b64_node("User", 1),
                             "type": "User", "site_admin": False,
                             "name": login}
        raise ApiError(404, "Not Found")
    if seg == ["user", "repos"]:
        if method == "GET":
            repos = [repo_json(r, base_url) for r in FORGE.repos.values()]
            page_items, page, per_page = paginate(repos, query)
            extra = {}
            link = page_link(base_url, "/api/v3/user/repos", query, page,
                             per_page, len(repos))
            if link:
                extra["Link"] = link
            return 200, extra, page_items
        if method == "POST":
            body = parse_json_body(raw_body)
            name = body.get("name")
            if not name or not isinstance(name, str):
                raise ApiError(422, "Validation Failed: name is required")
            if name in FORGE.repos:
                raise ApiError(422, "Validation Failed: name already exists")
            owner = body.get("owner") or body.get("login")
            if owner:
                FORGE.learn_login(owner)
            r = Repo(FORGE.next_dbid(), name, FORGE.login,
                     body.get("description"), body.get("private", False),
                     body.get("default_branch") or "main")
            FORGE.repos[name] = r
            if body.get("auto_init"):
                tree_sha, tdata = build_tree([])
                r.objects[tree_sha] = ("tree", tdata)
                sha = make_commit(r.objects, tree_sha, [],
                                  "Initial commit", FORGE.next_ts())
                r.refs["refs/heads/" + r.default_branch] = sha
            return 201, {}, repo_json(r, base_url)
        raise ApiError(404, "Not Found")
    if len(seg) >= 3 and seg[0] == "repos":
        return handle_repo_rest(method, seg[1:], query, raw_body, base_url)
    raise ApiError(404, "Not Found")


def _need_repo(owner, name):
    r = FORGE.find_repo(owner, name)
    if r is None:
        raise ApiError(404, "Not Found")
    return r


def handle_repo_rest(method, seg, query, raw_body, base_url):
    owner, name = seg[0], seg[1]
    rest = seg[2:]
    if not rest:
        r = _need_repo(owner, name)
        if method == "GET":
            return 200, {}, repo_json(r, base_url)
        if method == "PATCH":
            body = parse_json_body(raw_body)
            if "description" in body:
                r.description = body["description"] or ""
            if "default_branch" in body and body["default_branch"]:
                r.default_branch = body["default_branch"]
            if "name" in body and body["name"] and body["name"] != r.name:
                del FORGE.repos[r.name]
                r.name = body["name"]
                FORGE.repos[r.name] = r
            return 200, {}, repo_json(r, base_url)
        if method == "DELETE":
            del FORGE.repos[r.name]
            return 204, {}, None
        raise ApiError(404, "Not Found")
    if rest[0] == "contents":
        return handle_contents(method, owner, name, rest[1:], query,
                               raw_body, base_url)
    if rest[0] == "labels":
        r = _need_repo(owner, name)
        if method == "GET":
            return 200, {}, list(r.labels.values())
        if method == "POST":
            body = parse_json_body(raw_body)
            lname = body.get("name")
            if not lname:
                raise ApiError(422, "Validation Failed: name is required")
            lab = {"name": lname,
                   "color": body.get("color") or "ededed",
                   "description": body.get("description") or ""}
            r.labels[lname] = lab
            return 201, {}, lab
        raise ApiError(404, "Not Found")
    if rest[0] == "issues":
        return handle_issues(method, owner, name, rest[1:], query,
                             raw_body, base_url)
    if rest[0] == "pulls":
        return handle_pulls(method, owner, name, rest[1:], query,
                            raw_body, base_url)
    if rest[0] == "branches":
        r = _need_repo(owner, name)
        if method == "GET" and len(rest) == 1:
            out = []
            for ref, sha in sorted(r.refs.items()):
                if ref.startswith("refs/heads/"):
                    out.append({"name": ref[len("refs/heads/"):],
                                "commit": {"sha": sha,
                                           "url": "%s/api/v3/repos/%s/%s/commits/%s"
                                           % (base_url, owner, name, sha)},
                                "protected": False})
            return 200, {}, out
        raise ApiError(404, "Not Found")
    if rest[0] == "commits":
        r = _need_repo(owner, name)
        if method == "GET" and len(rest) == 1:
            out = []
            sha = r.head_sha()
            seen = set()
            while sha and sha in r.objects and sha not in seen:
                seen.add(sha)
                tname, content = r.objects[sha]
                if tname != "commit":
                    break
                _t, parents, msg = parse_commit(content)
                out.append({"sha": sha, "commit": {"message": msg},
                            "author": {"login": owner},
                            "committer": {"login": owner},
                            "parents": [{"sha": p} for p in parents]})
                sha = parents[0] if parents else None
                if len(out) >= 100:
                    break
            return 200, {}, out
        if method == "GET" and len(rest) == 2:
            sha = rest[1]
            if sha not in r.objects or r.objects[sha][0] != "commit":
                raise ApiError(404, "Not Found")
            _t, parents, msg = parse_commit(r.objects[sha][1])
            return 200, {}, {"sha": sha, "commit": {"message": msg},
                             "parents": [{"sha": p} for p in parents]}
        raise ApiError(404, "Not Found")
    if rest[0] == "git" and len(rest) >= 2 and rest[1] == "refs":
        r = _need_repo(owner, name)
        if method == "GET":
            if len(rest) == 2:
                out = [{"ref": ref,
                        "object": {"sha": sha, "type": "commit"}}
                       for ref, sha in sorted(r.refs.items())]
                return 200, {}, out
            refname = "/".join(rest[2:])
            if not refname.startswith("refs/"):
                refname = "refs/" + refname
            sha = r.refs.get(refname)
            if sha is None:
                raise ApiError(404, "Not Found")
            return 200, {}, {"ref": refname,
                             "object": {"sha": sha, "type": "commit"}}
        raise ApiError(404, "Not Found")
    raise ApiError(404, "Not Found")


def handle_contents(method, owner, name, rest, query, raw_body, base_url):
    r = _need_repo(owner, name)
    path = "/".join(unquote(p) for p in rest)
    branch = None
    if method in ("PUT", "DELETE"):
        body = parse_json_body(raw_body)
        branch = body.get("branch") or r.default_branch
    else:
        branch = (query.get("ref", [None])[0]) or r.default_branch
    if method == "GET":
        tip = r.head_sha(branch)
        if tip is None:
            raise ApiError(404, "Not Found")
        tree, _p, _m = parse_commit(r.objects[tip][1])
        files = flatten_tree(r.objects, tree) if tree else {}
        if path == "":
            out = []
            seen = set()
            for p in sorted(files):
                first = p.split("/")[0]
                if first in seen:
                    continue
                seen.add(first)
                is_dir = "/" in p
                sha = files[p][0] if not is_dir else None
                out.append({"type": "dir" if is_dir else "file",
                            "name": first, "path": first,
                            "sha": sha or "",
                            "size": 0 if is_dir else 0,
                            "url": "%s/api/v3/repos/%s/%s/contents/%s"
                            % (base_url, owner, name, first)})
            return 200, {}, out
        if path not in files:
            raise ApiError(404, "Not Found")
        blob_sha, _mode = files[path]
        content = r.objects[blob_sha][1]
        return 200, {}, {
            "type": "file", "encoding": "base64",
            "size": len(content), "name": path.rsplit("/", 1)[-1],
            "path": path, "content": base64.b64encode(content).decode(),
            "sha": blob_sha,
            "url": "%s/api/v3/repos/%s/%s/contents/%s"
            % (base_url, owner, name, path),
            "html_url": "%s/%s/%s/blob/%s/%s"
            % (base_url, owner, name, branch, path),
            "git_url": "%s/api/v3/repos/%s/%s/git/blobs/%s"
            % (base_url, owner, name, blob_sha),
            "download_url": "%s/api/v3/repos/%s/%s/contents/%s?ref=%s"
            % (base_url, owner, name, path, branch),
            "_links": {"self": "%s/api/v3/repos/%s/%s/contents/%s"
                       % (base_url, owner, name, path)}}
    if method == "PUT":
        try:
            content_bytes = base64.b64decode(body.get("content") or "", validate=False)
        except Exception:
            raise ApiError(400, "Invalid base64 content")
        tip = r.head_sha(branch)
        existed = False
        cur_sha = None
        if tip and tip in r.objects:
            tree, _p, _m = parse_commit(r.objects[tip][1])
            files = flatten_tree(r.objects, tree) if tree else {}
            if path in files:
                existed = True
                cur_sha = files[path][0]
        if existed:
            if not body.get("sha"):
                raise ApiError(409, "sha is required to update a file")
            if body.get("sha") != cur_sha:
                raise ApiError(409, "sha does not match the current file")
            blob_sha, commit_sha = content_commit(
                r, branch, path, content_bytes,
                body.get("message") or "Update %s" % path)
            return 200, {}, {"content": {"name": path.rsplit("/", 1)[-1],
                                         "path": path, "sha": blob_sha,
                                         "size": len(content_bytes),
                                         "type": "file"},
                             "commit": {"sha": commit_sha,
                                        "message": body.get("message") or ""}}
        blob_sha, commit_sha = content_commit(
            r, branch, path, content_bytes,
            body.get("message") or "Create %s" % path)
        return 201, {}, {"content": {"name": path.rsplit("/", 1)[-1],
                                     "path": path, "sha": blob_sha,
                                     "size": len(content_bytes),
                                     "type": "file"},
                         "commit": {"sha": commit_sha,
                                    "message": body.get("message") or ""}}
    if method == "DELETE":
        tip = r.head_sha(branch)
        if tip is None:
            raise ApiError(404, "Not Found")
        tree, _p, _m = parse_commit(r.objects[tip][1])
        files = flatten_tree(r.objects, tree) if tree else {}
        if path not in files:
            raise ApiError(404, "Not Found")
        if body.get("sha") and body.get("sha") != files[path][0]:
            raise ApiError(409, "sha does not match the current file")
        commit_sha = delete_content_commit(
            r, branch, path, body.get("message") or "Delete %s" % path)
        return 200, {}, {"commit": {"sha": commit_sha,
                                    "message": body.get("message") or ""}}
    raise ApiError(404, "Not Found")

def handle_issues(method, owner, name, rest, query, raw_body, base_url):
    r = _need_repo(owner, name)
    if not rest:
        if method == "GET":
            state = (query.get("state", ["open"])[0] or "open").lower()
            items = [issue_json(r, i, base_url)
                     for _n, i in sorted(r.issues.items())
                     if state == "all" or i["state"] == state]
            items.reverse()
            page_items, page, per_page = paginate(items, query)
            extra = {}
            link = page_link(base_url, "/api/v3/repos/%s/%s/issues"
                             % (owner, name), query, page, per_page,
                             len(items))
            if link:
                extra["Link"] = link
            return 200, extra, page_items
        if method == "POST":
            body = parse_json_body(raw_body)
            title = body.get("title")
            if not title:
                raise ApiError(422, "Validation Failed: title is required")
            labels = body.get("labels") or []
            if isinstance(labels, str):
                labels = [labels]
            for lab in labels:
                nm = lab["name"] if isinstance(lab, dict) else lab
                if nm not in r.labels:
                    raise ApiError(422, "Validation Failed: label '%s' "
                                        "does not exist" % nm)
            r.counter += 1
            num = r.counter
            dbid = FORGE.next_dbid()
            iss = {"dbid": dbid, "number": num, "title": title,
                   "body": body.get("body") or "",
                   "state": "open",
                   "labels": [l["name"] if isinstance(l, dict) else l
                              for l in labels],
                   "created_at": FIXED_ISO, "updated_at": FIXED_ISO,
                   "closed_at": None, "comments": []}
            r.issues[num] = iss
            return 201, {}, issue_json(r, iss, base_url)
        raise ApiError(404, "Not Found")
    try:
        num = int(rest[0])
    except ValueError:
        raise ApiError(404, "Not Found")
    iss = r.issues.get(num)
    if iss is None:
        raise ApiError(404, "Not Found")
    if len(rest) == 1:
        if method == "GET":
            return 200, {}, issue_json(r, iss, base_url)
        if method == "PATCH":
            body = parse_json_body(raw_body)
            if "title" in body and body["title"]:
                iss["title"] = body["title"]
            if "body" in body:
                iss["body"] = body["body"] or ""
            if "state" in body and body["state"] in ("open", "closed"):
                iss["state"] = body["state"]
                iss["closed_at"] = FIXED_ISO if body["state"] == "closed" else None
            if "labels" in body:
                labs = body["labels"] or []
                for lab in labs:
                    nm = lab["name"] if isinstance(lab, dict) else lab
                    if nm not in r.labels:
                        raise ApiError(422, "Validation Failed: label '%s' "
                                            "does not exist" % nm)
                iss["labels"] = [l["name"] if isinstance(l, dict) else l
                                 for l in labs]
            return 200, {}, issue_json(r, iss, base_url)
        raise ApiError(404, "Not Found")
    if rest[1] == "comments":
        if method == "GET":
            return 200, {}, iss.get("comments", [])
        if method == "POST":
            body = parse_json_body(raw_body)
            c = {"id": FORGE.next_dbid(),
                 "body": body.get("body") or "",
                 "user": {"login": r.owner or FORGE.owner_login()},
                 "created_at": FIXED_ISO, "updated_at": FIXED_ISO}
            iss.setdefault("comments", []).append(c)
            return 201, {}, c
        raise ApiError(404, "Not Found")
    raise ApiError(404, "Not Found")


def _create_pr(r, title, head_ref, base_ref, body_text):
    r.counter += 1
    num = r.counter
    dbid = FORGE.next_dbid()
    base_sha = r.head_sha(base_ref)
    head_sha = r.head_sha(head_ref)
    pr = {"dbid": dbid, "number": num, "title": title,
          "body": body_text or "", "state": "open",
          "head_ref": head_ref, "base_ref": base_ref,
          "head_sha": head_sha, "base_sha": base_sha,
          "merged": False, "merge_commit_sha": None,
          "created_at": FIXED_ISO, "updated_at": FIXED_ISO,
          "closed_at": None, "merged_at": None,
          "additions": 0, "deletions": 0, "changed_files": 0}
    if head_sha and base_sha and head_sha in r.objects and base_sha in r.objects:
        hf = tree_files_at(r, head_sha)
        bf = tree_files_at(r, base_sha)
        changed = [p for p in set(hf) | set(bf) if hf.get(p) != bf.get(p)]
        pr["changed_files"] = len(changed)
        pr["additions"] = len([p for p in changed if p not in bf])
        pr["deletions"] = len([p for p in changed if p not in hf])
    r.pulls[num] = pr
    return pr


def handle_pulls(method, owner, name, rest, query, raw_body, base_url):
    r = _need_repo(owner, name)
    if not rest:
        if method == "GET":
            state = (query.get("state", ["open"])[0] or "open").lower()
            items = [pr_json(r, p, base_url)
                     for _n, p in sorted(r.pulls.items())
                     if state == "all" or p["state"] == state]
            items.reverse()
            page_items, page, per_page = paginate(items, query)
            return 200, {}, page_items
        if method == "POST":
            body = parse_json_body(raw_body)
            title = body.get("title")
            head = body.get("head")
            base = body.get("base") or r.default_branch
            if not title or not head:
                raise ApiError(422, "Validation Failed: title and head "
                                    "are required")
            pr = _create_pr(r, title, head, base, body.get("body"))
            return 201, {}, pr_json(r, pr, base_url)
        raise ApiError(404, "Not Found")
    try:
        num = int(rest[0])
    except ValueError:
        raise ApiError(404, "Not Found")
    pr = r.pulls.get(num)
    if pr is None:
        raise ApiError(404, "Not Found")
    if len(rest) == 1:
        if method == "GET":
            return 200, {}, pr_json(r, pr, base_url)
        if method == "PATCH":
            body = parse_json_body(raw_body)
            if "title" in body and body["title"]:
                pr["title"] = body["title"]
            if "body" in body:
                pr["body"] = body["body"] or ""
            if body.get("state") == "closed":
                pr["state"] = "closed"
                pr["closed_at"] = FIXED_ISO
            return 200, {}, pr_json(r, pr, base_url)
        raise ApiError(404, "Not Found")
    if len(rest) == 2 and rest[1] == "merge":
        if method == "GET":
            if pr["merged"]:
                return 204, {}, None
            raise ApiError(404, "Not Found")
        if method == "PUT":
            _body = parse_json_body(raw_body)
            if pr["state"] != "open":
                if pr["merged"]:
                    raise ApiError(405, "Pull Request is already merged")
                raise ApiError(405, "Pull Request is closed")
            if not compute_mergeable(r, pr):
                raise ApiError(405, "Pull Request is not mergeable")
            sha = make_squash_commit(r, pr)
            pr["state"] = "closed"
            pr["merged"] = True
            pr["merge_commit_sha"] = sha
            pr["merged_at"] = FIXED_ISO
            pr["closed_at"] = FIXED_ISO
            return 200, {}, {"sha": sha, "merged": True,
                             "message": "Pull Request successfully merged"}
        raise ApiError(404, "Not Found")
    raise ApiError(404, "Not Found")

# ---------------------------------------------------------------- GraphQL

_GQL_PUNCT = set("{}()[]:!,$=@")
_GQL_NAME_RE = re.compile(r"[_A-Za-z][_0-9A-Za-z]*")


def gql_tokenize(src):
    toks = []
    i = 0
    n = len(src)
    while i < n:
        c = src[i]
        if c in " \t\r\n,":
            i += 1
            continue
        if c == "#":
            while i < n and src[i] != "\n":
                i += 1
            continue
        if src.startswith("...", i):
            toks.append(("PUNCT", "..."))
            i += 3
            continue
        if c in _GQL_PUNCT:
            toks.append(("PUNCT", c))
            i += 1
            continue
        if c == '"':
            if src.startswith('"""', i):
                j = src.find('"""', i + 3)
                if j < 0:
                    j = n - 3
                toks.append(("STRING", src[i + 3:j]))
                i = j + 3
                continue
            j = i + 1
            out = []
            while j < n and src[j] != '"':
                if src[j] == "\\" and j + 1 < n:
                    esc = src[j + 1]
                    out.append({"n": "\n", "t": "\t", "r": "\r",
                                '"': '"', "\\": "\\", "/": "/"}.get(esc, esc))
                    j += 2
                else:
                    out.append(src[j])
                    j += 1
            toks.append(("STRING", "".join(out)))
            i = j + 1
            continue
        m = _GQL_NAME_RE.match(src, i)
        if m:
            toks.append(("NAME", m.group(0)))
            i = m.end()
            continue
        if c.isdigit() or (c == "-" and i + 1 < n and src[i + 1].isdigit()):
            j = i
            if src[j] == "-":
                j += 1
            while j < n and src[j].isdigit():
                j += 1
            is_float = False
            if j < n and src[j] == ".":
                is_float = True
                j += 1
                while j < n and src[j].isdigit():
                    j += 1
            if j < n and src[j] in "eE":
                is_float = True
                j += 1
                if j < n and src[j] in "+-":
                    j += 1
                while j < n and src[j].isdigit():
                    j += 1
            toks.append(("FLOAT" if is_float else "INT", src[i:j]))
            i = j
            continue
        raise ValueError("unexpected char %r in query" % c)
    toks.append(("EOF", ""))
    return toks


class GQLParser:
    def __init__(self, src):
        self.toks = gql_tokenize(src)
        self.pos = 0

    def peek(self):
        return self.toks[self.pos]

    def next(self):
        t = self.toks[self.pos]
        self.pos += 1
        return t

    def expect_punct(self, v):
        k, val = self.next()
        if (k, val) != ("PUNCT", v):
            raise ValueError("expected %s got %r" % (v, val))

    def skip_punct(self, v):
        if self.peek() == ("PUNCT", v):
            self.pos += 1
            return True
        return False

    def parse_document(self):
        ops = []
        frags = {}
        while self.peek()[0] != "EOF":
            if self.peek() == ("NAME", "fragment"):
                self.next()
                _k, name = self.next()
                _k, on = self.next()  # "on"
                _k, tc = self.next()
                sel = self.parse_selection_set()
                frags[name] = {"type_condition": tc, "sel": sel}
            else:
                ops.append(self.parse_operation())
        return {"operations": ops, "fragments": frags}

    def parse_operation(self):
        otype = "query"
        name = None
        if self.peek()[0] == "NAME" and self.peek()[1] in (
                "query", "mutation", "subscription"):
            otype = self.next()[1]
            if self.peek()[0] == "NAME":
                name = self.next()[1]
        elif self.peek()[0] == "NAME":
            # named shorthand? treat as operation name with query type
            name = self.next()[1]
        if self.peek() == ("PUNCT", "("):
            self.parse_var_defs()
        self.parse_directives()
        sel = self.parse_selection_set()
        return {"type": otype, "name": name, "sel": sel}

    def parse_var_defs(self):
        self.expect_punct("(")
        depth = 1
        while depth:
            k, v = self.next()
            if (k, v) == ("PUNCT", "("):
                depth += 1
            elif (k, v) == ("PUNCT", ")"):
                depth -= 1
            elif k == "EOF":
                raise ValueError("unterminated var defs")

    def parse_directives(self):
        dirs = []
        while self.peek() == ("PUNCT", "@"):
            self.next()
            _k, name = self.next()
            args = {}
            if self.peek() == ("PUNCT", "("):
                args = self.parse_arguments()
            dirs.append((name, args))
        return dirs

    def parse_selection_set(self):
        self.expect_punct("{")
        sels = []
        while self.peek() != ("PUNCT", "}"):
            if self.peek()[0] == "EOF":
                raise ValueError("unterminated selection set")
            sels.append(self.parse_selection())
        self.expect_punct("}")
        return sels

    def parse_selection(self):
        if self.peek() == ("PUNCT", "..."):
            self.next()
            if self.peek() == ("NAME", "on"):
                self.next()
                _k, tc = self.next()
                dirs = self.parse_directives()
                sel = self.parse_selection_set()
                return {"kind": "inline", "type_condition": tc,
                        "sel": sel, "directives": dirs}
            _k, name = self.next()
            dirs = self.parse_directives()
            return {"kind": "fragment", "name": name, "directives": dirs}
        # field: [alias :] name [(args)] [directives] [selection set]
        _k, first = self.next()
        alias = None
        name = first
        if self.peek() == ("PUNCT", ":"):
            self.next()
            alias = first
            _k, name = self.next()
        args = {}
        if self.peek() == ("PUNCT", "("):
            args = self.parse_arguments()
        dirs = self.parse_directives()
        sel = None
        if self.peek() == ("PUNCT", "{"):
            sel = self.parse_selection_set()
        return {"kind": "field", "name": name, "alias": alias or name,
                "args": args, "sel": sel, "directives": dirs}

    def parse_arguments(self):
        self.expect_punct("(")
        args = {}
        while self.peek() != ("PUNCT", ")"):
            _k, name = self.next()
            self.expect_punct(":")
            args[name] = self.parse_value()
        self.expect_punct(")")
        return args

    def parse_value(self):
        k, v = self.next()
        if (k, v) == ("PUNCT", "$"):
            _k, name = self.next()
            return ("var", name)
        if k == "STRING":
            return v
        if k == "INT":
            return int(v)
        if k == "FLOAT":
            return float(v)
        if (k, v) == ("PUNCT", "["):
            out = []
            while self.peek() != ("PUNCT", "]"):
                out.append(self.parse_value())
            self.expect_punct("]")
            return out
        if (k, v) == ("PUNCT", "{"):
            out = {}
            while self.peek() != ("PUNCT", "}"):
                _k, name = self.next()
                self.expect_punct(":")
                out[name] = self.parse_value()
            self.expect_punct("}")
            return out
        if k == "NAME":
            if v == "true":
                return True
            if v == "false":
                return False
            if v == "null":
                return None
            return ("enum", v)
        raise ValueError("unexpected value token %r" % (v,))


def gql_resolve_value(val, variables):
    if isinstance(val, tuple) and val and val[0] == "var":
        return variables.get(val[1])
    if isinstance(val, tuple) and val and val[0] == "enum":
        return val[1]
    if isinstance(val, list):
        return [gql_resolve_value(v, variables) for v in val]
    if isinstance(val, dict):
        return {k: gql_resolve_value(v, variables) for k, v in val.items()}
    return val

# GraphQL introspection data: type -> {kind, fields, enumValues}
def _t(kind, name=None, of=None):
    return {"kind": kind, "name": name, "ofType": of}


def _f(name, type_ref):
    return {"name": name, "description": None, "args": [],
            "type": type_ref, "isDeprecated": False,
            "deprecationReason": None}


_S = lambda: _t("SCALAR", "String")
_I = lambda: _t("SCALAR", "Int")
_B = lambda: _t("SCALAR", "Boolean")
_ID = lambda: _t("SCALAR", "ID")
_NN = lambda inner: _t("NON_NULL", None, inner)
_LS = lambda inner: _t("LIST", None, inner)
_OBJ = lambda n: _t("OBJECT", n)
_ENUM = lambda n: _t("ENUM", n)

GQL_TYPES = {
    "Query": {"kind": "OBJECT", "fields": [
        _f("repository", _OBJ("Repository")),
        _f("viewer", _OBJ("User")),
        _f("search", _OBJ("SearchResultItemConnection")),
        _f("node", _OBJ("Node")),
        _f("__type", _OBJ("__Type")),
        _f("__schema", _OBJ("__Schema")),
    ]},
    "Mutation": {"kind": "OBJECT", "fields": [
        _f("createPullRequest", _OBJ("CreatePullRequestPayload")),
        _f("createIssue", _OBJ("CreateIssuePayload")),
    ]},
    "Repository": {"kind": "OBJECT", "fields": [
        _f("id", _NN(_ID())), _f("databaseId", _I()),
        _f("name", _S()), _f("nameWithOwner", _S()),
        _f("owner", _OBJ("User")),
        _f("defaultBranchRef", _OBJ("Ref")),
        _f("viewerPermission", _S()),
        _f("hasIssuesEnabled", _B()),
        _f("description", _S()), _f("url", _S()),
        _f("createdAt", _S()), _f("updatedAt", _S()),
        _f("isPrivate", _B()), _f("forkCount", _I()),
        _f("stargazerCount", _I()),
        _f("issue", _OBJ("Issue")),
        _f("issues", _OBJ("IssueConnection")),
        _f("pullRequest", _OBJ("PullRequest")),
        _f("pullRequests", _OBJ("PullRequestConnection")),
    ]},
    "Issue": {"kind": "OBJECT", "fields": [
        _f("id", _NN(_ID())), _f("number", _I()),
        _f("title", _S()), _f("state", _ENUM("IssueState")),
        _f("body", _S()), _f("url", _S()),
        _f("createdAt", _S()), _f("updatedAt", _S()),
        _f("closedAt", _S()), _f("author", _OBJ("User")),
        _f("labels", _LS(_OBJ("Label"))),
        _f("comments", _OBJ("IssueCommentConnection")),
        _f("repository", _OBJ("Repository")),
    ]},
    "PullRequest": {"kind": "OBJECT", "fields": [
        _f("id", _NN(_ID())), _f("number", _I()),
        _f("headRefName", _S()), _f("baseRefName", _S()),
        _f("mergeable", _B()), _f("state", _ENUM("PullRequestState")),
        _f("merged", _B()),
        _f("files", _OBJ("PullRequestChangedFileConnection")),
        _f("title", _S()), _f("body", _S()),
        _f("headRef", _OBJ("Ref")), _f("baseRef", _OBJ("Ref")),
        _f("author", _OBJ("User")),
        _f("createdAt", _S()), _f("updatedAt", _S()),
        _f("closedAt", _S()), _f("mergedAt", _S()),
        _f("mergeCommit", _OBJ("Commit")),
        _f("additions", _I()), _f("deletions", _I()),
        _f("changedFiles", _I()),
    ]},
    "User": {"kind": "OBJECT", "fields": [
        _f("id", _NN(_ID())), _f("login", _S()), _f("name", _S()),
    ]},
    "Ref": {"kind": "OBJECT", "fields": [
        _f("name", _S()), _f("target", _OBJ("Commit")),
    ]},
    "Commit": {"kind": "OBJECT", "fields": [
        _f("oid", _S()), _f("message", _S()),
        _f("abbreviatedOid", _S()),
    ]},
    "Label": {"kind": "OBJECT", "fields": [
        _f("name", _S()), _f("color", _S()), _f("description", _S()),
    ]},
    "IssueConnection": {"kind": "OBJECT", "fields": [
        _f("nodes", _LS(_OBJ("Issue"))),
        _f("edges", _LS(_OBJ("IssueEdge"))),
        _f("totalCount", _I()), _f("pageInfo", _OBJ("PageInfo")),
    ]},
    "IssueEdge": {"kind": "OBJECT", "fields": [
        _f("node", _OBJ("Issue")), _f("cursor", _S()),
    ]},
    "PullRequestConnection": {"kind": "OBJECT", "fields": [
        _f("nodes", _LS(_OBJ("PullRequest"))),
        _f("edges", _LS(_OBJ("PullRequestEdge"))),
        _f("totalCount", _I()), _f("pageInfo", _OBJ("PageInfo")),
    ]},
    "PullRequestEdge": {"kind": "OBJECT", "fields": [
        _f("node", _OBJ("PullRequest")), _f("cursor", _S()),
    ]},
    "PullRequestChangedFileConnection": {"kind": "OBJECT", "fields": [
        _f("nodes", _LS(_OBJ("PullRequestChangedFile"))),
        _f("totalCount", _I()), _f("pageInfo", _OBJ("PageInfo")),
    ]},
    "PullRequestChangedFile": {"kind": "OBJECT", "fields": [
        _f("path", _S()),
    ]},
    "IssueCommentConnection": {"kind": "OBJECT", "fields": [
        _f("nodes", _LS(_OBJ("IssueComment"))),
        _f("totalCount", _I()),
    ]},
    "IssueComment": {"kind": "OBJECT", "fields": [
        _f("id", _NN(_ID())), _f("body", _S()),
        _f("author", _OBJ("User")),
    ]},
    "PageInfo": {"kind": "OBJECT", "fields": [
        _f("hasNextPage", _B()), _f("hasPreviousPage", _B()),
        _f("startCursor", _S()), _f("endCursor", _S()),
    ]},
    "SearchResultItemConnection": {"kind": "OBJECT", "fields": [
        _f("nodes", _LS(_OBJ("Issue"))),
        _f("edges", _LS(_OBJ("IssueEdge"))),
        _f("totalCount", _I()), _f("issueCount", _I()),
        _f("pageInfo", _OBJ("PageInfo")),
    ]},
    "CreatePullRequestPayload": {"kind": "OBJECT", "fields": [
        _f("pullRequest", _OBJ("PullRequest")),
        _f("clientMutationId", _S()),
    ]},
    "CreateIssuePayload": {"kind": "OBJECT", "fields": [
        _f("issue", _OBJ("Issue")),
        _f("clientMutationId", _S()),
    ]},
    "SearchType": {"kind": "ENUM", "fields": [],
                   "enumValues": [{"name": "ISSUE"}, {"name": "REPOSITORY"},
                                  {"name": "USER"}, {"name": "DISCUSSION"}]},
    "IssueState": {"kind": "ENUM", "fields": [],
                   "enumValues": [{"name": "OPEN"}, {"name": "CLOSED"}]},
    "PullRequestState": {"kind": "ENUM", "fields": [],
                         "enumValues": [{"name": "OPEN"}, {"name": "CLOSED"},
                                        {"name": "MERGED"}]},
    "OrderDirection": {"kind": "ENUM", "fields": [],
                       "enumValues": [{"name": "ASC"}, {"name": "DESC"}]},
    "IssueOrderField": {"kind": "ENUM", "fields": [],
                        "enumValues": [{"name": "CREATED_AT"},
                                       {"name": "UPDATED_AT"},
                                       {"name": "COMMENTS"},
                                       {"name": "NUMBER"}]},
    "IssueOrder": {"kind": "INPUT_OBJECT", "fields": []},
    "String": {"kind": "SCALAR", "fields": []},
    "Int": {"kind": "SCALAR", "fields": []},
    "Boolean": {"kind": "SCALAR", "fields": []},
    "ID": {"kind": "SCALAR", "fields": []},
    "Node": {"kind": "INTERFACE", "fields": [_f("id", _NN(_ID()))]},
    "__Type": {"kind": "OBJECT", "fields": []},
    "__Schema": {"kind": "OBJECT", "fields": []},
}


def _type_desc(name):
    info = GQL_TYPES.get(name)
    if info is None:
        return None
    return {"name": name, "kind": info["kind"], "description": None,
            "fields": info.get("fields") or None,
            "enumValues": info.get("enumValues") or None,
            "inputFields": None, "interfaces": [],
            "possibleTypes": None, "specifiedByURL": None}


def _user_obj(login):
    return {"__gql_type": "User", "login": login, "id": 1}


def _repo_obj(r):
    return {"__gql_type": "Repository", "_repo": r}


def _issue_obj(r, iss):
    return {"__gql_type": "Issue", "_repo": r, "_issue": iss}


def _pr_obj(r, pr):
    return {"__gql_type": "PullRequest", "_repo": r, "_pr": pr}


def _page_info(has_next):
    return {"__gql_type": "PageInfo", "has_next": has_next,
            "end_cursor": None, "start_cursor": None}


def _issue_conn(r, issues):
    return {"__gql_type": "IssueConnection", "_repo": r,
            "_items": [_issue_obj(r, i) for i in issues],
            "total": len(issues)}


def _pr_conn(r, prs):
    return {"__gql_type": "PullRequestConnection", "_repo": r,
            "_items": [_pr_obj(r, p) for p in prs], "total": len(prs)}


def _sort_issues(issues, args):
    order = args.get("orderBy") or {}
    direction = (order.get("direction") or "DESC").upper()
    states = args.get("states")
    out = list(issues)
    if states:
        wanted = set(s.upper() for s in states)
        out = [i for i in out if i["state"].upper() in wanted]
    out.sort(key=lambda i: i["number"], reverse=(direction == "DESC"))
    first = args.get("first")
    if isinstance(first, int) and first >= 0:
        out = out[:first]
    return out


def _sort_prs(prs, args):
    order = args.get("orderBy") or {}
    direction = (order.get("direction") or "DESC").upper()
    states = args.get("states")
    out = list(prs)
    if states:
        wanted = set(s.upper() for s in states)
        def _st(p):
            if p["merged"]:
                return "MERGED"
            return p["state"].upper()
        out = [p for p in out if _st(p) in wanted]
    out.sort(key=lambda p: p["number"], reverse=(direction == "DESC"))
    first = args.get("first")
    if isinstance(first, int) and first >= 0:
        out = out[:first]
    return out


def _decode_node_id(nid):
    """node id -> (kind, int) or None."""
    if not isinstance(nid, str):
        return None
    if nid.startswith("R_"):
        try:
            return ("Repository", int(nid[2:]))
        except ValueError:
            return None
    try:
        raw = base64.b64decode(nid.encode()).decode()
    except Exception:
        return None
    if ":" in raw:
        kind, num = raw.split(":", 1)
        try:
            return kind, int(num)
        except ValueError:
            return None
    return None


def _find_by_dbid(kind, dbid):
    for r in FORGE.repos.values():
        if kind == "Repository" and r.dbid == dbid:
            return _repo_obj(r)
        if kind == "Issue":
            for iss in r.issues.values():
                if iss["dbid"] == dbid:
                    return _issue_obj(r, iss)
        if kind == "PullRequest":
            for pr in r.pulls.values():
                if pr["dbid"] == dbid:
                    return _pr_obj(r, pr)
    return None


def _changed_paths(r, pr):
    hf = tree_files_at(r, pr.get("head_sha"))
    bf = tree_files_at(r, pr.get("base_sha"))
    if not hf and not bf:
        return []
    return sorted(set(hf) | set(bf) - set(hf) & set(bf) |
                  {p for p in set(hf) & set(bf) if hf[p] != bf[p]})


# field resolvers: (type_name, field) -> fn(obj, args) -> (value, gql_type)
def _gql_field(typename, field, obj, args):
    if typename == "Query":
        if field == "repository":
            r = FORGE.find_repo(args.get("owner"), args.get("name"))
            return (_repo_obj(r) if r else None), "Repository"
        if field == "viewer":
            return _user_obj(FORGE.owner_login()), "User"
        if field == "search":
            q = (args.get("query") or "").lower()
            words = [w for w in re.split(r"\s+", q) if len(w) > 2
                     and not w.startswith("repo:")]
            found = []
            for r in FORGE.repos.values():
                for iss in r.issues.values():
                    hay = (iss["title"] + " " + (iss.get("body") or "")).lower()
                    if not words or any(w in hay for w in words):
                        found.append(_issue_obj(r, iss))
            first = args.get("first")
            if isinstance(first, int) and first >= 0:
                found = found[:first]
            return ({"__gql_type": "SearchResultItemConnection",
                     "_items": found, "total": len(found)}, 
                    "SearchResultItemConnection")
        if field == "node":
            dec = _decode_node_id(args.get("id"))
            if dec is None:
                return None, "Node"
            kind, dbid = dec
            obj2 = _find_by_dbid(kind, dbid)
            return obj2, (obj2 or {}).get("__gql_type", "Node")
        raise KeyError(field)
    if typename == "Mutation":
        if field == "createPullRequest":
            inp = args.get("input") or {}
            dec = _decode_node_id(inp.get("repositoryId"))
            repo_obj = None
            if dec is not None:
                repo_obj = _find_by_dbid("Repository", dec[1])
            if repo_obj is None:
                return ({"__gql_type": "CreatePullRequestPayload",
                         "pullRequest": None,
                         "clientMutationId": inp.get("clientMutationId")},
                        "CreatePullRequestPayload")
            r = repo_obj["_repo"]
            pr = _create_pr(r, inp.get("title") or "PR",
                            inp.get("headRefName") or r.default_branch,
                            inp.get("baseRefName") or r.default_branch,
                            inp.get("body"))
            return ({"__gql_type": "CreatePullRequestPayload",
                     "pullRequest": _pr_obj(r, pr),
                     "clientMutationId": inp.get("clientMutationId")},
                    "CreatePullRequestPayload")
        if field == "createIssue":
            inp = args.get("input") or {}
            dec = _decode_node_id(inp.get("repositoryId"))
            repo_obj = None
            if dec is not None:
                repo_obj = _find_by_dbid("Repository", dec[1])
            if repo_obj is None:
                return ({"__gql_type": "CreateIssuePayload",
                         "issue": None,
                         "clientMutationId": inp.get("clientMutationId")},
                        "CreateIssuePayload")
            r = repo_obj["_repo"]
            r.counter += 1
            num = r.counter
            iss = {"dbid": FORGE.next_dbid(), "number": num,
                   "title": inp.get("title") or "Issue",
                   "body": inp.get("body") or "", "state": "open",
                   "labels": [], "created_at": FIXED_ISO,
                   "updated_at": FIXED_ISO, "closed_at": None,
                   "comments": []}
            r.issues[num] = iss
            return ({"__gql_type": "CreateIssuePayload",
                     "issue": _issue_obj(r, iss),
                     "clientMutationId": inp.get("clientMutationId")},
                    "CreateIssuePayload")
        raise KeyError(field)
    if typename == "Repository":
        r = obj["_repo"]
        login = r.owner or FORGE.owner_login()
        if field == "id":
            return b64_node("Repository", r.dbid), None
        if field == "databaseId":
            return r.dbid, None
        if field == "name":
            return r.name, None
        if field == "nameWithOwner":
            return "%s/%s" % (login, r.name), None
        if field == "owner":
            return _user_obj(login), "User"
        if field == "defaultBranchRef":
            return ({"__gql_type": "Ref", "name": r.default_branch,
                     "_repo": r}, "Ref")
        if field == "viewerPermission":
            return "ADMIN", None
        if field == "hasIssuesEnabled":
            return True, None
        if field == "description":
            return r.description, None
        if field == "url":
            return "https://example.invalid/%s/%s" % (login, r.name), None
        if field == "createdAt" or field == "updatedAt":
            return FIXED_ISO, None
        if field == "isPrivate":
            return r.private, None
        if field == "forkCount" or field == "stargazerCount":
            return 0, None
        if field == "issue":
            iss = r.issues.get(args.get("number"))
            return (_issue_obj(r, iss) if iss else None), "Issue"
        if field == "issues":
            return _issue_conn(r, _sort_issues(list(r.issues.values()), args)), "IssueConnection"
        if field == "pullRequest":
            pr = r.pulls.get(args.get("number"))
            return (_pr_obj(r, pr) if pr else None), "PullRequest"
        if field == "pullRequests":
            return _pr_conn(r, _sort_prs(list(r.pulls.values()), args)), "PullRequestConnection"
        raise KeyError(field)
    if typename == "Issue":
        r, iss = obj["_repo"], obj["_issue"]
        if field == "id":
            return b64_node("Issue", iss["dbid"]), None
        if field == "number":
            return iss["number"], None
        if field == "title":
            return iss["title"], None
        if field == "state":
            return iss["state"].upper(), None
        if field == "body":
            return iss.get("body") or "", None
        if field == "url":
            login = r.owner or FORGE.owner_login()
            return "https://example.invalid/%s/%s/issues/%d" % (
                login, r.name, iss["number"]), None
        if field == "createdAt":
            return iss["created_at"], None
        if field == "updatedAt":
            return iss["updated_at"], None
        if field == "closedAt":
            return iss.get("closed_at"), None
        if field == "author":
            return _user_obj(r.owner or FORGE.owner_login()), "User"
        if field == "labels":
            return [{"__gql_type": "Label", **r.labels[nm]}
                    for nm in iss["labels"] if nm in r.labels], "Label"
        if field == "comments":
            nodes = [{"__gql_type": "IssueComment",
                      "id": b64_node("IssueComment", c["id"]),
                      "body": c["body"],
                      "author": _user_obj(r.owner or FORGE.owner_login())}
                     for c in iss.get("comments", [])]
            return ({"__gql_type": "IssueCommentConnection",
                     "nodes": nodes, "total": len(nodes)},
                    "IssueCommentConnection")
        if field == "repository":
            return _repo_obj(r), "Repository"
        raise KeyError(field)
    if typename == "PullRequest":
        r, pr = obj["_repo"], obj["_pr"]
        if field == "id":
            return b64_node("PullRequest", pr["dbid"]), None
        if field == "number":
            return pr["number"], None
        if field == "headRefName":
            return pr["head_ref"], None
        if field == "baseRefName":
            return pr["base_ref"], None
        if field == "mergeable":
            return compute_mergeable(r, pr), None
        if field == "state":
            return "MERGED" if pr["merged"] else pr["state"].upper(), None
        if field == "merged":
            return pr["merged"], None
        if field == "files":
            paths = _changed_paths(r, pr)
            nodes = [{"__gql_type": "PullRequestChangedFile", "path": p}
                     for p in paths]
            return ({"__gql_type": "PullRequestChangedFileConnection",
                     "nodes": nodes, "total": len(nodes),
                     "has_next": False}, "PullRequestChangedFileConnection")
        if field == "title":
            return pr["title"], None
        if field == "body":
            return pr.get("body") or "", None
        if field == "headRef":
            return ({"__gql_type": "Ref", "name": pr["head_ref"],
                     "_repo": r, "_sha": pr.get("head_sha")}, "Ref")
        if field == "baseRef":
            return ({"__gql_type": "Ref", "name": pr["base_ref"],
                     "_repo": r, "_sha": pr.get("base_sha")}, "Ref")
        if field == "author":
            return _user_obj(r.owner or FORGE.owner_login()), "User"
        if field == "createdAt":
            return pr["created_at"], None
        if field == "updatedAt":
            return pr["updated_at"], None
        if field == "closedAt":
            return pr.get("closed_at"), None
        if field == "mergedAt":
            return pr.get("merged_at"), None
        if field == "mergeCommit":
            sha = pr.get("merge_commit_sha")
            if not sha:
                return None, "Commit"
            msg = ""
            if sha in r.objects:
                _t, _p, msg = parse_commit(r.objects[sha][1])
            return ({"__gql_type": "Commit", "oid": sha, "message": msg},
                    "Commit")
        if field == "additions":
            return pr.get("additions", 0), None
        if field == "deletions":
            return pr.get("deletions", 0), None
        if field == "changedFiles":
            return pr.get("changed_files", 0), None
        raise KeyError(field)
    if typename in ("IssueConnection", "PullRequestConnection",
                    "SearchResultItemConnection"):
        items = obj.get("_items", [])
        if field == "nodes":
            return items, None
        if field == "edges":
            return [{"__gql_type": "IssueEdge" if "Issue" in typename
                     else "PullRequestEdge", "node": it,
                     "cursor": "Y3Vyc29yOnYyOpKAAAA="}
                    for it in items], None
        if field == "totalCount":
            return obj.get("total", len(items)), None
        if field == "issueCount":
            return obj.get("total", len(items)), None
        if field == "pageInfo":
            return _page_info(False), "PageInfo"
        raise KeyError(field)
    if typename in ("IssueEdge", "PullRequestEdge"):
        if field == "node":
            node = obj["node"]
            return node, node.get("__gql_type")
        if field == "cursor":
            return "Y3Vyc29yOnYyOpKAAAA=", None
        raise KeyError(field)
    if typename == "PullRequestChangedFileConnection":
        if field == "nodes":
            return obj.get("nodes", []), "PullRequestChangedFile"
        if field == "totalCount":
            return obj.get("total", 0), None
        if field == "pageInfo":
            return _page_info(False), "PageInfo"
        raise KeyError(field)
    if typename == "IssueCommentConnection":
        if field == "nodes":
            return obj.get("nodes", []), "IssueComment"
        if field == "totalCount":
            return obj.get("total", 0), None
        raise KeyError(field)
    if typename == "PageInfo":
        if field == "hasNextPage":
            return obj.get("has_next", False), None
        if field == "hasPreviousPage":
            return False, None
        if field == "startCursor":
            return obj.get("start_cursor"), None
        if field == "endCursor":
            return obj.get("end_cursor"), None
        raise KeyError(field)
    if typename == "User":
        if field == "id":
            return b64_node("User", obj.get("id", 1)), None
        if field == "login":
            return obj.get("login"), None
        if field == "name":
            return obj.get("login"), None
        raise KeyError(field)
    if typename == "Ref":
        if field == "name":
            return obj.get("name"), None
        if field == "target":
            sha = obj.get("_sha")
            if not sha:
                r = obj.get("_repo")
                sha = r.head_sha(obj.get("name")) if r else None
            if not sha:
                return None, "Commit"
            r = obj["_repo"]
            msg = ""
            if sha in r.objects and r.objects[sha][0] == "commit":
                _t, _p, msg = parse_commit(r.objects[sha][1])
            return ({"__gql_type": "Commit", "oid": sha, "message": msg},
                    "Commit")
        raise KeyError(field)
    if typename == "Commit":
        if field == "oid":
            return obj.get("oid"), None
        if field == "message":
            return obj.get("message", ""), None
        if field == "abbreviatedOid":
            return (obj.get("oid") or "")[:7], None
        raise KeyError(field)
    if typename == "Label":
        if field in ("name", "color", "description"):
            return obj.get(field), None
        raise KeyError(field)
    if typename == "PullRequestChangedFile":
        if field == "path":
            return obj.get("path"), None
        raise KeyError(field)
    if typename == "IssueComment":
        if field == "id":
            return obj.get("id"), None
        if field == "body":
            return obj.get("body"), None
        if field == "author":
            return obj.get("author"), "User"
        raise KeyError(field)
    if typename in ("CreatePullRequestPayload", "CreateIssuePayload"):
        if field in ("pullRequest", "issue"):
            v = obj.get(field)
            return v, (v or {}).get("__gql_type") if v else None
        if field == "clientMutationId":
            return obj.get("clientMutationId"), None
        raise KeyError(field)
    raise KeyError(field)


def _directive_skip(sel, variables):
    for name, args in sel.get("directives", []):
        cond = gql_resolve_value(args.get("if"), variables)
        if name == "skip" and cond is True:
            return True
        if name == "include" and cond is False:
            return True
    return False


def _exec_sel(obj, typename, sels, variables, errors, fragments):
    out = {}
    for sel in sels:
        if _directive_skip(sel, variables):
            continue
        if sel["kind"] == "fragment":
            frag = fragments.get(sel["name"])
            if frag is None:
                errors.append({"message": 'Unknown fragment "%s".'
                               % sel["name"]})
                continue
            out.update(_exec_sel(obj, typename, frag["sel"], variables,
                                 errors, fragments))
            continue
        if sel["kind"] == "inline":
            tc = sel.get("type_condition")
            if tc and tc != typename and tc != (obj or {}).get("__gql_type"):
                continue
            out.update(_exec_sel(obj, tc or typename, sel["sel"],
                                 variables, errors, fragments))
            continue
        name = sel["name"]
        alias = sel["alias"]
        if name == "__typename":
            out[alias] = (obj or {}).get("__gql_type", typename)
            continue
        if typename == "Query" and name == "__schema":
            types = [_type_desc(n) for n in GQL_TYPES]
            schema = {"queryType": {"name": "Query"},
                      "mutationType": {"name": "Mutation"},
                      "subscriptionType": None,
                      "types": types, "directives": []}
            out[alias] = schema
            continue
        if typename == "Query" and name == "__type":
            args = {k: gql_resolve_value(v, variables)
                    for k, v in sel["args"].items()}
            out[alias] = _type_desc(args.get("name"))
            continue
        args = {k: gql_resolve_value(v, variables)
                for k, v in sel["args"].items()}
        try:
            value, vtype = _gql_field(typename, name, obj, args)
        except KeyError:
            errors.append({"message": 'Cannot query field "%s" on type '
                                      '"%s".' % (name, typename)})
            out[alias] = None
            continue
        except ApiError as e:
            errors.append({"message": e.message})
            out[alias] = None
            continue
        if sel["sel"] is None:
            out[alias] = value
        elif value is None:
            out[alias] = None
        elif isinstance(value, list):
            item_type = vtype
            out[alias] = [
                _exec_sel(it, it.get("__gql_type", item_type) if isinstance(it, dict)
                          else item_type, sel["sel"], variables, errors,
                          fragments) if isinstance(it, dict) else it
                for it in value]
        elif isinstance(value, dict):
            vt = value.get("__gql_type", vtype)
            out[alias] = _exec_sel(value, vt, sel["sel"], variables,
                                   errors, fragments)
        else:
            out[alias] = value
    return out


def gql_execute(doc, variables, operation_name):
    errors = []
    ops = doc["operations"]
    op = None
    if operation_name:
        for o in ops:
            if o.get("name") == operation_name:
                op = o
                break
    if op is None:
        op = ops[0] if ops else None
    if op is None:
        return {"data": None,
                "errors": [{"message": "No operation provided."}]}
    root_type = "Mutation" if op["type"] == "mutation" else "Query"
    data = _exec_sel(None, root_type, op["sel"], variables, errors,
                     doc["fragments"])
    out = {"data": data}
    if errors:
        out["errors"] = errors
    return out


def handle_graphql(raw_body):
    """Return (status, result_obj). Raises ApiError."""
    if raw_body is None or raw_body == b"":
        raise ApiError(400, "Request body must be a JSON object")
    try:
        body = json.loads(raw_body.decode("utf-8"))
    except Exception:
        raise ApiError(400, "Problems parsing JSON")
    if isinstance(body, list):
        results = []
        for item in body:
            results.append(_gql_one(item))
        return 200, results
    return 200, _gql_one(body)


def _gql_one(item):
    if not isinstance(item, dict) or "query" not in item:
        return {"data": None,
                "errors": [{"message": "Must provide query string."}]}
    variables = item.get("variables") or {}
    if isinstance(variables, str):
        try:
            variables = json.loads(variables)
        except Exception:
            variables = {}
    try:
        doc = GQLParser(item["query"]).parse_document()
    except Exception as e:
        return {"data": None, "errors": [{"message": str(e)}]}
    with FORGE.lock:
        return gql_execute(doc, variables, item.get("operationName"))

# ---------------------------------------------------------------- MCP

MCP_TOOLS = [
    {"name": "create_repo",
     "description": "Create a new repository owned by the authenticated user.",
     "inputSchema": {"type": "object",
                     "properties": {"name": {"type": "string",
                                             "description": "Repository name"},
                                    "description": {"type": "string"},
                                    "private": {"type": "boolean"}},
                     "required": ["name"]}},
    {"name": "get_repo",
     "description": "Get a repository by owner and name.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "full_name": {"type": "string",
                                                "description": "owner/repo"}},
                     "required": ["owner", "repo"]}},
    {"name": "create_issue",
     "description": "Create an issue in a repository.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "full_name": {"type": "string"},
                                    "title": {"type": "string"},
                                    "body": {"type": "string"},
                                    "labels": {"type": "array",
                                               "items": {"type": "string"}}},
                     "required": ["owner", "repo", "title"]}},
    {"name": "list_issues",
     "description": "List issues in a repository, optionally by state.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "full_name": {"type": "string"},
                                    "state": {"type": "string",
                                              "description": "open, closed or all"}},
                     "required": ["owner", "repo"]}},
    {"name": "create_pull_request",
     "description": "Create a pull request from a head branch onto a base branch.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "full_name": {"type": "string"},
                                    "title": {"type": "string"},
                                    "head": {"type": "string"},
                                    "base": {"type": "string"},
                                    "body": {"type": "string"}},
                     "required": ["owner", "repo", "title", "head", "base"]}},
    {"name": "merge_pull_request",
     "description": "Merge a pull request by number with a squash commit onto its base branch.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "full_name": {"type": "string"},
                                    "pull_number": {"type": "integer"},
                                    "number": {"type": "integer"}},
                     "required": ["owner", "repo", "pull_number"]}},
    {"name": "get_issue",
     "description": "Get one issue by repository and number.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "full_name": {"type": "string"},
                                    "issue_number": {"type": "integer"},
                                    "number": {"type": "integer"}},
                     "required": ["owner", "repo", "issue_number"]}},
    {"name": "list_repos",
     "description": "List repositories owned by the authenticated user.",
     "inputSchema": {"type": "object", "properties": {},
                     "required": []}},
]

_TOOLS_LIST_BODY = json.dumps(
    {"tools": MCP_TOOLS}, separators=(",", ":"), sort_keys=False).encode()


def _mcp_owner_repo(args):
    owner = args.get("owner")
    repo = args.get("repo") or args.get("repository") or args.get("repo_name")
    full = args.get("full_name") or args.get("fullName")
    if (not owner or not repo) and full and "/" in str(full):
        parts = str(full).split("/", 1)
        owner = owner or parts[0]
        repo = repo or parts[1]
    return owner, repo


def _mcp_result(req_id, result):
    return {"jsonrpc": "2.0", "id": req_id, "result": result}


def _mcp_error(req_id, code, message):
    return {"jsonrpc": "2.0", "id": req_id,
            "error": {"code": code, "message": message}}


def _mcp_tool_error(req_id, text):
    return {"jsonrpc": "2.0", "id": req_id,
            "result": {"content": [{"type": "text", "text": text}],
                       "isError": True}}


def _mcp_tool_ok(req_id, obj, base_url):
    text = json.dumps(obj, separators=(",", ":"), sort_keys=False)
    return {"jsonrpc": "2.0", "id": req_id,
            "result": {"content": [{"type": "text", "text": text}],
                       "structuredContent": obj}}


def handle_mcp(raw_body, base_url):
    """Return (status, obj_or_None). Raises ApiError for 400/401 handled outside."""
    if raw_body is None or raw_body == b"":
        return 400, _mcp_error(None, -32700, "Parse error")
    try:
        req = json.loads(raw_body.decode("utf-8"))
    except Exception:
        return 400, _mcp_error(None, -32700, "Parse error")
    if not isinstance(req, dict):
        return 400, _mcp_error(None, -32700, "Parse error")
    method = req.get("method")
    req_id = req.get("id")
    params = req.get("params") or {}
    if method is None:
        return 200, _mcp_error(req_id, -32600, "Invalid Request")
    if method.startswith("notifications/"):
        return 202, None
    if method == "ping":
        return 200, _mcp_result(req_id, {})
    if method == "initialize":
        pver = params.get("protocolVersion") or "2026-07-28"
        return 200, _mcp_result(req_id, {
            "protocolVersion": pver,
            "supportedVersions": ["2026-07-28", "2025-11-25",
                                  "2025-06-18", "2025-03-26"],
            "capabilities": {"tools": {"listChanged": False}},
            "serverInfo": {"name": "forge", "version": VERSION}})
    if method == "server/discover":
        return 200, _mcp_result(req_id, {
            "protocolVersion": "2026-07-28",
            "supportedVersions": ["2026-07-28", "2025-11-25",
                                  "2025-06-18", "2025-03-26"],
            "capabilities": {"tools": {"listChanged": False}},
            "serverInfo": {"name": "forge", "version": VERSION}})
    if method == "tools/list":
        return 200, {"jsonrpc": "2.0", "id": req_id,
                     "result": {"tools": MCP_TOOLS}}
    if method == "tools/call":
        name = (params.get("name") or "")
        args = params.get("arguments") or {}
        if not isinstance(args, dict):
            args = {}
        return 200, _mcp_call(req_id, name, args, base_url)
    if method in ("resources/list", "prompts/list"):
        key = "resources" if method.startswith("resources") else "prompts"
        return 200, _mcp_result(req_id, {key: []})
    return 200, _mcp_error(req_id, -32601, "Method not found: %s" % method)


def _mcp_call(req_id, name, args, base_url):
    lname = name.lower()
    if lname.endswith("__create_repo") or lname == "create_repo":
        tool = "create_repo"
    elif lname.endswith("__get_repo") or lname == "get_repo":
        tool = "get_repo"
    elif lname.endswith("__create_issue") or lname == "create_issue":
        tool = "create_issue"
    elif lname.endswith("__list_issues") or lname == "list_issues":
        tool = "list_issues"
    elif lname.endswith("__create_pull_request") or lname == "create_pull_request":
        tool = "create_pull_request"
    elif lname.endswith("__merge_pull_request") or lname == "merge_pull_request":
        tool = "merge_pull_request"
    elif lname.endswith("__get_issue") or lname == "get_issue":
        tool = "get_issue"
    elif lname.endswith("__list_repos") or lname == "list_repos":
        tool = "list_repos"
    else:
        return _mcp_error(req_id, -32601, "Unknown tool: %s" % name)
    try:
        with FORGE.lock:
            if tool == "create_repo":
                rname = args.get("name") or args.get("repo")
                if not rname:
                    return _mcp_tool_error(req_id, "error: missing required "
                                           "argument: name")
                if rname in FORGE.repos:
                    return _mcp_tool_ok(req_id,
                                        repo_json(FORGE.repos[rname], base_url),
                                        base_url)
                r = Repo(FORGE.next_dbid(), rname, FORGE.login,
                         args.get("description"), args.get("private", False),
                         args.get("default_branch") or "main")
                FORGE.repos[rname] = r
                return _mcp_tool_ok(req_id, repo_json(r, base_url), base_url)
            if tool == "list_repos":
                return _mcp_tool_ok(
                    req_id, [repo_json(r, base_url)
                             for r in FORGE.repos.values()], base_url)
            owner, repo_name = _mcp_owner_repo(args)
            if not owner or not repo_name:
                return _mcp_tool_error(req_id, "error: missing required "
                                       "argument: owner/repo")
            r = FORGE.find_repo(owner, repo_name)
            if r is None:
                return _mcp_tool_error(req_id, "error: repository %s/%s "
                                       "not found" % (owner, repo_name))
            if tool == "get_repo":
                return _mcp_tool_ok(req_id, repo_json(r, base_url), base_url)
            if tool == "create_issue":
                title = args.get("title")
                if not title:
                    return _mcp_tool_error(req_id, "error: missing required "
                                           "argument: title")
                labels = args.get("labels") or []
                for lab in labels:
                    nm = lab["name"] if isinstance(lab, dict) else lab
                    if nm not in r.labels:
                        return _mcp_tool_error(
                            req_id, "error: label '%s' does not exist" % nm)
                r.counter += 1
                num = r.counter
                iss = {"dbid": FORGE.next_dbid(), "number": num,
                       "title": title, "body": args.get("body") or "",
                       "state": "open",
                       "labels": [l["name"] if isinstance(l, dict) else l
                                  for l in labels],
                       "created_at": FIXED_ISO, "updated_at": FIXED_ISO,
                       "closed_at": None, "comments": []}
                r.issues[num] = iss
                return _mcp_tool_ok(req_id, issue_json(r, iss, base_url),
                                    base_url)
            if tool == "list_issues":
                state = (args.get("state") or "open").lower()
                items = [issue_json(r, i, base_url)
                         for _n, i in sorted(r.issues.items())
                         if state == "all" or i["state"] == state]
                items.reverse()
                return _mcp_tool_ok(req_id, items, base_url)
            if tool == "get_issue":
                num = args.get("issue_number") or args.get("number")
                if num is None:
                    return _mcp_tool_error(req_id, "error: missing required "
                                           "argument: issue_number")
                iss = r.issues.get(int(num))
                if iss is None:
                    return _mcp_tool_error(req_id, "error: issue #%s not "
                                           "found" % num)
                return _mcp_tool_ok(req_id, issue_json(r, iss, base_url),
                                    base_url)
            if tool == "create_pull_request":
                title = args.get("title")
                head = args.get("head")
                base = args.get("base") or r.default_branch
                if not title:
                    return _mcp_tool_error(req_id, "error: missing required "
                                           "argument: title")
                if not head:
                    return _mcp_tool_error(req_id, "error: missing required "
                                           "argument: head")
                pr = _create_pr(r, title, head, base, args.get("body"))
                return _mcp_tool_ok(req_id, pr_json(r, pr, base_url),
                                    base_url)
            if tool == "merge_pull_request":
                num = (args.get("pull_number") or args.get("pullNumber")
                       or args.get("number") or args.get("pr_number"))
                if num is None:
                    return _mcp_tool_error(req_id, "error: missing required "
                                           "argument: pull_number")
                pr = r.pulls.get(int(num))
                if pr is None:
                    return _mcp_tool_error(req_id, "error: pull request #%s "
                                           "not found" % num)
                if pr["state"] != "open":
                    return _mcp_tool_error(req_id, "error: pull request is "
                                           "not open")
                if not compute_mergeable(r, pr):
                    return _mcp_tool_error(req_id, "error: pull request is "
                                           "not mergeable")
                sha = make_squash_commit(r, pr)
                pr["state"] = "closed"
                pr["merged"] = True
                pr["merge_commit_sha"] = sha
                pr["merged_at"] = FIXED_ISO
                pr["closed_at"] = FIXED_ISO
                return _mcp_tool_ok(req_id, {"sha": sha, "merged": True,
                                             "message": "Pull Request "
                                             "successfully merged"},
                                    base_url)
    except ApiError as e:
        return _mcp_tool_error(req_id, "error: %s" % e.message)
    return _mcp_error(req_id, -32602, "Invalid params")

# ---------------------------------------------------------------- git HTTP

def _git_repo(owner, name):
    r = FORGE.find_repo_any_owner(name)
    if r is None:
        return None
    if r.owner is None:
        FORGE.learn_login(owner)
    if r.owner is not None and r.owner != owner:
        return None
    return r


def _v0_advert(service, r):
    caps_up = ("side-band-64k multi_ack multi_ack_detailed thin-pack "
               "ofs-delta shallow agent=forge/%s" % VERSION)
    caps_down = ("report-status side-band-64k delete-refs ofs-delta quiet "
                 "agent=forge/%s" % VERSION)
    caps = caps_up if service == "git-upload-pack" else caps_down
    out = bytearray()
    out += pkt("# service=%s\n" % service)
    out += FLUSH
    refs = sorted(r.refs.items())
    head_sha = r.head_sha() or ZERO
    first = True
    # HEAD first (with capabilities), then the refs, like the reference.
    for ref, sha in [("HEAD", head_sha)] + refs:
        line = "%s %s" % (sha, ref)
        if first:
            line += "\0" + caps
            first = False
        out += pkt(line + "\n")
    if not refs:
        # unborn repo: the HEAD line above already advertised the default
        pass
    out += FLUSH
    return bytes(out)


def _v2_advert(r):
    out = bytearray()
    out += pkt("version 2\n")
    out += pkt("agent=forge/%s\n" % VERSION)
    out += pkt("ls-refs=unborn\n")
    out += pkt("fetch=shallow wait-for-done filter\n")
    out += pkt("server-option\n")
    out += pkt("object-format=sha1\n")
    out += FLUSH
    return bytes(out)


def handle_git_info_refs(owner, name, service, headers):
    r = _git_repo(owner, name)
    if r is None:
        return 404, "text/plain", b"Not Found"
    if service not in ("git-upload-pack", "git-receive-pack"):
        return 404, "text/plain", b"Not Found"
    proto = (headers.get("Git-Protocol") or "").strip()
    if service == "git-upload-pack" and proto == "version=2":
        return 200, "application/x-git-upload-pack-advertisement", \
            _v2_advert(r)
    ctype = ("application/x-git-upload-pack-advertisement"
             if service == "git-upload-pack"
             else "application/x-git-receive-pack-advertisement")
    return 200, ctype, _v0_advert(service, r)


def _v2_ls_refs(r, args):
    prefixes = [a.split(" ", 1)[1] for a in args
                if a.startswith("ref-prefix ")]
    peel = any(a == "peel" for a in args)
    symref = any(a in ("symref", "symrefs") for a in args)
    unborn = any(a == "unborn" for a in args)
    out = bytearray()
    head_sha = r.head_sha()
    refs = dict(r.refs)
    if head_sha:
        refs["HEAD"] = head_sha
    if not refs and unborn:
        line = "%s HEAD unborn" % ZERO
        if symref:
            line += " symref-target:refs/heads/%s" % r.default_branch
        out += pkt(line + "\n")
        out += FLUSH
        return bytes(out)
    for ref in sorted(refs):
        if prefixes and not any(ref.startswith(p) for p in prefixes):
            continue
        sha = refs[ref]
        attrs = ""
        if ref == "HEAD" and symref:
            attrs += " symref-target:refs/heads/%s" % r.default_branch
        if peel and sha in r.objects and r.objects[sha][0] == "tag":
            for line in r.objects[sha][1].decode("utf-8", "replace").split("\n"):
                if line.startswith("object "):
                    attrs += " peeled:%s" % line[7:].strip()
                    break
        out += pkt("%s %s%s\n" % (sha, ref, attrs))
    out += FLUSH
    return bytes(out)


def _v2_fetch(r, args):
    wants = []
    haves = []
    deepen = None
    want_refs = []
    wait_for_done = False
    for a in args:
        if a.startswith("want "):
            wants.append(a[5:].strip())
        elif a.startswith("have "):
            haves.append(a[5:].strip())
        elif a.startswith("deepen "):
            try:
                deepen = int(a[7:].strip())
            except ValueError:
                pass
        elif a.startswith("want-ref "):
            want_refs.append(a[9:].strip())
        elif a == "wait-for-done":
            wait_for_done = True
    out = bytearray()
    with FORGE.lock:
        objects_snapshot = dict(r.objects)
    if haves:
        out += pkt("acknowledgments\n")
        anc = set()
        for w in wants:
            anc |= ancestors(objects_snapshot, w)
        acked = False
        for h in haves:
            if h in anc or h in wants:
                out += pkt("ACK %s\n" % h)
                acked = True
        if not acked:
            out += pkt("NAK\n")
        # Reference framing (git 2.43 upload-pack v2, traced against the
        # real backend): the acknowledgment section ends with a "ready"
        # line and a delimiter packet (0001), not a flush. The "ready"
        # is sent whenever haves were negotiated, even without
        # wait-for-done.
        out += pkt("ready\n")
        out += b"0001"
    exclude = set()
    if haves:
        for h in haves:
            ex, _s = commit_closure(objects_snapshot, [h])
            exclude |= ex
    reachable, shallow = commit_closure(objects_snapshot, wants,
                                        depth=deepen)
    if deepen is not None:
        out += pkt("shallow-info\n")
        for s in sorted(shallow):
            out += pkt("shallow %s\n" % s)
        out += FLUSH
    if want_refs:
        out += pkt("wanted-refs\n")
        for ref in want_refs:
            sha = r.refs.get(ref)
            if sha:
                out += pkt("%s %s\n" % (sha, ref))
        out += FLUSH
    pack_objs = [(sha, objects_snapshot[sha]) for sha in sorted(reachable)
                 if sha not in exclude and sha in objects_snapshot]
    out += pkt("packfile\n")
    pack = write_pack(pack_objs)
    # Protocol v2 sends the packfile section sideband-framed (channel 1),
    # terminated by a flush packet, like the reference server does.
    pos = 0
    while pos < len(pack):
        chunk = pack[pos:pos + 65515]
        pos += len(chunk)
        out += pkt(b"\x01" + chunk)
    out += FLUSH
    # The fetch response ends with the sideband flush. There is no
    # trailing response-end packet here: the 0002 seen in git traces
    # belongs to the parent/remote-helper protocol, not the wire.
    return bytes(out)


def handle_upload_pack(owner, name, raw_body, headers):
    r = _git_repo(owner, name)
    if r is None:
        return 404, "text/plain", b"Not Found"
    proto = (headers.get("Git-Protocol") or "").strip()
    if proto == "version=2":
        lines, _pos = parse_pkt_lines(raw_body)
        args = [ln.decode("utf-8", "replace").rstrip("\n") for ln in lines]
        cmd = None
        for a in args:
            if a.startswith("command="):
                cmd = a[len("command="):]
                break
        if cmd == "ls-refs":
            return 200, "application/x-git-upload-pack-result", \
                _v2_ls_refs(r, args)
        if cmd == "fetch":
            return 200, "application/x-git-upload-pack-result", \
                _v2_fetch(r, args)
        return 200, "application/x-git-upload-pack-result", FLUSH
    # ---- protocol v0
    lines, _pos = parse_pkt_lines(raw_body)
    wants = []
    haves = []
    deepen = None
    sideband = False
    for ln in lines:
        text = ln.decode("utf-8", "replace").rstrip("\n")
        if "\0" in text:
            text = text.split("\0", 1)[0]
        if "side-band-64k" in text:
            sideband = True
        if text.startswith("want "):
            # v0: "want <oid>" plus space-separated capabilities
            wants.append(text[5:].strip().split(" ")[0])
        elif text.startswith("have "):
            haves.append(text[5:].strip().split(" ")[0])
        elif text.startswith("deepen "):
            try:
                deepen = int(text[7:].strip())
            except ValueError:
                pass
        elif text == "done":
            break
    out = bytearray()
    with FORGE.lock:
        objects_snapshot = dict(r.objects)
    if haves:
        anc = set()
        for w in wants:
            anc |= ancestors(objects_snapshot, w)
        acked = False
        for h in haves:
            if h in anc or h in wants:
                out += pkt("ACK %s\n" % h)
                acked = True
        if not acked:
            out += pkt("NAK\n")
    else:
        out += pkt("NAK\n")
    exclude = set()
    if haves:
        for h in haves:
            ex, _s = commit_closure(objects_snapshot, [h])
            exclude |= ex
    reachable, shallow = commit_closure(objects_snapshot, wants,
                                        depth=deepen)
    if deepen is not None:
        for s in sorted(shallow):
            out += pkt("shallow %s\n" % s)
    pack_objs = [(sha, objects_snapshot[sha]) for sha in sorted(reachable)
                 if sha not in exclude and sha in objects_snapshot]
    pack = write_pack(pack_objs)
    if sideband:
        pos = 0
        while pos < len(pack):
            chunk = pack[pos:pos + 65516]
            pos += len(chunk)
            out += pkt(b"\x01" + chunk)
        out += FLUSH
    else:
        out += pack
    return 200, "application/x-git-upload-pack-result", bytes(out)


def handle_receive_pack(owner, name, raw_body):
    r = _git_repo(owner, name)
    if r is None:
        return 404, "text/plain", b"Not Found"
    lines, pack_off = parse_pkt_lines(raw_body)
    commands = []
    sideband = False
    for ln in lines:
        text = ln.decode("utf-8", "replace").rstrip("\n")
        if "\0" in text:
            _left, caps = text.split("\0", 1)
            if "side-band-64k" in caps:
                sideband = True
            text = _left
        parts = text.split(" ")
        if len(parts) >= 3:
            commands.append((parts[0], parts[1], parts[2]))
    results = []
    unpack_ok = True
    new_objects = {}
    if commands:
        pack_data = raw_body[pack_off:]
        try:
            if pack_data:
                new_objects = read_pack(pack_data, r.objects)
            else:
                new_objects = {}
        except Exception as e:
            unpack_ok = False
            unpack_err = str(e)
    else:
        unpack_err = ""
    with FORGE.lock:
        if unpack_ok and new_objects:
            r.objects.update(new_objects)
        for old, new, ref in commands:
            if not unpack_ok:
                results.append((ref, "ng %s unpack failed" % ref))
                continue
            cur = r.refs.get(ref)
            if new == ZERO:
                # delete
                if cur is None:
                    results.append((ref, "ng %s ref does not exist" % ref))
                else:
                    del r.refs[ref]
                    results.append((ref, "ok %s" % ref))
                continue
            if old == ZERO:
                if cur is not None:
                    results.append((ref, "ng %s already exists" % ref))
                    continue
            else:
                if cur != old:
                    results.append((ref, "ng %s non-fast-forward" % ref))
                    continue
            if new not in r.objects or r.objects[new][0] != "commit":
                # allow creating a ref to a tag object too
                if new not in r.objects:
                    results.append((ref, "ng %s invalid new value" % ref))
                    continue
            if old != ZERO:
                anc = ancestors(r.objects, new)
                if old not in anc:
                    results.append((ref, "ng %s non-fast-forward" % ref))
                    continue
            r.refs[ref] = new
            results.append((ref, "ok %s" % ref))
    status = bytearray()
    if unpack_ok:
        status += pkt("unpack ok\n")
    else:
        status += pkt("unpack %s\n" % unpack_err)
    for ref, line in results:
        status += pkt(line + "\n")
    # The status section is terminated by a flush *inside* the band-1
    # data, like the reference server sends; one more flush then ends
    # the sideband stream.
    status += FLUSH
    out = bytearray()
    if sideband:
        # Like the reference server: status lines travel as sideband
        # channel-1 packets (error detail, if any, on channel 2).
        if not unpack_ok:
            out += pkt(b"\x02" + ("error: %s\n" % unpack_err).encode())
        pos = 0
        data = bytes(status)
        while pos < len(data):
            chunk = data[pos:pos + 65515]
            pos += len(chunk)
            out += pkt(b"\x01" + chunk)
        out += FLUSH
    else:
        out += status
    return 200, "application/x-git-receive-pack-result", bytes(out)

# ---------------------------------------------------------------- HTTP server

SHOP_TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN") or ""
ENV_URL = (os.environ.get("MAKEFUN_ENV_URL") or "").rstrip("/")


def check_auth(headers):
    """None if authorized, else an ApiError(401)."""
    auth = headers.get("Authorization") or ""
    if not auth.startswith("Bearer "):
        raise ApiError(401, "Bad credentials")
    token = auth[len("Bearer "):].strip()
    if not token:
        raise ApiError(401, "Bad credentials")
    if SHOP_TOKEN and token != SHOP_TOKEN:
        raise ApiError(401, "Bad credentials")


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "Forge/1.0"

    def log_message(self, *args):
        pass

    def _base_url(self):
        host = self.headers.get("Host") or "127.0.0.1"
        return "http://%s" % host

    def _send(self, status, ctype, body, extra=None):
        if body is None:
            body = b""
        if isinstance(body, str):
            body = body.encode()
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        if extra:
            for k, v in extra.items():
                self.send_header(k, v)
        self.end_headers()
        if body and self.command != "HEAD":
            self.wfile.write(body)

    def _send_json(self, status, obj, extra=None):
        if obj is None:
            body = b""
        else:
            body = json.dumps(obj, separators=(",", ":")).encode()
        hdrs = {"X-GitHub-Request-Id": FORGE.next_req_id()}
        if extra:
            hdrs.update(extra)
        self._send(status, "application/json", body, hdrs)

    def _read_body(self):
        length = self.headers.get("Content-Length")
        if length is None:
            return b""
        try:
            n = int(length)
        except ValueError:
            return b""
        if n <= 0:
            return b""
        return self.rfile.read(n)

    def _route(self):
        parsed = urlparse(self.path)
        path = parsed.path
        query = parse_qs(parsed.query)
        seg = [unquote(p) for p in path.split("/") if p != ""]
        raw = self._read_body()
        if os.environ.get("FORGE_DEBUG"):
            try:
                with open("/tmp/forge_debug.log", "a") as f:
                    f.write("%s %s proto=%r clen=%r body0=%r\n" % (
                        self.command, path,
                        self.headers.get("Git-Protocol"),
                        self.headers.get("Content-Length"),
                        raw[:120]))
            except Exception:
                pass
        try:
            if path == "/api/graphql":
                check_auth(self.headers)
                with FORGE.lock:
                    status, obj = handle_graphql(raw)
                self._send_json(status, obj)
                return
            if path == "/mcp":
                if self.command != "POST":
                    self._send_json(405, {"message": "Method Not Allowed"})
                    return
                check_auth(self.headers)
                with FORGE.lock:
                    status, obj = handle_mcp(raw, self._base_url())
                if status == 202:
                    self._send(202, "application/json", b"", {})
                    return
                self._send_json(status, obj)
                return
            if seg and seg[0] == "api" and len(seg) >= 2 and seg[1] == "v3":
                check_auth(self.headers)
                with FORGE.lock:
                    status, extra, obj = handle_rest(
                        self.command, seg[2:], query, raw, self._base_url())
                if status == 204:
                    self._send(204, "application/json", b"",
                               {"X-GitHub-Request-Id": FORGE.next_req_id()})
                    return
                self._send_json(status, obj, extra)
                return
            if len(seg) >= 2 and seg[1].endswith(".git"):
                # /{owner}/{repo}.git/...
                owner = seg[0]
                repo = seg[1][:-4]
                sub = path.split(".git", 1)[1] if ".git" in path else ""
                if sub.startswith("/"):
                    sub = sub[1:]
                if self.command == "GET" and sub == "info/refs":
                    service = query.get("service", [None])[0]
                    with FORGE.lock:
                        status, ctype, body = handle_git_info_refs(
                            owner, repo, service, self.headers)
                    self._send(status, ctype, body)
                    return
                if self.command == "POST" and sub == "git-upload-pack":
                    with FORGE.lock:
                        status, ctype, body = handle_upload_pack(
                            owner, repo, raw, self.headers)
                    self._send(status, ctype, body)
                    return
                if self.command == "POST" and sub == "git-receive-pack":
                    with FORGE.lock:
                        status, ctype, body = handle_receive_pack(
                            owner, repo, raw)
                    # The reference backend (CGI) closes the connection
                    # after the response; git reads the status to EOF.
                    self.close_connection = True
                    self._send(status, ctype, body,
                               {"Connection": "close"})
                    return
                self._send(404, "text/plain", b"Not Found")
                return
            self._send_json(404, {"message": "Not Found"})
        except ApiError as e:
            self._send_json(e.status, {"message": e.message})
        except BrokenPipeError:
            pass
        except Exception as e:
            try:
                self._send_json(500, {"message": "Internal Server Error: %s" % e})
            except Exception:
                pass

    def do_GET(self):
        self._route()

    def do_POST(self):
        self._route()

    def do_PUT(self):
        self._route()

    def do_PATCH(self):
        self._route()

    def do_DELETE(self):
        self._route()

    def do_HEAD(self):
        self._route()


def _http_json(url, payload, timeout=65):
    data = json.dumps(payload).encode()
    req = urllib.request.Request(url, data=data, method="POST",
                                 headers={"Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        try:
            return json.loads(e.read().decode("utf-8"))
        except Exception:
            return {}
    except Exception:
        return {}


def _http_get_json(url, timeout=65):
    req = urllib.request.Request(url, method="GET")
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        try:
            return json.loads(e.read().decode("utf-8"))
        except Exception:
            return {}
    except Exception:
        return {}


def main():
    server = ThreadingHTTPServer(("0.0.0.0", 0), Handler)
    server.daemon_threads = True
    port = server.server_address[1]
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    sys.stderr.write("forge listening on port %d\n" % port)
    sys.stderr.flush()
    if not ENV_URL:
        # Local dev: serve until killed.
        try:
            while True:
                time.sleep(3600)
        except KeyboardInterrupt:
            return 0
        return 0
    # Register with the suite, retrying until it answers.
    deadline = time.time() + 120
    registered = False
    while time.time() < deadline and not registered:
        res = _http_json(ENV_URL + "/register", {"port": port}, timeout=10)
        if isinstance(res, dict) and res.get("error") is None:
            registered = True
            break
        if isinstance(res, dict) and "port" in res:
            registered = True
            break
        time.sleep(0.5)
    # Long-poll /done until the suite finishes.
    while True:
        res = _http_get_json(ENV_URL + "/done", timeout=65)
        if isinstance(res, dict) and res.get("done") is True:
            break
        time.sleep(0.2)
    try:
        server.shutdown()
    except Exception:
        pass
    return 0


if __name__ == "__main__":
    sys.exit(main())
