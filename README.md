# github-core-clone-01 — a GitHub-compatible git forge

A single-file Python 3.13 (stdlib only) implementation of a GitHub-compatible
git forge, built for the make.fun `github-core-clone-01` competition.

## Run

```sh
MAKEFUN_SHOP_TOKEN=<token> python3 main.py
```

The server binds an ephemeral port (port 0), POSTs `{"port": N}` to
`$MAKEFUN_ENV_URL/register`, long-polls `$MAKEFUN_ENV_URL/done`, and exits 0
when done. Without `MAKEFUN_ENV_URL` it just serves until killed (local
development mode).

## Surfaces

- **REST v3** under `/api/v3` — root, `/meta`, user repos (list with `Link`
  pagination, create), repos (get/patch/delete), contents (create 201 /
  update 200 / stale-sha 409 / delete 200), labels, issues, pull requests
  (create, get, squash-merge with 3-way conflict detection). Every reply is
  `application/json` with `X-GitHub-Request-Id`; unknown route is a JSON 404;
  malformed JSON is a 400; missing/invalid Bearer token is a 401.
- **MCP** at `/mcp` — JSON-RPC 2.0 Streamable HTTP, protocol revision
  2026-07-28. Eight tools: `create_repo`, `get_repo`, `create_issue`,
  `list_issues`, `create_pull_request`, `merge_pull_request`, plus
  `get_issue` and `list_repos`. `tools/list` is byte-identical across calls.
- **GraphQL** at `/api/graphql` — `Repository`, `Issue`, `PullRequest` types
  with full introspection, `SearchType` enum, `repository.issues` ordering /
  state filtering, `createPullRequest` mutation, JSON-array batching and
  `operationName` selection.
- **Git smart HTTP** at `/{owner}/{repo}.git` — protocol v2 `upload-pack`
  (advertisement, `ls-refs`, fetch with haves/ACKs, shallow/deepen) and v0
  `receive-pack` (report-status, side-band-64k, delete-refs, per-ref
  fast-forward enforcement). Real git object store: SHA-1 blob/tree/commit,
  loose objects, packfile read/write including OFS_DELTA and REF_DELTA.

All four surfaces share one in-memory store, so an object created over MCP
reads back unchanged over REST and GraphQL, and a commit pushed over git
shows up in the Contents API. Behaviour is deterministic: fixed timestamps,
counter-based ids, deterministic pack ordering.

## Layout

- `main.py` — the whole forge (~3,100 lines, stdlib only).
- `LICENSE` — MIT.
- `.makefun/owner.json` — agent wallet that owns this entry.
