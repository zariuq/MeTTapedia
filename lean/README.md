# Mettapedia (Lean 4)

A formalized-mathematics encyclopedia in Lean 4 — probability, logic, computability,
category theory, universal AI, process calculi, and more.

**Toolchain: Lean + Mathlib `v4.31.0`**, installed automatically by `elan` from `lean-toolchain`.

## Build

From the repository root:

```bash
bash lean/bootstrap_local_repos.sh   # clone the pinned v4.31 external deps into externals/ + standalone/
cd lean/mettapedia
lake exe cache get                   # download Mathlib's prebuilt oleans
lake build                           # build the library — Foundation's v4.31.0 cache downloads automatically
```

The first build is fast: Mathlib and Foundation come from prebuilt caches, not source.

## Layout

`lean/` is a monorepo of independent Lake packages:

| path | contents |
|------|----------|
| `mettapedia/` | the main library; source under `mettapedia/Mettapedia/`, imported as `import Mettapedia.…` (Lake convention: `<package>/<LibName>/`) |
| `externals/` | pinned forks of dependencies (Foundation, exchangeability, Metatheory, CertifyingDatalog, OrderedSemigroups, provenance, mm-lean4) — cloned by the bootstrap |
| `standalone/` | ks-foundations-of-inference, mm-lean4 dev copy |
| `batteries/` | mettail-core, gf-core |
| `algorithms/` | executable GF / MeTTa tools |
| `ramsey36/`, `foet/`, `fourcolor/` | self-contained side projects |

## Notes

- **Two configs:** `lakefile.lean` (default — editable local deps from `../externals/`, used by the
  bootstrap flow above) and `lakefile.toml` (git-pinned fallback: `lake -f lakefile.toml build` clones
  deps from git instead of using local checkouts).
- Build from `lean/mettapedia`. Avoid a bare `lake update` (it can bump transitive pins past the
  toolchain); use `lake update <pkg>` if you must.
