# External Repos (Mettapedia)

This project embeds external Lean repos as local directories for deterministic builds.

## Canonical remotes

- `Mettapedia/external/CertifyingDatalog`
  - `origin`: `https://github.com/jt0202/CertifyingDatalog`
  - `branch`: `main`
  - parent repo policy: keep this as a local checkout only; do not track its files in `ai-agents`
- `Mettapedia/external/exchangeability`
  - `origin`: `https://github.com/zariuq/exchangeability.git`
  - `branch`: `mettapedia`
  - parent repo policy: keep this as a local checkout only; do not track its files in `ai-agents`
- `Mettapedia/external/provenance-lean`
  - `origin`: `https://github.com/zariuq/provenance-lean.git`
  - `branch`: `update/4.28`
  - parent repo policy: keep this as a local checkout only; do not track its files in `ai-agents`
- `Mettapedia/Logic/Foundation`
  - `origin`: `git@github.com:godelclaw/Foundation.git`
  - `upstream`: `https://github.com/zariuq/Foundation.git`
- `Mettapedia/Algebra/OrderedSemigroups`
  - `origin`: `git@github.com:godelclaw/OrderedSemigroups.git`
  - `upstream`: `https://github.com/zariuq/OrderedSemigroups.git`

## Branch/toolchain policy

- Keep `Foundation` and `OrderedSemigroups` on `main`.
- Lean toolchain target is `v4.27.0`.
- When syncing from upstream, fast-forward from `upstream/main` and then push to `origin/main`.

## Quick sync

```bash
# CertifyingDatalog
cd Mettapedia/external/CertifyingDatalog
git fetch origin --prune
git checkout main
git pull --ff-only origin main

# Exchangeability
cd Mettapedia/external/exchangeability
git fetch origin --prune
git checkout mettapedia
git pull --ff-only origin mettapedia

# provenance-lean
cd ../provenance-lean
git fetch origin --prune
git checkout update/4.28
git pull --ff-only origin update/4.28

# Foundation
cd ../../Logic/Foundation
git fetch upstream origin --prune
git checkout main
git merge --ff-only upstream/main
git push origin main

# OrderedSemigroups
cd ../../Algebra/OrderedSemigroups
git fetch upstream origin --prune
git checkout main
git merge --ff-only upstream/main
git push origin main
```

## Parent repo rule

- `CertifyingDatalog`, `exchangeability`, and `provenance-lean` are external working checkouts under `Mettapedia/external/`.
- The parent `ai-agents` repo should ignore them, like the other embedded external repos.
- If a checkout is missing, clone it manually:

```bash
cd lean-projects/mettapedia/Mettapedia/external
git clone --branch main https://github.com/jt0202/CertifyingDatalog CertifyingDatalog
git clone --branch mettapedia https://github.com/zariuq/exchangeability.git exchangeability
git clone --branch update/4.28 https://github.com/zariuq/provenance-lean.git provenance-lean
```
