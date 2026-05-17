# External Repos (Mettapedia)

This project embeds external Lean repos as local directories for deterministic builds.

## Canonical remotes

- `Mettapedia/external/CertifyingDatalog`
  - `origin`: `git@github.com:zariuq/CertifyingDatalog.git`
  - `upstream`: `https://github.com/knowsys/CertifyingDatalog.git`
  - `branch`: `main`
  - parent repo policy: keep this as a local checkout only; do not track its files in `ai-agents`
- `Mettapedia/external/exchangeability`
  - `origin`: `git@github.com:zariuq/exchangeability.git`
  - `upstream`: `https://github.com/cameronfreer/exchangeability.git`
  - `branch`: `mettapedia`
  - parent repo policy: keep this as a local checkout only; do not track its files in `ai-agents`
- `Mettapedia/external/provenance-lean`
  - `origin`: `git@github.com:zariuq/provenance-lean.git`
  - `upstream`: `https://github.com/PierreSenellart/provenance-lean.git`
  - `branch`: `update/4.28`
  - parent repo policy: keep this as a local checkout only; do not track its files in `ai-agents`
- `Mettapedia/Logic/Foundation`
  - `origin`: `git@github.com:zariuq/Foundation.git`
  - `godelclaw`: `git@github.com:godelclaw/Foundation.git` (optional mirror remote)
  - `upstream`: `https://github.com/FormalizedFormalLogic/Foundation`
  - `branch`: `master`
- `Mettapedia/Algebra/OrderedSemigroups`
  - `origin`: `git@github.com:zariuq/OrderedSemigroups.git`
  - `godelclaw`: `git@github.com:godelclaw/OrderedSemigroups.git` (optional mirror remote)
  - `upstream`: `https://github.com/ericluap/OrderedSemigroups.git`
  - `branch`: `main`

## Branch/toolchain policy

- Keep `Foundation` on `master`.
- Keep `OrderedSemigroups` on `main`.
- Lean toolchain target is `v4.28.0`.
- When syncing from upstream, fast-forward from `upstream/master` for `Foundation`.
- When syncing from upstream, fast-forward from `upstream/main` for `OrderedSemigroups`.
- Keep `zariuq` as `origin`.
- If a `godelclaw` mirror is used, keep it as a separate remote named `godelclaw`, never as `origin`.

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
git checkout master
git merge --ff-only upstream/master
# manual follow-up if desired:
# git push origin master
# git push godelclaw master

# OrderedSemigroups
cd ../../Algebra/OrderedSemigroups
git fetch upstream origin --prune
git checkout main
git merge --ff-only upstream/main
# manual follow-up if desired:
# git push origin main
# git push godelclaw main
```

## Parent repo rule

- `CertifyingDatalog`, `exchangeability`, and `provenance-lean` are external working checkouts under `Mettapedia/external/`.
- The parent `ai-agents` repo should ignore them, like the other embedded external repos.
- If a checkout is missing, clone it manually:

```bash
cd lean-projects/mettapedia/Mettapedia/external
git clone --branch main git@github.com:zariuq/CertifyingDatalog.git CertifyingDatalog
git clone --branch mettapedia git@github.com:zariuq/exchangeability.git exchangeability
git clone --branch update/4.28 git@github.com:zariuq/provenance-lean.git provenance-lean
```
