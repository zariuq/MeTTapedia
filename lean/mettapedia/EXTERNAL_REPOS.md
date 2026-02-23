# External Repos (Mettapedia)

This project embeds external Lean repos as local directories for deterministic builds.

## Canonical remotes

- `Mettapedia/Logic/Foundation`
  - `origin`: `git@github.com:godelclaw/Foundation.git`
  - `upstream`: `https://github.com/zariuq/Foundation.git`
- `Mettapedia/Algebra/OrderedSemigroups`
  - `origin`: `git@github.com:godelclaw/OrderedSemigroups.git`
  - `upstream`: `https://github.com/zariuq/OrderedSemigroups.git`

## Branch/toolchain policy

- Keep both embedded repos on `main`.
- Lean toolchain target is `v4.27.0`.
- When syncing from upstream, fast-forward from `upstream/main` and then push to `origin/main`.

## Quick sync

```bash
# Foundation
cd Mettapedia/Logic/Foundation
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
