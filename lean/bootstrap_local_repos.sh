#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)

clone_or_sync_repo() {
  local rel_path=$1
  local branch=$2
  local pinned_rev=$3
  local work_branch=$4
  local origin_url=$5
  local upstream_url=${6:-}
  local dest="$script_dir/$rel_path"
  local cloned_now=0

  if [ -e "$dest" ]; then
    echo "skip $rel_path: already exists"
  else
    mkdir -p "$(dirname "$dest")"
    git clone --branch "$branch" "$origin_url" "$dest"
    cloned_now=1
    echo "cloned $rel_path"
  fi

  git -C "$dest" remote set-url origin "$origin_url"

  if [ -n "$upstream_url" ] && git -C "$dest" remote get-url upstream >/dev/null 2>&1; then
    git -C "$dest" remote set-url upstream "$upstream_url"
  elif [ -n "$upstream_url" ]; then
      git -C "$dest" remote add upstream "$upstream_url"
  fi

  if [ -n "$pinned_rev" ] && [ "$cloned_now" -eq 1 ]; then
    git -C "$dest" checkout -B "$work_branch" "$pinned_rev"
    echo "pinned $rel_path -> $work_branch @ ${pinned_rev:0:12}"
  fi
}

# Integration repos are pinned to the exact revisions that the root Mettapedia
# build was verified against; standalone repos track their active branches.
clone_or_sync_repo "externals/Foundation" "mettapedia" \
  "c79048ee84be6e86f5a6d05f145576ecbe8379d1" "mettapedia-integration" \
  "git@github.com:zariuq/Foundation.git" \
  "https://github.com/FormalizedFormalLogic/Foundation.git"
clone_or_sync_repo "externals/exchangeability" "mettapedia" \
  "98f6c86e6131df562cc2f715c2e93b70b978c689" "mettapedia-integration" \
  "git@github.com:zariuq/exchangeability.git" \
  "https://github.com/cameronfreer/exchangeability.git"
clone_or_sync_repo "externals/Metatheory" "main" \
  "5ebc2dcecf05787432a18f96d6202518b3d5a8db" "mettapedia-integration" \
  "git@github.com:zariuq/Metatheory.git" \
  "https://github.com/Arthur742Ramos/Metatheory.git"
clone_or_sync_repo "externals/certifyingDatalog" "main" \
  "a269a8fdd097afad2a12081a04263214762faf1b" "mettapedia-integration" \
  "git@github.com:zariuq/CertifyingDatalog.git" \
  "https://github.com/knowsys/CertifyingDatalog.git"
clone_or_sync_repo "externals/ordered_semigroups" "main" \
  "63e9c6c3457420c16749837102966a5c32f27825" "mettapedia-integration" \
  "git@github.com:zariuq/OrderedSemigroups.git" \
  "https://github.com/ericluap/OrderedSemigroups.git"
clone_or_sync_repo "externals/provenance" "update/4.28" \
  "79aca19592af945e08f2d204dc1545a13849af3f" "mettapedia-integration" \
  "git@github.com:zariuq/provenance-lean.git" \
  "https://github.com/PierreSenellart/provenance-lean.git"
clone_or_sync_repo "externals/mm-lean4" "verified-mm-4.28" \
  "396a7a00ba85a6e9df295917031a669b92c7d1e2" "mettapedia-integration" \
  "git@github.com:zariuq/mm-lean4.git" \
  "https://github.com/digama0/mm-lean4.git"

clone_or_sync_repo "standalone/mm-lean4" "verified-mm-latest" \
  "" "" \
  "git@github.com:zariuq/mm-lean4.git" \
  "https://github.com/digama0/mm-lean4.git"
clone_or_sync_repo "standalone/ks-foundations-of-inference" "main" \
  "" "" \
  "git@github.com:zariuq/ks-foundations-of-inference.git"
