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
  "85314e340ea03e62c38a78e2d24c0643578d10ee" "mettapedia" \
  "git@github.com:zariuq/Foundation.git" \
  "https://github.com/FormalizedFormalLogic/Foundation.git"
clone_or_sync_repo "externals/exchangeability" "mettapedia" \
  "05330d5c92f4400161d5e31632efcaa4a2d91361" "mettapedia" \
  "git@github.com:zariuq/exchangeability.git" \
  "https://github.com/cameronfreer/exchangeability.git"
clone_or_sync_repo "externals/Metatheory" "main" \
  "8f3275528034ceb002e7e3dba0bbeacc8de258c4" "main" \
  "git@github.com:zariuq/Metatheory.git" \
  "https://github.com/Arthur742Ramos/Metatheory.git"
clone_or_sync_repo "externals/certifyingDatalog" "main" \
  "91adc633bfd8d2a1565f46ba7876b73dcda55471" "main" \
  "git@github.com:zariuq/CertifyingDatalog.git" \
  "https://github.com/knowsys/CertifyingDatalog.git"
clone_or_sync_repo "externals/ordered_semigroups" "mettapedia" \
  "4324a78c436f2150403159b96b91d0f8692f3b80" "mettapedia" \
  "git@github.com:zariuq/OrderedSemigroups.git" \
  "https://github.com/ericluap/OrderedSemigroups.git"
clone_or_sync_repo "externals/provenance" "update/4.28" \
  "fe0bb6d4b2a7acf99edb13d672b7483da95937a5" "update/4.28" \
  "git@github.com:zariuq/provenance-lean.git" \
  "https://github.com/PierreSenellart/provenance-lean.git"
clone_or_sync_repo "externals/mm-lean4" "verified-mm-latest" \
  "c5bbaa0d6d11dccf614dadd279ca56730887fe78" "verified-mm-latest" \
  "git@github.com:zariuq/mm-lean4.git" \
  "https://github.com/digama0/mm-lean4.git"

clone_or_sync_repo "standalone/mm-lean4" "verified-mm-latest" \
  "" "" \
  "git@github.com:zariuq/mm-lean4.git" \
  "https://github.com/digama0/mm-lean4.git"
clone_or_sync_repo "standalone/ks-foundations-of-inference" "main" \
  "" "" \
  "git@github.com:zariuq/ks-foundations-of-inference.git"
