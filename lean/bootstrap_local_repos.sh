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
    return
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
    if ! git -C "$dest" cat-file -e "${pinned_rev}^{commit}" 2>/dev/null &&
        [ -n "$upstream_url" ]; then
      git -C "$dest" fetch upstream "$pinned_rev"
    fi
    git -C "$dest" checkout -B "$work_branch" "$pinned_rev"
    echo "pinned $rel_path -> $work_branch @ ${pinned_rev:0:12}"
  fi

  if [ "$cloned_now" -eq 1 ]; then
    python3 "$script_dir/upgrades/4.33.1/replay.py" "$rel_path" --verify
  fi
}

# Editable dependencies use the published Lean 4.33.1 commits.
# Existing checkouts are preserved; source fingerprints verify new checkouts.
clone_or_sync_repo "externals/Foundation" "lean-upgrade/tauceti-lean__externals__Foundation" \
  "d37fa8cc888c2417d0aa04aed3ff238f2f76342b" "lean-upgrade/tauceti-lean__externals__Foundation" \
  "git@github.com:zariuq/Foundation.git" \
  "https://github.com/FormalizedFormalLogic/Foundation.git"
clone_or_sync_repo "externals/exchangeability" "lean-upgrade/tauceti-lean__externals__exchangeability" \
  "715a9df61e8cb4ede79e2adde95dc958f5cf9278" "lean-upgrade/tauceti-lean__externals__exchangeability" \
  "git@github.com:zariuq/exchangeability.git" \
  "https://github.com/cameronfreer/exchangeability.git"
clone_or_sync_repo "externals/Metatheory" "lean-upgrade/tauceti-lean__externals__Metatheory" \
  "9bcb1f996378fb88d1389b9b7d2ae24c8b73ded2" "lean-upgrade/tauceti-lean__externals__Metatheory" \
  "git@github.com:zariuq/Metatheory.git" \
  "https://github.com/Arthur742Ramos/Metatheory.git"
clone_or_sync_repo "externals/certifyingDatalog" "lean-upgrade/tauceti-lean__externals__certifyingDatalog" \
  "242c273d773265b677868658398d8a35e78b1d5f" "lean-upgrade/tauceti-lean__externals__certifyingDatalog" \
  "git@github.com:zariuq/CertifyingDatalog.git" \
  "https://github.com/knowsys/CertifyingDatalog.git"
clone_or_sync_repo "externals/ordered_semigroups" "lean-upgrade/tauceti-lean__externals__ordered_semigroups" \
  "30a63c14fac5a7c14b49f69668a963f4d9388d1a" "lean-upgrade/tauceti-lean__externals__ordered_semigroups" \
  "git@github.com:zariuq/OrderedSemigroups.git" \
  "https://github.com/ericluap/OrderedSemigroups.git"
clone_or_sync_repo "externals/provenance" "lean-upgrade/tauceti-lean__externals__provenance" \
  "69ca3c5232338e27dc9600a37fd827158715572e" "lean-upgrade/tauceti-lean__externals__provenance" \
  "git@github.com:zariuq/provenance-lean.git" \
  "https://github.com/PierreSenellart/provenance-lean.git"
clone_or_sync_repo "externals/lean4lean" "lean-upgrade/tauceti-lean__externals__lean4lean" \
  "8c2a13400be28a96a89072be1f0296e0edbf2d6c" "lean-upgrade/tauceti-lean__externals__lean4lean" \
  "git@github.com:zariuq/lean4lean.git" \
  "https://github.com/digama0/lean4lean.git"
clone_or_sync_repo "externals/mm-lean4" "lean-upgrade/tauceti-lean__externals__mm-lean4" \
  "124dfbe1d65993255f0e5de2f6eea5c28c66726b" "lean-upgrade/tauceti-lean__externals__mm-lean4" \
  "git@github.com:zariuq/mm-lean4.git" \
  "https://github.com/digama0/mm-lean4.git"

clone_or_sync_repo "standalone/mm-lean4" "lean-upgrade/tauceti-lean__standalone__mm-lean4" \
  "e031768460d5c1053c5e0d540b10560a9618fae3" "lean-upgrade/tauceti-lean__standalone__mm-lean4" \
  "git@github.com:zariuq/mm-lean4.git" \
  "https://github.com/digama0/mm-lean4.git"
clone_or_sync_repo "standalone/ks-foundations-of-inference" "lean-upgrade/tauceti-lean__standalone__ks-foundations-of-inference" \
  "47cd19d04da6543e078890bdcfbfdd385d57554b" "lean-upgrade/tauceti-lean__standalone__ks-foundations-of-inference" \
  "git@github.com:zariuq/ks-foundations-of-inference.git"

clone_or_sync_repo "externals/TauCeti" "lean-upgrade/4.33.1" \
  "96e6fcc5d7ce99124826f8e0f13ed151d6c2abbf" "lean-upgrade/4.33.1" \
  "git@github.com:zariuq/TauCeti.git" \
  "https://github.com/TauCetiProject/TauCeti.git"

clone_or_sync_repo "externals/doc-gen4-tauceti" "lean-upgrade/tauceti-docgen" \
  "932691f4ada44325a66733f309c3be773dc55195" "lean-upgrade/tauceti-docgen" \
  "git@github.com:zariuq/doc-gen4.git"

clone_or_sync_repo "externals/LeaTTa" "lean-upgrade/tauceti-lean__externals__LeaTTa" \
  "e5c5d364158caca098fcb50bfc5f553b01cb38cc" "lean-upgrade/tauceti-lean__externals__LeaTTa" \
  "git@github.com:zariuq/LeaTTa.git"

clone_or_sync_repo "externals/LeaTTa-vanilla" "lean-upgrade/tauceti-lean__externals__LeaTTa-vanilla" \
  "c21680176fc31e1636bcd3cfc71d750e22f6569b" "lean-upgrade/tauceti-lean__externals__LeaTTa-vanilla" \
  "git@github.com:zariuq/LeaTTa.git"
