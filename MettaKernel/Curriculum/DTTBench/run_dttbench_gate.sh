#!/usr/bin/env bash
set -eu

DIR="$(cd "$(dirname "$0")" && pwd)"
AIHUB="${AIHUB:-$(cd "$DIR/../../../.." && pwd)}"
DTTBENCH_DIR="${DTTBENCH_DIR:-$AIHUB/repos/Canonical-min}"
PIN_FILE="$DIR/source_pin.tsv"

IFS=$'\t' read -r repository revision lean_toolchain expected_files expected_declarations role frontier \
  < <(sed -n '2p' "$PIN_FILE")

if [ ! -d "$DTTBENCH_DIR/.git" ]; then
  echo "DTTBENCH-FAIL: source checkout unavailable: $repository" >&2
  exit 1
fi

actual_revision="$(git -C "$DTTBENCH_DIR" rev-parse HEAD)"
if [ "$actual_revision" != "$revision" ]; then
  echo "DTTBENCH-FAIL: expected revision $revision, found $actual_revision" >&2
  exit 1
fi

if ! git -C "$DTTBENCH_DIR" diff --quiet "$revision" -- \
    DTTBench-lean CanonicalMin CanonicalMin.lean lakefile.toml lake-manifest.json lean-toolchain; then
  echo "DTTBENCH-FAIL: pinned source or solver files have local modifications" >&2
  exit 1
fi

work="$(mktemp -d "$DIR/.replay.XXXXXX")"
trap 'rm -rf "$work"' EXIT

python3 "$DIR/replay_dttbench.py" \
  --repo "$DTTBENCH_DIR" \
  --work-dir "$work" \
  --negative "$DIR/neg_uninhabited_arrow.lean" \
  --expected-files "$expected_files" \
  --expected-declarations "$expected_declarations"
