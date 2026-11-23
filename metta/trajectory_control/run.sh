#!/usr/bin/env bash
set -euo pipefail
demo_dir=$(cd -- "$(dirname -- "$0")" && pwd)
cetta_bin=${CETTA_BIN:-"$demo_dir/../../../hyperon/CeTTa/cetta"}
exec "$cetta_bin" --lang petta --no-results "$demo_dir/demo.metta" "$@"
