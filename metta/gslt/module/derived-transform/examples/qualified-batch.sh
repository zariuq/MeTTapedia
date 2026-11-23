#!/usr/bin/env bash
set -euo pipefail
example_dir=$(cd -- "$(dirname -- "$0")" && pwd)
cetta_bin=${CETTA_BIN:-"$example_dir/../../../../../../hyperon/CeTTa/cetta"}
exec "$cetta_bin" --lang petta --no-results "$example_dir/qualified-batch.metta" "$@"
