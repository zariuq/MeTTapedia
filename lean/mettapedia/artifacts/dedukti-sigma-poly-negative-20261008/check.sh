#!/usr/bin/env bash
# Replays the negative results on Section 5 (Sigma_poly) of arXiv 2609.24604v1 with the Dedukti checker.
# Each file either must be accepted (exit 0) or must be rejected (exit 255) by `dk check`.
# accepted + rejected pairs show a term accepted whose beta-reduct is rejected at the same type.
set -u
cd "$(dirname "$0")"
DK=${DK:-$(command -v dk || echo "$HOME/.opam/default/bin/dk")}
[ -x "$DK" ] || { echo "SKIP: dk not found (set DK=...)"; exit 0; }
echo "dk $("$DK" --version 2>/dev/null | head -1)"
fail=0
while read -r file expected; do
  "$DK" check "$file" 2>&1 | sed 's/\x1b\[[0-9;]*m//g' >"${file%.dk}.log"; got=${PIPESTATUS[0]}
  if [ "$got" = "$expected" ]; then echo "PASS $file exit=$got"; else echo "FAIL $file exit=$got expected=$expected"; fail=1; fi
done <<'LIST'
paper_substitution.dk 0
paper_reduct_rejected.dk 255
paper_empty.dk 0
paper_no_fallback.dk 255
sigma_only_forged.dk 0
sigma_only_reduct.dk 255
LIST
exit $fail
