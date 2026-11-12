#!/usr/bin/env bash
# The Lean reading on the Megalodon kernel of CeTTa.
#
#   kernel/check.sh
#
# Opens the reading as a live kernel theory (session.metta: the document that
# ../check.sh hands to the two checkers, checked once in process), builds each
# test's statement from the reader's terms as kernel terms (terms.metta) and
# compares it with what the document states (check-statements.metta).  Then
# the way back: the built statements, written as Megalodon text and each
# closed by the document's own theorem, must be accepted by Megalodon and by
# mg-check, and a statement with another test's answer must be refused by
# both at the same position.
#
#   CETTA      the CeTTa binary       (default: cetta on PATH)
#   MEGALODON  the Megalodon binary   (default: megalodon/bin/megalodon here)
#   MG_CHECK   the mg-check binary    (default: mg-check on PATH)
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
project=$(cd "$here/../../../.." && pwd)
root=$(cd "$here/../../../../../.." && pwd)
cetta=${CETTA:-cetta}
megalodon=${MEGALODON:-$root/megalodon/bin/megalodon}
mgcheck=${MG_CHECK:-mg-check}
preamble=$root/megalodon/examples/egal/PfgEAug2022Preamble.mgs
decls=$project/artifacts/lean-declarations
work=$(mktemp -d "${TMPDIR:-/tmp}/lean-egal-kernel.XXXXXX")
cleanup() {
  rm -f -- "$work"/*.metta "$work"/*.mg "$work"/*.txt "$work"/*.json "$work"/*.out
  rmdir -- "$work"
}
trap cleanup EXIT

# The reader's inputs, as ../generate.sh prepares them: CeTTa's answers on the
# code-equation slice and the typing lemmas proved by hand.
python3 "$project/scripts/lean_code_equations_diff.py" --cetta "$cetta" \
    --report "$work/report.json" > "$work/slice.txt" || { cat "$work/slice.txt"; exit 1; }
"$cetta" --lang petta --quiet "$here/answers.metta" "$work/report.json" \
  "$work/answers.metta" "$work/binary.txt" with-source "$project/artifacts/lean-code-equations/core/tests.tsv" > /dev/null
"$cetta" --lang petta "$here/splice.metta" facts "$here/proofs/functions" "$work/typing.metta" > /dev/null

{ echo '!(import! &self megalodon)'
  cat "$decls/families.metta" "$decls/terms.metta" "$work/answers.metta" "$work/typing.metta" \
      "$here/support.metta" "$here/generate.metta" "$here/interpret.metta"
  printf '(EgalProofLibraryRoot "%s")\n' "$here"
  cat "$here/kernel/session.metta" "$here/kernel/terms.metta"
  printf '!(case (lean:open "%s" "%s" "%s") (((LeanSession $verdict $summary) (println! (format-args "session: {}" ($verdict)))) ($other (println! $other))))\n' \
      "$preamble" "$here" "$work"
  cat "$here/kernel/check-statements.metta"
} > "$work/driver.metta"
"$cetta" --lang petta "$work/driver.metta" "$work" | grep -E '^"?(session|statements):' | tr -d '"' > "$work/kernel.out" || true
cat "$work/kernel.out"
fail=0
grep -qx 'session: verified' "$work/kernel.out" || { echo "FAIL kernel: the document is not verified in process"; fail=1; }
line=$(grep '^statements:' "$work/kernel.out" || true)
tests=$(sed -n 's/^statements: \([0-9]*\) tests; .*/\1/p' <<<"$line")
same=$(sed -n 's/.*; \([0-9]*\) equal the document.*/\1/p' <<<"$line")
refused=$(sed -n 's/.*crossed: \([0-9]*\) of \([0-9]*\) refused$/\1 \2/p' <<<"$line")
[[ -n "$tests" && "$tests" == "$same" ]] || { echo "FAIL kernel: not every built statement equals the document's"; fail=1; }
[[ -n "$refused" && "${refused% *}" == "${refused#* }" && "${refused% *}" != 0 ]] || { echo "FAIL kernel: a crossed statement was not refused"; fail=1; }

# The way back, in the two checkers.
position() { sed -n 's/.*[Ff]ailure at line \([0-9]*\) char \([0-9]*\).*/\1 \2/p' | head -1; }
cat "$work/lean-document.mg" "$work/restated.mg" > "$work/doc.mg"
if out=$("$megalodon" -I "$preamble" "$work/doc.mg" 2>&1); then echo "megalodon: the built statements, as text, accepted"
else echo "FAIL megalodon: $(tail -c 300 <<<"$out")"; fail=1; fi
if out=$("$mgcheck" -I "$preamble" "$work/doc.mg" 2>&1); then echo "mg-check:  the built statements, as text, $(grep '^summary' <<<"$out" | sed 's/^summary: //; s/:.*//') verified"
else echo "FAIL mg-check: $(grep -v '^(Meg' <<<"$out" | tail -3)"; fail=1; fi
cat "$work/lean-document.mg" "$work/crossed.mg" > "$work/doc.mg"
m=$("$megalodon" -I "$preamble" "$work/doc.mg" 2>&1) && { echo "FAIL crossed: accepted by megalodon"; fail=1; }
c=$("$mgcheck" -I "$preamble" "$work/doc.mg" 2>&1) && { echo "FAIL crossed: verified by mg-check"; fail=1; }
mp=$(position <<<"$m"); cp=$(position <<<"$c"); lines=$(wc -l < "$work/lean-document.mg")
if [[ -n "$mp" && "$mp" == "$cp" && "${mp% *}" -gt "$lines" ]]; then echo "refused:   a crossed statement, by both at the same position"
else echo "FAIL crossed: megalodon '$mp', mg-check '$cp' (the document has $lines lines)"; fail=1; fi
exit $fail
