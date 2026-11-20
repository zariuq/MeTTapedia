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
# both at the same position.  Last, the computations: each listed test's term
# is computed in the live theory by Lean's own equations (typing.metta,
# invert.metta, rules.metta, numerals.metta, compute.metta), and the theorem
# the kernel made must state what the document's theorem states
# (check-compute.metta); and what the prover decides is shown on small goals,
# beside each goal that must be proved one that must not be, with two
# decisions computed by Lean's own decision procedure (check-examples.metta).
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
  echo '!(import! &self (library megalodon_equations))'
  cat "$decls/families.metta" "$decls/terms.metta" "$work/answers.metta" "$work/typing.metta" \
      "$here/support.metta" "$here/generate.metta" "$here/interpret.metta"
  printf '(EgalProofLibraryRoot "%s")\n' "$here"
  cat "$here/kernel/session.metta" "$here/kernel/terms.metta"
  printf '!(case (lean:open "%s" "%s" "%s") (((LeanSession $verdict $summary) (println! (format-args "session: {}" ($verdict)))) ($other (println! $other))))\n' \
      "$preamble" "$here" "$work"
} > "$work/prefix.metta"
cat "$work/prefix.metta" "$here/kernel/check-statements.metta" > "$work/driver.metta"
"$cetta" --lang petta "$work/driver.metta" "$work" | grep -E '^"?(session|statements):' | tr -d '"' > "$work/kernel.out" || true

# The computations, each listed test in a process of its own (a process
# keeps every term its kernel built, so the tests do not share one).
listed=$(sed -n 's/^(= (computed-today) (\(.*\)))$/\1/p' "$here/kernel/check-compute.metta")
{ cat "$work/prefix.metta"
  sed '/^!/,$d' "$here/kernel/check-statements.metta"
  cat "$here/kernel/typing.metta" "$here/kernel/invert.metta" "$here/kernel/rules.metta" \
      "$here/kernel/numerals.metta" "$here/kernel/compute.metta" "$here/kernel/check-compute.metta"
} > "$work/compute.metta"
first=${listed%% *}; computed=0; refused=0; count=0; : > "$work/computed.txt"
set -- $listed
while [ $# -gt 0 ]; do
  i=$1; shift; j=${1:-$first}; count=$((count + 1))
  { cat "$work/compute.metta"; echo "!(compute:report $i $j)"; } > "$work/one.metta"
  line=$("$cetta" --lang petta "$work/one.metta" "$work" 2>/dev/null | grep -E '^"?computed ' | tr -d '"' || true)
  echo "${line:-computed $i no accepted}" >> "$work/computed.txt"
  case "$line" in "computed $i yes "*) computed=$((computed + 1));; esac
  case "$line" in *" refused") refused=$((refused + 1));; esac
done
notyet=""; for k in $(seq 1 30); do case " $listed " in *" $k "*) ;; *) notyet="$notyet $k";; esac; done
echo "computations: 30 tests; $computed of $count listed are computed by kernel conversion and state the document's theorems; crossed: $refused of $count refused; not yet:$notyet" >> "$work/kernel.out"

# The examples: one line for each, "example LABEL as-expected".
wanted=$(sed -n 's/^(= (examples:expected) \([0-9]*\))$/\1/p' "$here/kernel/check-examples.metta")
groups=$(sed -n 's/^(= (examples:groups) (\(.*\)))$/\1/p' "$here/kernel/check-examples.metta")
: > "$work/examples.txt"
for group in $groups; do
  { cat "$work/compute.metta" "$here/kernel/check-examples.metta"; echo "!(examples:report $group)"; } > "$work/one.metta"
  "$cetta" --lang petta "$work/one.metta" "$work" 2>/dev/null | grep -E '^"?example ' | tr -d '"' >> "$work/examples.txt" || true
done
shown=$(wc -l < "$work/examples.txt"); asexpected=$(grep -c ' as-expected$' "$work/examples.txt" || true)
echo "examples: ${wanted:-0} goals; $shown decided, $asexpected as they must be (proved where a proof is due, not proved beside it)" >> "$work/kernel.out"
cat "$work/kernel.out"
fail=0
grep -qx 'session: verified' "$work/kernel.out" || { echo "FAIL kernel: the document is not verified in process"; fail=1; }
line=$(grep '^statements:' "$work/kernel.out" || true)
tests=$(sed -n 's/^statements: \([0-9]*\) tests; .*/\1/p' <<<"$line")
same=$(sed -n 's/.*; \([0-9]*\) equal the document.*/\1/p' <<<"$line")
refused=$(sed -n 's/.*crossed: \([0-9]*\) of \([0-9]*\) refused$/\1 \2/p' <<<"$line")
[[ -n "$tests" && "$tests" == "$same" ]] || { echo "FAIL kernel: not every built statement equals the document's"; fail=1; }
[[ -n "$refused" && "${refused% *}" == "${refused#* }" && "${refused% *}" != 0 ]] || { echo "FAIL kernel: a crossed statement was not refused"; fail=1; }
line=$(grep '^computations:' "$work/kernel.out" || true)
computed=$(sed -n 's/^computations: [0-9]* tests; \([0-9]*\) of \([0-9]*\) listed .*/\1 \2/p' <<<"$line")
crossed=$(sed -n 's/.*crossed: \([0-9]*\) of \([0-9]*\) refused; .*/\1 \2/p' <<<"$line")
[[ -n "$computed" && "${computed% *}" == "${computed#* }" && "${computed% *}" != 0 ]] || { echo "FAIL kernel: a listed test is not computed to the document's theorem"; fail=1; }
[[ -n "$crossed" && "${crossed% *}" == "${crossed#* }" && "${crossed% *}" != 0 ]] || { echo "FAIL kernel: a computed theorem states another test's statement"; fail=1; }
[[ -n "$wanted" && "$wanted" != 0 && "$shown" == "$wanted" && "$asexpected" == "$wanted" ]] || { echo "FAIL kernel: an example is not decided as it must be: $(grep -v ' as-expected$' "$work/examples.txt" | tr '\n' ';')"; fail=1; }

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
