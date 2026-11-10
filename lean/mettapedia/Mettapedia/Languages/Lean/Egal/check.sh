#!/usr/bin/env bash
# Check the interpretation of Lean in Egal with two checkers.
#
# The document, in this order, must be accepted by Megalodon and verified by
# mg-check: the general construction (LeanInEgal.mg, with Library/Conversion.mg
# before it and Library/Typing.mg and the numerals' digits, Library/Digits.mg,
# after it), the generated families,
# facts about equality (Library/EqFacts.mg) and about them (FamilyFacts.mg), numerals (Numerals.mg), decidable
# propositions read by their type (Decidable.mg) and decisions about numerals
# (Library/NumeralDecisions.mg), the generated
# functions, decide at canonical elements (Library/DecideFacts.mg), the natively
# computed operations (Library/NatAdd.mg, Library/NatMul.mg), subtraction,
# Nat.decLe, division and remainder between numerals (Library/NatSub.mg,
# Library/NatDecide.mg, Library/NatDiv.mg)
# and the generated computations.  Each controls/reject_*.mg is appended to it and
# must be refused by both, at the same source position, inside the control.
#
# Then the scaling checks: three workloads (scaling.metta: many independent
# declarations, a growing notation table, one lemma cited many times), each
# checked at sizes 0, N and 2N.  The counted work is mg-check's: its kernel
# work units and its reader's relation calls (both exact), and, where perf is
# available, the instructions each checker executes.
# Above the cost of the empty document, doubling the size may at most double
# the work: the workloads are linear by construction, and the limit 2.2
# leaves room for tables that grow by doubling.  mg-check, the checker built
# with CeTTa, is held to the limit; Megalodon, the reference, is reported.
#
#   MEGALODON  the Megalodon binary   (default: megalodon/bin/megalodon here)
#   MG_CHECK   the mg-check binary    (default: mg-check on PATH)
#   CETTA      the CeTTa binary       (default: cetta on PATH)
#   SCALING_N  the workloads' size N  (default 200)
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(cd "$here/../../../../../.." && pwd)
megalodon=${MEGALODON:-$root/megalodon/bin/megalodon}
mgcheck=${MG_CHECK:-mg-check}
cetta=${CETTA:-cetta}
preamble=$root/megalodon/examples/egal/PfgEAug2022Preamble.mgs
(cd "$root" && sha256sum --status --check "$here/Foundation.sha256") || {
    echo "check: the imported Egal signature differs from Foundation.sha256" >&2; exit 1;
}
work=$(mktemp -d "${TMPDIR:-/tmp}/lean-in-egal.XXXXXX")
cleanup() {
    rm -f -- "$work"/*.mg "$work"/*.tsv "$work"/evidence-*.txt "$work/Skipped.txt"
    rm -f -- "$work/answers-control.metta" "$work/answers-control-binary.txt" "$work/answers-control.log"
    rmdir -- "$work"
}
library=$work/library.mg
trap cleanup EXIT
# Qualification is recomputed from the current source inventory and proof
# references. A stale ledger cannot certify an otherwise checked document.
cp "$here/generated/LeanFamilies.mg" "$work/Families.mg"
cp "$here/generated/LeanFunctions.mg" "$work/Functions.mg"
cp "$here/generated/LeanComputations.mg" "$work/Computations.mg"
cp "$here/generated/Outcomes.tsv" "$work/Outcomes.tsv"
cp "$here/generated/Skipped.txt" "$work/Skipped.txt"
: > "$work/Theorems.mg"
decls=$root/lean/mettapedia/artifacts/lean-declarations
"$cetta" --lang petta --quiet "$decls/terms.metta" "$decls/families.metta" "$here/evidence.metta" \
  "$work/Evidence.tsv" "$work/Qualification.tsv" "$work/evidence-summary.txt" "$decls" "$work" > /dev/null
cmp "$work/Evidence.tsv" "$here/generated/Evidence.tsv"
cmp "$work/Qualification.tsv" "$here/generated/Qualification.tsv"
cmp "$work/evidence-summary.txt" "$here/generated/EvidenceSummary.txt"
cat "$work/evidence-summary.txt"
for control in answers-crash answers-missing; do
    if "$cetta" --lang petta --quiet "$here/answers.metta" "$here/controls/$control.json" \
        "$work/answers-control.metta" "$work/answers-control-binary.txt" without-source \
        "$here/controls/answers-tests.tsv" > "$work/answers-control.log" 2>&1; then
        echo "FAIL $control: invalid observation accepted"; exit 1
    fi
    grep -q '^answers:' "$work/answers-control.log" || { cat "$work/answers-control.log"; exit 1; }
    echo "refused:   $control (runtime observation)"
done
# Guard substitution and projection templates share the term interpreter.
# Keep their scope controls in the normal gate, before checking generated proofs.
"$cetta" --lang petta --quiet "$here/../../../../artifacts/lean-declarations/families.metta" \
  "$here/generate.metta" "$here/interpret.metta" "$here/guard-controls.metta"
if "$cetta" --lang petta --quiet "$decls/families.metta" "$decls/terms.metta" \
    "$here/generate.metta" "$here/interpret.metta" "$here/controls/unexported-source-equation.metta" \
    > "$work/evidence-source-control.txt" 2>&1; then
    echo "FAIL source control: an unexported equation accepted a target proof"; exit 1
fi
grep -q '^source-equation proof .* is not an exported obligation' "$work/evidence-source-control.txt"
echo "refused:   unexported source equation"
after_functions=()
for relative in Library/DecideFacts.mg Library/NatAdd.mg Library/NatMul.mg Library/NatSub.mg Library/NatDecide.mg Library/NatDiv.mg; do
    if ! grep -Fqx "(** Embedded proof support: $relative **)" "$here/generated/LeanFunctions.mg"; then
        after_functions+=("$here/$relative")
    fi
done
cat "$here/Library/Conversion.mg" "$here/Library/Quotients.mg" "$here/Library/EquivalenceClosure.mg" "$here/Library/RankedRecursion.mg" "$here/LeanInEgal.mg" "$here/Library/Typing.mg" "$here/Library/QuotientTyping.mg" "$here/Library/Digits.mg" "$here/generated/LeanFamilies.mg" "$here/Library/EqFacts.mg" "$here/Library/QuotientProofs.mg" "$here/FamilyFacts.mg" \
    "$here/Numerals.mg" "$here/Decidable.mg" "$here/Library/NumeralDecisions.mg" \
    "$here/Library/AlgebraicStructures.mg" "$here/Library/NatAlgebra.mg" "$here/Library/Propositions.mg" \
    "$here/generated/LeanFunctions.mg" "${after_functions[@]}" \
    "$here/generated/LeanComputations.mg" > "$library"
trap cleanup EXIT
fail=0

if out=$("$megalodon" -I "$preamble" "$library" 2>&1); then
    echo "megalodon: library accepted"
else
    echo "megalodon: library refused: $out"; fail=1
fi
if out=$("$mgcheck" -I "$preamble" "$library" 2>&1); then
    echo "mg-check:  library $(grep '^summary' <<<"$out")"
else
    echo "mg-check:  library not verified:"; grep -v '^(Meg' <<<"$out"; fail=1
fi

# The source equation that seeds H3: a receipt of the code-equation slice
# (the theorem its MeTTa rule for List.length was taken from), checked above
# as an Egal theorem with the receipt's statement digest.
seed=Lean_List_length_eq_2
receipt=$(grep -o '(\*\* Receipt: List.length.eq_2 is the source of the MeTTa rule for List.length, statement digest [0-9]*' \
  "$here/generated/LeanFunctions.mg" | grep -o '[0-9]*$' || true)
if grep -q "^Theorem $seed :" "$library" && [[ -n "$receipt" ]] && [[ $fail == 0 ]]; then
    echo "seed:      $seed, the receipt List.length.eq_2 (digest $receipt), verified by both checkers"
else
    echo "FAIL seed: $seed not verified as the receipt's Egal theorem"; fail=1
fi

[[ $fail == 0 ]] || exit 1
echo "receipts:  $(grep -c $'\tgenerated ' "$here/generated/ReceiptCoverage.tsv") generated candidates checked by both engines"

offset=$(wc -l < "$library")
"$cetta" --lang petta --quiet "$decls/families.metta" "$decls/terms.metta" \
    "$here/generate.metta" "$here/interpret.metta" "$here/numeral-controls.metta" \
    "$work/numeral-positive.mg" "$work/numeral-negative.mg" > /dev/null
cat "$library" "$work/numeral-positive.mg" > "$work/doc.mg"
for checker in "$megalodon" "$mgcheck"; do
    if ! "$checker" -I "$preamble" "$work/doc.mg" > "$work/evidence-numerals.txt" 2>&1; then
        cat "$work/evidence-numerals.txt"; exit 1
    fi
done
echo "numerals:  eight divisibility branch proofs checked by both engines"

for control in "$here"/controls/reject_*.mg "$work/numeral-negative.mg"; do
    name=$(basename "$control")
    cat "$library" "$control" > "$work/doc.mg"
    m=$("$megalodon" -I "$preamble" "$work/doc.mg" 2>&1) && { echo "FAIL $name: accepted by megalodon"; fail=1; continue; }
    c=$("$mgcheck" -I "$preamble" "$work/doc.mg" 2>&1) && { echo "FAIL $name: verified by mg-check"; fail=1; continue; }
    mline=$(grep -o '^Failure at line [0-9]* char [0-9]*' <<<"$m" | head -1 || true)
    cline=$(grep -o 'failed: Failure at line [0-9]* char [0-9]*' <<<"$c" | head -1 | sed 's/^failed: //' || true)
    line=$(grep -o 'line [0-9]*' <<<"$mline" | grep -o '[0-9]*' || echo 0)
    if [[ -n "$mline" && "$mline" == "$cline" && "$line" -gt "$offset" ]]; then
        echo "refused:   $name (control line $((line - offset)), $(grep -o 'char [0-9]*' <<<"$mline"), both checkers)"
    else
        echo "FAIL $name: megalodon '$mline', mg-check '$cline' (library has $offset lines)"; fail=1
    fi
done

# Scaling: work above the empty document at 2N against N.
scale_n=${SCALING_N:-200}
limit=2.2
have_perf=0
perf stat -x, -e instructions:u true >/dev/null 2>&1 && have_perf=1
# Kernel work units and the reader's relation calls, or "fail fail".
counts() {
    local out u r
    out=$("$mgcheck" --verbose -I "$preamble" "$1" 2>&1) || { echo "fail fail"; return; }
    u=$(sed -n 's/.*, \([0-9]*\) work units).*/\1/p' <<<"$out" | awk '{s += $1} END {print s + 0}')
    r=$(sed -n 's/^reading: \([0-9]*\) relation calls$/\1/p' <<<"$out")
    echo "$u ${r:-none}"
}
instructions() { perf stat -x, -e instructions:u "$@" 2>&1 >/dev/null | awk -F, '/instructions/ {print $1}'; }
ratio() { awk -v a="$1" -v b="$2" -v z="$3" 'BEGIN {if (b - z <= 0) print "inf"; else printf "%.2f", (a - z) / (b - z)}'; }
above() { awk -v r="$1" -v l="$limit" 'BEGIN {exit !(r == "inf" || r + 0 > l + 0)}'; }
for kind in decls notation shared; do
    sizes=(0 "$scale_n" $((2 * scale_n)))
    for n in "${sizes[@]}"; do
        (cd "$work" && "$cetta" --lang petta "$here/scaling.metta" "$kind" "$n" "scaling-$kind-$n.mg" > /dev/null)
    done
    u=(); q=()
    for n in "${sizes[@]}"; do
        read -r a b <<<"$(counts "$work/scaling-$kind-$n.mg")"; u+=("$a"); q+=("$b")
    done
    if [[ " ${u[*]} " == *" fail "* ]]; then
        echo "FAIL scaling: $kind: a workload is not verified by mg-check"; fail=1; continue
    fi
    r=$(ratio "${u[2]}" "${u[1]}" "${u[0]}")
    line="scaling:   $kind (N = $scale_n): kernel work $r"
    above "$r" && { echo "FAIL scaling: $kind: kernel work grows by $r when the size doubles (limit $limit)"; fail=1; }
    if [[ " ${q[*]} " == *" none "* ]]; then
        line="$line, reader calls not counted (mg-check built without GN_COUNT)"
    else
        rq=$(ratio "${q[2]}" "${q[1]}" "${q[0]}")
        line="$line, reader calls $rq"
        above "$rq" && { echo "FAIL scaling: $kind: the reader's relation calls grow by $rq when the size doubles (limit $limit)"; fail=1; }
    fi
    if [[ $have_perf == 1 ]]; then
        c=(); m=()
        for n in "${sizes[@]}"; do
            c+=("$(instructions "$mgcheck" -I "$preamble" "$work/scaling-$kind-$n.mg")")
            m+=("$(instructions "$megalodon" -I "$preamble" "$work/scaling-$kind-$n.mg")")
        done
        rc=$(ratio "${c[2]}" "${c[1]}" "${c[0]}"); rm_=$(ratio "${m[2]}" "${m[1]}" "${m[0]}")
        line="$line, mg-check instructions $rc, megalodon instructions $rm_ (reported)"
        above "$rc" && { echo "FAIL scaling: $kind: mg-check's instructions grow by $rc when the size doubles (limit $limit)"; fail=1; }
    else
        line="$line (instructions not counted: perf is not available)"
    fi
    echo "$line"
done
exit $fail
