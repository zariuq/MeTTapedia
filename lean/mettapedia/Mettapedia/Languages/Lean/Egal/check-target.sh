#!/usr/bin/env bash
# Check the Egal reading of a carried Lean development with two checkers.
#
#   check-target.sh TARGET
#
# The document, in this order, must be accepted by Megalodon and verified by
# mg-check: the general construction (LeanInEgal.mg, with Library/Conversion.mg
# before it and Library/Typing.mg and the numerals' digits, Library/Digits.mg,
# after it), TARGET's generated
# families, facts about equality (Library/EqFacts.mg), numerals (Numerals.mg),
# decidable propositions (Decidable.mg), decisions about numerals
# (Library/NumeralDecisions.mg), the library files listed in
# targets/TARGET.library, TARGET's generated functions, the natively computed
# operations listed in targets/TARGET.primitives, TARGET's generated
# computations and theorems, and the reader's presentation/TARGET.mg if any.  Each controls/TARGET/reject_*.mg is appended to the reading it
# contradicts (the document before the computations and theorems) and must be refused by both,
# at the same source position, inside the control.
#
#   MEGALODON  the Megalodon binary   (default: megalodon/bin/megalodon here)
#   MG_CHECK   the mg-check binary    (default: mg-check on PATH)
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(cd "$here/../../../../../.." && pwd)
megalodon=${MEGALODON:-$root/megalodon/bin/megalodon}
mgcheck=${MG_CHECK:-mg-check}
preamble=$root/megalodon/examples/egal/PfgEAug2022Preamble.mgs
target=${1:?usage: check-target.sh TARGET}
gen=$here/generated/$target
work=$(mktemp -d "${TMPDIR:-/tmp}/lean-in-egal-target.XXXXXX")
cleanup() {
    rm -f -- "$work/doc.mg" "$work/library.mg" "$work/reading.mg" "$work"/[mc].out "$work"/[mc].status
    rmdir -- "$work"
}
trap cleanup EXIT
library=$work/library.mg
listed() {
    [[ -e "$here/targets/$target.$1" ]] || return 0
    grep -v '^\s*\(#\|$\)' "$here/targets/$target.$1" | sed "s|^|$here/|"
}
# The core files read after the families: targets/TARGET.core, or by default
# equality, numerals and decidable propositions.
if [[ -e "$here/targets/$target.core" ]]; then
    mapfile -t core < <(listed core)
else
    core=("$here/Library/EqFacts.mg" "$here/Numerals.mg" "$here/Decidable.mg" "$here/Library/NumeralDecisions.mg")
fi
mapfile -t extra < <(listed library)
mapfile -t primitives < <(listed primitives)
reading=$work/reading.mg
cat "$here/Library/Conversion.mg" "$here/LeanInEgal.mg" "$here/Library/Typing.mg" "$here/Library/Digits.mg" "$gen/Families.mg" "${core[@]}" "${extra[@]}" "$gen/Functions.mg" "${primitives[@]}" \
    > "$reading"
presentation=()
[[ -e "$here/presentation/$target.mg" ]] && presentation=("$here/presentation/$target.mg")
cat "$reading" "$gen/Computations.mg" "$gen/Theorems.mg" "${presentation[@]}" > "$library"
fail=0

# The two checkers run side by side; each writes its output and exit status.
run() {
    rm -f -- "$3.status"
    if "$1" -I "$preamble" "$2" > "$3.out" 2>&1; then echo 0 > "$3.status"; else echo 1 > "$3.status"; fi
}
run "$megalodon" "$library" "$work/m" & run "$mgcheck" "$library" "$work/c" & wait
if [[ $(cat "$work/m.status") == 0 ]]; then
    echo "megalodon: $target accepted"
else
    echo "megalodon: $target refused: $(cat "$work/m.out")"; fail=1
fi
if [[ $(cat "$work/c.status") == 0 ]]; then
    echo "mg-check:  $target $(grep '^summary' "$work/c.out")"
else
    echo "mg-check:  $target not verified:"; grep -v '^(Meg' "$work/c.out"; fail=1
fi

offset=$(wc -l < "$reading")
for control in "$here"/controls/"$target"/reject_*.mg; do
    [[ -e "$control" ]] || continue
    name=$(basename "$control")
    cat "$reading" "$control" > "$work/doc.mg"
    run "$megalodon" "$work/doc.mg" "$work/m" & run "$mgcheck" "$work/doc.mg" "$work/c" & wait
    m=$(cat "$work/m.out"); c=$(cat "$work/c.out")
    [[ $(cat "$work/m.status") == 0 ]] && { echo "FAIL $name: accepted by megalodon"; fail=1; continue; }
    [[ $(cat "$work/c.status") == 0 ]] && { echo "FAIL $name: verified by mg-check"; fail=1; continue; }
    mline=$(grep -o '^Failure at line [0-9]* char [0-9]*' <<<"$m" | head -1 || true)
    cline=$(grep -o 'failed: Failure at line [0-9]* char [0-9]*' <<<"$c" | head -1 | sed 's/^failed: //' || true)
    line=$(grep -o 'line [0-9]*' <<<"$mline" | grep -o '[0-9]*' || echo 0)
    if [[ -n "$mline" && "$mline" == "$cline" && "$line" -gt "$offset" ]]; then
        echo "refused:   $name (control line $((line - offset)), $(grep -o 'char [0-9]*' <<<"$mline"), both checkers)"
    else
        echo "FAIL $name: megalodon '$mline', mg-check '$cline' (the reading has $offset lines)"; fail=1
    fi
done
exit $fail
