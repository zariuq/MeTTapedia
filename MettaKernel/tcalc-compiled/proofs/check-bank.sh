#!/bin/sh
# Qualify the accepted mathematics and exact leaves independently of the WIP adapter.
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(dirname -- "$here")
mode=native
if [ "${1:-}" = --math-only ]; then mode=math; shift; fi
if [ "$#" -gt 1 ]; then echo "usage: $0 [--math-only] [OUTPUT-DIRECTORY]" >&2; exit 2; fi
HOLDIR=$(CDPATH= cd -- "${HOLDIR:-$here/../../../../repos/hol-light}" && pwd)
S2N=$(CDPATH= cd -- "${S2N:-$here/../../../../repos/s2n-bignum}" && pwd)
export HOLLIGHT_DIR="$HOLDIR" HOLLIGHT_USE_MODULE=1
HOLLIGHT_LOAD_PATH="$S2N:$root/..${HOLLIGHT_LOAD_PATH:+:$HOLLIGHT_LOAD_PATH}"
export HOLLIGHT_LOAD_PATH
if [ "$#" -eq 1 ]; then
  if [ -e "$1" ]; then echo "output already exists: $1" >&2; exit 2; fi
  mkdir -p -- "$1"
  out=$(CDPATH= cd -- "$1" && pwd)
else
  mkdir -p -- "$root/build-proof-bank"
  out=$(mktemp -d "$root/build-proof-bank/$mode.XXXXXX")
fi
ml_string() { printf '%s' "$1" | sed 's/\\/\\\\/g; s/"/\\"/g'; }
record() { sha256sum -- "$1" >> "$out/inputs.before"; }
: > "$out/inputs.before"
for name in flat_spec ordinary_flat ordinary_pack_spec cesta_adapter_semantics bank_controls bank_math; do
  record "$here/$name.ml"
done
record "$here/check-bank.sh"
record "$HOLDIR/hol.sh"
record "$HOLDIR/hol_lib.cmxa"
record "$HOLDIR/hol_lib.a"
printf 'bank %s: %s\n' "$mode" "$out"
if [ "$mode" = native ]; then
  for name in flat_fire flat_fire_trace flat_trace_base flat_trace_weaken flat_workspace flat_trace_workspace flat_trace_wide flat_fire_wide mm_sub1_leaf bank_native; do
    record "$here/$name.ml"
  done
  record "$root/flat_fire.S"
  record "$root/flat_fire.h"
  record "$root/test_flat_fire.c"
  record "$root/mm_sub1_leaf.o"
  record "$here/../../../../cesta/adapters/hol/pilot/span_words.ml"
  as --64 "$root/flat_fire.S" -o "$out/flat_fire.o"
  for cc in gcc clang; do
    "$cc" -std=c11 -O2 -Wall -Wextra -Werror "$root/test_flat_fire.c" "$out/flat_fire.o" -o "$out/flat-$cc"
    "$out/flat-$cc" > "$out/runtime-$cc.log"
  done
  sed 's/cmovne %ebp, %r11d/cmove %ebp, %r11d/' "$root/flat_fire.S" > "$out/flat-mutant.S"
  if cmp -s "$root/flat_fire.S" "$out/flat-mutant.S"; then echo "semantic mutation did not apply" >&2; exit 1; fi
  gcc -std=c11 -O2 -Wall -Wextra -Werror "$root/test_flat_fire.c" "$out/flat-mutant.S" -o "$out/flat-mutant"
  if "$out/flat-mutant" > "$out/mutation.log" 2>&1; then echo "semantic mutation survived" >&2; exit 1; fi
fi
{
  if [ "$mode" = native ]; then
    printf 'let flat_fire_object = "%s";;\n' "$(ml_string "$out/flat_fire.o")"
    printf 'let mm_sub1_leaf_object = "%s";;\n' "$(ml_string "$root/mm_sub1_leaf.o")"
  fi
  printf 'needs "%s";;\n' "$(ml_string "$here/bank_$mode.ml")"
  if [ "$mode" = native ]; then
    printf 'let theorems = bank_math_theorems @ bank_native_theorems;;\n'
  else
    printf 'let theorems = bank_math_theorems;;\n'
  fi
  cat <<'ML'
List.iter (fun (name,theorem) ->
  if hyp theorem <> [] then failwith ("undischarged assumptions: " ^ name)) theorems;;
check_axioms ();;
print_endline "BANK_AXIOMS_CHECKED";;
List.iter (fun (name,theorem) ->
  Printf.printf "BANK_THEOREM %s %s\n%!" name (string_of_thm theorem)) theorems;;
Printf.printf "BANK_ACCEPTED %d\n%!" (List.length theorems);;
ML
} > "$out/bank.ml"
(
  cd -- "$out"
  "$HOLDIR/hol.sh" inline-load "$out/bank.ml" "$out/bank.inlined.ml"
  "$HOLDIR/hol.sh" compile "$out/bank.inlined.ml" -o "$out/bank.cmx" -w -a
  "$HOLDIR/hol.sh" link "$out/bank.cmx" -o "$out/bank.native"
) > "$out/build.log" 2>&1
"$out/bank.native" > "$out/proof.log" 2>&1
grep -q '^BANK_AXIOMS_CHECKED$' "$out/proof.log"
grep -q '^BANK_ACCEPTED ' "$out/proof.log"
if [ "$mode" = native ]; then
  for name in FLAT_FIRE_CORRECT FLAT_FIRE_TRACED_CORRECT FLAT_FIRE_FULL_WORKSPACE_CORRECT FLAT_FIRE_TRACED_FULL_WORKSPACE_CORRECT MM_SUB1_LEAF_INSIDE MM_SUB1_LEAF_OUTSIDE; do
    grep -q "^BANK_THEOREM $name " "$out/proof.log"
  done
fi
for name in ORDINARY_FIRE_REFINEMENT ORDINARY_ADAPTER_PACKED_VALID ORDINARY_ADAPTER_FIRE_REFINEMENT ORDINARY_BANK_SELECTS_CONSTANT ORDINARY_BANK_REFUSES_MISMATCH ORDINARY_BANK_REFUSES_BAD_COLUMN ORDINARY_BANK_REFUSES_SHORT_SOURCE; do
  grep -q "^BANK_THEOREM $name " "$out/proof.log"
done
sha256sum -c "$out/inputs.before" > "$out/inputs.checked"
{
  printf 'scope: accepted %s contracts; complete adapter and pack proofs remain open\n' "$mode"
  printf 'fresh-process: yes\naxiom-audit: passed\n'
  grep '^BANK_ACCEPTED ' "$out/proof.log"
  if [ "$mode" = native ]; then printf 'native-controls: GCC and Clang passed; changed guard refused\n'; fi
} > "$out/result.txt"
sha256sum -- "$out/bank.inlined.ml" "$out/bank.native" "$out/proof.log" > "$out/artifacts.sha256"
cat "$out/result.txt"
printf 'evidence: %s\n' "$out"
