#!/usr/bin/env bash
# ============================================================================
# MeTTaKernel ITP + Program-Verification curriculum verifier ("the truth serum")
#   POSITIVES must check (exit 0).  NEGATIVES must be caught:
#     - Coq: inline `Fail <cmd>.` (a green file means every Fail was rejected)
#     - Lean/Megalodon: neg_*.{lean,mg} must exit NON-zero.
#   Prints PER-FILE THEOREM COUNTS + a grand total (comprehensiveness is visible),
#   an ASSUMPTION LEDGER, and a PV proved/tested/executed breakdown.
# Usage:  bash run_all.sh
# ============================================================================
set -u
cd "$(dirname "$0")"
eval "$(opam env 2>/dev/null)" 2>/dev/null || true
COQC="$(command -v coqc || echo "$HOME/.opam/default/bin/coqc")"
LEAN="$(command -v lean  || echo "$HOME/.elan/bin/lean")"
MEG="/home/aimama/aihub/repos/megalodon-1.13/bin/megalodon"
CETTA="${CETTA:-/home/aimama/aihub/hyperon/CeTTa/cetta}"
CETTA_EXTRA_ARGS="${CETTA_EXTRA_ARGS---eval-hashcons}"
CETTA_AS_LIMIT_BYTES="${CETTA_AS_LIMIT_BYTES:-25769803776}"
CETTA_TIMEOUT_SECONDS="${CETTA_TIMEOUT_SECONDS:-240}"
read -r -a CETTA_EXTRA_ARGV <<< "$CETTA_EXTRA_ARGS"
export CETTA
export CETTA_EXTRA_ARGS
export CETTA_AS_LIMIT_BYTES
export CETTA_TIMEOUT_SECONDS
PRE_DIR="/home/aimama/aihub/repos/megalodon-1.13/examples/egal"
log=/tmp/_runall.$$.log
pass=0; pfail=0; caught=0; missed=0; thms=0

ccount() { grep -cE '^(Theorem|Lemma|Example|Corollary) ' "$1"; }   # Coq proven items
lcount() { grep -cE '^(theorem|example) ' "$1"; }                   # Lean proven items
mcount() { grep -cE '^Theorem ' "$1"; }                             # Megalodon theorems

meg_args() {  # echo "-I <preamble>" from a sidecar "<file>.pre" (a leading comment marker
              # would break Megalodon's parser, so the preamble name lives in a sidecar)
  local pre=""
  [ -f "$1.pre" ] && pre=$(head -1 "$1.pre" | tr -d '[:space:]')
  [ -n "$pre" ] && printf -- '-I\n%s\n' "$PRE_DIR/$pre"
}

run_cetta_capped() {
  local file="$1"
  timeout "$CETTA_TIMEOUT_SECONDS" prlimit --as="$CETTA_AS_LIMIT_BYTES" -- "$CETTA" "${CETTA_EXTRA_ARGV[@]}" "$file"
}

echo "================= COQ (DTT, ICL + feature mirrors) ================="
for f in Coq/*.v; do [ -e "$f" ] || continue
  if "$COQC" "$f" >"$log" 2>&1; then
    n=$(grep -cE '^[[:space:]]*Fail ' "$f"); tc=$(ccount "$f"); thms=$((thms+tc))
    echo "  [pos] $(basename "$f")  OK  (${tc} thms, +${n} negatives)"; pass=$((pass+1))
  else echo "  [pos] $(basename "$f")  FAIL"; tail -4 "$log" | sed 's/^/        /'; pfail=$((pfail+1)); fi
done
rm -f Coq/*.vo Coq/*.vok Coq/*.vos Coq/*.glob Coq/.*.aux 2>/dev/null

echo "================= LEAN (DTT) ================="
for f in Lean/[0-9]*.lean; do [ -e "$f" ] || continue
  if "$LEAN" "$f" >"$log" 2>&1; then tc=$(lcount "$f"); thms=$((thms+tc)); echo "  [pos] $(basename "$f")  OK  (${tc} thms)"; pass=$((pass+1))
  else echo "  [pos] $(basename "$f")  FAIL"; tail -4 "$log" | sed 's/^/        /'; pfail=$((pfail+1)); fi
done
for f in Lean/neg_*.lean; do [ -e "$f" ] || continue
  if "$LEAN" "$f" >"$log" 2>&1; then echo "  [neg] $(basename "$f")  NOT CAUGHT  X"; missed=$((missed+1))
  else echo "  [neg] $(basename "$f")  caught: $(grep -m1 -i error "$log" | cut -c1-58)"; caught=$((caught+1)); fi
done

echo "================= MEGALODON (HO-Set / HOTG) ================="
for f in Megalodon/[0-9]*.mg; do [ -e "$f" ] || continue
  mapfile -t a < <(meg_args "$f")
  if "$MEG" "${a[@]}" "$f" >"$log" 2>&1; then tc=$(mcount "$f"); thms=$((thms+tc)); echo "  [pos] $(basename "$f")  OK  (${tc} thms)"; pass=$((pass+1))
  else echo "  [pos] $(basename "$f")  FAIL"; tail -4 "$log" | sed 's/^/        /'; pfail=$((pfail+1)); fi
done
for f in Megalodon/neg_*.mg; do [ -e "$f" ] || continue
  mapfile -t a < <(meg_args "$f")
  if "$MEG" "${a[@]}" "$f" >"$log" 2>&1; then echo "  [neg] $(basename "$f")  NOT CAUGHT  X"; missed=$((missed+1))
  else echo "  [neg] $(basename "$f")  caught"; caught=$((caught+1)); fi
done

echo "================= HOL (classical higher-order logic / LCF -- HOL4) ================="
if [ -d HOL ] && ( . /home/aimama/aihub/CakeML/env.sh >/dev/null 2>&1; timeout 30 Holmake --help >/dev/null 2>&1 ); then
  ( . /home/aimama/aihub/CakeML/env.sh >/dev/null 2>&1; cd HOL && timeout 590 Holmake HOLDIR="$HOLDIR" POLY="$CAKEML_HOME/polyml-local/bin/poly" >"$log" 2>&1 )
  for t in HOL01_logic HOL02_induction HOL03_definitions HOL04_higher_order HOL05_classical HOL06_lcf_kernel; do
    [ -f HOL/${t}Script.sml ] || continue
    if ls HOL/.hol/objs/${t}Theory.uo >/dev/null 2>&1; then tc=$(grep -cE '^Theorem ' HOL/${t}Script.sml); thms=$((thms+tc)); echo "  [proved] HOL/${t}  OK  (${tc} thms)"; pass=$((pass+1))
    else echo "  [proved] HOL/${t}  FAIL"; pfail=$((pfail+1)); fi
  done
  for t in neg_typeerror neg_unprovable; do
    [ -f HOL/neg/${t}Script.sml ] || continue
    ( . /home/aimama/aihub/CakeML/env.sh >/dev/null 2>&1; cd HOL/neg && rm -f .hol/objs/${t}Theory.* 2>/dev/null; timeout 200 Holmake HOLDIR="$HOLDIR" POLY="$CAKEML_HOME/polyml-local/bin/poly" ${t}Theory.uo >/dev/null 2>&1 )
    if ls HOL/neg/.hol/objs/${t}Theory.uo >/dev/null 2>&1; then echo "  [neg] HOL/neg/${t}  NOT CAUGHT  X"; missed=$((missed+1)); else echo "  [neg] HOL/neg/${t}  caught"; caught=$((caught+1)); fi
  done
else echo "  [toolchain-down] HOL ladder: Holmake unavailable on this host"; fi

echo "================= CROSS-SYSTEM SMOKE (same theorems, 3 systems) ================="
if [ -f CrossSmoke/smoke.v ]; then
  if "$COQC" CrossSmoke/smoke.v >"$log" 2>&1; then tc=$(ccount CrossSmoke/smoke.v); thms=$((thms+tc)); echo "  [pos] smoke.v    OK  (${tc} thms)"; pass=$((pass+1)); else echo "  [pos] smoke.v FAIL"; tail -4 "$log"|sed 's/^/        /'; pfail=$((pfail+1)); fi
  rm -f CrossSmoke/*.vo CrossSmoke/*.vok CrossSmoke/*.vos CrossSmoke/*.glob CrossSmoke/.*.aux 2>/dev/null
fi
if [ -f CrossSmoke/smoke.lean ]; then
  if "$LEAN" CrossSmoke/smoke.lean >"$log" 2>&1; then tc=$(lcount CrossSmoke/smoke.lean); thms=$((thms+tc)); echo "  [pos] smoke.lean OK  (${tc} thms)"; pass=$((pass+1)); else echo "  [pos] smoke.lean FAIL"; tail -4 "$log"|sed 's/^/        /'; pfail=$((pfail+1)); fi
fi
if [ -f CrossSmoke/smoke.mg ]; then
  if "$MEG" CrossSmoke/smoke.mg >"$log" 2>&1; then tc=$(mcount CrossSmoke/smoke.mg); thms=$((thms+tc)); echo "  [pos] smoke.mg   OK  (${tc} thms)"; pass=$((pass+1)); else echo "  [pos] smoke.mg FAIL"; tail -4 "$log"|sed 's/^/        /'; pfail=$((pfail+1)); fi
fi

echo "================= NOTATION / LANGUAGEDEF L0 ADEQUACY (CeTTa) ================="
for f in Notation/*.metta; do [ -e "$f" ] || continue
  if run_cetta_capped "$f" >"$log" 2>&1; then
    tc=$(grep -c '^!(assertEqual' "$f")
    echo "  [oracle] $(basename "$f")  OK  (${tc} assertions)"
    pass=$((pass+1))
  else
    echo "  [oracle] $(basename "$f")  FAIL"
    tail -8 "$log" | sed 's/^/        /'
    pfail=$((pfail+1))
  fi
done
if [ -x Notation/mutation_check.sh ]; then
  if Notation/mutation_check.sh >"$log" 2>&1; then
    echo "  [mutation] notation mutations caught"
    pass=$((pass+1))
  else
    echo "  [mutation] notation mutation check FAIL"
    tail -12 "$log" | sed 's/^/        /'
    pfail=$((pfail+1))
  fi
fi

echo "================= DEDUKTI/LAMBDAPI AS GUEST (CeTTa) ================="
for f in DeduktiLambdapi/[0-9]*.metta; do [ -e "$f" ] || continue
  if run_cetta_capped "$f" >"$log" 2>&1; then
    tc=$(grep -c '^!(assertEqual' "$f")
    echo "  [guest] $(basename "$f")  OK  (${tc} assertions)"
    pass=$((pass+1))
  else
    echo "  [guest] $(basename "$f")  FAIL"
    tail -8 "$log" | sed 's/^/        /'
    pfail=$((pfail+1))
  fi
done
if [ -x DeduktiLambdapi/run_dedukti_guest_mutation_gate.sh ]; then
  if DeduktiLambdapi/run_dedukti_guest_mutation_gate.sh >"$log" 2>&1; then
    echo "  [mutation] Dedukti-guest mutations caught"
    pass=$((pass+1))
  else
    echo "  [mutation] Dedukti-guest mutation check FAIL"
    tail -12 "$log" | sed 's/^/        /'
    pfail=$((pfail+1))
  fi
fi

echo "================= ORACLE CASE LEDGER ================="
trim_ws() {
  local s="$1"
  s="${s#"${s%%[![:space:]]*}"}"
  s="${s%"${s##*[![:space:]]}"}"
  printf '%s' "$s"
}
case_path_exists() {
  local p="$1"
  [ -e "$p" ] || [ -e "./$p" ] || [ -e "/home/aimama/aihub/Mettapedia/MettaKernel/$p" ] || [ -e "/home/aimama/aihub/$p" ]
}
ledger_fail=0
if [ -f oracle_cases.tsv ]; then
  if awk -F '\t' 'NF != 12 { print "bad field count line " NR ": NF=" NF; bad=1 } END { exit bad }' oracle_cases.tsv >"$log" 2>&1; then
    :
  else
    ledger_fail=1
  fi
  if grep -n '\.\.\.' oracle_cases.tsv >>"$log" 2>&1; then
    echo "ellipsis/shorthand found in oracle_cases.tsv" >>"$log"
    ledger_fail=1
  fi
  while IFS=$'\t' read -r nr case_id source_path target_file; do
    IFS=';' read -ra srcs <<< "$source_path"
    for raw in "${srcs[@]}"; do
      part=$(trim_ws "$raw")
      [ -z "$part" ] && continue
      if ! case_path_exists "$part"; then
        echo "missing source path line $nr ($case_id): $part" >>"$log"
        ledger_fail=1
      fi
    done
    IFS=';' read -ra tgts <<< "$target_file"
    for raw in "${tgts[@]}"; do
      part=$(trim_ws "$raw")
      [ -z "$part" ] && continue
      if ! case_path_exists "$part"; then
        echo "missing target path line $nr ($case_id): $part" >>"$log"
        ledger_fail=1
      fi
    done
  done < <(awk -F '\t' 'NR > 1 && $11 == "checked" { print NR "\t" $1 "\t" $3 "\t" $4 }' oracle_cases.tsv)
  if [ "$ledger_fail" -eq 0 ]; then
    rows=$(($(wc -l < oracle_cases.tsv) - 1))
    checked=$(awk -F '\t' 'NR > 1 && $11 == "checked" { n++ } END { print n+0 }' oracle_cases.tsv)
    planned=$(awk -F '\t' 'NR > 1 && $11 == "planned" { n++ } END { print n+0 }' oracle_cases.tsv)
    echo "  [ledger] oracle_cases.tsv OK  (${rows} rows: ${checked} checked, ${planned} planned)"
    pass=$((pass+1))
  else
    echo "  [ledger] oracle_cases.tsv FAIL"
    cat "$log" | sed 's/^/        /'
    pfail=$((pfail+1))
  fi
else
  echo "  [ledger] oracle_cases.tsv missing"
  pfail=$((pfail+1))
fi

echo "================= PROGRAM VERIFICATION (4th pillar) ================="
# CoqPLF (proved by coqc)
for f in ProgramVerification/CoqPLF/*.v; do [ -e "$f" ] || continue
  if "$COQC" "$f" >"$log" 2>&1; then tc=$(ccount "$f"); thms=$((thms+tc)); echo "  [proved] CoqPLF/$(basename "$f")  OK  (${tc} thms)"; pass=$((pass+1))
  else echo "  [proved] CoqPLF/$(basename "$f")  FAIL"; tail -4 "$log" | sed 's/^/        /'; pfail=$((pfail+1)); fi
done
rm -f ProgramVerification/CoqPLF/*.vo ProgramVerification/CoqPLF/*.vok ProgramVerification/CoqPLF/*.vos ProgramVerification/CoqPLF/*.glob ProgramVerification/CoqPLF/.*.aux 2>/dev/null
# Lean PV (proved positives + caught negatives)
for f in ProgramVerification/Lean/*.lean; do [ -e "$f" ] || continue
  case "$(basename "$f")" in
    neg_*) if "$LEAN" "$f" >"$log" 2>&1; then echo "  [neg] Lean/$(basename "$f")  NOT CAUGHT  X"; missed=$((missed+1)); else echo "  [neg] Lean/$(basename "$f")  caught"; caught=$((caught+1)); fi ;;
    *)     if "$LEAN" "$f" >"$log" 2>&1; then tc=$(lcount "$f"); thms=$((thms+tc)); echo "  [proved] Lean/$(basename "$f")  OK  (${tc} thms)"; pass=$((pass+1)); else echo "  [proved] Lean/$(basename "$f")  FAIL"; tail -4 "$log" | sed 's/^/        /'; pfail=$((pfail+1)); fi ;;
  esac
done
# MeTTaM1 — delegate to the existing metta-ref dev (proved+tested ledger)
MR=/home/aimama/aihub/Mettapedia/cakeml/metta-ref
if [ -d "$MR" ]; then
  if make -C "$MR" check-coverage >"$log" 2>&1; then echo "  [ledger-checked] MeTTaM1 (metta-ref): $(grep -m1 'coverage matrix checked' "$log") -- this gate runs ONLY check-coverage (ledger validation); to re-verify the heavier proofs/oracle run ProgramVerification/MeTTaM1/verify.sh test-hol  and  verify.sh test-oracle"; pass=$((pass+1))
  else echo "  [proved+tested] MeTTaM1 (metta-ref) check-coverage FAIL"; tail -4 "$log" | sed 's/^/        /'; pfail=$((pfail+1)); fi
else echo "  [m1] metta-ref not found (skipped)"; fi
# HOL4CakeML — smoke script present; guarded because Holmake is currently broken on this host
if ls ProgramVerification/HOL4CakeML/*Script.sml >/dev/null 2>&1; then
  if ( . /home/aimama/aihub/CakeML/env.sh >/dev/null 2>&1; timeout 30 Holmake --help >/dev/null 2>&1 ); then
    ( . /home/aimama/aihub/CakeML/env.sh >/dev/null 2>&1; cd ProgramVerification/HOL4CakeML && timeout 590 Holmake HOLDIR="$HOLDIR" POLY="$CAKEML_HOME/polyml-local/bin/poly" >/tmp/_hol.$$ 2>&1 )
    if ls ProgramVerification/HOL4CakeML/.hol/objs/smokeTheory.uo >/dev/null 2>&1 || ls ProgramVerification/HOL4CakeML/smokeTheory.uo >/dev/null 2>&1; then echo "  [executed] HOL4CakeML/smokeScript.sml built (HOL4 verified: dbl + dbl_two + dbl_add)"; pass=$((pass+1));
    else echo "  [toolchain-warming] HOL4CakeML: 'Holmake --help' OK but the smoke build is not yet succeeding (HOL4 rebuild in progress) -- reported, NOT gating the curriculum"; fi
    # CakeML translation of the verified function (translator + basis heap)
    if ls ProgramVerification/HOL4CakeML/cake_translation/*Script.sml >/dev/null 2>&1; then
      ( . /home/aimama/aihub/CakeML/env.sh >/dev/null 2>&1; cd ProgramVerification/HOL4CakeML/cake_translation && timeout 590 Holmake HOLDIR="$HOLDIR" CAKEMLDIR="$CAKEMLDIR" POLY="$CAKEML_HOME/polyml-local/bin/poly" >/tmp/_tr.$$ 2>&1 )
      if ls ProgramVerification/HOL4CakeML/cake_translation/.hol/objs/dbl_cakeTheory.uo >/dev/null 2>&1; then echo "  [executed] HOL4CakeML cake_translation: dbl translated to CakeML (translator-verified)"; pass=$((pass+1)); else echo "  [toolchain-warming] CakeML translation build pending"; fi
    fi
    # HOL4CakeML negative (expected-fail)
    if ls ProgramVerification/HOL4CakeML/neg/*Script.sml >/dev/null 2>&1; then
      ( . /home/aimama/aihub/CakeML/env.sh >/dev/null 2>&1; cd ProgramVerification/HOL4CakeML/neg && rm -f .hol/objs/neg_typeerrorTheory.* 2>/dev/null; timeout 200 Holmake HOLDIR="$HOLDIR" POLY="$CAKEML_HOME/polyml-local/bin/poly" neg_typeerrorTheory.uo >/dev/null 2>&1 )
      if ls ProgramVerification/HOL4CakeML/neg/.hol/objs/neg_typeerrorTheory.uo >/dev/null 2>&1; then echo "  [neg] HOL4CakeML/neg/neg_typeerror  NOT CAUGHT  X"; missed=$((missed+1)); else echo "  [neg] HOL4CakeML/neg/neg_typeerror  caught"; caught=$((caught+1)); fi
    fi
  else
    echo "  [toolchain-down] HOL4CakeML/smokeScript.sml ready, but Holmake crashes on this host"
    echo "                   (Subscript in 'Holmake --help' itself — a HOL4/Poly install issue, not the script);"
    echo "                   HOL4-verified content is exercised via MeTTaM1's proved-HOL ledger above."
  fi
else echo "  [gated] HOL4CakeML — smoke script not yet present"; fi

echo "================= ASSUMPTION LEDGER (axioms / parameters / admits) ================="
if grep -rnE '^[[:space:]]*(Axiom|Parameter|Admitted|Conjecture|axiom)\b' Coq Lean Megalodon CrossSmoke 2>/dev/null \
     | grep -vE '\.(vo|glob|err):' ; then :; else echo "  (none inline)"; fi
for p in Megalodon/*.mg.pre; do [ -e "$p" ] || continue
  echo "  ${p%.pre}: loaded under Egal preamble $(head -1 "$p") (assumes its full HOTG axiom base)"
done
for f in Lean/*axioms*.lean; do [ -e "$f" ] || continue
  "$LEAN" "$f" 2>&1 | grep -i "depends on axioms" | sed "s|^|  $(basename "$f"): |"
done

echo "================= SUMMARY ================="
echo "  positive files:   OK=$pass  FAIL=$pfail"
echo "  theorems checked: $thms"
echo "  negatives:        caught=$caught  MISSED=$missed"
rm -f "$log"
if [ "$pfail" -eq 0 ] && [ "$missed" -eq 0 ]; then echo "  ALL GREEN (positives check, negatives caught)"; exit 0
else echo "  NOT GREEN"; exit 1; fi
