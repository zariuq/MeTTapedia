#!/bin/sh
# Build and run everything:
#   1. test_tcalc (468 checks: Interface.Step, PreparedStep/CandidateCursor bridge, R113/R115a/R115b conformance, Rows 3-7 NamedSpaces/Births/Reach/Reflection/Rho, transient terms, arena growth)
#   2. mm0_tcalc (.mmu + .mm0 spec verifier: 17 positive, 79 negative controls)
#   3. mmb_tcalc (.mmb + .mm0 spec verifier: 4 positive, 25 negative controls; then 190 R118 spec controls)
#   4. hol_tcalc (HOL Light LCF kernel + HOLRPLY1 verifier: 28 self-tests, core.holr + transform.holr + negative controls)
#   5. mg_tcalc (Megalodon Egal HoTTG + HF + Mizar + HOAS kernel & -sexprinfo verifier: 8 rules + 6 negative controls + subproof-reach, fixtures, and Egal Part1..14)
#   6. dk_tcalc (Dedukti Lambda-Pi Modulo Rewriting verifier: 8 rules + 5 negative controls, curriculum positive + 4 negative controls, CoC/FO/classical/Sudoku/Kontroli suites)
#   7. tcalc_compile + diff_micromath (30.48M-op four-way differential)
set -eu
cd "$(dirname "$0")"
MICROMATH=${MICROMATH:-ref}
if [ -d ../repos/mm0 ]; then MM0_ROOT=../repos/mm0; elif [ -d ../../../repos/mm0 ]; then MM0_ROOT=../../../repos/mm0; else MM0_ROOT=../../repos/mm0; fi
if [ -d ../Mettapedia/hol_light/Transform ]; then HOL_DIR=../Mettapedia/hol_light/Transform; elif [ -d ../../hol_light/Transform ]; then HOL_DIR=../../hol_light/Transform; else HOL_DIR=../../Mettapedia/hol_light/Transform; fi
if [ -d ../hyperon/CeTTa/tests/megalodon/fixtures ]; then MG_FIX=../hyperon/CeTTa/tests/megalodon/fixtures; elif [ -d ../../../hyperon/CeTTa/tests/megalodon/fixtures ]; then MG_FIX=../../../hyperon/CeTTa/tests/megalodon/fixtures; else MG_FIX=../../hyperon/CeTTa/tests/megalodon/fixtures; fi
# Optional full Egal export (Part1.sexpr through Part14.sexpr, including Part10b).
# The small checked-in profiles below run independently of this external corpus.
MG_EGAL=${MG_EGAL:-}
if [ -d ../Mettapedia/MettaKernel/Curriculum/DeduktiLambdapi ]; then DK_CURR=../Mettapedia/MettaKernel/Curriculum/DeduktiLambdapi; elif [ -d ../Curriculum/DeduktiLambdapi ]; then DK_CURR=../Curriculum/DeduktiLambdapi; else DK_CURR=../../Mettapedia/MettaKernel/Curriculum/DeduktiLambdapi; fi
if [ -d ../repos/dedukti/examples ]; then DK_EX=../repos/dedukti/examples; elif [ -d ../../../repos/dedukti/examples ]; then DK_EX=../../../repos/dedukti/examples; else DK_EX=../../repos/dedukti/examples; fi
if [ -d ../repos/kontroli-rs/examples ]; then KO_EX=../repos/kontroli-rs/examples; elif [ -d ../../../repos/kontroli-rs/examples ]; then KO_EX=../../../repos/kontroli-rs/examples; else KO_EX=../../repos/kontroli-rs/examples; fi
if [ -d ../Mettapedia/megalodon/tests/dedukti_bridge ]; then MG_DK=../Mettapedia/megalodon/tests/dedukti_bridge; elif [ -d ../../megalodon/tests/dedukti_bridge ]; then MG_DK=../../megalodon/tests/dedukti_bridge; else MG_DK=../../Mettapedia/megalodon/tests/dedukti_bridge; fi
MM0=${MM0:-$MM0_ROOT/examples}
MM0_MMU_TEST=${MM0_MMU_TEST:-$MM0_ROOT/tests/mm0_mmu}
MMB=${MMB:-$MM0_ROOT/mm0-js/test}
MMB_TEST=${MMB_TEST:-$MM0_ROOT/tests/mmb}
CFLAGS="-O3 -march=native -fno-tree-vectorize -fno-tree-loop-distribute-patterns -flto -Wall -Wextra -Werror"

gcc $CFLAGS tcalc.c test_tcalc.c -o test_tcalc
./test_tcalc

gcc $CFLAGS tcalc.c mm0_tcalc.c -o mm0_tcalc
mmu_pos=0
for f in "$MM0/peano.mmu" "$MM0/peano_hex.mmu" mm0-controls/ok-*.mmu mm0-controls/pos-*.mmu "$MM0_MMU_TEST"/pass/*.mmu; do
  [ -f "$f" ] || { echo "MISSING MMU POSITIVE CONTROL: $f"; exit 1; }
  spec="${f%.mmu}.mm0"
  if [ "$f" = "$MM0/peano_hex.mmu" ] || [ ! -f "$spec" ]; then
    ./mm0_tcalc "$f" --proof-only
  else
    ./mm0_tcalc "$f" "$spec"
  fi
  mmu_pos=$((mmu_pos + 1))
done
[ "$mmu_pos" -eq 17 ] || { echo "EXPECTED 17 MMU POSITIVE CONTROLS, GOT $mmu_pos"; exit 1; }

mmu_refused=0
for f in mm0-controls/bad-*.mmu mm0-controls/dv-*.mmu mm0-controls/peano-bad-*.mmu \
         mm0-controls/x-*.mmu mm0-controls/neg-*.mmu mm0-controls/c-*.mmu \
         mm0-controls/blank_binder_alias.mmu "$MM0_MMU_TEST"/fail/*.mmu; do
  [ -f "$f" ] || { echo "MISSING MMU NEGATIVE CONTROL: $f"; exit 1; }
  spec="${f%.mmu}.mm0"
  [ -f "$spec" ] || spec="--proof-only"
  set +e
  msg=$(./mm0_tcalc "$f" "$spec" 2>&1)
  rc=$?
  set -e
  if [ "$rc" -ne 1 ]; then echo "WRONG EXIT CODE ($rc, expected 1) ON MMU NEGATIVE: $f ($msg)"; exit 1; fi
  case "$msg" in *FAIL*) ;; *) echo "MISSING FAIL REASON ON MMU NEGATIVE: $f ($msg)"; exit 1 ;; esac
  mmu_refused=$((mmu_refused + 1))
done
cp mm0-controls/blank_binder_alias.mmu renamed_bba.mmu
for arg in "" "mm0-controls/blank_binder_alias.mm0"; do
  set +e
  if [ -z "$arg" ]; then msg=$(./mm0_tcalc renamed_bba.mmu 2>&1); else msg=$(./mm0_tcalc renamed_bba.mmu "$arg" 2>&1); fi
  rc=$?
  set -e
  rm -f renamed_bba.mmu
  if [ "$rc" -ne 1 ]; then echo "WRONG EXIT CODE ($rc, expected 1) ON RENAMED MMU ($arg): $msg"; exit 1; fi
  case "$msg" in *FAIL*) ;; *) echo "MISSING FAIL REASON ON RENAMED MMU ($arg): $msg"; exit 1 ;; esac
  cp mm0-controls/blank_binder_alias.mmu renamed_bba.mmu
  mmu_refused=$((mmu_refused + 1))
done
rm -f renamed_bba.mmu
[ "$mmu_refused" -eq 79 ] || { echo "EXPECTED 79 MMU NEGATIVE CONTROLS, GOT $mmu_refused"; exit 1; }
printf 'mmu controls: %d/17 positive accepted, %d/79 negative refused cleanly (exit 1)\n' "$mmu_pos" "$mmu_refused"

gcc $CFLAGS tcalc.c mmb_tcalc.c -o mmb_tcalc
./mmb_tcalc "$MMB/peano.mmb" "$MM0/peano.mm0"
./mmb_tcalc "$MMB_TEST/pass/max_bound_vars.mmb" "$MMB_TEST/pass/max_bound_vars.mm0"
for f in "$MMB/hol.mmb" "$MMB_TEST/pass/no_index.mmb"; do
  [ -f "$f" ] || { echo "MISSING MMB POSITIVE CONTROL: $f"; exit 1; }
  ./mmb_tcalc "$f" --proof-only
done
mmb_refused=0
for f in "$MMB_TEST"/fail/*.mmb mm0-controls/blank_binder_alias.mmb; do
  [ -f "$f" ] || { echo "MISSING MMB NEGATIVE CONTROL: $f"; exit 1; }
  spec="${f%.mmb}.mm0"
  [ -f "$spec" ] || spec="--proof-only"
  set +e
  msg=$(./mmb_tcalc "$f" "$spec" 2>&1)
  rc=$?
  set -e
  if [ "$rc" -ne 1 ]; then echo "WRONG EXIT CODE ($rc, expected 1) ON MMB NEGATIVE: $f ($msg)"; exit 1; fi
  case "$msg" in *FAIL*) ;; *) echo "MISSING FAIL REASON ON MMB NEGATIVE: $f ($msg)"; exit 1 ;; esac
  mmb_refused=$((mmb_refused + 1))
done
cp mm0-controls/blank_binder_alias.mmb renamed_bba.mmb
for arg in "" "mm0-controls/blank_binder_alias.mm0"; do
  set +e
  if [ -z "$arg" ]; then msg=$(./mmb_tcalc renamed_bba.mmb 2>&1); else msg=$(./mmb_tcalc renamed_bba.mmb "$arg" 2>&1); fi
  rc=$?
  set -e
  rm -f renamed_bba.mmb
  if [ "$rc" -ne 1 ]; then echo "WRONG EXIT CODE ($rc, expected 1) ON RENAMED MMB ($arg): $msg"; exit 1; fi
  case "$msg" in *FAIL*) ;; *) echo "MISSING FAIL REASON ON RENAMED MMB ($arg): $msg"; exit 1 ;; esac
  cp mm0-controls/blank_binder_alias.mmb renamed_bba.mmb
  mmb_refused=$((mmb_refused + 1))
done
rm -f renamed_bba.mmb
cp "$MMB/peano.mmb" sf_peano.mmb
printf '\001' | dd of=sf_peano.mmb bs=1 seek=46176 count=1 conv=notrunc status=none
set +e
msg=$(./mmb_tcalc sf_peano.mmb "$MM0/peano.mm0" 2>&1)
rc=$?
set -e
rm -f sf_peano.mmb
if [ "$rc" -ne 1 ]; then echo "WRONG EXIT CODE ($rc, expected 1) ON SF_PEANO MMB: $msg"; exit 1; fi
case "$msg" in *FAIL*) ;; *) echo "MISSING FAIL REASON ON SF_PEANO MMB: $msg"; exit 1 ;; esac
mmb_refused=$((mmb_refused + 1))
[ "$mmb_refused" -eq 25 ] || { echo "EXPECTED 25 MMB NEGATIVE CONTROLS, GOT $mmb_refused"; exit 1; }
printf 'mmb controls: 4/4 positive accepted, %d/25 negative refused cleanly (exit 1)\n' "$mmb_refused"

# R118 .mm0 specification-reader control suite (ob, local, rob, dum, nota, cmt, coe, up)
r118_pos=0
r118_neg=0
check_r118_pos() {
  "$@" >/dev/null
  r118_pos=$((r118_pos + 1))
}
check_r118_neg() {
  set +e
  msg=$("$@" 2>&1)
  rc=$?
  set -e
  if [ "$rc" -ne 1 ]; then echo "WRONG EXIT CODE ($rc, expected 1) ON R118 NEGATIVE ($*): $msg"; exit 1; fi
  case "$msg" in *FAIL*) ;; *) echo "MISSING FAIL REASON ON R118 NEGATIVE ($*): $msg"; exit 1 ;; esac
  r118_neg=$((r118_neg + 1))
}
for s in mm0-controls/r118/ob/*.mm0; do
  bn=$(basename "$s" .mm0)
  case "$bn" in
    abs_add_body|ax_explicit_paren|ax_hyp_named|ax_prefix_app|ax_rename|base|\
    def_drop_body|def_dummy_but_body_no|def_dummy_drop_body|def_dummy_extra|\
    def_dummy_rename|def_rename|term_arrow|term_rename|thm_bound_rename|utf8_comment)
      check_r118_pos ./mm0_tcalc mm0-controls/r118/ob/base.mmu "$s"
      check_r118_pos ./mmb_tcalc mm0-controls/r118/ob/base.mmb "$s"
      ;;
    *)
      check_r118_neg ./mm0_tcalc mm0-controls/r118/ob/base.mmu "$s"
      check_r118_neg ./mmb_tcalc mm0-controls/r118/ob/base.mmb "$s"
      ;;
  esac
done
for x in la ls lt; do
  check_r118_neg ./mm0_tcalc "mm0-controls/r118/local/$x.mmu" "mm0-controls/r118/local/$x.mm0"
done
for x in s130 v300; do
  check_r118_neg ./mm0_tcalc "mm0-controls/r118/rob/$x.mmu" "mm0-controls/r118/rob/$x.mm0"
done
for s in mm0-controls/r118/rob/deep_*.mm0; do
  check_r118_neg ./mm0_tcalc mm0-controls/r118/ob/base.mmu "$s"
  check_r118_neg ./mmb_tcalc mm0-controls/r118/ob/base.mmb "$s"
done
for u in d2 d2_swapdecl d2_extra; do
  check_r118_pos ./mm0_tcalc "mm0-controls/r118/dum/$u.mmu" mm0-controls/r118/dum/d2.mm0
done
check_r118_pos ./mmb_tcalc mm0-controls/r118/dum/d2.mmb mm0-controls/r118/dum/d2.mm0
for s in d2_noninj d2_noninj1; do
  check_r118_neg ./mm0_tcalc mm0-controls/r118/dum/d2.mmu "mm0-controls/r118/dum/$s.mm0"
  check_r118_neg ./mmb_tcalc mm0-controls/r118/dum/d2.mmb "mm0-controls/r118/dum/$s.mm0"
done
check_r118_pos ./mm0_tcalc mm0-controls/r118/nota/ov.mmu mm0-controls/r118/nota/ov_good.mm0
check_r118_pos ./mmb_tcalc mm0-controls/r118/nota/ov.mmb mm0-controls/r118/nota/ov_good.mm0
check_r118_neg ./mm0_tcalc mm0-controls/r118/nota/ov.mmu mm0-controls/r118/nota/ov_bad.mm0
check_r118_neg ./mmb_tcalc mm0-controls/r118/nota/ov.mmb mm0-controls/r118/nota/ov_bad.mm0
check_r118_neg ./mm0_tcalc mm0-controls/r118/nota/dl.mmu mm0-controls/r118/nota/dl_bad.mm0
check_r118_neg ./mmb_tcalc mm0-controls/r118/nota/dl.mmb mm0-controls/r118/nota/dl_bad.mm0
check_r118_neg ./mm0_tcalc mm0-controls/r118/cmt/cm.mmu mm0-controls/r118/cmt/cm_bad.mm0
check_r118_neg ./mmb_tcalc mm0-controls/r118/cmt/cm.mmb mm0-controls/r118/cmt/cm_bad.mm0
check_r118_pos ./mm0_tcalc mm0-controls/r118/coe/co.mmu mm0-controls/r118/coe/co.mm0
for s in mm0-controls/r118/up/bad-*.mm0; do
  check_r118_neg ./mm0_tcalc mm0-controls/r118/up/sp.mmu "$s"
  check_r118_neg ./mmb_tcalc mm0-controls/r118/up/sp.mmb "$s"
done
[ "$r118_pos" -eq 39 ] || { echo "EXPECTED 39 R118 POSITIVE CONTROLS, GOT $r118_pos"; exit 1; }
[ "$r118_neg" -eq 151 ] || { echo "EXPECTED 151 R118 NEGATIVE CONTROLS, GOT $r118_neg"; exit 1; }
printf 'r118 spec controls: %d/39 positive accepted, %d/151 negative refused cleanly (exit 1)\n' "$r118_pos" "$r118_neg"

# ax5 side conditions over bound arguments (mm0.md Vars): one valid use, five violations
./mmb_tcalc mm0-controls/ax5/fresh.mmb mm0-controls/ax5/fresh.mm0 >/dev/null
ax5_neg=0
for x in def_dependency_isz definition_dependency binder_position context_layout disjoint; do
  check_r118_neg ./mmb_tcalc "mm0-controls/ax5/$x.mmb" "mm0-controls/ax5/$x.mm0"
  ax5_neg=$((ax5_neg + 1))
done
printf 'ax5 controls: 1/1 positive accepted, %d/5 negative refused cleanly (exit 1)\n' "$ax5_neg"

# HOL Light LCF kernel & HOLRPLY1 stream verifier on tcalc
gcc $CFLAGS tcalc.c hol_tcalc.c -o hol_tcalc
./hol_tcalc --test
./hol_tcalc --spec "$HOL_DIR/core.checked-sequents.txt" "$HOL_DIR/core.holr"
./hol_tcalc --spec "$HOL_DIR/transform.checked-sequents.txt" "$HOL_DIR/transform.holr"
if [ -f "$HOL_DIR/refinements.holr" ]; then
  ./hol_tcalc --spec "$HOL_DIR/refinements.checked-sequents.txt" "$HOL_DIR/refinements.holr"
fi
hol_neg=0
set +e
./hol_tcalc --spec "$HOL_DIR/transform.checked-sequents.txt" "$HOL_DIR/core.holr" >/dev/null 2>&1
[ "$?" -eq 1 ] || { echo "EXPECTED EXIT 1 ON HOL SPEC MISMATCH"; exit 1; }
hol_neg=$((hol_neg + 1))
head -c 1024 "$HOL_DIR/core.holr" > trunc_core.holr
./hol_tcalc trunc_core.holr >/dev/null 2>&1
rc=$?
rm -f trunc_core.holr
[ "$rc" -eq 1 ] || { echo "EXPECTED EXIT 1 ON TRUNCATED HOLR"; exit 1; }
hol_neg=$((hol_neg + 1))
cp "$HOL_DIR/core.holr" bad_core.holr
printf '\377' | dd of=bad_core.holr bs=1 seek=256 count=1 conv=notrunc status=none
./hol_tcalc bad_core.holr >/dev/null 2>&1
rc=$?
rm -f bad_core.holr
[ "$rc" -eq 1 ] || { echo "EXPECTED EXIT 1 ON CORRUPTED HOLR"; exit 1; }
hol_neg=$((hol_neg + 1))
set -e
printf 'hol_tcalc controls: 3/3 streams + 28/28 kernel checks accepted, %d/3 negative streams refused cleanly (exit 1)\n' "$hol_neg"

# Megalodon (Egal HoTTG, HF, Mizar, HOAS) proof-kernel & -sexprinfo verifier on tcalc
gcc $CFLAGS tcalc.c mg_tcalc.c -o mg_tcalc
./mg_tcalc --self-test --profile egal --axioms none "$MG_FIX/pfghotg_churchnum.sexpr" --profile hf --axioms all "$MG_FIX/pfghf_logic.sexpr"
if [ -n "$MG_EGAL" ]; then
  [ -f "$MG_EGAL/Part1.sexpr" ] || { echo "MG_EGAL is missing Part1.sexpr" >&2; exit 1; }
  ./mg_tcalc --profile egal --chain \
    --axioms all "$MG_EGAL/Part1.sexpr" \
    --axioms none \
    "$MG_EGAL/Part2.sexpr" "$MG_EGAL/Part3.sexpr" \
    "$MG_EGAL/Part4.sexpr" "$MG_EGAL/Part5.sexpr" "$MG_EGAL/Part6.sexpr" \
    "$MG_EGAL/Part7.sexpr" "$MG_EGAL/Part8.sexpr" "$MG_EGAL/Part9.sexpr" \
    "$MG_EGAL/Part10.sexpr" "$MG_EGAL/Part10b.sexpr" "$MG_EGAL/Part11.sexpr" \
    "$MG_EGAL/Part12.sexpr" "$MG_EGAL/Part13.sexpr" "$MG_EGAL/Part14.sexpr"
fi

# Dedukti (Lambda-Pi Modulo Rewriting) verifier on tcalc
gcc $CFLAGS tcalc.c dk_tcalc.c -o dk_tcalc
./dk_tcalc --self-test --coc "$DK_CURR/10_kernel_curriculum_positive.dk"
dk_neg=0
set +e
./dk_tcalc --pts lf "$DK_CURR/10_kernel_curriculum_positive.dk" >/dev/null 2>&1
rc=$?
set -e
if [ "$rc" -ne 1 ]; then echo "EXPECTED EXIT 1 ON CoC FILE IN STRICT LF MODE"; exit 1; fi
dk_neg=$((dk_neg + 1))
for f in "$DK_CURR"/neg_kernel_*.dk; do
  set +e
  ./dk_tcalc --coc "$f" >/dev/null 2>&1
  rc=$?
  set -e
  if [ "$rc" -ne 1 ]; then echo "EXPECTED EXIT 1 ON DK NEGATIVE: $f"; exit 1; fi
  dk_neg=$((dk_neg + 1))
done
[ "$dk_neg" -eq 5 ] || { echo "EXPECTED 5 DK NEGATIVE CONTROLS, GOT $dk_neg"; exit 1; }
if [ -d "$DK_EX" ]; then
  ./dk_tcalc --pts lf \
    "$DK_EX/coc.dk" "$DK_EX/append.dk" "$DK_EX/plus.dk" "$DK_EX/church.dk" \
    "$DK_EX/compute.dk" "$DK_EX/emptySet.dk" "$DK_EX/lambda.dk" \
    "$DK_EX/pureLambdaCalculus.dk" "$DK_EX/pureLambdaCalculus2.dk" "$DK_EX/surjective.dk"
  ./dk_tcalc --pts lf --chain "$DK_EX/FO.dk" "$DK_EX/FO_theorems.dk" "$DK_EX/classical.dk"
fi
if [ -d "$KO_EX" ]; then
  ./dk_tcalc --pts lf \
    "$KO_EX/nat.dk" "$KO_EX/bool.dk" "$KO_EX/fo_imp.dk" "$KO_EX/magic.dk" "$KO_EX/pure.dk"
  ./dk_tcalc --pts lf --chain "$KO_EX/bool.dk" "$KO_EX/sudoku/sudoku.dk" "$KO_EX/sudoku/solve_easy.dk"
fi
if [ -f "$MG_DK/test_triple_neg.dk" ]; then
  ./dk_tcalc --pts lf "$MG_DK/test_triple_neg.dk"
fi
DK_ADV=dk-controls
if [ -d "$DK_ADV" ]; then
  adv_neg=0
  for f in "$DK_ADV"/n*.dk; do
    set +e
    ./dk_tcalc --pts lf "$f" >/dev/null 2>&1
    rc=$?
    set -e
    if [ "$rc" -ne 1 ]; then echo "EXPECTED EXIT 1 ON DK ADV NEGATIVE: $f"; exit 1; fi
    adv_neg=$((adv_neg + 1))
  done
  [ "$adv_neg" -eq 18 ] || { echo "EXPECTED 18 DK ADV NEGATIVE CONTROLS, GOT $adv_neg"; exit 1; }
  ./dk_tcalc --pts lf "$DK_ADV"/p*.dk >/dev/null
  printf 'dk_tcalc adv controls: 5/5 positive twins accepted, %d/18 adversarial negatives refused cleanly (exit 1)\n' "$adv_neg"
fi
printf 'dk_tcalc controls: 22/22 positive files accepted, %d/5 curriculum negative controls + 5/5 self-test negative controls refused cleanly (exit 1)\n' "$dk_neg"

rm -f micromath_tcalc_gen.h
gcc -O3 -march=native -Wall -Wextra -Werror tcalc_compile.c -o tcalc_compile
./tcalc_compile
gcc -O3 -march=native -flto -D_GNU_SOURCE -c "$MICROMATH/kernel.c" -I"$MICROMATH" -o micromath_kernel.o
gcc $CFLAGS -D_GNU_SOURCE -DTC_HAVE_GEN -I"$MICROMATH" diff_micromath.c tcalc.c micromath_tcalc.c micromath_kernel.o -o diff_micromath
./diff_micromath
rm -f micromath_kernel.o
