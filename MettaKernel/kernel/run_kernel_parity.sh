#!/usr/bin/env bash
set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CETTA="/home/aimama/aihub/hyperon/CeTTa/cetta"
PETTA="/home/aimama/aihub/hyperon/PeTTa/run.sh"
LOGDIR="$ROOT/parity_logs"
mkdir -p "$LOGDIR"

rows=(
  "LCF core|CeTTa|lcf_core.metta|trusted LCF rules; invalid MP rejects"
  "LCF core|PeTTa|lcf_core_petta.metta|same rules; PeTTa adapter names/assertions"
  "Admitted signature kernel|CeTTa|kernel_signature_v0.metta|wf declarations; duplicate/forward/bad-def rejects; axiom provenance; WM evidence cannot mint theorem"
  "Admitted signature kernel|PeTTa|kernel_signature_v0_petta.metta|same claims; PeTTa adapter names/assertions"
  "Admitted lambda-Pi kernel|CeTTa|kernel_signature_lf_v0.metta|finite admitted signatures; checked definitions; dependent proof terms; axiom provenance; client of kernel_binding_waist_v1 with local de Bruijn replay teeth for index decrement/capture avoidance/binder-depth/shadowing"
  "Admitted lambda-Pi kernel|PeTTa|kernel_signature_lf_v0_petta.metta|same claims; PeTTa adapter names/assertions"
  "Lambda-Pi natrec kernel|CeTTa|kernel_signature_lf_natrec_v0.metta|dependent NatRec; zero/successor iota; plus computes; rfl proves concrete plus-zero; client of kernel_binding_waist_v1, including NatRecF four-child non-binding traversal replay"
  "Lambda-Pi natrec kernel|PeTTa|kernel_signature_lf_natrec_v0_petta.metta|same claims; PeTTa adapter names/assertions"
  # RETIRED v3: the equality kernel (GEq/GRfl/GTransp/Transp + cong-s + plus-O-r) is SUBSUMED
  #   by the generated J in kernel_signature_lf_indexed_v0.metta (retirement gate proven v6; replay-confirmed:
  #   J diagonal, cong-s, plus-O-r, and forged-reject all re-derive via generated Id/J). Slice -> retired_fixtures/.
  #   Fully generic transport is a future helper-factoring task, not a live primitive.
  # RETIRED v4: the non-indexed inductive slices (DInd Nat/Bool; DInd telescopes List/Tree)
  #   are SUBSUMED by the DIndG engine in kernel_signature_lf_indexed_v0.metta.  Replay-
  #   confirmed there (v4 SLICE-COLLAPSE REPLAY): Nat/List families + recursors; Bool (ibool)
  #   2-nullary-ctor enum + bnot recursor + bnot(bnot b)=b involution via GENERATED J (no
  #   GEq/GRfl); Tree-leaf non-recursive payload + eliminator.  The eq primitives these
  #   slices bundled (GEq/GRfl/GTransp/Transp) re-derive via generated J (cong-s, plus-O-r)
  #   already in indexed_v0.  Slices -> retired_fixtures/ (regression oracles, not deleted).
  # RETIRED v3: Id/Rfl/J + guarded j-iota are SUBSUMED by the generated Id eliminator (= J) in
  #   kernel_signature_lf_indexed_v0.metta (Id is a DIndG; J its generated eliminator; diagonal iota;
  #   forged proofs rejected by typing). Slice -> retired_fixtures/.
  # RETIRED v4: the parameterized + indexed inductive slices (DIndP List A/Pair A B; Vec A n;
  #   DIndPI Id/Rfl/J; generic IndRecPI Fin n) are SUBSUMED by the DIndG engine in
  #   kernel_signature_lf_indexed_v0.metta.  Replay-confirmed there: List A length / Pair A B
  #   fst; Vec vnil/vcons exact-index + wrong index/tail/element negatives; Fin n rank; Id as a
  #   DIndG with generated J + diagonal iota.  The old schema constraints DISSOLVE under DIndG:
  #   index-schema whitelists (I1Nat/I2Self/IUnknown) -> arbitrary index telescopes; named-
  #   eliminator collisions -> the eliminator is generated, never named; "Id must have a refl
  #   ctor" -> an Id with no refl is just an empty inductive (admitted, vacuous eliminator).
  #   Slices -> retired_fixtures/ (regression oracles, not deleted).
  "Lambda-Pi curriculum demo|CeTTa|curriculum_lf_demo.metta|DTT/HOTG/HOL positives; wrong proofs reject; Bad-as-type rejects; client of kernel_binding_waist_v1 with local binding replay teeth"
  "Lambda-Pi curriculum demo|PeTTa|curriculum_lf_demo_petta.metta|same claims; PeTTa adapter names/assertions"
  "Lambda-Pi break probes|CeTTa|break_probes.metta|documents currently accepted raw-signature holes; client of kernel_binding_waist_v1 with local binding replay teeth"
  "Lambda-Pi break probes|PeTTa|break_probes_petta.metta|same probes; PeTTa adapter names/assertions"
  "Imp coherence exp1|CeTTa|imp_coherence_exp1.metta|bounded derivability search emits certs accepted by checker"
  "Imp coherence exp1|PeTTa|imp_coherence_exp1_petta.metta|same claims; PeTTa adapter names/assertions"
  "DTT wall exp2|CeTTa|exp2_dtt_wall.metta|beta/delta/rfl pass; recursor/iota/induction wall documented; client of kernel_binding_waist_v1 with local binding replay teeth"
  "DTT wall exp2|PeTTa|exp2_dtt_wall_petta.metta|same claims; PeTTa adapter names/assertions"
  "HOTG both-ways exp3|CeTTa|exp3_hotg_both_ways.metta|same tiny HO-Set fragment as sequent certificate and lambda-Pi proof term; lambda-Pi side is a client of kernel_binding_waist_v1 with local binding replay teeth"
  "HOTG both-ways exp3|PeTTa|exp3_hotg_both_ways_petta.metta|same claims; PeTTa adapter names/assertions"
  "NIK Metamath stack|CeTTa|nik_metamath_stack_v0.metta|floating-hypothesis FH/Use proof layer; id theorem; DV and essential-hyp negatives"
  "NIK Metamath stack|PeTTa|nik_metamath_stack_v0_petta.metta|same claims; PeTTa adapter names/assertions"
  "NIK Metamath L0 ingestion|CeTTa|nik_metamath_l0_v0.metta|parsed-AST admission validates labels/floats/DV/assertion/proof invariants before lowering to the NIK checker"
  "NIK Metamath L0 ingestion|PeTTa|nik_metamath_l0_v0_petta.metta|same claims; PeTTa adapter names/assertions"
  "NIK Metamath CeTTa parser smoke|CeTTa|nik_metamath_l0_cetta_parse_smoke.metta|actual tiny .mm file parsed by CeTTa textual parser, lowered through L0 admission, then checked by NIK"
  "Provenance tree|CeTTa|provenance_tree_v0.metta|same checked trace projects to Boolean ledger and WM evidence; evidence cannot mint theorem"
  "Provenance tree|PeTTa|provenance_tree_v0_petta.metta|same claims; PeTTa adapter names/assertions"
  "Evaluator ground-recursion invariant|CeTTa|evaluator_ground_recursion_invariant.metta|ground recursive same-head infer reaches spec normal form (Srt kind) and still rejects bad domains; guards the CeTTa bind-mode regression against the LeaTTa/Hyperon/PeTTa oracle; client of kernel_binding_waist_v1 with local binding replay teeth"
  "Evaluator ground-recursion invariant|PeTTa|evaluator_ground_recursion_invariant_petta.metta|same invariant; PeTTa adapter names/assertions"
  "Vec OSLF/NTT target contract|CeTTa|oslf_targets/vec_indexed_family_ntt_target.metta|post-upgrade Lean target: indexed Vec LanguageDef/NTT diagnostics must go beyond unaryCrossings-only"
  "Vec OSLF/NTT target contract|PeTTa|oslf_targets/vec_indexed_family_ntt_target_petta.metta|same target contract; PeTTa adapter names/assertions"
  "Indexed telescope IR (DIndG) Phase 1+2+3+4|CeTTa|kernel_signature_lf_indexed_v0.metta|DIndG telescope IR: generated family/ctor/eliminator types for Nat/List/Pair/Vec/Fin/Id plus v4 slice-collapse replays for Bool/Tree/Vec constructor indices/positivity/empty inductives; strengthened admission view; generated constructor-headed iota including J diagonal; typed IndG checking against generated eliminator type; CheckedPrf minting with axiom provenance; retirement gate proved via generated J (no GEq/GRfl/GTransp/Transp): cong-s + checked plus DDef over the generated recursor + forall n. plus n z = n by generated Nat induction; eta-free + predicative calculus verdicts pinned; SR wedge: infer t = infer (nf t) for generated iota witnesses nat/list/vec/fin/J/pair; positive replays and typed negatives (incl. plus-O-r off-by-one); binding capture spec v1 (B1-B6: de Bruijn shift/subst/conv capture-avoidance + alpha + IndG-binder teeth); indexed_v0 is a client of kernel_binding_waist_v1: no active client-side shift/subst/Args/Cases dispatch remains; public evaluator-stable fast path and arity table are owned by the waist; gated by run_binding_mutation_gate.sh (mutation-complete M1-M5 indexed live-waist mutations + L1-L5 lower LF/NatRec client mutations + P1-P4 parity-demo client mutations incl. exp3 + G1-G14 replay/arity/BindingDecl mutations; baseline guards enforce 116/102/23/32/20/9/15/14/7/32)"
  "Indexed telescope IR (DIndG) Phase 1+2+3+4|PeTTa|kernel_signature_lf_indexed_v0_petta.metta|same claims; PeTTa adapter names/assertions"
  "Minimal binding waist v1|CeTTa|kernel_binding_waist_v1.metta|import-free ABT/de-Bruijn waist owns checked arities, generic bind-shift/bind-subst, and the public evaluator-stable shift/subst/Args/Cases fast path over Var/Srt/Con/Def/Bad/App/Pi/Lam/IndG/NatRec/Args/Cases; no checker/nf/conv/iota/signature dependency"
  "Minimal binding waist v1|PeTTa|kernel_binding_waist_v1_petta.metta|same waist; PeTTa adapter names/assertions"
  "BindingDecl LanguageDef interface v1|CeTTa|kernel_binding_decl_v1.metta|shared hosted-LanguageDef binding declarations over the minimal waist: Bind0/Bind1/BindFields/BindPi, dependent-Pi domain/codomain depths, forall/exists body binding, comprehension field binding, duplicate/depth negatives, and depth-2 LanguageDef traversal helpers"
  "BindingDecl LanguageDef interface v1|PeTTa|kernel_binding_decl_v1_petta.metta|same BindingDecl interface; PeTTa adapter imports the PeTTa waist exactly once"
  "ABT binding shared engine v1|CeTTa|kernel_binding_abt_engine_v1.metta|compatibility wrapper imports only the minimal waist; indexed routing is proved by run_binding_mutation_gate.sh to avoid duplicate imports and CeTTa/LeaTTa re-export fragility"
  "ABT binding shared engine v1|PeTTa|kernel_binding_abt_engine_v1_petta.metta|same wrapper; PeTTa adapter imports the PeTTa waist"
  "ABT binding generic replay v1|CeTTa|kernel_binding_abtg_replay_v1.metta|client replay oracle imports the waist + BindingDecl layer and checks public shift/subst/Args/Cases fast path against generic bind-shift/bind-subst over Var/App/Pi/Lam/IndG/Args/Cases, plus hosted BindingDecl examples for Pi/forall/exists/comprehension/depth-2; client-side indexed dispatch retired"
  "ABT binding generic replay v1|PeTTa|kernel_binding_abtg_replay_v1_petta.metta|same claims; PeTTa adapter imports BindingDecl, which imports the PeTTa waist exactly once"
  "Conv-soundness shadow v1|CeTTa|conv_soundness_shadow_v1.metta|conv is a SOUND decidable shadow of context-bisimulation (conv subset of ~): structural-congruence 0-unit conv => bounded bisim; strict gap conv (XS) ~ exhibited (+-idempotence, +/|-commutativity, expansion law are ~-only); discriminators a.b+a.c vs a.(b+c) and a|a vs a refused by both; gated by run_conv_soundness_gate.sh (mutation-complete 4/4: unsound conv coarsenings + ~ over-match caught). Operational complement to knot-rho/knotted-topoi FA"
  "Conv-soundness shadow v1|PeTTa|conv_soundness_shadow_v1_petta.metta|same claims; PeTTa adapter names/assertions"
  "Ocoherence HM-adequacy v1|CeTTa|ocoherence_hm_adequacy_v1.metta|bounded OSLF/Hennessy-Milner adequacy shadow: bisimilar examples agree on probe formulae; each listed ~/~ pair is split by an EXPLICIT separating <F>phi (a.b+a.c vs a.(b+c); a|a vs a; a.b vs a.c); triangle tie conv subset of ~ subset of modal-eq on the finitary core, with dT-label = LTS-label = modal-index; gated by run_ocoherence_gate.sh (mutation-complete 4/4: modal label-ignore/vacuous-diamond/dropped-conjunct + ~ over-match). Operational shadow of knotted-topoi keystone Omega-classifies-bisimilarity"
  "Ocoherence HM-adequacy v1|PeTTa|ocoherence_hm_adequacy_v1_petta.metta|same claims; PeTTa adapter names/assertions"
  "MeTTa2rho opcorr shadow v1|CeTTa|mettarho_opcorr_shadow_v1.metta|bounded operational shadow of knotted-topoi ob:opcorr on a genuine 2-rule Peano-add GSLT: the desugaring's dT-transitions correspond to the GSLT rewrites, each on its location channel c(l)=quote(l) (FORWARD+BACKWARD via list eq; rw is the independent term-side reference, dfire reads channels off the annotation -- non-circular); channel injectivity (distinct locations -> distinct channels, collapse caught); bounded bisimulation to normal form with explicit multi-step normalisation witnesses; gated by run_mettarho_opcorr_gate.sh (mutation-complete 4/4: channel collision/wrong location/dropped+wrong re-emit, exact-19 baseline). Lifts the conv/~/<> shadows onto a real LanguageDef"
  "MeTTa2rho opcorr shadow v1|PeTTa|mettarho_opcorr_shadow_v1_petta.metta|same claims; PeTTa adapter names/assertions"
)

run_one() {
  local claim="$1" engine="$2" file="$3" notes="$4"
  local src="$ROOT/$file"
  local log_file="${file//\//__}"
  local log="$LOGDIR/${engine}_${log_file}.log"
  local status="PASS"

  if [[ "$engine" == "CeTTa" ]]; then
    timeout 120 "$CETTA" "$src" >"$log" 2>&1
  else
    timeout 120 "$PETTA" "$src" >"$log" 2>&1
  fi

  local code=$?
  if [[ $code -ne 0 ]] || grep -q "❌" "$log" || grep -q "(Error" "$log"; then
    status="FAIL"
  fi

  printf '%-30s | %-5s | %-30s | %-4s | %s\n' "$claim" "$engine" "$file" "$status" "$notes"
  if [[ "$status" != "PASS" ]]; then
    printf '  log: %s\n' "$log"
    return 1
  fi
  return 0
}

echo "MeTTaKernel parity gate"
echo "Logs: $LOGDIR"
printf '%-30s | %-5s | %-30s | %-4s | %s\n' "claim" "engine" "file" "stat" "notes"
printf '%-30s-+-%-5s-+-%-30s-+-%-4s-+-%s\n' "------------------------------" "-----" "------------------------------" "----" "-----"

fails=0
for row in "${rows[@]}"; do
  IFS='|' read -r claim engine file notes <<<"$row"
  run_one "$claim" "$engine" "$file" "$notes" || fails=$((fails + 1))
done

echo
if [[ $fails -eq 0 ]]; then
  echo "PARITY: PASS"
else
  echo "PARITY: FAIL ($fails row(s))"
fi
exit "$fails"
