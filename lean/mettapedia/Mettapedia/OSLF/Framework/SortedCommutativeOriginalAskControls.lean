import Mettapedia.OSLF.Framework.SortedCommutativeOriginalAskExclusion
import Mettapedia.OSLF.Framework.SortedCommutativeUnitReactionControls

/-!
# Complete ask readouts with independently authored original reactions

The same original unit reaction that competes under get cannot supply any
ask IPO. The combined family still retains complete pair coordinates,
nondeterministic ordered Cut matches, nullary bundles and distinct supplied
origins. Original declarations cannot replace an empty administrative origin
type. An independently chosen nonidentity prefix gives a genuine commuting
ask square which is excluded by its explicit smaller candidate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeOriginalAskControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence
open SortedCommutativeInstruments
open SortedCommutativeInstrumentControls (Symbol arity)
open SortedCommutativeSourceControls (low high sourceCut)
open SortedCommutativeProbeSourceControls (ordered pairValue pairTarget firstCutTarget secondCutTarget)

def originalDeclarations (_ : Nat) : ReactionRule (.origin : Source.SourceCategory (arity := arity)) :=
  unitSourceRule low

def sourceRules (rule : ReactionRule (.origin : Source.SourceCategory (arity := arity))) : Prop :=
  ∃ origin : Nat, originalDeclarations origin = rule

def combinedRules (rule : ReactionRule (.origin : ContextCategory arity)) : Prop :=
  rules arity Nat rule ∨ Source.mappedRules sourceRules rule

theorem no_original_rule_supplies_an_ask_result
    (result : (.origin : ContextCategory arity) ⟶ .interface (.arguments (.ordinary Symbol.pair))) :
    ¬ ActIPO (Source.mappedRules sourceRules) (askLabel (.ordinary Symbol.pair))
      (RawArrow.value (Source.classEmbedding (classOf pairValue))) result :=
  source_rules_do_not_fire_under_ask sourceRules (.ordinary Symbol.pair) _ result

theorem combined_pair_ask_iff
    (result : (.origin : ContextCategory arity) ⟶ .interface (.arguments (.ordinary Symbol.pair))) :
    ActIPO combinedRules (askLabel (.ordinary Symbol.pair))
      (RawArrow.value (Source.classEmbedding (classOf pairValue))) result ↔ result = pairTarget := by
  refine (combined_ask_step_iff_administrative (Origins := Nat) sourceRules
    (.ordinary Symbol.pair) _ result).trans ?_
  change ActIPO (rules arity Nat) (askLabel (.ordinary Symbol.pair))
    (RawArrow.value (Source.classEmbedding (classOf (Source.sourceNode (.ordinary Symbol.pair) ordered)))) result ↔
      result = pairTarget
  rw [ordinary_ask_step_iff (Origins := Nat) Symbol.pair ordered result]
  exact ⟨fun witness => witness.2, fun same => ⟨⟨7⟩, same⟩⟩

theorem actual_combined_pair_assay_fires :
    ActIPO combinedRules (askLabel (.ordinary Symbol.pair))
      (RawArrow.value (Source.classEmbedding (classOf pairValue))) pairTarget :=
  (combined_pair_ask_iff pairTarget).mpr rfl

theorem full_pair_readout_retains_both_coordinates
    (result : (.origin : ContextCategory arity) ⟶ .interface (.arguments (.ordinary Symbol.pair)))
    (step : ActIPO combinedRules (askLabel (.ordinary Symbol.pair))
      (RawArrow.value (Source.classEmbedding (classOf pairValue))) result) :
    result = RawArrow.value (classOf (bundle arity (.ordinary Symbol.pair)
      (Fin.cases (Source.embed low) (fun _ => Source.embed high)))) :=
  ((combined_pair_ask_iff result).mp step).trans SortedCommutativeProbeSourceControls.pair_payload_keeps_both_coordinates

theorem a_wrong_source_head_still_has_no_combined_assay
    (result : (.origin : ContextCategory arity) ⟶ .interface (.arguments (.ordinary Symbol.pair))) :
    ¬ ActIPO combinedRules (askLabel (.ordinary Symbol.pair))
      (RawArrow.value (Source.classEmbedding (classOf low))) result := by
  intro step
  exact SortedCommutativeProbeSourceControls.wrong_source_head_has_no_actual_pair_assay result
    ((combined_ask_step_iff_administrative (Origins := Nat) sourceRules (.ordinary Symbol.pair) _ result).mp step)

theorem both_ordered_cut_matches_survive_original_rules :
    ActIPO combinedRules (askLabel SourceSymbol.properCut)
        (RawArrow.value (Source.classEmbedding (classOf sourceCut))) firstCutTarget ∧
      ActIPO combinedRules (askLabel SourceSymbol.properCut)
        (RawArrow.value (Source.classEmbedding (classOf sourceCut))) secondCutTarget ∧
      firstCutTarget ≠ secondCutTarget :=
  ⟨(combined_ask_step_iff_administrative (Origins := Nat) sourceRules .properCut _ _).mpr
      SortedCommutativeProbeSourceControls.two_ordered_source_matches_really_fire.1,
    (combined_ask_step_iff_administrative (Origins := Nat) sourceRules .properCut _ _).mpr
      SortedCommutativeProbeSourceControls.two_ordered_source_matches_really_fire.2,
    SortedCommutativeProbeSourceControls.complete_ordered_cut_targets_are_distinct⟩

theorem original_rules_do_not_supply_an_empty_administrative_origin
    (result : (.origin : ContextCategory arity) ⟶ .interface (.arguments (.ordinary Symbol.pair))) :
    ¬ ActIPO (fun rule => rules arity Empty rule ∨ Source.mappedRules sourceRules rule)
      (askLabel (.ordinary Symbol.pair)) (RawArrow.value (Source.classEmbedding (classOf pairValue))) result := by
  intro step
  exact SortedCommutativeProbeSourceControls.no_origins_means_no_real_assay result
    ((combined_ask_step_iff_administrative (Origins := Empty) sourceRules (.ordinary Symbol.pair) _ result).mp step)

theorem actual_nullary_ask_survives_original_rules :
    ActIPO combinedRules (askLabel SourceSymbol.unit)
      (RawArrow.value (Source.classEmbedding (classOf (.zero rfl : Source.Value arity))))
      (RawArrow.value (classOf (bundle arity .unit (fun position => Fin.elim0 position)))) := by
  refine (combined_ask_source_step_iff (Origins := Nat) sourceRules .unit _ _).mpr
    ⟨37, (fun position => Fin.elim0 position), rfl, ?_⟩
  apply congrArg (fun arguments : Fin 0 → Value arity .base =>
    RawArrow.value (classOf (bundle arity .unit arguments)))
  funext position
  exact Fin.elim0 position

theorem duplicate_actual_ask_receipts_keep_origins :
    (SortedCommutativeProbeSourceControls.pairOccurrence 7).target =
      (SortedCommutativeProbeSourceControls.pairOccurrence 8).target ∧
      directReceipt (SortedCommutativeProbeSourceControls.pairOccurrence 7) ≠
        directReceipt (SortedCommutativeProbeSourceControls.pairOccurrence 8) :=
  SortedCommutativeProbeSourceControls.same_target_does_not_merge_supplied_origins

def nonidentityPrefix : RawContext (signature arity) (Parallel arity) .base .base :=
  .left rfl .hole (Source.embed low)

def wholeReaction : ContextClass (signature arity) (Parallel arity) .base (.arguments (.ordinary Symbol.pair)) :=
  contextClassOf (nonidentityPrefix.comp (probeContext arity (.ask (.ordinary Symbol.pair))))

def prefixedBody : ValueClass arity .base :=
  classOf (nonidentityPrefix.fill (Source.embed high))

theorem genuine_nonidentity_prefix_is_not_the_context_unit :
    contextClassOf nonidentityPrefix ≠ ContextClass.identity (signature := signature arity) (Parallel := Parallel arity) .base := by
  intro same
  have atUnit := congrArg
    (fun context : ContextClass (signature arity) (Parallel arity) .base .base =>
      context.fill (classOf (.zero rfl : Value arity .base))) same
  change classOf (.cut (signature := signature arity) (Parallel := Parallel arity)
    rfl (.zero rfl) (Source.embed low)) = classOf (.zero rfl : Value arity .base) at atUnit
  have leftRead : classOf (.cut (signature := signature arity) (Parallel := Parallel arity)
      rfl (.zero rfl) (Source.embed low)) = classOf (Source.embed low) :=
    Quotient.sound ((Equation.comm (signature := signature arity) (Parallel := Parallel arity)
      rfl (.zero rfl) (Source.embed low)).trans
      (Equation.unit (signature := signature arity) (Parallel := Parallel arity) rfl (Source.embed low)))
  have nativeSame := leftRead.symm.trans atUnit
  have sourceSame : classOf low = classOf (.zero rfl : Source.Value arity) :=
    Source.classEmbedding_injective nativeSame
  have inventoryRead := congrArg inventoryQ sourceSame
  change ({_} : Multiset (Head (signature := Source.signature arity) (Parallel := Source.Parallel arity) (ULift.up ()))) = 0 at inventoryRead
  exact Multiset.singleton_ne_zero _ inventoryRead

theorem the_prefixed_ask_square_really_commutes :
    (RawArrow.value prefixedBody : (.origin : ContextCategory arity) ⟶ .interface .base) ≫
      askLabel (.ordinary Symbol.pair) = RawArrow.value (classOf (Source.embed high)) ≫ RawArrow.context wholeReaction :=
  congrArg RawArrow.value (congrArg classOf
    (RawContext.fill_comp nonidentityPrefix (probeContext arity (.ask (.ordinary Symbol.pair))) (Source.embed high))).symm

theorem the_actual_prefixed_square_is_not_an_ipo :
    ¬ IsIdemPushout (C := ContextCategory arity)
      (RawArrow.value prefixedBody) (RawArrow.value (classOf (Source.embed high)))
      (askLabel (.ordinary Symbol.pair)) (RawArrow.context wholeReaction)
      the_prefixed_ask_square_really_commutes :=
  base_ask_square_not_ipo (.ordinary Symbol.pair) prefixedBody _ wholeReaction
    the_prefixed_ask_square_really_commutes

theorem the_same_original_rule_still_competes_under_get :
    ActIPO SortedCommutativeUnitReactionControls.combinedRules (getLabel (.ordinary Symbol.pair) 0)
      (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered))
      SortedCommutativeUnitReactionControls.originalResult :=
  SortedCommutativeUnitReactionControls.the_original_rule_really_fires 11

end Mettapedia.OSLF.Framework.SortedCommutativeOriginalAskControls
