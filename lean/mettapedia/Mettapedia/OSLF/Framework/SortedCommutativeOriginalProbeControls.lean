import Mettapedia.OSLF.Framework.SortedCommutativeOriginalProbeExclusion
import Mettapedia.OSLF.Framework.SortedCommutativeCombinedObserverSeparation
import Mettapedia.OSLF.Framework.SortedCommutativeOriginalAskControls

/-!
# Actual nonunit original rules beside complete administrative probes

The independently authored Cut(low,high) rule has a nonunit redex and a real
source-category firing. Its complete occurrence survives the source inclusion.
The combined administrative family nevertheless reads exactly both supplied
get coordinates and the whole build target. A genuine nonidentity bundle
prefix gives a commuting square which fails IPO minimality by the earned
factorization. Empty origins and the actual excluded unit-rule competition
separate the two necessary qualifications.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeOriginalProbeControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence
open SortedCommutativeInstruments
open SortedCommutativeInstrumentControls (Symbol arity)
open SortedCommutativeSourceControls (low high sourceCut)
open SortedCommutativeProbeSourceControls (ordered pairValue)
open SortedCommutativeProbeReconstructionControls (lowTarget highTarget pairBuildTarget)

theorem proper_redex_is_not_the_source_unit :
    classOf sourceCut ≠ classOf (.zero rfl : Source.Value arity) := by
  intro same
  have counts := congrArg (fun value => (inventoryQ value).card) same
  change 2 = 0 at counts
  omega

def properRule : ReactionRule (.origin : Source.SourceCategory (arity := arity)) where
  codomain := .interface (ULift.up ())
  redex := RawArrow.value (classOf sourceCut)
  reactum := RawArrow.value (classOf high)

def originalDeclarations (_ : Nat) := properRule

def sourceRules (rule : ReactionRule (.origin : Source.SourceCategory (arity := arity))) : Prop :=
  ∃ origin : Nat, originalDeclarations origin = rule

theorem every_declared_original_redex_is_nonunit :
    ∀ rule, sourceRules rule → Source.NonunitRedex rule := by
  rintro rule ⟨origin, rfl⟩ forbidden
  exact proper_redex_is_not_the_source_unit (RawArrow.value.inj (eq_of_heq forbidden))

def originalFiring (origin : Nat) :
    Source.FiringEvidence (.origin : Source.SourceCategory (arity := arity)) Nat originalDeclarations where
  occurrence := origin
  sourceInterface := .interface (ULift.up ())
  targetInterface := .interface (ULift.up ())
  agent := properRule.redex
  label := 𝟙 _
  reaction := 𝟙 _
  square := rfl
  minimal := raw_right_identity_isIPO (𝟙 _) (Category.comp_id properRule.redex)

theorem independently_authored_nonunit_rule_really_fires (origin : Nat) :
    ActIPO sourceRules (originalFiring origin).label (originalFiring origin).agent
      (originalFiring origin).result := (originalFiring origin).step

theorem full_original_target_survives_the_inclusion (origin : Nat) :
    (Source.mapFiring originalDeclarations (originalFiring origin)).result =
      RawArrow.value (Source.classEmbedding (classOf high)) := by
  rw [Source.mapFiring_result]
  change Source.inclusion.map (properRule.reactum ≫ 𝟙 _) = _
  rw [Category.comp_id]
  rfl

theorem identical_original_results_keep_distinct_origins :
    (Source.mapFiring originalDeclarations (originalFiring 7)).result =
        (Source.mapFiring originalDeclarations (originalFiring 8)).result ∧
      Source.mapFiring originalDeclarations (originalFiring 7) ≠
        Source.mapFiring originalDeclarations (originalFiring 8) :=
  ⟨(full_original_target_survives_the_inclusion 7).trans
      (full_original_target_survives_the_inclusion 8).symm,
    Source.distinct_origins_keep_distinct_firings originalDeclarations _ _ (by decide)⟩

def combinedRules (rule : ReactionRule (.origin : ContextCategory arity)) : Prop :=
  rules arity Nat rule ∨ Source.mappedRules sourceRules rule

theorem complete_pair_get_iff (position : Fin 2)
    (result : (.origin : ContextCategory arity) ⟶ .interface .base) :
    ActIPO combinedRules (getLabel (.ordinary Symbol.pair) position)
      (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered)) result ↔
        result = RawArrow.value (Source.classEmbedding (classOf (ordered position))) := by
  refine (combined_nonunit_get_source_step_iff (Origins := Nat) sourceRules
    every_declared_original_redex_is_nonunit (.ordinary Symbol.pair) ordered position result).trans ?_
  exact ⟨fun witness => witness.2, fun same => ⟨⟨7⟩, same⟩⟩

theorem both_supplied_pair_children_are_retained :
    ActIPO combinedRules (getLabel (.ordinary Symbol.pair) 0)
        (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered)) lowTarget ∧
      ActIPO combinedRules (getLabel (.ordinary Symbol.pair) 1)
        (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered)) highTarget ∧
      lowTarget ≠ highTarget :=
  ⟨(complete_pair_get_iff 0 lowTarget).mpr rfl,
    (complete_pair_get_iff 1 highTarget).mpr rfl,
    fun same => SortedCommutativeSourceControls.source_values_are_distinct
      (Source.classEmbedding_injective (RawArrow.value.inj same))⟩

theorem complete_pair_build_iff (result : (.origin : ContextCategory arity) ⟶ .interface .base) :
    ActIPO combinedRules (buildLabel (.ordinary Symbol.pair))
      (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered)) result ↔
        result = pairBuildTarget := by
  refine (combined_nonunit_build_source_step_iff (Origins := Nat) sourceRules
    every_declared_original_redex_is_nonunit (.ordinary Symbol.pair) ordered result).trans ?_
  exact ⟨fun witness => witness.2, fun same => ⟨⟨8⟩, same⟩⟩

theorem the_whole_supplied_constructor_is_rebuilt :
    ActIPO combinedRules (buildLabel (.ordinary Symbol.pair))
      (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered)) pairBuildTarget :=
  (complete_pair_build_iff _).mpr rfl

theorem original_rules_cannot_replace_empty_administrative_origins
    (result : (.origin : ContextCategory arity) ⟶ .interface .base) :
    ¬ ActIPO (fun rule => rules arity Empty rule ∨ Source.mappedRules sourceRules rule)
      (getLabel (.ordinary Symbol.pair) 0)
      (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered)) result := by
  intro step
  obtain ⟨⟨origin⟩, _⟩ := (combined_nonunit_get_source_step_iff (Origins := Empty) sourceRules
    every_declared_original_redex_is_nonunit (.ordinary Symbol.pair) ordered 0 result).mp step
  exact Empty.elim origin

theorem a_nullary_build_keeps_the_unit_target :
    ActIPO combinedRules (buildLabel SourceSymbol.unit)
      (RawArrow.value (sourceBundle SourceSymbol.unit (fun position => Fin.elim0 position)))
      (RawArrow.value (Source.classEmbedding (classOf (.zero rfl : Source.Value arity)))) :=
  (combined_nonunit_build_source_step_iff (Origins := Nat) sourceRules
    every_declared_original_redex_is_nonunit .unit (fun position => Fin.elim0 position) _).mpr ⟨⟨19⟩, rfl⟩

def bundlePrefix : RawContext (signature arity) (Parallel arity) .base
    (.arguments (.ordinary Symbol.pair)) :=
  RawContext.frame (signature := signature arity) (Parallel := Parallel arity)
    (Constructor.arguments (.ordinary Symbol.pair)) 0 (fun _ _ => Source.embed high) .hole

def prefixedBody : ValueClass arity (.arguments (.ordinary Symbol.pair)) :=
  classOf (bundlePrefix.fill (Source.embed sourceCut))

def wholeReaction : ContextClass (signature arity) (Parallel arity) .base .base :=
  contextClassOf (bundlePrefix.comp (probeContext arity (.get (.ordinary Symbol.pair) 1)))

theorem the_nonunit_prefixed_square_really_commutes :
    (RawArrow.value prefixedBody : (.origin : ContextCategory arity) ⟶
        .interface (.arguments (.ordinary Symbol.pair))) ≫ getLabel (.ordinary Symbol.pair) 1 =
      RawArrow.value (Source.classEmbedding (classOf sourceCut)) ≫ RawArrow.context wholeReaction :=
  congrArg RawArrow.value (congrArg classOf
    (RawContext.fill_comp bundlePrefix (probeContext arity (.get (.ordinary Symbol.pair) 1))
      (Source.embed sourceCut))).symm

theorem that_actual_complete_square_fails_ipo_minimality :
    ¬ IsIdemPushout (C := ContextCategory arity) (RawArrow.value prefixedBody)
      (RawArrow.value (Source.classEmbedding (classOf sourceCut))) (getLabel (.ordinary Symbol.pair) 1)
      (RawArrow.context wholeReaction) the_nonunit_prefixed_square_really_commutes :=
  nonunit_base_probe_square_not_ipo (.get (.ordinary Symbol.pair) 1) prefixedBody (classOf sourceCut)
    proper_redex_is_not_the_source_unit wholeReaction the_nonunit_prefixed_square_really_commutes

theorem complete_combined_observers_separate_original_heads :
    ¬ IPOBisimilar combinedRules lowTarget highTarget := by
  intro related
  exact SortedCommutativeSourceControls.source_values_are_distinct
    ((combined_observer_bisimilar_iff_source_equal sourceRules
      every_declared_original_redex_is_nonunit (Origins := Nat) ⟨7⟩ _ _).mp related)

theorem complete_combined_observers_respect_actual_source_commutativity :
    IPOBisimilar combinedRules (RawArrow.value (Source.classEmbedding (classOf sourceCut)))
      (RawArrow.value (Source.classEmbedding (classOf SortedCommutativeSourceControls.swappedCut))) :=
  (combined_observer_raw_bisimilar_iff_source_equation sourceRules
    every_declared_original_redex_is_nonunit (Origins := Nat) ⟨8⟩ _ _).mpr
      SortedCommutativeSourceControls.original_commutative_equation

theorem repeated_administrative_gets_keep_their_supplied_origins :
    (SortedCommutativeProbeReconstructionControls.getOccurrence 7).target =
        (SortedCommutativeProbeReconstructionControls.getOccurrence 8).target ∧
      directReceipt (SortedCommutativeProbeReconstructionControls.getOccurrence 7) ≠
        directReceipt (SortedCommutativeProbeReconstructionControls.getOccurrence 8) :=
  ⟨SortedCommutativeProbeReconstructionControls.equal_full_selected_targets_keep_distinct_origins.1.trans
      SortedCommutativeProbeReconstructionControls.equal_full_selected_targets_keep_distinct_origins.2.1.symm,
    SortedCommutativeProbeReconstructionControls.equal_full_selected_targets_keep_distinct_origins.2.2⟩

theorem the_source_unit_rule_fails_nonunit_admission :
    ¬ Source.NonunitRedex (unitSourceRule low) := by
  intro admitted
  apply admitted
  apply heq_of_eq
  apply congrArg RawArrow.value
  exact Quotient.sound (Equation.unit (signature := Source.signature arity) (Parallel := Source.Parallel arity)
    rfl (.zero rfl : Source.Value arity))

theorem dropping_the_nonunit_premise_restores_actual_competing_results :
    ActIPO SortedCommutativeUnitReactionControls.combinedRules (getLabel (.ordinary Symbol.pair) 0)
        (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered)) lowTarget ∧
      ActIPO SortedCommutativeUnitReactionControls.combinedRules (getLabel (.ordinary Symbol.pair) 0)
        (RawArrow.value (sourceBundle (.ordinary Symbol.pair) ordered))
        SortedCommutativeUnitReactionControls.originalResult ∧
      lowTarget ≠ SortedCommutativeUnitReactionControls.originalResult :=
  SortedCommutativeUnitReactionControls.actual_get_result_is_not_unique

end Mettapedia.OSLF.Framework.SortedCommutativeOriginalProbeControls
