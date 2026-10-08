import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitObservationComparison
import Mettapedia.OSLF.Framework.SortedTypedStructuralObservationControls
import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitTransitionControls

/-!
# Proper typed partial-kit observations, whole context residues and origin boundaries

The finite kit opens send, one channel and the process unit. Its generated
class includes an actual unit-padded representative with an unopened Cut
root. Both literal IPO and same-fixed-point payload observation recover the
complete class. Changed channels and multiplicities are genuinely separated.
Nonidentity context substitution retains its whole stored process. Original
unit-get competition survives unchanged, and the independently empty origin
family shows why the administrative inhabitance condition is necessary.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstrumentKitObservationControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence
open SortedTypedInstruments SortedTypedInstrumentControls
open SortedTypedStructuralObservationControls

def opened : Kit.Policy sourceSignature sourceParallel := finiteKit
def originalRules : Nat → ReactionRule (.origin : SourceCategory sourceSignature sourceParallel) :=
  SortedTypedInstrumentKitTransitionControls.originalRules

theorem the_unopened_raw_root_still_has_a_generated_equation_class :
    ¬StructuralObservations.Supported opened padded ∧ StructuralObservations.Generated opened (classOf padded) :=
  ⟨the_unopened_cut_representative_is_not_raw_supported,
    its_actual_equation_class_is_nevertheless_generated⟩

theorem actual_literal_observation_tests_its_complete_class (right : Class sourceSignature sourceParallel .process) :
    IPOBisimilar (Kit.categoryRules (NativeOrigins := Nat) originalRules opened)
      (Kit.value (classEmbedding (classOf padded)) (Kit.classEmbedding_supported opened _))
      (Kit.value (classEmbedding right) (Kit.classEmbedding_supported opened right)) ↔
        classOf padded = right :=
  Kit.observer_bisimilar_iff_source_equal_of_generated opened originalRules ⟨24⟩ _ right
    its_actual_equation_class_is_nevertheless_generated

theorem actual_same_fixed_point_observation_tests_every_supported_native_right
    (right : ValueClass (source := sourceSignature) (Parallel := sourceParallel) (.original .process))
    (supported : Kit.ClassSupported opened right) :
    (Kit.payloadSystem (NativeOrigins := Nat) opened originalRules).Bisimilar (.original .process)
      (classEmbedding (classOf padded)) right ↔ classEmbedding (classOf padded) = right :=
  Kit.payload_bisimilar_iff_embedded_equal_of_generated opened originalRules ⟨24⟩ _
    its_actual_equation_class_is_nevertheless_generated right supported

theorem the_actual_partial_structural_and_interactive_observations_agree
    (right : Class sourceSignature sourceParallel .process) :
    StructuralObservations.PartialLogicalEquivalent opened (classOf padded) right ↔
      (Kit.payloadSystem (NativeOrigins := Nat) opened originalRules).Bisimilar (.original .process)
        (classEmbedding (classOf padded)) (classEmbedding right) :=
  Kit.partialLogicalEquivalent_iff_actual_payload_observer_of_generated opened originalRules ⟨24⟩ _ right
    its_actual_equation_class_is_nevertheless_generated

theorem actual_unit_padding_is_accepted_by_both_observer_systems :
    IPOBisimilar (Kit.categoryRules (NativeOrigins := Nat) originalRules opened)
      (Kit.value (classEmbedding (classOf padded)) (Kit.classEmbedding_supported opened _))
      (Kit.value (classEmbedding (classOf (sourcePayload 7))) (Kit.classEmbedding_supported opened _)) ∧
      (Kit.payloadSystem (NativeOrigins := Nat) opened originalRules).Bisimilar (.original .process)
        (classEmbedding (classOf padded)) (classEmbedding (classOf (sourcePayload 7))) :=
  ⟨(actual_literal_observation_tests_its_complete_class _).mpr
      actual_unit_padding_changes_the_raw_root_but_not_the_class,
    (Kit.payload_bisimilar_iff_source_equal_of_generated opened originalRules (NativeOrigins := Nat) ⟨24⟩ _ _
      its_actual_equation_class_is_nevertheless_generated).mpr
        actual_unit_padding_changes_the_raw_root_but_not_the_class⟩

theorem changing_the_complete_channel_is_rejected_by_the_coarsest_payload_observer :
    ¬(Kit.payloadSystem (NativeOrigins := Nat) opened originalRules).Bisimilar (.original .process)
      (classEmbedding (classOf (sourcePayload 7))) (classEmbedding (classOf (sourcePayload 11))) := by
  intro related
  have logical := (Kit.partialLogicalEquivalent_iff_actual_payload_observer_of_generated
    opened originalRules (NativeOrigins := Nat) ⟨24⟩ _ _
    ⟨sourcePayload 7, the_whole_typed_send_is_supported, rfl⟩).mpr related
  exact changing_the_complete_channel_rejects_the_structural_test
    ((logical (StructuralObservations.characteristic (sourcePayload 7))
      its_independent_characteristic_formula_really_holds.1).mp
        its_independent_characteristic_formula_really_holds.2)

theorem duplicating_the_complete_process_is_rejected_by_the_coarsest_payload_observer :
    ¬(Kit.payloadSystem (NativeOrigins := Nat) opened originalRules).Bisimilar (.original .process)
      (classEmbedding (classOf (sourcePayload 7)))
      (classEmbedding (classOf (.cut (signature := sourceSignature) (Parallel := sourceParallel)
        (sort := .process) rfl (sourcePayload 7) (sourcePayload 7)))) := by
  intro related
  have same := (Kit.payload_bisimilar_iff_source_equal_of_generated opened originalRules (NativeOrigins := Nat)
    ⟨24⟩ _ _ ⟨sourcePayload 7, the_whole_typed_send_is_supported, rfl⟩).mp related
  have counts := congrArg (fun supplied => (inventoryQ supplied).card) same
  change 1 = 1 + 1 at counts
  omega

def arguments : Arguments (SourceHead.ordinary (source := sourceSignature) (Parallel := sourceParallel) Symbol.send) :=
  sendArguments 7 (.zero rfl)

theorem children_supported : ∀ position, Kit.Supported opened (arguments position) := by
  intro position
  fin_cases position
  · exact Kit.embed_supported opened (sourceName 7)
  · exact Kit.embed_supported opened (.zero rfl : SourceValue .process)

def askReceipt (origin : Nat) := Kit.directAdministrativeFiring originalRules
  (.ask origin (.ordinary Symbol.send) arguments) ⟨Or.inl rfl, children_supported⟩

theorem the_actual_ask_receipt_retains_the_full_tuple_and_origin :
    (askReceipt 24).occurrence.origin = (Sum.inr 24 : Nat ⊕ Nat) ∧
      ((askReceipt 24).result).val = RawArrow.value (classOf
        (bundle (SourceHead.ordinary (source := sourceSignature) (Parallel := sourceParallel) Symbol.send) arguments)) :=
  ⟨rfl, Kit.directAdministrativeFiring_result originalRules _ _⟩

theorem duplicate_supplied_origins_remain_distinct : ¬HEq (askReceipt 24) (askReceipt 25) :=
  Kit.directAdministrativeFiring_distinct_origins originalRules 24 25 (by omega) _ arguments _

def storedContext : ContextClass (signature sourceSignature sourceParallel) NativeParallel
    (.original .process) (.original .process) :=
  contextClassOf (.left rfl .hole (embed (sourcePayload 11)))

theorem storedContext_supported : Kit.ClassContextSupported opened storedContext :=
  ⟨_, .left (source := sourceSignature) (Parallel := sourceParallel)
    (second := .original .process) rfl
    (.hole (source := sourceSignature) (Parallel := sourceParallel) (.original .process))
    (Kit.embed_supported opened (sourcePayload 11)), rfl⟩

theorem nonidentity_substitution_retains_the_whole_stored_process :
    storedContext.fill (classEmbedding (classOf padded)) =
      classOf (.cut (signature := signature sourceSignature sourceParallel) (Parallel := NativeParallel)
        (sort := .original .process) rfl (embed (sourcePayload 7)) (embed (sourcePayload 11))) := by
  rw [actual_unit_padding_changes_the_raw_root_but_not_the_class]
  rfl

theorem the_actual_complete_context_comparison_retains_both_supported_outputs :
    Kit.ClassSupported opened (storedContext.fill (classEmbedding (classOf padded))) ∧
      Kit.ClassSupported opened (storedContext.fill (classEmbedding (classOf (sourcePayload 7)))) ∧
        storedContext.fill (classEmbedding (classOf padded)) =
          storedContext.fill (classEmbedding (classOf (sourcePayload 7))) ∧
          (Kit.payloadSystem (NativeOrigins := Nat) opened originalRules).Bisimilar (.original .process)
            (storedContext.fill (classEmbedding (classOf padded)))
            (storedContext.fill (classEmbedding (classOf (sourcePayload 7)))) :=
  Kit.generated_payload_context_readout opened originalRules ⟨24⟩ _
    its_actual_equation_class_is_nevertheless_generated _ (Kit.classEmbedding_supported opened _)
    storedContext storedContext_supported actual_unit_padding_is_accepted_by_both_observer_systems.2

theorem omitting_the_stored_process_changes_the_complete_substitution :
    storedContext.fill (classEmbedding (classOf padded)) ≠ classEmbedding (classOf (sourcePayload 7)) := by
  intro erased
  rw [nonidentity_substitution_retains_the_whole_stored_process] at erased
  have counts := congrArg (fun supplied => (inventoryQ supplied).card) erased
  change 1 + 1 = 1 at counts
  omega

theorem opensFinite : ∀ head, SortedTypedInstrumentKitTransitionControls.oldKit head → opened head :=
  fun _ permission => Or.inl permission

def oldOriginalCompetitor := Kit.expandFiring opensFinite originalRules SortedTypedInstrumentKitTransitionControls.originalCompetitor

theorem the_independent_unit_rule_competitor_retains_its_entire_observer_bearing_result :
    oldOriginalCompetitor.result = RawArrow.value
      (classOf (.cut (signature := signature sourceSignature sourceParallel) (Parallel := NativeParallel)
        (sort := .original .process) rfl (embed (sourcePayload 11))
          (getAssay SortedTypedInstrumentKitTransitionControls.sendHead SortedTypedInstrumentKitTransitionControls.arguments 1))) := by
  rw [oldOriginalCompetitor, Kit.expandFiring_result]
  rfl

theorem the_original_competitor_is_not_the_administrative_selected_child :
    oldOriginalCompetitor.result ≠ (processGet 24 7 (sourcePayload 9)).target := by
  rw [oldOriginalCompetitor, Kit.expandFiring_result]
  exact SortedTypedInstrumentKitTransitionControls.the_competing_get_result_does_not_erase_the_assay

def noOriginalRules : Empty → ReactionRule (.origin : SourceCategory sourceSignature sourceParallel) := Empty.elim

theorem no_firing_without_either_origin_family {before after : Kit.Object opened}
    (agent : Kit.origin opened ⟶ before) (label : before ⟶ after) (next : Kit.origin opened ⟶ after) :
    ¬ActIPO (Kit.categoryRules (NativeOrigins := Empty) noOriginalRules opened) label agent next := by
  rintro ⟨_, ⟨declaration, _⟩, _, _, _, _⟩
  cases declaration with
  | original absent => exact Empty.elim absent
  | administrative occurrence permitted => exact Empty.elim occurrence.origin

theorem empty_administrative_origins_do_not_give_the_generated_observer_ceiling :
    IPOBisimilar (Kit.categoryRules (NativeOrigins := Empty) noOriginalRules opened)
      (Kit.value (classEmbedding (classOf (sourcePayload 7))) (Kit.classEmbedding_supported opened _))
      (Kit.value (classEmbedding (classOf (sourcePayload 11))) (Kit.classEmbedding_supported opened _)) := by
  refine ⟨fun _ _ _ => True, ?_, True.intro⟩
  intro current first second _related
  constructor
  · intro target label next step
    exact (no_firing_without_either_origin_family first label next step).elim
  · intro target label next step
    exact (no_firing_without_either_origin_family second label next step).elim

def activeProperRule : ReactionRule (.origin : SourceCategory sourceSignature sourceParallel) where
  codomain := .interface .process
  redex := RawArrow.value (classOf (.cut rfl (sourcePayload 7) (.zero rfl)))
  reactum := RawArrow.value (classOf (sourcePayload 11))

def activeOriginalRules : Nat → ReactionRule (.origin : SourceCategory sourceSignature sourceParallel) :=
  fun _ => activeProperRule

def activeFirst : Kit.origin SortedTypedInstrumentKitTransitionControls.emptyKit ⟶
    Kit.interface SortedTypedInstrumentKitTransitionControls.emptyKit (.original .process) :=
  (Kit.sourceInclusion SortedTypedInstrumentKitTransitionControls.emptyKit).map activeProperRule.redex

def inactiveFirst : Kit.origin SortedTypedInstrumentKitTransitionControls.emptyKit ⟶
    Kit.interface SortedTypedInstrumentKitTransitionControls.emptyKit (.original .process) :=
  Kit.value (classOf (.zero (signature := signature sourceSignature sourceParallel)
    (Parallel := NativeParallel) (sort := .original .process) rfl))
    ⟨_, .zero (source := sourceSignature) (Parallel := sourceParallel) (sort := .original .process) rfl, rfl⟩

def activeFiring : Source.FiringAt
    (Kit.Declaration sourceSignature sourceParallel Nat Nat SortedTypedInstrumentKitTransitionControls.emptyKit)
    (fun declaration => declaration.rule activeOriginalRules) activeFirst (𝟙 _) where
  occurrence := .original 31
  reaction := 𝟙 _
  square := rfl
  minimal := (Kit.idemPushout_iff rfl).mpr
    (raw_right_identity_isIPO _ (Category.comp_id activeFirst.val))

def allConstructorWeight : (signature sourceSignature sourceParallel).Constructor → Nat := fun _ => 1

theorem the_actual_proper_redex_has_nonzero_constructor_weight :
    HereditaryWeight.arrow allConstructorWeight (Source.mapReactionRule activeProperRule).redex = 2 := by
  change HereditaryWeight.term allConstructorWeight
    (.cut (signature := signature sourceSignature sourceParallel) (Parallel := NativeParallel)
      (sort := .original .process) rfl (embed (sourcePayload 7)) (.zero rfl)) = 2
  rw [HereditaryWeight.term_cut]
  change (1 + ∑ position : Fin 2,
    HereditaryWeight.term allConstructorWeight (embed
      (Fin.cases (motive := fun coordinate : Fin 2 => SourceValue (sourceSignature.input Symbol.send coordinate))
        (sourceName 7) (fun _ => (.zero rfl : SourceValue .process)) position))) + 0 = 2
  rw [Fin.sum_univ_two]
  rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl, Fin.cases_succ]
  norm_num [Fin.cases_zero, HereditaryWeight.term, embed, sourceName, allConstructorWeight]

theorem an_inactive_unit_cannot_match_the_actual_original_identity_firing
    (next : Kit.origin SortedTypedInstrumentKitTransitionControls.emptyKit ⟶
      Kit.interface SortedTypedInstrumentKitTransitionControls.emptyKit (.original .process)) :
    ¬ActIPO (Kit.categoryRules (NativeOrigins := Nat) activeOriginalRules
      SortedTypedInstrumentKitTransitionControls.emptyKit) (𝟙 _) inactiveFirst next := by
  rintro ⟨_, ⟨declaration, rfl⟩, reaction, square, _minimal, _output⟩
  cases declaration with
  | administrative occurrence permitted =>
    cases occurrence <;> exact permitted.1 rfl
  | original index =>
    have counts := congrArg (HereditaryWeight.arrow allConstructorWeight) (congrArg Subtype.val square)
    change HereditaryWeight.arrow allConstructorWeight (inactiveFirst.val ≫ 𝟙 _) =
      HereditaryWeight.arrow allConstructorWeight
        ((Source.mapReactionRule activeProperRule).redex ≫ reaction.val) at counts
    rw [HereditaryWeight.arrow_comp, HereditaryWeight.arrow_comp] at counts
    have redexRead := the_actual_proper_redex_has_nonzero_constructor_weight
    change HereditaryWeight.arrow allConstructorWeight inactiveFirst.val + 0 =
      HereditaryWeight.arrow allConstructorWeight (Source.mapReactionRule activeProperRule).redex +
        HereditaryWeight.arrow allConstructorWeight reaction.val at counts
    rw [redexRead] at counts
    have inactiveRead : HereditaryWeight.arrow allConstructorWeight inactiveFirst.val = 0 := rfl
    rw [inactiveRead] at counts
    omega

private theorem no_empty_kit_formula {sort : DataSort}
    (formula : StructuralObservations.Formula sourceSignature sourceParallel sort)
    (allowed : formula.Allowed SortedTypedInstrumentKitTransitionControls.emptyKit) : False := by
  revert allowed
  apply @StructuralObservations.Formula.rec sourceSignature sourceParallel
    (fun _ formula => formula.Allowed SortedTypedInstrumentKitTransitionControls.emptyKit → False)
    (t := formula)
  · intro sort parallel allowed
    exact allowed rfl
  · intro sort parallel first second firstRead secondRead allowed
    exact allowed.1 rfl
  · intro constructor arguments children allowed
    exact allowed.1 rfl

theorem current_partial_structural_tests_do_not_supply_unrestricted_interactive_adequacy :
    StructuralObservations.PartialLogicalEquivalent SortedTypedInstrumentKitTransitionControls.emptyKit
      (classOf (.cut (signature := sourceSignature) (Parallel := sourceParallel)
        (sort := .process) rfl (sourcePayload 7) (.zero rfl)))
      (classOf (.zero (signature := sourceSignature) (Parallel := sourceParallel) (sort := .process) rfl)) ∧
      ¬IPOBisimilar (Kit.categoryRules (NativeOrigins := Nat) activeOriginalRules
        SortedTypedInstrumentKitTransitionControls.emptyKit) activeFirst inactiveFirst := by
  constructor
  · intro formula allowed
    exact (no_empty_kit_formula formula allowed).elim
  · intro related
    obtain ⟨matched, matchedStep, _successors⟩ := ipoBisimilar_forward related activeFiring.step
    exact an_inactive_unit_cannot_match_the_actual_original_identity_firing matched matchedStep

end Mettapedia.OSLF.Framework.SortedTypedInstrumentKitObservationControls
