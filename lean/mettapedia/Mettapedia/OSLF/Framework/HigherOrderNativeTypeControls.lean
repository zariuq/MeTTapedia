import Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes
import Mettapedia.GSLT.Logic.HigherOrderHMLControls
import Mettapedia.GSLT.Logic.HennessyMilnerBehavioralCoverControls

/-!
# Higher-order observations through generated native types

The existing process example exercises native-type adequacy with actual
finite successor witnesses. Distinct typed successor observations remain
distinct. Unrestricted native predicates can separate higher-order bisimilar
states, so the adequacy statement is restricted to the HML formula fragment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.HigherOrderNativeTypeControls

open Mettapedia.GSLT
open HigherOrderBisimulation HigherOrderHML
open GSLTTypeSynthesis HennessyMilnerNativeTypes

private abbrev processes := PayloadControls.system
private abbrev packedProcesses := packedGSLT processes.classLabelSystem

theorem actual_process_native_adequacy (left right : PayloadControls.Process) :
    (∀ formula : HennessyMilner.Formula (classSystem processes).Atom
      (classSystem processes).Label,
      ((gsltOSLF packedProcesses).satisfies (S := ()) ⟨(), left⟩
          (formulaNativeType (classSystem processes) formula).pred ↔
        (gsltOSLF packedProcesses).satisfies (S := ()) ⟨(), right⟩
          (formulaNativeType (classSystem processes) formula).pred)) ↔
      processes.Bisimilar () left right :=
  higherOrder_formulaNativeTypes_equivalent_iff_bisimilar processes
    HigherOrderHMLControls.process_class_system_image_finite left right

theorem nested_payloads_share_formula_native_types
    (formula : HennessyMilner.Formula (classSystem processes).Atom
      (classSystem processes).Label) :
    ((gsltOSLF packedProcesses).satisfies (S := ())
        ⟨(), .send false (.send true (.halt false))⟩
        (formulaNativeType (classSystem processes) formula).pred ↔
      (gsltOSLF packedProcesses).satisfies (S := ())
        ⟨(), .send false (.send true (.halt true))⟩
        (formulaNativeType (classSystem processes) formula).pred) :=
  higherOrder_formulaNativeTypes_equivalent_of_bisimilar processes
    PayloadControls.nested_payloads_are_bisimilar formula

theorem distinct_typed_successors_separated_by_native_type :
    (gsltOSLF (packedGSLT TypedPayloadControls.system.classLabelSystem)).satisfies (S := ())
        ⟨true, 0⟩
        (formulaNativeType (classSystem TypedPayloadControls.system)
          (.atom (.inr ⟨true, (0 : Nat)⟩))).pred ∧
      ¬(gsltOSLF (packedGSLT TypedPayloadControls.system.classLabelSystem)).satisfies (S := ())
        ⟨true, 1⟩
        (formulaNativeType (classSystem TypedPayloadControls.system)
          (.atom (.inr ⟨true, (0 : Nat)⟩))).pred :=
  HigherOrderHMLControls.mixed_successor_formula_separates

/-- A genuine negative boundary: formula-generated types and all native
predicates do not induce the same equivalence. -/
theorem higher_order_related_but_unrestricted_native_types_separate :
    processes.Bisimilar () (.send false (.halt false)) (.send false (.halt true)) ∧
      ¬(∀ nativeType : GSLTNativeType packedProcesses,
        ((gsltOSLF packedProcesses).satisfies (S := ())
            ⟨(), .send false (.halt false)⟩ nativeType.pred ↔
          (gsltOSLF packedProcesses).satisfies (S := ())
            ⟨(), .send false (.halt true)⟩ nativeType.pred)) := by
  have related := PayloadControls.bisimilar_of_code_eq
    (left := .send false (.halt false)) (right := .send false (.halt true)) rfl
  refine ⟨related, ?_⟩
  apply (bisimilar_not_equiv_not_allNativeTypes_equivalent (classSystem processes)
    ((class_bisimilar_iff processes _ _).mpr related) ?_).2
  intro same
  change (⟨(), PayloadControls.Process.send false (.halt false)⟩ :
    PackedState PayloadControls.States) = ⟨(), .send false (.halt true)⟩ at same
  have stateSame := eq_of_heq (Sigma.mk.inj same).2
  cases stateSame

/-- The broader native-type theorem is exercised on infinitely many literal
successors with two observed behavioral classes, not just a finite model. -/
theorem infinite_literal_successors_native_adequacy
    (left right : HennessyMilner.BehavioralCoverControls.State) :
    (∀ formula : HennessyMilner.Formula
        HennessyMilner.BehavioralCoverControls.system.Atom
        HennessyMilner.BehavioralCoverControls.system.Label,
      ((gsltOSLF HennessyMilner.BehavioralCoverControls.theory).satisfies (S := ()) left
          (formulaNativeType HennessyMilner.BehavioralCoverControls.system formula).pred ↔
        (gsltOSLF HennessyMilner.BehavioralCoverControls.theory).satisfies (S := ()) right
          (formulaNativeType HennessyMilner.BehavioralCoverControls.system formula).pred)) ↔
      HennessyMilner.BehavioralCoverControls.system.Bisimilar left right :=
  formulaNativeTypes_equivalent_iff_bisimilar_of_behavioral_cover
    HennessyMilner.BehavioralCoverControls.system
    HennessyMilner.BehavioralCoverControls.behavioral_successors_have_two_class_cover left right

theorem infinite_literal_successors_positive_native_adequacy
    (left right : HennessyMilner.BehavioralCoverControls.State) :
    (∀ formula : HennessyMilner.PosFormula
        HennessyMilner.BehavioralCoverControls.system.Atom
        HennessyMilner.BehavioralCoverControls.system.Label,
      (gsltOSLF HennessyMilner.BehavioralCoverControls.theory).satisfies (S := ()) left
          (positiveFormulaNativeType HennessyMilner.BehavioralCoverControls.system formula).pred →
        (gsltOSLF HennessyMilner.BehavioralCoverControls.theory).satisfies (S := ()) right
          (positiveFormulaNativeType HennessyMilner.BehavioralCoverControls.system formula).pred) ↔
      HennessyMilner.BehavioralCoverControls.system.Similar left right :=
  positiveFormulaNativeTypes_preorder_iff_similar_of_behavioral_cover
    HennessyMilner.BehavioralCoverControls.system
    HennessyMilner.BehavioralCoverControls.behavioral_successors_have_two_class_cover left right

/-- Positive native observations order these states in one direction only;
the full formula fragment still distinguishes them. -/
theorem positive_native_order_is_not_bisimilarity :
    (∀ formula : HennessyMilner.PosFormula
        HennessyMilner.BehavioralCoverControls.system.Atom
        HennessyMilner.BehavioralCoverControls.system.Label,
      (gsltOSLF HennessyMilner.BehavioralCoverControls.theory).satisfies (S := ()) (.terminal 0)
          (positiveFormulaNativeType HennessyMilner.BehavioralCoverControls.system formula).pred →
        (gsltOSLF HennessyMilner.BehavioralCoverControls.theory).satisfies (S := ()) (.terminal 1)
          (positiveFormulaNativeType HennessyMilner.BehavioralCoverControls.system formula).pred) ∧
      ¬HennessyMilner.BehavioralCoverControls.system.Bisimilar (.terminal 0) (.terminal 1) :=
  ⟨(infinite_literal_successors_positive_native_adequacy _ _).mpr
      HennessyMilner.BehavioralCoverControls.terminal_zero_similar_terminal_one,
    HennessyMilner.BehavioralCoverControls.parity_representatives_are_behaviorally_distinct⟩

/-- The behavioral-cover generalization does not erase the parity observation. -/
theorem parity_native_type_separates :
    (gsltOSLF HennessyMilner.BehavioralCoverControls.theory).satisfies (S := ()) (.terminal 1)
        (formulaNativeType HennessyMilner.BehavioralCoverControls.system (.atom .odd)).pred ∧
      ¬(gsltOSLF HennessyMilner.BehavioralCoverControls.theory).satisfies (S := ()) (.terminal 0)
        (formulaNativeType HennessyMilner.BehavioralCoverControls.system (.atom .odd)).pred := by
  exact ⟨rfl, Nat.zero_ne_one⟩

end Mettapedia.OSLF.Framework.HigherOrderNativeTypeControls
