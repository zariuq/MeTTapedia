import Mettapedia.OSLF.Framework.SortedTypedPartialStructuralObservations
import Mettapedia.OSLF.Framework.SortedTypedInstrumentPayloadControls

/-!
# Typed structural tests, unit transport and unopened-root boundaries

Independent structural satisfaction retains both heterogeneous send
coordinates and rejects a changed nested channel or duplicated process.
The actual AC1 swap and unit-padding equations remain accepted. A finite
declared kit supports a whole send with its channel and unit child, and
its generated class includes an unopened-Cut representative by the earned
unit equation.

Opening only channel names gives no structural formula at process sort.
That fragment relates distinct processes which complete administrative
observation separates. This is an actual typed partial-fragment boundary,
not a partial-kit IPO adequacy claim or an arbitrary equation admission.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedStructuralObservationControls

open Mettapedia.OSLF.SortedCommutative
open SortedTypedInstruments SortedTypedInstruments.StructuralObservations
open SortedTypedInstrumentControls

def finiteKit : Policy sourceSignature sourceParallel := fun head =>
  head = .ordinary Symbol.send ∨ head = .ordinary (.name 7) ∨ head = .unit .process rfl

theorem the_whole_typed_send_is_supported : Supported finiteKit (sourcePayload 7) := by
  change finiteKit (.ordinary Symbol.send) ∧ ∀ position : Fin 2, _
  refine ⟨Or.inl rfl, ?_⟩
  intro position
  fin_cases position
  · refine ⟨Or.inr (Or.inl rfl), ?_⟩
    intro absent
    exact Fin.elim0 absent
  · exact Or.inr (Or.inr rfl)

theorem its_independent_characteristic_formula_really_holds :
    (characteristic (sourcePayload 7)).Allowed finiteKit ∧
      Holds (characteristic (sourcePayload 7)) (classOf (sourcePayload 7)) :=
  ⟨(characteristic_allowed_iff finiteKit _).mpr the_whole_typed_send_is_supported,
    (characteristic_holds_iff _ _).mpr rfl⟩

theorem changing_the_complete_channel_rejects_the_structural_test :
    ¬Holds (characteristic (sourcePayload 7)) (classOf (sourcePayload 11)) := by
  intro satisfies
  have recovered := (characteristic_holds_iff (sourcePayload 7) (classOf (sourcePayload 11))).mp satisfies
  have coordinates := (node_class_eq_iff (signature := sourceSignature) (Parallel := sourceParallel)
    Symbol.send _ _).mp recovered
  exact different_channel_indices_remain_distinct 11 7 (by omega) (congrArg classEmbedding (coordinates 0))

theorem duplicating_the_complete_process_rejects_the_structural_test :
    ¬Holds (characteristic (sourcePayload 9))
      (classOf (.cut (signature := sourceSignature) (Parallel := sourceParallel)
        (sort := .process) rfl (sourcePayload 9) (sourcePayload 9))) := by
  intro satisfies
  have recovered := (characteristic_holds_iff (sourcePayload 9) _).mp satisfies
  have counts := congrArg (fun supplied => (inventoryQ supplied).card) recovered
  change 1 + 1 = 1 at counts
  omega

theorem the_ac1_swap_is_accepted_by_the_whole_formula :
    Holds (characteristic (.cut (signature := sourceSignature) (Parallel := sourceParallel)
      (sort := .process) rfl (sourcePayload 7) (sourcePayload 9)))
      (classOf (.cut (signature := sourceSignature) (Parallel := sourceParallel)
        (sort := .process) rfl (sourcePayload 9) (sourcePayload 7))) :=
  (characteristic_holds_iff _ _).mpr (Quotient.sound
    (Equation.comm (signature := sourceSignature) (Parallel := sourceParallel)
      (sort := .process) rfl (sourcePayload 9) (sourcePayload 7)))

def padded : SourceValue .process := .cut rfl (.zero rfl) (sourcePayload 7)

theorem actual_unit_padding_changes_the_raw_root_but_not_the_class :
    classOf padded = classOf (sourcePayload 7) :=
  Quotient.sound ((Equation.comm (signature := sourceSignature) (Parallel := sourceParallel)
    (sort := .process) rfl (.zero rfl) (sourcePayload 7)).trans
      (Equation.unit (signature := sourceSignature) (Parallel := sourceParallel) rfl (sourcePayload 7)))

theorem the_unopened_cut_representative_is_not_raw_supported : ¬Supported finiteKit padded := by
  intro supported
  rcases supported.1 with impossible | impossible | impossible <;> cases impossible

theorem its_actual_equation_class_is_nevertheless_generated : Generated finiteKit (classOf padded) :=
  ⟨sourcePayload 7, the_whole_typed_send_is_supported,
    actual_unit_padding_changes_the_raw_root_but_not_the_class.symm⟩

theorem the_admitted_formula_still_tests_that_complete_class :
    Holds (characteristic (sourcePayload 7)) (classOf padded) :=
  (characteristic_holds_iff _ _).mpr actual_unit_padding_changes_the_raw_root_but_not_the_class

theorem the_fragment_separates_that_generated_class_from_every_right_class
    (right : Class sourceSignature sourceParallel .process) :
    PartialLogicalEquivalent finiteKit (classOf padded) right ↔ classOf padded = right :=
  partialLogicalEquivalent_iff_equal_of_generated finiteKit _ right
    its_actual_equation_class_is_nevertheless_generated

def namesOnly : Policy sourceSignature sourceParallel := fun head =>
  ∃ index : Nat, head = .ordinary (Symbol.name index)

private theorem names_only_formula_has_channel_output {sort : DataSort}
    (formula : Formula sourceSignature sourceParallel sort) (allowed : formula.Allowed namesOnly) :
    sort = .channel := by
  revert allowed
  apply @Formula.rec sourceSignature sourceParallel
    (fun sort formula => formula.Allowed namesOnly → sort = .channel) (t := formula)
  · intro sort parallel allowed
    obtain ⟨index, impossible⟩ := allowed
    cases impossible
  · intro sort parallel first second firstRead secondRead allowed
    obtain ⟨index, impossible⟩ := allowed.1
    cases impossible
  · intro constructor arguments inductionHypothesis allowed
    obtain ⟨index, headRead⟩ := allowed.1
    have constructorRead := SourceHead.ordinary.inj headRead
    subst constructor
    rfl

theorem a_name_only_fragment_cannot_enter_an_unopened_process_root :
    PartialLogicalEquivalent namesOnly (classOf (sourcePayload 7)) (classOf (sourcePayload 11)) := by
  intro formula allowed
  have impossible := names_only_formula_has_channel_output formula allowed
  cases impossible

theorem complete_observation_still_separates_those_processes :
    ¬(PayloadLabels.firingSystem
      (combinedSourceRules SortedTypedInstrumentOriginalProbeControls.originalRules Nat)).Bisimilar
      (.original .process) (classOf (embed (sourcePayload 7))) (classOf (embed (sourcePayload 11))) := by
  intro related
  have equivalent := (logicalEquivalent_iff_payloadObserver_bisimilar
    SortedTypedInstrumentOriginalProbeControls.originalRules (Origins := Nat) ⟨24⟩
      (classOf (sourcePayload 7)) (classOf (sourcePayload 11))).mpr related
  exact changing_the_complete_channel_rejects_the_structural_test
    ((equivalent (characteristic (sourcePayload 7))).mp
      its_independent_characteristic_formula_really_holds.2)

theorem the_literal_unit_formula_accepts_the_proper_binary_zero_cut :
    Holds (Formula.unit (source := sourceSignature) (Parallel := sourceParallel)
      (sort := .process) rfl)
      (classOf (.cut (signature := sourceSignature) (Parallel := sourceParallel)
        (sort := .process) rfl (.zero rfl) (.zero rfl))) :=
  Quotient.sound (Equation.unit (signature := sourceSignature) (Parallel := sourceParallel)
    (sort := .process) rfl (.zero rfl))

end Mettapedia.OSLF.Framework.SortedTypedStructuralObservationControls
