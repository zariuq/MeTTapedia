import Mettapedia.Languages.MeTTa.PeTTa.StableGroundGuardDischarge

/-! Positive and negative controls for the ground-uninterpreted guard discharge. -/

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000

namespace Mettapedia.Languages.MeTTa.PeTTa.StableGroundGuardDischarge.Controls

open Mettapedia.Logic.LP
open IntrinsicTypeFacts (signature TypeTerm Declaration named undefinedType)
open IndependentTypeOutput (row)
open StableGroundTypeQueries (GroundUninterpreted groundSchema admitted_is_ground)
open Mettapedia.Logic.LP.ConjunctiveUnification (applyTerm_of_isGround)

def unrelatedOverloads : List Declaration :=
  [⟨0, .symbol "other", named "Number"⟩, ⟨1, .symbol "other", named "String"⟩]

def value : TypeTerm := row [named "raw", .const (.number "7")]
def expected : TypeTerm := .var 0
def entered : Subst signature := Subst.single 0 (groundSchema value)

theorem admitted_despite_unrelated_overloads : GroundUninterpreted unrelatedOverloads value := by
  simp only [value, row, GroundUninterpreted]
  intro index
  fin_cases index <;> simp [GroundUninterpreted, unrelatedOverloads, named]

theorem input_check_is_one_actual_refinement :
    check unrelatedOverloads 10 [] (Subst.id signature) value expected = some [entered] := by
  have entered := input_guard_single_refinement unrelatedOverloads 10 [] (Subst.id signature)
    value expected 0 rfl
    (by simpa only [Subst.applyTerm_id] using admitted_despite_unrelated_overloads)
    (by simp [Subst.applyTerm_id, value, row, named, Term.size])
  simpa only [Subst.applyTerm_id, Subst.comp_id_right, Controls.entered] using entered

theorem return_check_is_literally_readonly :
    check unrelatedOverloads 10 [] entered value expected = some [entered] := by
  have unchanged : entered.applyTerm value = value :=
    applyTerm_of_isGround entered (admitted_is_ground _ _ admitted_despite_unrelated_overloads)
  apply return_guard_readonly
  · rw [unchanged]
    exact admitted_despite_unrelated_overloads
  · rw [unchanged]
    simp [value, row, named, Term.size]
  · rw [unchanged]
    exact Subst.single_eq (σ := signature) 0 (groundSchema value)

theorem observing_the_type_name_prevents_input_erasure :
    (Subst.id signature).applyTerm expected ≠ entered.applyTerm expected := by
  simp [expected, entered, Subst.applyTerm, Subst.id, Subst.single, value, row, groundSchema]

def observedOverloads : List Declaration :=
  [⟨0, .symbol "raw", named "Number"⟩, ⟨1, .symbol "raw", named "String"⟩]

theorem groundness_alone_does_not_give_one_continuation :
    (named "raw").isGround ∧
      (check observedOverloads 1 [] (Subst.id signature) (named "raw") expected).map List.length = some 2 := by
  constructor
  · trivial
  · cbv

def changedWorld : List Declaration := [⟨0, .symbol "raw", named "Number"⟩]

theorem changed_declarations_can_invalidate_a_ground_range :
    (check changedWorld 1 [] (Subst.single 0 undefinedType) (named "raw") expected).map List.length = some 0 := by
  cbv

theorem open_values_need_the_other_path (library : List Declaration) (name : Nat) :
    ¬ GroundUninterpreted library (.var name) := fun impossible => impossible

end Mettapedia.Languages.MeTTa.PeTTa.StableGroundGuardDischarge.Controls
