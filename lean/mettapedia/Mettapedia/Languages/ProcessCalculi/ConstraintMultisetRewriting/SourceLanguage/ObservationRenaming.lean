import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Observation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.LawRenaming

/-!
# The renaming law for what a configuration shows

Renaming bound names (`Renaming.KeyRenaming`) keeps the bag of answers (`answers_rConfig`). With the
typed absence, a configuration also shows its refusals and the reasons its alternatives wait on. These
carry data, and the renaming maps them: a renamed configuration shows the same answers, the renamed
refusals, and the renamed reasons (`observe_rConfig`). Each reason is kept because the renaming keeps
most general solutions (`principal_iff_rename`), determination of an address and readings.

So under this observation the laws about runs hold unchanged (they relate configurations), the bag
laws for dead alternatives hold (`Observation.observe_add_dead`), and the renaming law holds with the
reasons renamed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ObservationRenaming

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Laws Renaming Observation

variable (π : KeyRenaming) {D : Discipline MSig [] ()}

/-- A reason renamed. -/
def rWaiting {Ty : Type} : Waiting mkeys [] () Ty → Waiting mkeys [] () Ty
  | .address sp => .address (π.rD sp)
  | .noPrincipal t => .noPrincipal (π.rD t)
  | .mixed v T => .mixed (π.rD v) T

theorem rStore_inv (K : List (Constraint mkeys [] ())) : renameStore π.inv.asg (π.rStore K) = K := by
  simp only [KeyRenaming.rStore, renameStore, List.map_map]
  conv_rhs => rw [← List.map_id K]
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply, ← Assignment.instantiate_compose, π.compose_inv, instantiate_identity]
  rfl

/-- **A renamed store has a most general solution exactly when the store has one.** -/
theorem principal_iff_rename (K : List (Constraint mkeys [] ())) :
    (∃ θ, Principal (π.rStore K) θ) ↔ ∃ θ, Principal K θ := by
  constructor
  · rintro ⟨θ, principal⟩
    have back := principal_rename (ρ := π.inv.asg) (ρ' := π.asg) π.inv_compose π.compose_inv principal
    rw [rStore_inv] at back
    exact ⟨_, back⟩
  · rintro ⟨θ, principal⟩
    exact ⟨_, principal_rename (ρ := π.asg) (ρ' := π.inv.asg) π.compose_inv π.inv_compose principal⟩

theorem solvable_rStore (K : List (Constraint mkeys [] ())) : Solvable (π.rStore K) ↔ Solvable K :=
  solvable_rename π.compose_inv K

/-- **The reason a renamed alternative waits on is the renamed reason.** -/
theorem reason_rBranch (b : Branch mkeys [] () D.Ty) : reason (π.rBranch b) = (reason b).map (rWaiting π) := by
  classical
  rcases b with ⟨K, focus, frames, pending⟩
  cases focus with
  | eval c =>
      cases c with
      | run t =>
          show (if ∃ θ, Principal (π.rStore K) θ then none else some (Waiting.noPrincipal (π.rD t))) =
            (if ∃ θ, Principal K θ then none else some (Waiting.noPrincipal t)).map (rWaiting π)
          by_cases has : ∃ θ, Principal K θ
          · rw [if_pos ((principal_iff_rename π K).mpr has), if_pos has]
            rfl
          · rw [if_neg (fun h => has ((principal_iff_rename π K).mp h)), if_neg has]
            rfl
      | query sp p k =>
          show (if ∃ h, Determines (π.rStore K) (π.rD sp) h then none else some (Waiting.address (π.rD sp))) =
            (if ∃ h, Determines K sp h then none else some (Waiting.address sp)).map (rWaiting π)
          have same : (∃ h, Determines (π.rStore K) (π.rD sp) h) ↔ ∃ h, Determines K sp h :=
            exists_congr fun h => determines_rename π.compose_inv K sp h
          by_cases has : ∃ h, Determines K sp h
          · rw [if_pos (same.mpr has), if_pos has]
            rfl
          · rw [if_neg (fun h => has (same.mp h)), if_neg has]
            rfl
      | add sp t k =>
          show (if ∃ h, Determines (π.rStore K) (π.rD sp) h then none else some (Waiting.address (π.rD sp))) =
            (if ∃ h, Determines K sp h then none else some (Waiting.address sp)).map (rWaiting π)
          have same : (∃ h, Determines (π.rStore K) (π.rD sp) h) ↔ ∃ h, Determines K sp h :=
            exists_congr fun h => determines_rename π.compose_inv K sp h
          by_cases has : ∃ h, Determines K sp h
          · rw [if_pos (same.mpr has), if_pos has]
            rfl
          · rw [if_neg (fun h => has (same.mp h)), if_neg has]
            rfl
      | remove sp t k =>
          show (if ∃ h, Determines (π.rStore K) (π.rD sp) h then none else some (Waiting.address (π.rD sp))) =
            (if ∃ h, Determines K sp h then none else some (Waiting.address sp)).map (rWaiting π)
          have same : (∃ h, Determines (π.rStore K) (π.rD sp) h) ↔ ∃ h, Determines K sp h :=
            exists_congr fun h => determines_rename π.compose_inv K sp h
          by_cases has : ∃ h, Determines K sp h
          · rw [if_pos (same.mpr has), if_pos has]
            rfl
          · rw [if_neg (fun h => has (same.mp h)), if_neg has]
            rfl
      | ret _ => rfl
      | apply _ => rfl
      | let_ _ _ _ _ => rfl
      | choice _ _ => rfl
      | fail => rfl
      | new _ _ _ => rfl
      | check _ _ => rfl
      | delay _ _ _ _ => rfl
      | force _ => rfl
  | value v =>
      cases frames with
      | nil => rfl
      | cons f fs =>
          cases f with
          | checkAt T =>
              show (if (∀ g, Reads (π.rStore K) (π.rD v) g → D.admits T g) ∨
                    (∀ g, Reads (π.rStore K) (π.rD v) g → ¬ D.admits T g) then none
                  else some (Waiting.mixed (π.rD v) T)) =
                (if (∀ g, Reads K v g → D.admits T g) ∨ (∀ g, Reads K v g → ¬ D.admits T g) then none
                  else some (Waiting.mixed v T)).map (rWaiting π)
              have same : ∀ g, Reads (π.rStore K) (π.rD v) g ↔ Reads K v g :=
                fun g => reads_rename π.compose_inv K v g
              simp only [same]
              split <;> rfl
          | bindTo _ _ _ => rfl
          | memo _ => rfl
  | refused _ _ => rfl

/-- The refusal of a renamed alternative is the renamed refusal. -/
theorem refusal_rBranch (b : Branch mkeys [] () D.Ty) :
    refusal (π.rBranch b) = (refusal b).map fun r => (π.rD r.1, r.2) := by
  rcases b with ⟨K, focus, frames, pending⟩
  cases focus <;> rfl

theorem live_rConfig (C : Config mkeys [] () D.Ty) : live (π.rConfig C) = (live C).map π.rBranch := by
  classical
  simp only [live, KeyRenaming.rConfig, Multiset.filter_map]
  congr 1
  apply Multiset.filter_congr
  intro b _
  exact solvable_rStore π b.store

/-- **The renaming law for the observation**: a renamed configuration shows the same answers, the
renamed refusals, and the renamed reasons for waiting. -/
theorem observe_rConfig (C : Config mkeys [] () D.Ty) :
    observe (π.rConfig C) =
      ⟨C.answers, (observe C).refusals.map (fun r => (π.rD r.1, r.2)), (observe C).waiting.map (rWaiting π)⟩ := by
  simp only [observe, π.answers_rConfig, live_rConfig, Multiset.filterMap_map, Multiset.map_filterMap]
  congr 1
  · congr 1
    funext b
    exact refusal_rBranch π b
  · congr 1
    funext b
    exact reason_rBranch π b

#print axioms principal_iff_rename
#print axioms reason_rBranch
#print axioms observe_rConfig

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ObservationRenaming
