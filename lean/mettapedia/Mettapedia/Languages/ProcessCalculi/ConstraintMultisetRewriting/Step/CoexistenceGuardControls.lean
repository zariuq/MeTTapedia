import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceGuards
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceControls

/-! # Positive growth, shared matching identities and solution-relative checks -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Coexistence.GuardControls

def rigid : Frames (fun _ : Unit => Nat) (fun _ _ : Unit => Unit) where
  E := Eq
  equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  act _ term := term
  id _ := ()
  comp _ _ := ()
  act_id _ := rfl
  act_comp _ _ _ := rfl
  preserves := by intro _ _ _ _ _ same; exact same

noncomputable def selected (store : Finset Nat) : Finset Nat :=
  matchedOccurrences rigid (a := ()) (b := ()) () id 0 store

@[simp] theorem selected_empty : selected ∅ = ∅ := by
  ext occurrence
  simp [selected, mem_matches]

@[simp] theorem selected_singleton : selected {0} = {0} := by
  ext occurrence
  simp [selected, mem_matches, rigid, eq_comm]

@[simp] theorem selected_pair : selected {0, 1} = {0} := by
  ext occurrence
  simp [selected, mem_matches, rigid, eq_comm]
  tauto

theorem shared_count_without_blindness :
    (selected ({0} ∪ {0, 1})).card = 1 ∧
      NoNewMatches rigid (a := ()) (b := ()) () id 0 {0} {0, 1} ∧
        ∃ occurrence ∈ ({0, 1} : Finset Nat), rigid.E (a := ()) 0 (id occurrence) := by
  refine ⟨?_, ?_, ⟨0, by simp, rfl⟩⟩
  · have together : ({0} : Finset Nat) ∪ {0, 1} = {0, 1} := by decide
    rw [together, selected_pair]
    rfl
  · intro occurrence _ matched
    change 0 = occurrence at matched
    subst occurrence
    exact Finset.mem_singleton_self _

theorem matching_growth_breaks_absence_and_count :
    selected ∅ = ∅ ∧ selected (∅ ∪ {0}) ≠ ∅ ∧
      (selected (∅ ∪ {0})).card ≠ (selected ∅).card := by
  simp

noncomputable def absentGuard : SpatialGuard (fun _ _ : Unit => Unit) Nat () :=
  fun _ _ store => selected store = ∅

theorem absence_not_monotone : ¬SpatialGuard.Monotone absentGuard := by
  intro monotone
  have broken := monotone () () (show (∅ : Finset Nat) ⊆ {0} from Finset.empty_subset _)
    (by simp [absentGuard])
  simp [absentGuard] at broken

noncomputable def countOne : SpatialGuard (fun _ _ : Unit => Unit) Nat () :=
  fun b σ store => (matchedOccurrences rigid (a := ()) (b := b) σ (fun _ => 0) 0 store).card = 1

theorem exact_count_not_monotone : ¬SpatialGuard.Monotone countOne := by
  intro monotone
  have broken := monotone () ()
    (show ({0} : Finset Nat) ⊆ {0, 1} by simp)
    (by simp [countOne, matchedOccurrences, rigid])
  simp [countOne, matchedOccurrences, rigid] at broken

theorem positive_guard_needs_no_blindness :
    SpatialGuard.Monotone (hasMatch rigid (a := ()) (fun _ : Nat => 0) 0) ∧
      hasMatch rigid (a := ()) (fun _ : Nat => 0) 0 () () ({0} ∪ {0, 1}) := by
  refine ⟨hasMatch_monotone rigid _ _, ?_⟩
  simp [hasMatch, matchedOccurrences, rigid]

/-- Without the original count, no-new-matches does not imply an arbitrary count. -/
theorem original_count_is_needed :
    NoNewMatches rigid (a := ()) (b := ()) () id 0 ∅ ∅ ∧
      (selected (∅ ∪ ∅)).card ≠ 1 := by
  constructor
  · intro occurrence member
    exact False.elim (Finset.notMem_empty occurrence member)
  · simp

open AdmissionObservationCover.Controls (World frame)
open PreparedStep.Controls (bit no)
open Coexistence.Controls (yes)

def joint : EquationStore (World → Bool) := [(bit, yes)]

theorem joint_solvable : frame.Solvable (a := ()) joint := Controls.one_solvable

theorem joint_no_new_matches : frame.Entails (a := ()) joint
    (fun b σ => NoNewMatches frame (a := ()) (b := b) σ (fun _ : Nat => no) bit ∅ {9}) := by
  intro b σ solved occurrence _ matched
  cases b
  have first := solved (bit, yes) (by simp [joint])
  change frame.act (a := ()) (b := ()) σ bit = yes at first
  change frame.act (a := ()) (b := ()) σ bit = no at matched
  have impossible := congrFun (first.symm.trans matched) (fun _ => false)
  cases impossible

theorem not_globally_blind : ¬∀ (b : Unit) (σ : World → World),
    NoNewMatches frame (a := ()) (b := b) σ (fun _ : Nat => no) bit ∅ {9} := by
  intro blind
  have impossible := blind () (fun _ _ => false) 9 (by simp) rfl
  exact Finset.notMem_empty _ impossible

theorem count_valid_at_joint_solutions : frame.Entails (a := ()) joint
    (fun b σ => (matchedOccurrences frame (a := ()) (b := b) σ
      (fun _ : Nat => no) bit (∅ ∪ {9})).card = 0) := by
  apply (entails_count_iff frame (a := ()) (fun _ : Nat => no) bit ∅ {9} joint 0 ?_).mpr
    joint_no_new_matches
  intro b σ _
  simp [matchedOccurrences]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Coexistence.GuardControls
