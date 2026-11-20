import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.Cost
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleRace

/-! # Charged schedules for a shared-space query and insertion -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.Controls

open Elaboration Toolkit ExampleRace

private def preferred (prioritizeReads : Bool) (branch : Branch mkeys [] () MTy) : Bool :=
  match spaceRequest branch with
  | some (.query ..) => prioritizeReads
  | some (.insert ..) => !prioritizeReads
  | _ => false

private def schedule (prioritizeReads : Bool) : Strategy mkeys [] () MTy where
  chooses state branch := branch ∈ state.branches ∧
    (preferred prioritizeReads branch = true ∨ ∀ other ∈ state.branches, preferred prioritizeReads other = false)
  solverSteps _ branch := branch.store.length
  selectionVisits _ _ := 1
  spaceSteps _ request := match request with
    | .query .. => 5
    | .insert .. => 3
    | .erase .. => 4

theorem read_refused_during_insertion_priority : ¬ (schedule false).chooses C1 bQuery := by
  intro admitted
  rcases admitted.2 with contrary | noInsert
  · cases contrary
  · have refused := noInsert bAdd (by simp [C1])
    cases refused

theorem empty_query_still_charges_a_read :
    ∃ entry, ChargedStep D program supply (schedule true) C1 entry ⟨W0.fresh, bAdd ::ₘ 0⟩ ∧
      entry.request = some (.query H a) ∧ entry.alternatives = 0 ∧ entry.units = 8 := by
  let rest : Multiset (Branch mkeys [] () MTy) := bAdd ::ₘ 0
  let ordered : Config mkeys [] () MTy := ⟨W0, bQuery ::ₘ rest⟩
  let entry := charge (schedule true) ordered bQuery 0
  have reorder : C1 = ordered := by
    unfold C1 ordered rest
    rw [Multiset.cons_swap]
  have chosen : (schedule true).chooses ordered bQuery :=
    ⟨by simp [ordered], Or.inl rfl⟩
  have read : Move D program supply W0 bQuery W0.fresh 0 := by
    have moved := Move.query (D := D) (P := program) (supply := supply)
      W0 [] H a (.ret (num 2)) [] [] h0 H_determined
    simpa [W0, bQuery, queryAlt] using moved
  refine ⟨entry, ?_, rfl, rfl, rfl⟩
  rw [reorder]
  have step := ChargedStep.move (D := D) (P := program) (supply := supply)
    (strategy := schedule true) W0 W0.fresh bQuery rest 0 chosen live_nil read
  simpa only [zero_add] using step

theorem one_source_choice_charges_its_fork :
    ∃ entry, ChargedStep D program supply (schedule true) start6 entry C1 ∧
      entry.alternatives = 2 ∧ entry.choicePoints = 1 ∧ entry.request = none := by
  let branch : Branch mkeys [] () MTy := ⟨[], .eval query6, [], []⟩
  let choices : Multiset (Branch mkeys [] () MTy) := bAdd ::ₘ bQuery ::ₘ 0
  have selected : (schedule true).chooses start6 branch := by
    refine ⟨by simp [start6, Config.initial, branch], Or.inr ?_⟩
    intro alternative member
    have equal : alternative = branch := by simpa [start6, Config.initial, branch] using member
    rw [equal]
    rfl
  let entry := charge (schedule true) start6 branch choices
  refine ⟨entry, ?_, rfl, rfl, rfl⟩
  have moved := ChargedStep.move (D := D) (P := program) (supply := supply)
    (strategy := schedule true) W0 W0 branch 0 choices selected live_nil (.choice W0 [] _ _ [] [])
  simpa only [add_zero, entry, choices, C1, start6, Config.initial, branch, W0, Multiset.cons_zero] using moved

theorem unit_price_cannot_cover_arbitrarily_long_outputs (multiplier setup : Nat) :
    ¬ ∀ length : Nat, length ≤ multiplier * 1 + setup := by
  intro bounded
  have impossible := bounded (multiplier + setup + 1)
  omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.Controls
