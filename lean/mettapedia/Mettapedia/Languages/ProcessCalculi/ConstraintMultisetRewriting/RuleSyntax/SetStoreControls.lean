import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreLifting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.AskTimingControls

/-! # Idempotence, transport order, multiplicity and finite-closure controls -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreControls

open SetStoreClosure

theorem duplicate_production_adds_once :
    SetStore.update id ({1} : Finset ℕ) ∅ {2, 2} = {1, 2} := by decide

theorem known_production_changes_nothing :
    SetStore.update id ({1, 2} : Finset ℕ) ∅ {2} = {1, 2} := by decide

theorem remove_before_merging_retains_survivor :
    SetStore.update (fun _ : ℕ => 7) {0, 1} {0} ∅ = {7} := by decide

theorem merge_before_removing_loses_survivor :
    (({0, 1} : Finset ℕ).image (fun _ => 7)) \ ({0} : Finset ℕ).image (fun _ => 7) = ∅ := by decide

theorem a_duplicate_source_is_not_membership_removal :
    (({0, 1} : Finset ℕ) \ {0}).image (fun _ => 7) = {7} ∧
      SetStore.update id ({7} : Finset ℕ) {7} ∅ = ∅ := by decide

def pathRules : Fin 6 → Instance ℕ
  | ⟨0, _⟩ => ⟨{0}, {3}⟩
  | ⟨1, _⟩ => ⟨{1}, {4}⟩
  | ⟨2, _⟩ => ⟨{2}, {5}⟩
  | ⟨3, _⟩ => ⟨{3, 1}, {6}⟩
  | ⟨4, _⟩ => ⟨{4, 2}, {7}⟩
  | ⟨5, _⟩ => ⟨{6, 2}, {8}⟩

def edges : Finset ℕ := {0, 1, 2}
def paths : Finset ℕ := {0, 1, 2, 3, 4, 5, 6, 7, 8}

theorem paths_closed : Closed pathRules paths := by unfold Closed; decide

theorem paths_reached : Relation.ReflTransGen (SetStoreClosure.Step pathRules) edges paths := by
  have first : SetStoreClosure.Step pathRules edges {0, 1, 2, 3} := by unfold SetStoreClosure.Step; decide
  have second : SetStoreClosure.Step pathRules {0, 1, 2, 3} {0, 1, 2, 3, 4} := by unfold SetStoreClosure.Step; decide
  have third : SetStoreClosure.Step pathRules {0, 1, 2, 3, 4} {0, 1, 2, 3, 4, 5} := by unfold SetStoreClosure.Step; decide
  have fourth : SetStoreClosure.Step pathRules {0, 1, 2, 3, 4, 5} {0, 1, 2, 3, 4, 5, 6} := by unfold SetStoreClosure.Step; decide
  have fifth : SetStoreClosure.Step pathRules {0, 1, 2, 3, 4, 5, 6} {0, 1, 2, 3, 4, 5, 6, 7} := by unfold SetStoreClosure.Step; decide
  have sixth : SetStoreClosure.Step pathRules {0, 1, 2, 3, 4, 5, 6, 7} paths := by unfold SetStoreClosure.Step; decide
  exact .tail (.tail (.tail (.tail (.tail (.single first) second) third) fourth) fifth) sixth

theorem paths_are_least_closure : (paths : Set ℕ) = closure pathRules edges :=
  terminal_eq_closure pathRules edges paths_reached ((terminal_iff_closed _ _).mpr paths_closed)

theorem no_second_path_outcome {after : Finset ℕ}
    (run : Relation.ReflTransGen (SetStoreClosure.Step pathRules) edges after) (terminal : Terminal pathRules after) :
    after = paths := terminal_unique pathRules edges run terminal paths_reached ((terminal_iff_closed _ _).mpr paths_closed)

def grow (n : ℕ) : Instance ℕ := ⟨{n}, {n + 1}⟩
def growing (n : ℕ) : Finset ℕ := Finset.range (n + 1)

theorem grow_forever (n : ℕ) : SetStoreClosure.Step grow (growing n) (growing (n + 1)) := by
  refine ⟨n, ?_, ?_, ?_⟩
  · simp [grow, growing]
  · simp only [grow, growing, SetStore.update, Finset.sdiff_empty, Finset.image_id]
    rw [Finset.range_add_one]
    simp
  · intro same
    have cards := congrArg Finset.card same
    simp only [growing, Finset.card_range] at cards
    omega

theorem finite_input_does_not_supply_a_finite_closed_carrier (carrier : Finset ℕ) (seed : 0 ∈ carrier) :
    ¬ Closed grow carrier := by
  intro closed
  apply no_infinite_run grow carrier closed growing (by simpa [growing] using seed)
  exact grow_forever

section Counts

open Mettapedia.Logic.LP
open OneFrame (frames)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls (atoms)

def constantLabel (_ : ℕ) : Term atoms := .const 5

theorem same_support_different_count :
    ({0, 1} : Finset ℕ).image constantLabel = ({0} : Finset ℕ).image constantLabel ∧
      (matchesAt Examples.X (a := PUnit.unit) (b := PUnit.unit) (Subst.id atoms) constantLabel {0, 1} (.const 5)).card = 2 ∧
      (matchesAt Examples.X (a := PUnit.unit) (b := PUnit.unit) (Subst.id atoms) constantLabel {0} (.const 5)).card = 1 := by
  have whole : ∀ rows : Finset ℕ,
      matchesAt Examples.X (a := PUnit.unit) (b := PUnit.unit) (Subst.id atoms) constantLabel rows (.const 5) = rows := by
    intro rows
    classical
    apply Finset.filter_true_of_mem
    intro _ _
    rfl
  rw [whole, whole]
  constructor
  · simp [constantLabel]
  · decide

end Counts

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreControls
