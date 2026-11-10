import Mettapedia.Languages.Lean.Recursion.RelationFuel
import Mettapedia.Languages.Lean.Recursion.RelationalCore

/-! A natural rank for the calls in Lean's actual merge recipe. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Lean.Recursion.MergeRank

universe u
variable {α : Type u}

def rank (state : (_ : List α) ×' List α) : Nat :=
  state.1.length + state.2.length

theorem locality (le : α → α → Bool) :
    RelationFuel.Local RelationalCore.Merge.relation rank
      (RelationalCore.Merge.recipe le) := by
  intro state first second agree
  cases state with
  | mk xs ys =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      cases ys with
      | nil => rfl
      | cons y ys =>
        dsimp only [RelationalCore.Merge.recipe]
        split
        · exact congrArg (List.cons x) (agree ⟨xs, y :: ys⟩ (by simp [rank]))
        · exact congrArg (List.cons y) (agree ⟨x :: xs, ys⟩ (by simp [rank]))

/-- Zero would give no information about the calls that merge observes. -/
theorem zeroRank_rejected :
    ¬ RelationFuel.Local (@RelationalCore.Merge.relation Unit) (fun _ => 0)
      (RelationalCore.Merge.recipe (fun _ _ => true)) := by
  intro hlocality
  have equality := hlocality ⟨[()], [()]⟩ (fun _ => []) (fun _ => [()])
    (fun _ smaller => False.elim (Nat.not_lt_zero _ smaller))
  change [()] = [(), ()] at equality
  simp at equality

end Mettapedia.Languages.Lean.Recursion.MergeRank
