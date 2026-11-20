import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep
import Mettapedia.GSLT.Core.SpeculativePromotion

/-!
# Controls for the step's predicate queries

A check `Check.predicate q p` asks the quantifier `q` of the present rows its pattern matches.
These controls pin down how the two quantifiers react to a write, and that only the positive one
may take the take-only fast path:

* `any` survives every insertion, in particular one that matches nothing (`any_survives_insertion`,
  `any_survives_unrelated_insertion`);
* `none` survives an insertion that matches nothing (`none_survives_unmatched_insertion`) and is
  invalidated by one that matches (`none_invalidated_by_matching_insertion`);
* the fast path's precondition, stability under growth, holds for a positive `exists` guard and fails
  for the `none` guard (`none_guard_not_growthStable`), so a `none` guard is re-checked at the commit.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PredicateQueryControls

open Mettapedia.GSLT.Core.RegionQueries
open Mettapedia.GSLT.Core.SpeculativePromotion

/-! ## General laws -/

section Laws

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO}

/-- **`any` survives every insertion.** -/
theorem any_survives_insertion (A : SubstitutionAction T S) (σ : S) (label : O → T)
    {world world' : Finset O} (grows : world ⊆ world') (pattern : T)
    (holds : (Check.predicate .any pattern).Holds A σ label world) :
    (Check.predicate .any pattern).Holds A σ label world' :=
  Quantifier.holds_any_mono grows holds

/-- **`none` survives every deletion.** -/
theorem none_survives_deletion (A : SubstitutionAction T S) (σ : S) (label : O → T)
    {world world' : Finset O} (shrinks : world ⊆ world') (pattern : T)
    (holds : (Check.predicate .none pattern).Holds A σ label world') :
    (Check.predicate .none pattern).Holds A σ label world :=
  Quantifier.holds_none_anti shrinks holds

/-- **`none` survives an insertion that matches nothing.** -/
theorem none_survives_unmatched_insertion [DecidableEq O] (A : SubstitutionAction T S) (σ : S)
    (label : O → T) (world added : Finset O) (pattern : T)
    (unmatched : ∀ o ∈ added, ¬ A.E (A.apply σ pattern) (A.apply σ (label o)))
    (holds : (Check.predicate .none pattern).Holds A σ label world) :
    (Check.predicate .none pattern).Holds A σ label (world ∪ added) := by
  intro o member
  rcases Finset.mem_union.mp member with old | new
  · exact holds o old
  · exact unmatched o new

end Laws

/-! ## Concrete rows -/

/-- Natural-number rows compared by equality; the solution does nothing. -/
def rows : SubstitutionAction ℕ Unit where
  E := Eq
  equivalence := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
  apply _ t := t
  identity := ()
  compose _ _ := ()
  apply_identity _ := rfl
  apply_compose _ _ _ := rfl
  preserves _ _ _ same := same

/-- Each row is labelled by its own number. -/
def label : ℕ → ℕ := id

/-- **`any` survives an insertion that matches nothing**: row 5 is present; row 9 is added. -/
theorem any_survives_unrelated_insertion :
    (Check.predicate .any 5).Holds rows () label {5, 7} ∧
      (Check.predicate .any 5).Holds rows () label {5, 7, 9} :=
  ⟨⟨5, by simp, rfl⟩, ⟨5, by simp, rfl⟩⟩

/-- **`none` is invalidated by a matching insertion**: no row 5 before; row 5 is added. -/
theorem none_invalidated_by_matching_insertion :
    (Check.predicate .none 5).Holds rows () label {7} ∧
      ¬ (Check.predicate .none 5).Holds rows () label {5, 7} := by
  refine ⟨?_, fun holds => holds 5 (by simp) rfl⟩
  intro o member same
  simp only [Finset.mem_singleton] at member
  subst member
  simp [rows, label] at same

/-! ## The take-only fast path -/

/-- The `none` guard of a pattern as a guard of the promotion model. -/
def noneGuard : Guard ℕ := fun store pattern => noneQuery (fun row => decide (row = pattern)) store

/-- The `any` guard of a pattern as a guard of the promotion model. -/
def anyGuard : Guard ℕ := fun store pattern => existsQuery (fun row => decide (row = pattern)) store

/-- **The positive guard may take the fast path.** -/
theorem anyGuard_growthStable : GrowthStable anyGuard :=
  growthStable_existsQuery fun pattern row => decide (row = pattern)

/-- **The `none` guard may not**: it holds at the empty store and fails once the matching row is
added, so take-only validation would commit a firing the atomic step refuses. -/
theorem none_guard_not_growthStable : ¬ GrowthStable noneGuard := by
  intro stable
  have grown := stable 0 {5} 5 (Multiset.zero_subset _) (by decide)
  exact absurd grown (by decide)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PredicateQueryControls
