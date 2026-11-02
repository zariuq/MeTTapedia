import Mettapedia.Algebra.Order.FixedPointIteration
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Explicit stabilization bounds for finite state sets

A monotone set operator started at bottom or top is stable after at most
the number of states strict changes. One additional equality test detects
that stabilization. The bound counts set iterations, not the cost of the
operator, a symbolic representation or a source evaluator instruction.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Order.FiniteSetIteration

open FixedPointIteration

variable {State : Type} [Fintype State]

theorem bottom_stable_or_card (operator : Set State →o Set State) (n : Nat) :
    iterateFrom operator ⊥ (n + 1) = iterateFrom operator ⊥ n ∨
      n ≤ (iterateFrom operator ⊥ n).toFinite.toFinset.card := by
  classical
  induction n with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ n ih =>
      by_cases stable : iterateFrom operator ⊥ (n + 1) = iterateFrom operator ⊥ n
      · exact Or.inl (congrArg operator stable)
      · have count := ih.resolve_left stable
        have included := iterateFrom_mono operator ⊥ bot_le (Nat.le_succ n)
        have strict : (iterateFrom operator ⊥ n).toFinite.toFinset ⊂
            (iterateFrom operator ⊥ (n + 1)).toFinite.toFinset := by
          apply Finset.ssubset_iff_subset_ne.mpr
          refine ⟨?_, ?_⟩
          · intro state member
            simpa only [Set.Finite.mem_toFinset] using included (by simpa using member)
          · intro same
            apply stable
            exact (Set.Finite.toFinset_inj.mp same).symm
        exact Or.inr (Nat.lt_of_le_of_lt count (Finset.card_lt_card strict))

theorem bottom_stable_at_card (operator : Set State →o Set State) :
    iterateFrom operator ⊥ (Fintype.card State + 1) = iterateFrom operator ⊥ (Fintype.card State) := by
  classical
  by_contra unstable
  have count := (bottom_stable_or_card operator (Fintype.card State)).resolve_left unstable
  have full : iterateFrom operator ⊥ (Fintype.card State) = Set.univ := by
    apply Set.Finite.toFinset_eq_univ.mp
    exact Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) count)
  have included := iterateFrom_mono operator ⊥ bot_le (Nat.le_succ (Fintype.card State))
  apply unstable
  rw [full] at included ⊢
  exact Set.eq_univ_of_univ_subset included

theorem bottom_at_card_is_lfp (operator : Set State →o Set State) :
    iterateFrom operator ⊥ (Fintype.card State) = operator.lfp :=
  stable_bottom_is_lfp operator _ (bottom_stable_at_card operator)

/-- Complement conjugates descending iteration to ascending iteration. -/
def complementOperator (operator : Set State →o Set State) : Set State →o Set State where
  toFun set := (operator setᶜ)ᶜ
  monotone' _ _ included := Set.compl_subset_compl.mpr
    (operator.monotone (Set.compl_subset_compl.mpr included))

omit [Fintype State] in
theorem complement_iteration (operator : Set State →o Set State) (n : Nat) :
    iterateFrom (complementOperator operator) ⊥ n = (iterateFrom operator ⊤ n)ᶜ := by
  induction n with
  | zero => change (∅ : Set State) = Set.univᶜ; simp
  | succ n ih =>
      change (operator (iterateFrom (complementOperator operator) ⊥ n)ᶜ)ᶜ =
        (operator (iterateFrom operator ⊤ n))ᶜ
      rw [ih, compl_compl]

theorem top_stable_at_card (operator : Set State →o Set State) :
    iterateFrom operator ⊤ (Fintype.card State + 1) = iterateFrom operator ⊤ (Fintype.card State) := by
  have stable := bottom_stable_at_card (complementOperator operator)
  rw [complement_iteration, complement_iteration] at stable
  exact compl_injective stable

theorem top_at_card_is_gfp (operator : Set State →o Set State) :
    iterateFrom operator ⊤ (Fintype.card State) = operator.gfp :=
  stable_top_is_gfp operator _ (top_stable_at_card operator)

namespace Controls

def grow : Set (Fin 3) →o Set (Fin 3) where
  toFun set := {state | state = 0 ∨ ∃ prior ∈ set, prior.val + 1 = state.val}
  monotone' _ _ included _ member := by
    rcases member with base | ⟨prior, present, next⟩
    · exact Or.inl base
    · exact Or.inr ⟨prior, included present, next⟩

theorem fewer_than_three_changes_is_insufficient :
    (2 : Fin 3) ∉ iterateFrom grow ⊥ 2 ∧ (2 : Fin 3) ∈ iterateFrom grow ⊥ 3 := by
  change ¬((2 : Fin 3) = 0 ∨ ∃ p : Fin 3, (p = 0 ∨ ∃ q : Fin 3, False ∧ q.val + 1 = p.val) ∧ p.val + 1 = 2) ∧
    ((2 : Fin 3) = 0 ∨ ∃ p : Fin 3,
      (p = 0 ∨ ∃ q : Fin 3, (q = 0 ∨ ∃ r : Fin 3, False ∧ r.val + 1 = q.val) ∧ q.val + 1 = p.val) ∧ p.val + 1 = 2)
  decide

theorem final_check_follows_last_change :
    iterateFrom grow ⊥ 3 ≠ iterateFrom grow ⊥ 2 ∧ iterateFrom grow ⊥ 4 = iterateFrom grow ⊥ 3 := by
  constructor
  · intro same
    exact fewer_than_three_changes_is_insufficient.1 (same ▸ fewer_than_three_changes_is_insufficient.2)
  · exact bottom_stable_at_card grow

end Controls

end Mettapedia.Algebra.Order.FiniteSetIteration
