import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# P vs NP crux: feature-preserving involutions force exact `1/2` accuracy

This file abstracts a recurring obstruction pattern in the current proof attempt.

Suppose a finite sample space carries an involution `τ` such that:

* the candidate feature map `u` is invariant under `τ`, and
* the target bit `y` is flipped by `τ`.

Then any classifier depending only on `u` has exactly `1/2` average accuracy.  In particular,
any proposed feature-collapse theorem that removes the component changed by the involution
cannot support a domination argument.
-/

namespace Mettapedia.Computability.PNP

section

variable {α U : Type*}

/-- A point `x` is correctly classified by the feature-only classifier `h ∘ u`. -/
def Correct (u : α → U) (y : α → Bool) (h : U → Bool) (x : α) : Prop :=
  h (u x) = y x

/-- A point `x` is incorrectly classified by the feature-only classifier `h ∘ u`. -/
def Incorrect (u : α → U) (y : α → Bool) (h : U → Bool) (x : α) : Prop :=
  h (u x) ≠ y x

instance decidableCorrect (u : α → U) (y : α → Bool) (h : U → Bool) :
    DecidablePred (Correct u y h) := by
  intro x
  unfold Correct
  infer_instance

instance decidableIncorrect (u : α → U) (y : α → Bool) (h : U → Bool) :
    DecidablePred (Incorrect u y h) := by
  intro x
  unfold Incorrect
  infer_instance

lemma incorrect_iff_not_correct (u : α → U) (y : α → Bool) (h : U → Bool) (x : α) :
    Incorrect u y h x ↔ ¬ Correct u y h x := by
  rfl

lemma correct_under_pair_iff_incorrect
    (τ : α → α) (u : α → U) (y : α → Bool) (h : U → Bool)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (x : α) :
    Correct u y h x ↔ Incorrect u y h (τ x) := by
  unfold Correct Incorrect
  constructor
  · intro hx
    simp [hu x, hy x, hx]
  · intro hx
    have hx' : h (u x) ≠ !(y x) := by simpa [hu x, hy x] using hx
    by_cases hpred : h (u x) = y x
    · exact hpred
    · cases hyx : y x
      · simp [hyx] at hpred hx' ⊢
        exact hx'
      · simp [hyx] at hpred hx' ⊢
        exact hx'

def correctEquivIncorrect
    (τ : α → α) (u : α → U) (y : α → Bool) (h : U → Bool)
    [Fintype α]
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x)) :
    {x : α // Correct u y h x} ≃ {x : α // Incorrect u y h x} where
  toFun x := ⟨τ x.1, (correct_under_pair_iff_incorrect τ u y h hu hy x.1).1 x.2⟩
  invFun x := ⟨τ x.1, by
    have hxτ : Incorrect u y h (τ (τ x.1)) := by simpa [hτ x.1] using x.2
    exact (correct_under_pair_iff_incorrect τ u y h hu hy (τ x.1)).2 hxτ⟩
  left_inv x := by
    simp [hτ x.1]
  right_inv x := by
    simp [hτ x.1]

theorem card_correct_eq_card_incorrect
    (τ : α → α) (u : α → U) (y : α → Bool) (h : U → Bool)
    [Fintype α]
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x)) :
    Fintype.card {x : α // Correct u y h x} =
      Fintype.card {x : α // Incorrect u y h x} :=
by
  classical
  exact Fintype.card_congr (correctEquivIncorrect τ u y h hτ hu hy)

theorem two_mul_card_correct_eq_card
    (τ : α → α) (u : α → U) (y : α → Bool) (h : U → Bool)
    [Fintype α]
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x)) :
    2 * Fintype.card {x : α // Correct u y h x} = Fintype.card α := by
  classical
  set a : ℕ := Fintype.card {x : α // Correct u y h x}
  have hcomp :
      Fintype.card {x : α // Incorrect u y h x} = Fintype.card α - a := by
    simpa [a, incorrect_iff_not_correct] using
      (Fintype.card_subtype_compl fun x : α => Correct u y h x)
  have heq : a = Fintype.card {x : α // Incorrect u y h x} := by
    simpa [a] using card_correct_eq_card_incorrect τ u y h hτ hu hy
  have hsub : Fintype.card α - a = a := by
    simpa [heq] using hcomp.symm
  have hle : a ≤ Fintype.card α := by
    simpa [a] using Fintype.card_subtype_le (fun x : α => Correct u y h x)
  have hsum : Fintype.card α = a + a := Nat.eq_add_of_sub_eq hle hsub
  simpa [a, two_mul, Nat.add_comm] using hsum.symm

end

end Mettapedia.Computability.PNP
