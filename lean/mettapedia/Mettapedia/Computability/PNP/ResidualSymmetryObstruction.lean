import Mettapedia.Computability.PNP.OrbitNeutralityObstruction
import Mathlib.Tactic

/-!
# P vs NP crux: unresolved symmetric slices stay at chance

One remaining charitable rescue is to keep a controlled amount of
involution-sensitive information.  This may break the exact symmetry on some
part of the domain while leaving other points unresolved.

This file isolates the right obstruction: every residual slice on which the
retained features are still involution-invariant remains exactly at chance under
any involution-invariant weighting.  So such a repair only helps insofar as it
proves the unresolved slice has negligible mass.
-/

namespace Mettapedia.Computability.PNP

section

variable {α U β : Type*} [Fintype α] [AddCommMonoid β]

/-- The total weight of correctly classified points. -/
def weightedCorrectMass
    (u : α → U) (y : α → Bool) (w : α → β) (h : U → Bool) : β :=
  ∑ x : {x : α // Correct u y h x}, w x.1

/-- The total weight of incorrectly classified points. -/
def weightedIncorrectMass
    (u : α → U) (y : α → Bool) (w : α → β) (h : U → Bool) : β :=
  ∑ x : {x : α // Incorrect u y h x}, w x.1

/-- Under an involution that preserves features and weights and flips the
target, the correct and incorrect weighted masses are equal. -/
theorem weightedCorrectMass_eq_weightedIncorrectMass
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → β) (h : U → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    weightedCorrectMass u y w h = weightedIncorrectMass u y w h := by
  classical
  unfold weightedCorrectMass weightedIncorrectMass
  refine Fintype.sum_equiv
    (correctEquivIncorrect τ u y h hτ hu hy)
    (fun x : {x : α // Correct u y h x} => w x.1)
    (fun x : {x : α // Incorrect u y h x} => w x.1) ?_
  intro x
  simpa [correctEquivIncorrect] using (hw x.1).symm

/-- The involution induced on a slice stable under `τ`. -/
def sliceInvolution
    (τ : α → α) (p : α → Prop)
    (hp : ∀ x, p x → p (τ x)) :
    {x : α // p x} → {x : α // p x} :=
  fun x => ⟨τ x.1, hp x.1 x.2⟩

omit [Fintype α] in
lemma sliceInvolution_involutive
    (τ : α → α) (p : α → Prop)
    (hp : ∀ x, p x → p (τ x))
    (hτ : Function.Involutive τ) :
    Function.Involutive (sliceInvolution τ p hp) := by
  intro x
  ext
  simp [sliceInvolution, hτ x.1]

/-- Therefore any residual slice on which the retained features are still
involution-invariant remains exactly balanced under involution-invariant
weights. -/
theorem weightedCorrectMass_eq_weightedIncorrectMass_on_slice
    (τ : α → α) (p : α → Prop)
    (u : α → U) (y : α → Bool) (w : α → β) (h : U → Bool)
    [DecidablePred p]
    (hτ : Function.Involutive τ)
    (hp : ∀ x, p x → p (τ x))
    (hu : ∀ x, p x → u (τ x) = u x)
    (hy : ∀ x, p x → y (τ x) = !(y x))
    (hw : ∀ x, p x → w (τ x) = w x) :
    weightedCorrectMass (fun x : {x : α // p x} => u x.1)
        (fun x : {x : α // p x} => y x.1)
        (fun x : {x : α // p x} => w x.1) h
      =
    weightedIncorrectMass (fun x : {x : α // p x} => u x.1)
        (fun x : {x : α // p x} => y x.1)
        (fun x : {x : α // p x} => w x.1) h := by
  let τp : {x : α // p x} → {x : α // p x} := sliceInvolution τ p hp
  have hτp : Function.Involutive τp := sliceInvolution_involutive τ p hp hτ
  have hu' : ∀ x : {x : α // p x}, u (τ x.1) = u x.1 := by
    intro x
    exact hu x.1 x.2
  have hy' : ∀ x : {x : α // p x}, y (τ x.1) = !(y x.1) := by
    intro x
    exact hy x.1 x.2
  have hw' : ∀ x : {x : α // p x}, w (τ x.1) = w x.1 := by
    intro x
    exact hw x.1 x.2
  simpa [τp, sliceInvolution] using
    (weightedCorrectMass_eq_weightedIncorrectMass
      (α := {x : α // p x}) (U := U) (β := β)
      τp
      (fun x : {x : α // p x} => u x.1)
      (fun x : {x : α // p x} => y x.1)
      (fun x : {x : α // p x} => w x.1)
      h hτp
      (fun x => hu' x)
      (fun x => hy' x)
      (fun x => hw' x))

end

end Mettapedia.Computability.PNP
