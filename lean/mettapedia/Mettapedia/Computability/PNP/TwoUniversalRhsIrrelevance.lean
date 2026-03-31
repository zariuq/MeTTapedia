import Mettapedia.Computability.PNP.RhsBiasIrrelevance

open scoped BigOperators

/-!
# P vs NP crux: exact 2-universality makes RHS bias irrelevant to first moments

This file packages `RhsBiasIrrelevance.lean` in hash-family language.  If the
seeded hash family is genuinely uniform on each single input and jointly uniform
on each distinct input pair, then averaging against any finite probability weight
on the right-hand side gives the same single-hit and pair-hit moments as under a
uniform right-hand side.

So once the manuscript's `A`-family is strong enough to supply exact finite
2-universality, the `δ`-biased right-hand side `b` cannot change these two
moments at all.
-/

namespace Mettapedia.Computability.PNP

section

variable {Seed Input Label : Type*} [Fintype Seed] [Fintype Label]

/-- A finite exact 2-universal family, presented as explicit single-input and
distinct-pair output uniformity. -/
structure FiniteTwoUniversalFamily where
  eval : Seed → Input → Label
  single_uniform :
    ∀ x : Input, ∃ d : Nat, 0 < d ∧ ∃ e : Seed ≃ Fin d × Label,
      ∀ s : Seed, eval s x = (e s).2
  pair_uniform :
    ∀ x y : Input, x ≠ y → ∃ d : Nat, 0 < d ∧ ∃ e : Seed ≃ Fin d × Label × Label,
      ∀ s : Seed, eval s x = (e s).2.1 ∧ eval s y = (e s).2.2

/-- Average weighted single-hit mass for one input. -/
noncomputable def weightedSingleHitAverage
    (H : FiniteTwoUniversalFamily (Seed := Seed) (Input := Input) (Label := Label))
    (w : FiniteWeight Label) (x : Input) : ℝ :=
  (∑ s : Seed, w.weight (H.eval s x)) / Fintype.card Seed

theorem weightedSingleHitAverage_eq_uniform
    (H : FiniteTwoUniversalFamily (Seed := Seed) (Input := Input) (Label := Label))
    (w : FiniteWeight Label) (x : Input) :
    weightedSingleHitAverage H w x = 1 / Fintype.card Label := by
  rcases H.single_uniform x with ⟨d, hd, e, he⟩
  exact average_mass_of_uniform_labels w e (fun s => H.eval s x) he hd

end

section

variable {Seed Input Label : Type*} [Fintype Seed] [Fintype Label] [DecidableEq Label]

/-- Average weighted joint-hit mass for a distinct input pair. -/
noncomputable def weightedPairHitAverage
    (H : FiniteTwoUniversalFamily (Seed := Seed) (Input := Input) (Label := Label))
    (w : FiniteWeight Label) (x y : Input) : ℝ :=
  (∑ s : Seed, (if H.eval s x = H.eval s y then w.weight (H.eval s x) else 0)) / Fintype.card Seed

theorem weightedPairHitAverage_eq_uniform
    (H : FiniteTwoUniversalFamily (Seed := Seed) (Input := Input) (Label := Label))
    (w : FiniteWeight Label) (x y : Input) (hxy : x ≠ y) :
    weightedPairHitAverage H w x y = 1 / (Fintype.card Label * Fintype.card Label) := by
  rcases H.pair_uniform x y hxy with ⟨d, hd, e, he⟩
  refine average_joint_mass_of_uniform_label_pairs w e
    (fun s => H.eval s x) (fun s => H.eval s y) ?_ ?_ hd
  · intro s
    exact (he s).1
  · intro s
    exact (he s).2

end

end Mettapedia.Computability.PNP
