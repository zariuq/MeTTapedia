import Mathlib

open scoped BigOperators

/-!
# P vs NP crux: conditioning can destroy a perfectly uniform label map

This file records the simplest exact countermodel to any naive transfer from
pre-conditioning label uniformity to post-conditioning label uniformity.  Start
with the canonical uniform label map on `Fin d × Label`, namely projection to the
second coordinate.  If one conditions on a single label fiber, the conditional
distribution collapses to a point mass on that label.

So even perfect pre-conditioning uniformity says nothing by itself about the
distribution after conditioning on an event such as uniqueness.
-/

namespace Mettapedia.Computability.PNP

section

variable {Label : Type*} [Fintype Label] [DecidableEq Label]

/-- The fiber over `b` for the canonical uniform label map `(i,ℓ) ↦ ℓ`. -/
def canonicalLabelFiber (d : Nat) (b : Label) := { p : Fin d × Label // p.2 = b }

noncomputable instance canonicalLabelFiberFintype (d : Nat) (b : Label) :
    Fintype (canonicalLabelFiber d b) := by
  classical
  dsimp [canonicalLabelFiber]
  infer_instance

noncomputable def canonicalLabelFiberEquiv (d : Nat) (b : Label) :
    canonicalLabelFiber d b ≃ Fin d where
  toFun s := s.1.1
  invFun i := ⟨(i, b), rfl⟩
  left_inv s := by
    cases s with
    | mk p hp =>
        cases p with
        | mk i ℓ =>
            simp at hp
            simp [hp]
  right_inv i := by
    simp

theorem card_canonicalLabelFiber (d : Nat) (b : Label) :
    Fintype.card (canonicalLabelFiber d b) = d := by
  simpa using (Fintype.card_congr (canonicalLabelFiberEquiv d b))

theorem conditioned_target_indicator_average_eq_one
    {d : Nat} (hd : 0 < d) (b : Label) :
    (∑ s : canonicalLabelFiber d b, (if s.1.2 = b then (1 : ℝ) else 0))
      / Fintype.card (canonicalLabelFiber d b) = 1 := by
  have hcard : Fintype.card (canonicalLabelFiber d b) = d := card_canonicalLabelFiber d b
  have hd0 : (Fintype.card (canonicalLabelFiber d b) : ℝ) ≠ 0 := by
    rw [hcard]
    exact_mod_cast Nat.ne_of_gt hd
  have hsum :
      ∑ s : canonicalLabelFiber d b, (if s.1.2 = b then (1 : ℝ) else 0)
        = Fintype.card (canonicalLabelFiber d b) := by
    calc
      ∑ s : canonicalLabelFiber d b, (if s.1.2 = b then (1 : ℝ) else 0)
        = ∑ _s : canonicalLabelFiber d b, (1 : ℝ) := by
            refine Fintype.sum_congr
              (fun s : canonicalLabelFiber d b => (if s.1.2 = b then (1 : ℝ) else 0))
              (fun _s : canonicalLabelFiber d b => (1 : ℝ)) ?_
            intro s
            simp [s.2]
      _ = Fintype.card (canonicalLabelFiber d b) := by simp
  rw [hsum, hcard]
  field_simp [hd0]

theorem conditioned_other_indicator_average_eq_zero
    {d : Nat} {b c : Label} (hbc : c ≠ b) :
    (∑ s : canonicalLabelFiber d b, (if s.1.2 = c then (1 : ℝ) else 0))
      / Fintype.card (canonicalLabelFiber d b) = 0 := by
  have hcard : Fintype.card (canonicalLabelFiber d b) = d := card_canonicalLabelFiber d b
  have hsum :
      ∑ s : canonicalLabelFiber d b, (if s.1.2 = c then (1 : ℝ) else 0) = (0 : ℝ) := by
    calc
      ∑ s : canonicalLabelFiber d b, (if s.1.2 = c then (1 : ℝ) else 0)
        = ∑ _s : canonicalLabelFiber d b, (0 : ℝ) := by
            refine Fintype.sum_congr
              (fun s : canonicalLabelFiber d b => (if s.1.2 = c then (1 : ℝ) else 0))
              (fun _s : canonicalLabelFiber d b => (0 : ℝ)) ?_
            intro s
            have hs : s.1.2 ≠ c := by
              intro h
              apply hbc
              calc
                c = s.1.2 := h.symm
                _ = b := s.2
            simp [hs]
      _ = (0 : ℝ) := by simp
  rw [hsum, hcard]
  simp

end

end Mettapedia.Computability.PNP
