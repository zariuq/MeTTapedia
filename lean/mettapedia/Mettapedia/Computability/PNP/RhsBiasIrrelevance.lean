import Mathlib

open scoped BigOperators

/-!
# P vs NP crux: RHS bias is irrelevant once the hash labels are uniform

This file isolates the exact kernel needed for the `δ`-biased VV right-hand side.
If the label map for a candidate is uniform over the hash-label space, then the
average hit mass against any finite probability weight on labels is exactly the
uniform value. Likewise, if the pair of labels for two candidates is jointly
uniform, then the average joint-hit mass is exactly the uniform diagonal value.

So any real effect of a `δ`-biased right-hand side must come from failure of the
underlying label maps to be genuinely uniform, not from the bias itself.
-/

namespace Mettapedia.Computability.PNP

structure FiniteWeight (β : Type*) [Fintype β] where
  weight : β → ℝ
  nonneg : ∀ b, 0 ≤ weight b
  sum_eq_one : ∑ b, weight b = 1

theorem FiniteWeight.nonempty {β : Type*} [Fintype β] (w : FiniteWeight β) : Nonempty β := by
  by_contra h
  have hsum0 : (∑ b : β, w.weight b) = 0 := by
    simp [not_nonempty_iff.mp h]
  linarith [w.sum_eq_one, hsum0]

theorem FiniteWeight.card_pos {β : Type*} [Fintype β] (w : FiniteWeight β) :
    0 < Fintype.card β := by
  letI : Nonempty β := w.nonempty
  exact Fintype.card_pos_iff.mpr inferInstance

private theorem diagonal_weight_sum {Label : Type*} [Fintype Label] [DecidableEq Label]
    (w : Label → ℝ) (b : Label) :
    ∑ c : Label, (if b = c then w b else 0) = w b := by
  have h := Finset.sum_ite_eq (s := Finset.univ) (a := b) (b := fun _ : Label => w b)
  simp only [Finset.mem_univ, ↓reduceIte] at h
  exact h

section

variable {Seed Label : Type*} [Fintype Seed] [Fintype Label]

theorem weighted_mass_of_uniform_labels
    (w : FiniteWeight Label)
    {d : Nat}
    (e : Seed ≃ Fin d × Label)
    (f : Seed → Label)
    (hf : ∀ s, f s = (e s).2) :
    ∑ s : Seed, w.weight (f s) = d := by
  calc
    ∑ s : Seed, w.weight (f s)
      = ∑ p : Fin d × Label, w.weight p.2 := by
          refine Fintype.sum_equiv e _ _ ?_
          intro s
          rw [hf s]
    _ = ∑ i : Fin d, ∑ b : Label, w.weight b := by
          rw [Fintype.sum_prod_type]
    _ = ∑ _i : Fin d, (1 : ℝ) := by
          simp [w.sum_eq_one]
    _ = d := by
          simp

theorem average_mass_of_uniform_labels
    (w : FiniteWeight Label)
    {d : Nat}
    (e : Seed ≃ Fin d × Label)
    (f : Seed → Label)
    (hf : ∀ s, f s = (e s).2)
    (hd : 0 < d) :
    (∑ s : Seed, w.weight (f s)) / Fintype.card Seed = 1 / Fintype.card Label := by
  have hsum := weighted_mass_of_uniform_labels w e f hf
  have hcard : Fintype.card Seed = d * Fintype.card Label := by
    rw [Fintype.card_congr e]
    simp
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hd
  have hLabel0 : (Fintype.card Label : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt w.card_pos
  rw [hsum, hcard]
  rw [Nat.cast_mul]
  field_simp [hd0, hLabel0]

end

section

variable {Seed Label : Type*} [Fintype Seed] [Fintype Label] [DecidableEq Label]

theorem weighted_joint_mass_of_uniform_label_pairs
    (w : FiniteWeight Label)
    {d : Nat}
    (e : Seed ≃ Fin d × Label × Label)
    (f g : Seed → Label)
    (hf : ∀ s, f s = (e s).2.1)
    (hg : ∀ s, g s = (e s).2.2) :
    ∑ s : Seed, (if f s = g s then w.weight (f s) else 0) = d := by
  calc
    ∑ s : Seed, (if f s = g s then w.weight (f s) else 0)
      = ∑ p : Fin d × Label × Label,
          (if p.2.1 = p.2.2 then w.weight p.2.1 else 0) := by
            refine Fintype.sum_equiv e _ _ ?_
            intro s
            rw [hf s, hg s]
      _ = ∑ i : Fin d, ∑ p : Label × Label,
          (if p.1 = p.2 then w.weight p.1 else 0) := by
            rw [Fintype.sum_prod_type]
      _ = ∑ i : Fin d, ∑ b : Label, w.weight b := by
            refine Fintype.sum_congr
              (fun _i : Fin d => ∑ p : Label × Label, (if p.1 = p.2 then w.weight p.1 else 0))
              (fun _i : Fin d => ∑ b : Label, w.weight b) ?_
            intro i
            rw [Fintype.sum_prod_type]
            refine Fintype.sum_congr
              (fun b : Label => ∑ c : Label, (if b = c then w.weight b else 0))
              (fun b : Label => w.weight b) ?_
            intro b
            exact diagonal_weight_sum w.weight b
      _ = ∑ _i : Fin d, (1 : ℝ) := by
            simp [w.sum_eq_one]
      _ = d := by
            simp

theorem average_joint_mass_of_uniform_label_pairs
    (w : FiniteWeight Label)
    {d : Nat}
    (e : Seed ≃ Fin d × Label × Label)
    (f g : Seed → Label)
    (hf : ∀ s, f s = (e s).2.1)
    (hg : ∀ s, g s = (e s).2.2)
    (hd : 0 < d) :
    (∑ s : Seed, (if f s = g s then w.weight (f s) else 0)) / Fintype.card Seed
      = 1 / (Fintype.card Label * Fintype.card Label) := by
  have hsum := weighted_joint_mass_of_uniform_label_pairs w e f g hf hg
  have hcard : Fintype.card Seed = d * Fintype.card Label * Fintype.card Label := by
    rw [Fintype.card_congr e]
    simp [Nat.mul_assoc]
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hd
  have hLabel0 : (Fintype.card Label : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt w.card_pos
  rw [hsum, hcard]
  repeat rw [Nat.cast_mul]
  field_simp [hd0, hLabel0]

end

end Mettapedia.Computability.PNP
