import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Inference
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Shore–Johnson expected-value constraint language (discrete)

This file defines a Lean-friendly expected-value constraint language for finite distributions,
matching the constraint style used in Shore–Johnson's discrete theorem.

The goal is to make subset-independence statements concrete: constraints supported on a block
become linear constraints on the combined distribution once the block mass is fixed.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Constraints

open Classical
open Finset
open scoped BigOperators

open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Inference
open Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropy

/-! ## Expected-value constraints -/

/-- A single affine constraint on a finite distribution: `∑ q_i * coeff_i = rhs`. -/
structure EVConstraint (n : ℕ) where
  coeff : Fin n → ℝ
  rhs : ℝ

/-- A distribution satisfies an expected-value constraint. -/
def satisfies {n : ℕ} (c : EVConstraint n) (q : ProbDist n) : Prop :=
  (∑ i : Fin n, q.p i * c.coeff i) = c.rhs

namespace EVConstraint

variable {n : ℕ}

/-! ### Permutation action -/

/-- Permute a constraint by relabeling coefficients. -/
def permute (σ : Equiv.Perm (Fin n)) (c : EVConstraint n) : EVConstraint n :=
  { coeff := fun i => c.coeff (σ⁻¹ i), rhs := c.rhs }

theorem satisfies_permute (σ : Equiv.Perm (Fin n)) (c : EVConstraint n) (q : ProbDist n) :
    satisfies (permute σ c) (ProbDist.permute σ q) ↔ satisfies c q := by
  classical
  dsimp [satisfies, permute, ProbDist.permute]
  -- Reindex the sum using the permutation.
  have hsum :
      (∑ i : Fin n, q.p (σ⁻¹ i) * c.coeff (σ⁻¹ i)) =
        ∑ i : Fin n, q.p i * c.coeff i := by
    simpa using (Equiv.sum_comp (σ⁻¹) (fun i : Fin n => q.p i * c.coeff i))
  simp [hsum]

end EVConstraint

/-- A finite list of expected-value constraints. -/
abbrev EVConstraintSet (n : ℕ) := List (EVConstraint n)

/-- A distribution satisfies every constraint in a list. -/
def satisfiesSet {n : ℕ} (cs : EVConstraintSet n) (q : ProbDist n) : Prop :=
  ∀ c ∈ cs, satisfies c q

namespace EVConstraintSet

variable {n : ℕ}

/-- Permute a list of constraints by relabeling coefficients. -/
def permute (σ : Equiv.Perm (Fin n)) (cs : EVConstraintSet n) : EVConstraintSet n :=
  cs.map (EVConstraint.permute σ)

theorem satisfiesSet_permute (σ : Equiv.Perm (Fin n)) (cs : EVConstraintSet n) (q : ProbDist n) :
    satisfiesSet (permute σ cs) (ProbDist.permute σ q) ↔ satisfiesSet cs q := by
  classical
  constructor
  · intro h c hc
    have h' := h (EVConstraint.permute σ c)
      (by simpa [permute] using List.mem_map.mpr ⟨c, hc, rfl⟩)
    exact (EVConstraint.satisfies_permute σ c q).1 h'
  · intro h c hc
    rcases List.mem_map.mp hc with ⟨c', hc', rfl⟩
    have h' := h c' hc'
    exact (EVConstraint.satisfies_permute σ c' q).2 h'

end EVConstraintSet

/-- Interpret a list of expected-value constraints as a constraint set. -/
def toConstraintSet {n : ℕ} (cs : EVConstraintSet n) : ConstraintSet n :=
  {q | satisfiesSet cs q}

theorem mem_toConstraintSet {n : ℕ} (cs : EVConstraintSet n) (q : ProbDist n) :
    q ∈ toConstraintSet cs ↔ satisfiesSet cs q := Iff.rfl

theorem toConstraintSet_permute {n : ℕ} (σ : Equiv.Perm (Fin n)) (cs : EVConstraintSet n) :
    ConstraintSet.permute σ (toConstraintSet cs) =
      toConstraintSet (EVConstraintSet.permute σ⁻¹ cs) := by
  ext q
  constructor
  · intro hq
    have hq' : satisfiesSet cs (ProbDist.permute σ q) := hq
    have hperm : ProbDist.permute σ⁻¹ (ProbDist.permute σ q) = q := by
      ext i
      simp [ProbDist.permute]
    have hq'' :
        satisfiesSet (EVConstraintSet.permute σ⁻¹ cs)
          (ProbDist.permute σ⁻¹ (ProbDist.permute σ q)) :=
      (EVConstraintSet.satisfiesSet_permute (σ := σ⁻¹) cs (ProbDist.permute σ q)).2 hq'
    simpa [hperm] using hq''
  · intro hq
    have hperm : ProbDist.permute σ⁻¹ (ProbDist.permute σ q) = q := by
      ext i
      simp [ProbDist.permute]
    have hq' :
        satisfiesSet (EVConstraintSet.permute σ⁻¹ cs)
          (ProbDist.permute σ⁻¹ (ProbDist.permute σ q)) := by
      simpa [hperm] using hq
    exact (EVConstraintSet.satisfiesSet_permute (σ := σ⁻¹) cs (ProbDist.permute σ q)).1 hq'

/-! ## Block-mass constraints -/

/-- The coefficient function of a subset indicator. -/
def indicatorCoeff {n : ℕ} (s : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ s then 1 else 0

/-- The constraint `∑_{i∈s} q_i = r`. -/
def blockMassConstraint {n : ℕ} (s : Finset (Fin n)) (r : ℝ) : EVConstraint n :=
  { coeff := indicatorCoeff s, rhs := r }

theorem satisfies_blockMassConstraint {n : ℕ} (s : Finset (Fin n)) (r : ℝ) (q : ProbDist n) :
    satisfies (blockMassConstraint s r) q ↔ (Finset.sum s fun i => q.p i) = r := by
  classical
  dsimp [satisfies, blockMassConstraint, indicatorCoeff]
  -- Turn the indicator-weighted sum over `univ` into a sum over `s`.
  have :
      (∑ i : Fin n, q.p i * (if i ∈ s then (1 : ℝ) else 0)) =
        Finset.sum s (fun i => q.p i) := by
    calc
      (∑ i : Fin n, q.p i * (if i ∈ s then (1 : ℝ) else 0))
          = ∑ i : Fin n, (if i ∈ s then q.p i else 0) := by
              refine sum_congr rfl ?_
              intro i _
              by_cases hi : i ∈ s <;> simp [hi]
      _ = Finset.sum s (fun i => q.p i) := by
            -- Rewrite using `sum_filter` on `univ`.
            have hsum :=
              (Finset.sum_filter (s := (Finset.univ : Finset (Fin n)))
                (f := fun i : Fin n => q.p i) (p := fun i : Fin n => i ∈ s))
            have hfilter : (Finset.univ.filter fun i : Fin n => i ∈ s) = s := by
              ext i
              simp
            calc
              (∑ i : Fin n, (if i ∈ s then q.p i else 0))
                  = Finset.sum (Finset.univ : Finset (Fin n))
                      (fun i : Fin n => if i ∈ s then q.p i else 0) := by simp
              _ = Finset.sum (Finset.univ.filter (fun i : Fin n => i ∈ s))
                    (fun i : Fin n => q.p i) := by
                    simp [hsum.symm]
              _ = Finset.sum s (fun i => q.p i) := by
                    simp [hfilter]
  simp

/-! ## Two-block lift of constraints -/

section TwoBlock

variable {n m : ℕ}

/-- The left-block inclusion `Fin n → Fin (n+m)` from the `Fin n ⊕ Fin m ≃ Fin (n+m)` equivalence. -/
def inlFin (i : Fin n) : Fin (n + m) :=
  (finSumFinEquiv (m := n) (n := m)) (Sum.inl i)

/-- The right-block inclusion `Fin m → Fin (n+m)` from the `Fin n ⊕ Fin m ≃ Fin (n+m)` equivalence. -/
def inrFin (i : Fin m) : Fin (n + m) :=
  (finSumFinEquiv (m := n) (n := m)) (Sum.inr i)

theorem inlFin_eq_inlFin {i j : Fin n} :
    inlFin (n := n) (m := m) i = inlFin (n := n) (m := m) j ↔ i = j := by
  constructor
  · intro h
    have h' :=
      congrArg (fun x => (finSumFinEquiv (m := n) (n := m)).symm x) h
    simpa [inlFin] using h'
  · intro h
    simp [inlFin, h]

theorem inrFin_eq_inrFin {i j : Fin m} :
    inrFin (n := n) (m := m) i = inrFin (n := n) (m := m) j ↔ i = j := by
  constructor
  · intro h
    have h' :=
      congrArg (fun x => (finSumFinEquiv (m := n) (n := m)).symm x) h
    simpa [inrFin] using h'
  · intro h
    simp [inrFin, h]

theorem inlFin_ne_inrFin (i : Fin n) (j : Fin m) :
    inlFin (n := n) (m := m) i ≠ inrFin (n := n) (m := m) j := by
  intro h
  have h' :=
    congrArg (fun x => (finSumFinEquiv (m := n) (n := m)).symm x) h
  have h'' := h'
  simp [inlFin, inrFin] at h''

theorem twoBlock_apply_inl (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (P₁ : ProbDist n) (P₂ : ProbDist m) (i : Fin n) :
    (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂).p
        (inlFin (n := n) (m := m) i) = w * P₁.p i := by
  simp [ProbDist.twoBlock, inlFin]

theorem twoBlock_apply_inr (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (P₁ : ProbDist n) (P₂ : ProbDist m) (i : Fin m) :
    (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂).p
        (inrFin (n := n) (m := m) i) = (1 - w) * P₂.p i := by
  simp [ProbDist.twoBlock, inrFin]

/-- Lift coefficients from the left block into `Fin (n+m)`, zero on the right. -/
def liftLeft (coeff : Fin n → ℝ) : Fin (n + m) → ℝ :=
  fun i =>
    match (finSumFinEquiv (m := n) (n := m)).symm i with
    | Sum.inl i₁ => coeff i₁
    | Sum.inr _ => 0

/-- Lift coefficients from the right block into `Fin (n+m)`, zero on the left. -/
def liftRight (coeff : Fin m → ℝ) : Fin (n + m) → ℝ :=
  fun i =>
    match (finSumFinEquiv (m := n) (n := m)).symm i with
    | Sum.inl _ => 0
    | Sum.inr i₂ => coeff i₂

theorem sum_liftLeft
    (Q : ProbDist (n + m)) (coeff : Fin n → ℝ) :
    (∑ i : Fin (n + m), Q.p i * liftLeft (n := n) (m := m) coeff i)
      = ∑ i : Fin n, Q.p (inlFin (n := n) (m := m) i) * coeff i := by
  classical
  -- Reindex by `Fin n ⊕ Fin m`.
  let e : Fin (n + m) ≃ Fin n ⊕ Fin m := (finSumFinEquiv (m := n) (n := m)).symm
  let g : Fin n ⊕ Fin m → ℝ := fun s =>
    match s with
    | Sum.inl i₁ => Q.p (e.symm (Sum.inl i₁)) * coeff i₁
    | Sum.inr i₂ => Q.p (e.symm (Sum.inr i₂)) * 0
  have hrew :
      ∀ i : Fin (n + m),
        Q.p i * liftLeft (n := n) (m := m) coeff i = g (e i) := by
    intro i
    cases h : e i with
    | inl i₁ =>
        have hi : i = e.symm (Sum.inl i₁) := by
          have := congrArg e.symm h
          simpa using this
        subst hi
        simp [e, g, liftLeft]
    | inr i₂ =>
        have hi : i = e.symm (Sum.inr i₂) := by
          have := congrArg e.symm h
          simpa using this
        subst hi
        simp [e, g, liftLeft]
  have hsum :
      (∑ i : Fin (n + m), Q.p i * liftLeft (n := n) (m := m) coeff i) =
        ∑ s : Fin n ⊕ Fin m, g s := by
    calc
      (∑ i : Fin (n + m), Q.p i * liftLeft (n := n) (m := m) coeff i)
          = ∑ i : Fin (n + m), g (e i) := by
              refine sum_congr rfl ?_
              intro i _
              simp [hrew]
      _ = ∑ s : Fin n ⊕ Fin m, g s := by
            simpa [e, g] using (Equiv.sum_comp e g)
  calc
    (∑ i : Fin (n + m), Q.p i * liftLeft (n := n) (m := m) coeff i)
        = ∑ s : Fin n ⊕ Fin m, g s := hsum
    _ = ∑ i : Fin n, Q.p (e.symm (Sum.inl i)) * coeff i := by
          simp [Fintype.sum_sum_type, g]
    _ = ∑ i : Fin n, Q.p (inlFin (n := n) (m := m) i) * coeff i := by
          simp [inlFin, e]

theorem sum_liftRight
    (Q : ProbDist (n + m)) (coeff : Fin m → ℝ) :
    (∑ i : Fin (n + m), Q.p i * liftRight (n := n) (m := m) coeff i)
      = ∑ i : Fin m, Q.p (inrFin (n := n) (m := m) i) * coeff i := by
  classical
  -- Reindex by `Fin n ⊕ Fin m`.
  let e : Fin (n + m) ≃ Fin n ⊕ Fin m := (finSumFinEquiv (m := n) (n := m)).symm
  let g : Fin n ⊕ Fin m → ℝ := fun s =>
    match s with
    | Sum.inl i₁ => Q.p (e.symm (Sum.inl i₁)) * 0
    | Sum.inr i₂ => Q.p (e.symm (Sum.inr i₂)) * coeff i₂
  have hrew :
      ∀ i : Fin (n + m),
        Q.p i * liftRight (n := n) (m := m) coeff i = g (e i) := by
    intro i
    cases h : e i with
    | inl i₁ =>
        have hi : i = e.symm (Sum.inl i₁) := by
          have := congrArg e.symm h
          simpa using this
        subst hi
        simp [e, g, liftRight]
    | inr i₂ =>
        have hi : i = e.symm (Sum.inr i₂) := by
          have := congrArg e.symm h
          simpa using this
        subst hi
        simp [e, g, liftRight]
  have hsum :
      (∑ i : Fin (n + m), Q.p i * liftRight (n := n) (m := m) coeff i) =
        ∑ s : Fin n ⊕ Fin m, g s := by
    calc
      (∑ i : Fin (n + m), Q.p i * liftRight (n := n) (m := m) coeff i)
          = ∑ i : Fin (n + m), g (e i) := by
              refine sum_congr rfl ?_
              intro i _
              simp [hrew]
      _ = ∑ s : Fin n ⊕ Fin m, g s := by
            simpa [e, g] using (Equiv.sum_comp e g)
  calc
    (∑ i : Fin (n + m), Q.p i * liftRight (n := n) (m := m) coeff i)
        = ∑ s : Fin n ⊕ Fin m, g s := hsum
    _ = ∑ i : Fin m, Q.p (e.symm (Sum.inr i)) * coeff i := by
          simp [Fintype.sum_sum_type, g]
    _ = ∑ i : Fin m, Q.p (inrFin (n := n) (m := m) i) * coeff i := by
          simp [inrFin, e]

/-- Left-block constraint lifted to the combined space, with mass scaling `w`. -/
def liftLeftScaled (w : ℝ) (c : EVConstraint n) : EVConstraint (n + m) :=
  { coeff := liftLeft (n := n) (m := m) c.coeff, rhs := w * c.rhs }

/-- Right-block constraint lifted to the combined space, with mass scaling `1-w`. -/
def liftRightScaled (w : ℝ) (c : EVConstraint m) : EVConstraint (n + m) :=
  { coeff := liftRight (n := n) (m := m) c.coeff, rhs := (1 - w) * c.rhs }

theorem sum_twoBlock_left
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (P₁ : ProbDist n) (P₂ : ProbDist m) (coeff : Fin n → ℝ) :
    (∑ i : Fin (n + m),
        (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂).p i *
          liftLeft (n := n) (m := m) coeff i)
      = w * ∑ i : Fin n, P₁.p i * coeff i := by
  classical
  -- Reindex by `Fin n ⊕ Fin m`.
  let e : Fin (n + m) ≃ Fin n ⊕ Fin m := (finSumFinEquiv (m := n) (n := m)).symm
  let g : Fin n ⊕ Fin m → ℝ := fun s =>
    match s with
    | Sum.inl i₁ => (w * P₁.p i₁) * coeff i₁
    | Sum.inr i₂ => (1 - w) * P₂.p i₂ * 0
  have hrew :
      ∀ i : Fin (n + m),
        (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂).p i *
          liftLeft (n := n) (m := m) coeff i =
        g (e i) := by
    intro i
    cases h : e i with
    | inl i₁ =>
        simp [e, g, ProbDist.twoBlock, liftLeft, h]
    | inr i₂ =>
        simp [e, g, ProbDist.twoBlock, liftLeft, h]
  have hsum :
      (∑ i : Fin (n + m),
        (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂).p i *
          liftLeft (n := n) (m := m) coeff i) =
        ∑ s : Fin n ⊕ Fin m, g s := by
    calc
      (∑ i : Fin (n + m),
          (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂).p i *
            liftLeft (n := n) (m := m) coeff i)
          = ∑ i : Fin (n + m), g (e i) := by
              refine sum_congr rfl ?_
              intro i _
              simp [hrew]
      _ = ∑ s : Fin n ⊕ Fin m, g s := by
            simpa [e, g] using (Equiv.sum_comp e g)
  calc
    (∑ i : Fin (n + m),
        (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂).p i *
          liftLeft (n := n) (m := m) coeff i)
        = ∑ s : Fin n ⊕ Fin m, g s := hsum
    _ = ∑ i : Fin n, (w * P₁.p i) * coeff i := by
          simp [Fintype.sum_sum_type, g]
    _ = w * ∑ i : Fin n, P₁.p i * coeff i := by
          calc
            (∑ i : Fin n, (w * P₁.p i) * coeff i)
                = ∑ i : Fin n, w * (P₁.p i * coeff i) := by
                    refine sum_congr rfl ?_
                    intro i _
                    ring
            _ = w * ∑ i : Fin n, P₁.p i * coeff i := by
                  simpa using
                    (Finset.mul_sum (s := (Finset.univ : Finset (Fin n))) (a := w)
                      (f := fun i : Fin n => P₁.p i * coeff i)).symm

theorem sum_twoBlock_right
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (P₁ : ProbDist n) (P₂ : ProbDist m) (coeff : Fin m → ℝ) :
    (∑ i : Fin (n + m),
        (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂).p i *
          liftRight (n := n) (m := m) coeff i)
      = (1 - w) * ∑ i : Fin m, P₂.p i * coeff i := by
  classical
  -- Reindex by `Fin n ⊕ Fin m`.
  let e : Fin (n + m) ≃ Fin n ⊕ Fin m := (finSumFinEquiv (m := n) (n := m)).symm
  let g : Fin n ⊕ Fin m → ℝ := fun s =>
    match s with
    | Sum.inl i₁ => (w * P₁.p i₁) * 0
    | Sum.inr i₂ => (1 - w) * P₂.p i₂ * coeff i₂
  have hrew :
      ∀ i : Fin (n + m),
        (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂).p i *
          liftRight (n := n) (m := m) coeff i =
        g (e i) := by
    intro i
    cases h : e i with
    | inl i₁ =>
        simp [e, g, ProbDist.twoBlock, liftRight, h]
    | inr i₂ =>
        simp [e, g, ProbDist.twoBlock, liftRight, h]
  have hsum :
      (∑ i : Fin (n + m),
        (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂).p i *
          liftRight (n := n) (m := m) coeff i) =
        ∑ s : Fin n ⊕ Fin m, g s := by
    calc
      (∑ i : Fin (n + m),
          (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂).p i *
            liftRight (n := n) (m := m) coeff i)
          = ∑ i : Fin (n + m), g (e i) := by
              refine sum_congr rfl ?_
              intro i _
              simp [hrew]
      _ = ∑ s : Fin n ⊕ Fin m, g s := by
            simpa [e, g] using (Equiv.sum_comp e g)
  calc
    (∑ i : Fin (n + m),
        (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂).p i *
          liftRight (n := n) (m := m) coeff i)
        = ∑ s : Fin n ⊕ Fin m, g s := hsum
    _ = ∑ i : Fin m, (1 - w) * P₂.p i * coeff i := by
          simp [Fintype.sum_sum_type, g]
    _ = (1 - w) * ∑ i : Fin m, P₂.p i * coeff i := by
          calc
            (∑ i : Fin m, (1 - w) * P₂.p i * coeff i)
                = ∑ i : Fin m, (1 - w) * (P₂.p i * coeff i) := by
                    refine sum_congr rfl ?_
                    intro i _
                    ring
            _ = (1 - w) * ∑ i : Fin m, P₂.p i * coeff i := by
                  simpa using
                    (Finset.mul_sum (s := (Finset.univ : Finset (Fin m))) (a := (1 - w))
                      (f := fun i : Fin m => P₂.p i * coeff i)).symm

theorem satisfies_liftLeftScaled_of_twoBlock
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (c : EVConstraint n) (P₁ : ProbDist n) (P₂ : ProbDist m) :
    satisfies (liftLeftScaled (n := n) (m := m) w c)
      (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂) ↔
      w * (∑ i : Fin n, P₁.p i * c.coeff i) = w * c.rhs := by
  dsimp [satisfies, liftLeftScaled]
  simp [sum_twoBlock_left (n := n) (m := m) w hw0 hw1 P₁ P₂ c.coeff]

theorem satisfies_liftRightScaled_of_twoBlock
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (c : EVConstraint m) (P₁ : ProbDist n) (P₂ : ProbDist m) :
    satisfies (liftRightScaled (n := n) (m := m) w c)
      (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂) ↔
      (1 - w) * (∑ i : Fin m, P₂.p i * c.coeff i) = (1 - w) * c.rhs := by
  dsimp [satisfies, liftRightScaled]
  simp [sum_twoBlock_right (n := n) (m := m) w hw0 hw1 P₁ P₂ c.coeff]

/-! ## Lifted constraint sets (block mass + scaled constraints) -/

/-- Lift a list of constraints from the left block, scaling RHS by `w`. -/
def liftSetLeftScaled (w : ℝ) (cs : EVConstraintSet n) : EVConstraintSet (n + m) :=
  cs.map (liftLeftScaled (n := n) (m := m) w)

/-- Lift a list of constraints from the right block, scaling RHS by `1-w`. -/
def liftSetRightScaled (w : ℝ) (cs : EVConstraintSet m) : EVConstraintSet (n + m) :=
  cs.map (liftRightScaled (n := n) (m := m) w)

/-- Mass constraint for the left block, expressed via `liftLeftScaled`. -/
def massConstraintLeft (w : ℝ) : EVConstraint (n + m) :=
  liftLeftScaled (n := n) (m := m) w { coeff := fun _ => (1 : ℝ), rhs := 1 }

/-- Mass constraint for the right block, expressed via `liftRightScaled`. -/
def massConstraintRight (w : ℝ) : EVConstraint (n + m) :=
  liftRightScaled (n := n) (m := m) w { coeff := fun _ => (1 : ℝ), rhs := 1 }

/-- Combined two-block constraint list: block masses + lifted constraints. -/
def twoBlockConstraints (w : ℝ) (cs₁ : EVConstraintSet n) (cs₂ : EVConstraintSet m) :
    EVConstraintSet (n + m) :=
  massConstraintLeft (n := n) (m := m) w ::
    massConstraintRight (n := n) (m := m) w ::
      (liftSetLeftScaled (n := n) (m := m) w cs₁ ++ liftSetRightScaled (n := n) (m := m) w cs₂)

theorem satisfies_massConstraintLeft_of_twoBlock
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (P₁ : ProbDist n) (P₂ : ProbDist m) :
    satisfies (massConstraintLeft (n := n) (m := m) w)
      (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂) := by
  -- Use `sum_twoBlock_left` with coeff ≡ 1.
  have hsum :=
    sum_twoBlock_left (n := n) (m := m) w hw0 hw1 P₁ P₂ (fun _ => (1 : ℝ))
  dsimp [massConstraintLeft, liftLeftScaled, satisfies] at *
  -- `∑ P₁.p i * 1 = 1` by `sum_one`.
  simp [P₁.sum_one, hsum]

theorem satisfies_massConstraintRight_of_twoBlock
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (P₁ : ProbDist n) (P₂ : ProbDist m) :
    satisfies (massConstraintRight (n := n) (m := m) w)
      (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂) := by
  have hsum :=
    sum_twoBlock_right (n := n) (m := m) w hw0 hw1 P₁ P₂ (fun _ => (1 : ℝ))
  dsimp [massConstraintRight, liftRightScaled, satisfies] at *
  simp [P₂.sum_one, hsum]

theorem satisfies_liftLeftScaled_of_twoBlock_of_satisfies
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (c : EVConstraint n) (P₁ : ProbDist n) (P₂ : ProbDist m)
    (hc : satisfies c P₁) :
    satisfies (liftLeftScaled (n := n) (m := m) w c)
      (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂) := by
  have h := satisfies_liftLeftScaled_of_twoBlock (n := n) (m := m) w hw0 hw1 c P₁ P₂
  dsimp [satisfies] at hc
  -- Multiply both sides by `w`.
  have hc' : w * (∑ i : Fin n, P₁.p i * c.coeff i) = w * c.rhs := by
    simp [hc]
  exact (h.mpr hc')

theorem satisfies_liftRightScaled_of_twoBlock_of_satisfies
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (c : EVConstraint m) (P₁ : ProbDist n) (P₂ : ProbDist m)
    (hc : satisfies c P₂) :
    satisfies (liftRightScaled (n := n) (m := m) w c)
      (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂) := by
  have h := satisfies_liftRightScaled_of_twoBlock (n := n) (m := m) w hw0 hw1 c P₁ P₂
  dsimp [satisfies] at hc
  have hc' : (1 - w) * (∑ i : Fin m, P₂.p i * c.coeff i) = (1 - w) * c.rhs := by
    simp [hc]
  exact (h.mpr hc')

theorem satisfiesSet_twoBlock_of_satisfies
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (cs₁ : EVConstraintSet n) (cs₂ : EVConstraintSet m)
    (P₁ : ProbDist n) (P₂ : ProbDist m)
    (h₁ : satisfiesSet cs₁ P₁) (h₂ : satisfiesSet cs₂ P₂) :
    satisfiesSet (twoBlockConstraints (n := n) (m := m) w cs₁ cs₂)
      (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂) := by
  intro c hc
  -- Unfold the combined constraint list and analyze membership.
  dsimp [twoBlockConstraints] at hc
  simp at hc
  rcases hc with hmassL | hrest
  · -- Left block mass constraint.
    subst hmassL
    exact satisfies_massConstraintLeft_of_twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂
  rcases hrest with hmassR | hrest
  · subst hmassR
    exact satisfies_massConstraintRight_of_twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂
  -- Lifted constraints from either left or right.
  rcases hrest with hleft | hright
  · -- Left side: membership in `liftSetLeftScaled`.
    rcases List.mem_map.mp hleft with ⟨c₁, hc₁, rfl⟩
    exact satisfies_liftLeftScaled_of_twoBlock_of_satisfies (n := n) (m := m) w hw0 hw1 c₁ P₁ P₂
      (h₁ c₁ hc₁)
  · -- Right side: membership in `liftSetRightScaled`.
    rcases List.mem_map.mp hright with ⟨c₂, hc₂, rfl⟩
    exact satisfies_liftRightScaled_of_twoBlock_of_satisfies (n := n) (m := m) w hw0 hw1 c₂ P₁ P₂
      (h₂ c₂ hc₂)

/-- Soundness: a two-block mixture of feasible posteriors satisfies the lifted EV constraints. -/
theorem twoBlockConstraints_sound
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (cs₁ : EVConstraintSet n) (cs₂ : EVConstraintSet m)
    (P₁ : ProbDist n) (P₂ : ProbDist m)
    (h₁ : P₁ ∈ toConstraintSet cs₁) (h₂ : P₂ ∈ toConstraintSet cs₂) :
    ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 P₁ P₂ ∈
      toConstraintSet (twoBlockConstraints (n := n) (m := m) w cs₁ cs₂) := by
  -- Unfold to constraint satisfaction.
  exact satisfiesSet_twoBlock_of_satisfies (n := n) (m := m) w hw0 hw1 cs₁ cs₂ P₁ P₂ h₁ h₂

theorem twoBlockConstraints_sound_set
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (cs₁ : EVConstraintSet n) (cs₂ : EVConstraintSet m) :
    ConstraintSet.twoBlock (n := n) (m := m) w hw0 hw1 (toConstraintSet cs₁) (toConstraintSet cs₂) ⊆
      toConstraintSet (twoBlockConstraints (n := n) (m := m) w cs₁ cs₂) := by
  intro Q hQ
  rcases hQ with ⟨P₁, h₁, P₂, h₂, rfl⟩
  exact twoBlockConstraints_sound (n := n) (m := m) w hw0 hw1 cs₁ cs₂ P₁ P₂ h₁ h₂

theorem twoBlockConstraints_complete_set
    (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
    (cs₁ : EVConstraintSet n) (cs₂ : EVConstraintSet m) :
    toConstraintSet (twoBlockConstraints (n := n) (m := m) w cs₁ cs₂) ⊆
      ConstraintSet.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1)
        (toConstraintSet cs₁) (toConstraintSet cs₂) := by
  intro Q hQ
  have hsat : satisfiesSet (twoBlockConstraints (n := n) (m := m) w cs₁ cs₂) Q := hQ
  have hwne : w ≠ 0 := ne_of_gt hw0
  have h1w_pos : 0 < 1 - w := sub_pos.mpr hw1
  have h1w_ne : 1 - w ≠ 0 := ne_of_gt h1w_pos

  -- Extract the block-mass constraints.
  have hmassL :
      satisfies (massConstraintLeft (n := n) (m := m) w) Q := by
    exact hsat _ (by simp [twoBlockConstraints])
  have hmassR :
      satisfies (massConstraintRight (n := n) (m := m) w) Q := by
    exact hsat _ (by simp [twoBlockConstraints])

  -- Compute the left and right masses.
  have hleftMass : (∑ i : Fin n, Q.p (inlFin (n := n) (m := m) i)) = w := by
    -- `massConstraintLeft` is `liftLeftScaled w` applied to coeff≡1, rhs=1.
    dsimp [massConstraintLeft, liftLeftScaled, satisfies] at hmassL
    -- Rewrite the lifted sum into the left-block sum.
    have hsum :=
      sum_liftLeft (n := n) (m := m) Q (fun _ : Fin n => (1 : ℝ))
    -- `∑ i, Q.p (inlFin i) * 1 = ∑ i, Q.p (inlFin i)`.
    simpa [hsum] using hmassL
  have hrightMass : (∑ i : Fin m, Q.p (inrFin (n := n) (m := m) i)) = 1 - w := by
    dsimp [massConstraintRight, liftRightScaled, satisfies] at hmassR
    have hsum :=
      sum_liftRight (n := n) (m := m) Q (fun _ : Fin m => (1 : ℝ))
    simpa [hsum] using hmassR

  -- Define the normalized left and right block distributions.
  let P₁ : ProbDist n := by
    refine
      { p := fun i => Q.p (inlFin (n := n) (m := m) i) / w
        nonneg := ?_
        sum_one := ?_ }
    · intro i
      exact div_nonneg (Q.nonneg _) (le_of_lt hw0)
    · classical
      calc
        (∑ i : Fin n, Q.p (inlFin (n := n) (m := m) i) / w)
            = ∑ i : Fin n, Q.p (inlFin (n := n) (m := m) i) * w⁻¹ := by
                simp [div_eq_mul_inv]
        _ = w⁻¹ * (∑ i : Fin n, Q.p (inlFin (n := n) (m := m) i)) := by
              -- Pull out the constant `w⁻¹` from the sum.
              calc
                (∑ i : Fin n, Q.p (inlFin (n := n) (m := m) i) * w⁻¹)
                    = ∑ i : Fin n, w⁻¹ * Q.p (inlFin (n := n) (m := m) i) := by
                        refine Finset.sum_congr rfl ?_
                        intro i _
                        ac_rfl
                _ = w⁻¹ * (∑ i : Fin n, Q.p (inlFin (n := n) (m := m) i)) := by
                        simp [Finset.mul_sum]
        _ = w⁻¹ * w := by rw [hleftMass]
        _ = 1 := by simp [hwne]
  let P₂ : ProbDist m := by
    refine
      { p := fun i => Q.p (inrFin (n := n) (m := m) i) / (1 - w)
        nonneg := ?_
        sum_one := ?_ }
    · intro i
      exact div_nonneg (Q.nonneg _) (le_of_lt h1w_pos)
    · classical
      calc
        (∑ i : Fin m, Q.p (inrFin (n := n) (m := m) i) / (1 - w))
            = ∑ i : Fin m, Q.p (inrFin (n := n) (m := m) i) * (1 - w)⁻¹ := by
                simp [div_eq_mul_inv]
        _ = (1 - w)⁻¹ * (∑ i : Fin m, Q.p (inrFin (n := n) (m := m) i)) := by
              -- Pull out the constant `(1-w)⁻¹` from the sum.
              calc
                (∑ i : Fin m, Q.p (inrFin (n := n) (m := m) i) * (1 - w)⁻¹)
                    = ∑ i : Fin m, (1 - w)⁻¹ * Q.p (inrFin (n := n) (m := m) i) := by
                        refine Finset.sum_congr rfl ?_
                        intro i _
                        ac_rfl
                _ = (1 - w)⁻¹ * (∑ i : Fin m, Q.p (inrFin (n := n) (m := m) i)) := by
                        simp [Finset.mul_sum]
        _ = (1 - w)⁻¹ * (1 - w) := by rw [hrightMass]
        _ = 1 := by simp [h1w_ne]

  have hP₁ : P₁ ∈ toConstraintSet cs₁ := by
    intro c hc
    -- Get the lifted constraint from the combined list.
    have hmem :
        liftLeftScaled (n := n) (m := m) w c ∈
          twoBlockConstraints (n := n) (m := m) w cs₁ cs₂ := by
      -- `liftLeftScaled w c` lives in the lifted-left part of the combined list.
      have hmemLift : liftLeftScaled (n := n) (m := m) w c ∈ liftSetLeftScaled (n := n) (m := m) w cs₁ := by
        exact List.mem_map.mpr ⟨c, hc, rfl⟩
      have hmemApp :
          liftLeftScaled (n := n) (m := m) w c ∈
            liftSetLeftScaled (n := n) (m := m) w cs₁ ++ liftSetRightScaled (n := n) (m := m) w cs₂ := by
        exact (List.mem_append).2 (Or.inl hmemLift)
      have hmemTail :
          liftLeftScaled (n := n) (m := m) w c ∈
            massConstraintRight (n := n) (m := m) w ::
              (liftSetLeftScaled (n := n) (m := m) w cs₁ ++ liftSetRightScaled (n := n) (m := m) w cs₂) :=
        List.mem_cons_of_mem _ hmemApp
      exact List.mem_cons_of_mem _ hmemTail
    have hlift : satisfies (liftLeftScaled (n := n) (m := m) w c) Q :=
      hsat _ hmem
    -- Rewrite it to a statement about the left block only.
    dsimp [liftLeftScaled, satisfies] at hlift
    have hsum :=
      sum_liftLeft (n := n) (m := m) Q c.coeff
    have hlift' : (∑ i : Fin n, Q.p (inlFin (n := n) (m := m) i) * c.coeff i) = w * c.rhs := by
      simpa [hsum] using hlift
    -- Cancel the factor `w` using the definition of `P₁`.
    dsimp [toConstraintSet, satisfiesSet, satisfies]
    -- Prove `∑ P₁_i * coeff_i = rhs`.
    have : w * (∑ i : Fin n, P₁.p i * c.coeff i) = w * c.rhs := by
      -- `w * P₁.p i = Q.p (inlFin i)`
      calc
        w * (∑ i : Fin n, P₁.p i * c.coeff i)
            = ∑ i : Fin n, w * (P₁.p i * c.coeff i) := by
                simpa using (Finset.mul_sum (s := (Finset.univ : Finset (Fin n))) (a := w)
                  (f := fun i : Fin n => P₁.p i * c.coeff i))
        _ = ∑ i : Fin n, (w * P₁.p i) * c.coeff i := by
              refine Finset.sum_congr rfl ?_
              intro i _
              ring
        _ = ∑ i : Fin n, Q.p (inlFin (n := n) (m := m) i) * c.coeff i := by
              refine Finset.sum_congr rfl ?_
              intro i _
              -- unfold `P₁.p`
              have hscale : w * P₁.p i = Q.p (inlFin (n := n) (m := m) i) := by
                simp [P₁, mul_div_cancel₀, hwne]
              simp [hscale]
        _ = w * c.rhs := hlift'
    have hcancel := mul_left_cancel₀ hwne this
    simpa [satisfies, P₁] using hcancel

  have hP₂ : P₂ ∈ toConstraintSet cs₂ := by
    intro c hc
    have hmem :
        liftRightScaled (n := n) (m := m) w c ∈
          twoBlockConstraints (n := n) (m := m) w cs₁ cs₂ := by
      have hmemLift :
          liftRightScaled (n := n) (m := m) w c ∈ liftSetRightScaled (n := n) (m := m) w cs₂ := by
        exact List.mem_map.mpr ⟨c, hc, rfl⟩
      have hmemApp :
          liftRightScaled (n := n) (m := m) w c ∈
            liftSetLeftScaled (n := n) (m := m) w cs₁ ++ liftSetRightScaled (n := n) (m := m) w cs₂ := by
        exact (List.mem_append).2 (Or.inr hmemLift)
      have hmemTail :
          liftRightScaled (n := n) (m := m) w c ∈
            massConstraintRight (n := n) (m := m) w ::
              (liftSetLeftScaled (n := n) (m := m) w cs₁ ++ liftSetRightScaled (n := n) (m := m) w cs₂) :=
        List.mem_cons_of_mem _ hmemApp
      exact List.mem_cons_of_mem _ hmemTail
    have hlift : satisfies (liftRightScaled (n := n) (m := m) w c) Q :=
      hsat _ hmem
    dsimp [liftRightScaled, satisfies] at hlift
    have hsum :=
      sum_liftRight (n := n) (m := m) Q c.coeff
    have hlift' :
        (∑ i : Fin m, Q.p (inrFin (n := n) (m := m) i) * c.coeff i) = (1 - w) * c.rhs := by
      simpa [hsum] using hlift
    have : (1 - w) * (∑ i : Fin m, P₂.p i * c.coeff i) = (1 - w) * c.rhs := by
      calc
        (1 - w) * (∑ i : Fin m, P₂.p i * c.coeff i)
            = ∑ i : Fin m, (1 - w) * (P₂.p i * c.coeff i) := by
                simpa using (Finset.mul_sum (s := (Finset.univ : Finset (Fin m))) (a := (1 - w))
                  (f := fun i : Fin m => P₂.p i * c.coeff i))
        _ = ∑ i : Fin m, ((1 - w) * P₂.p i) * c.coeff i := by
              refine Finset.sum_congr rfl ?_
              intro i _
              ring
        _ = ∑ i : Fin m, Q.p (inrFin (n := n) (m := m) i) * c.coeff i := by
              refine Finset.sum_congr rfl ?_
              intro i _
              have hscale : (1 - w) * P₂.p i = Q.p (inrFin (n := n) (m := m) i) := by
                -- `(1-w) * (Q / (1-w)) = Q`
                simp [P₂, mul_div_cancel₀, h1w_ne]
              -- Use `hscale` to rewrite the coefficient term.
              simp [hscale]
        _ = (1 - w) * c.rhs := hlift'
    have hcancel := mul_left_cancel₀ h1w_ne this
    simpa [satisfies, P₂] using hcancel

  -- Finally build the `ConstraintSet.twoBlock` witness.
  refine ⟨P₁, hP₁, P₂, hP₂, ?_⟩
  -- Show `Q = twoBlock w P₁ P₂`.
  apply ProbDist.ext
  intro i
  classical
  -- Split by which block `i` belongs to.
  cases h : (finSumFinEquiv (m := n) (n := m)).symm i with
  | inl i₁ =>
      -- left block
      have : i = inlFin (n := n) (m := m) i₁ := by
        -- `finSumFinEquiv` is an equivalence.
        simpa [inlFin] using congrArg (fun s => (finSumFinEquiv (m := n) (n := m)) s) h
      subst this
      have : w * (P₁.p i₁) = Q.p (inlFin (n := n) (m := m) i₁) := by
        -- `P₁.p i₁ = Q(left)/w`
        simp [P₁, mul_div_cancel₀, hwne]
      simp [Inference.ProbDist.twoBlock, inlFin, this]
  | inr i₂ =>
      have : i = inrFin (n := n) (m := m) i₂ := by
        simpa [inrFin] using congrArg (fun s => (finSumFinEquiv (m := n) (n := m)) s) h
      subst this
      have : (1 - w) * (P₂.p i₂) = Q.p (inrFin (n := n) (m := m) i₂) := by
        simp [P₂, mul_div_cancel₀, h1w_ne]
      simp [Inference.ProbDist.twoBlock, inrFin, this]

theorem twoBlockConstraints_equiv_set
    (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
    (cs₁ : EVConstraintSet n) (cs₂ : EVConstraintSet m) :
    toConstraintSet (twoBlockConstraints (n := n) (m := m) w cs₁ cs₂) =
      ConstraintSet.twoBlock (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1)
        (toConstraintSet cs₁) (toConstraintSet cs₂) := by
  apply le_antisymm
  · exact twoBlockConstraints_complete_set (n := n) (m := m) w hw0 hw1 cs₁ cs₂
  · exact twoBlockConstraints_sound_set (n := n) (m := m) w (le_of_lt hw0) (le_of_lt hw1) cs₁ cs₂

end TwoBlock

end Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Constraints
