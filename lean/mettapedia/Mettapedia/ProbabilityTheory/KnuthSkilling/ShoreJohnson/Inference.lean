import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Proof

/-!
# Shore–Johnson (discrete) inference-operator interface (SJ1–SJ4)

This file defines a **discrete** interface for Shore–Johnson's axioms (1980), phrased in a way
usable for connecting their “consistency across applications” premise to the K&S Appendix C
variational story.

Paper reference:
- J. E. Shore and R. W. Johnson, *Axiomatic Derivation of the Principle of Maximum Entropy and the
  Principle of Minimum Cross-Entropy*, IEEE Trans. Info. Theory 26(1), 1980.
  (Local copy: `literature/InformationTheory/shore-johnson-axiomatic-derivation.pdf`.)

Important design choice:
- We model “information” / “constraints” extensionally as a set of admissible posteriors.
  This keeps the interface independent of a particular constraint language (expected values,
  inequalities, etc.). A concrete constraint language can be added later as a refinement.

Implemented axioms (finite/discrete, Lean-friendly):
- SJ1 (Uniqueness) as `unique` / `uniqueProd`.
- SJ2 (Invariance) specialized to permutation invariance (`perm_invariant`).
- SJ4 (System independence) specialized to product state spaces (`system_independent`), matching
  Shore–Johnson's Axiom III / equation (11): inferring on two independent systems separately vs
  jointly yields the same factorized posterior.
- SJ3 (Subset independence) specialized to a two-block partition (`subset_independent_twoBlock`),
  matching Shore–Johnson's Axiom IV / equation (14) in the special case of a two-way partition
  with known block mass `w`.

Note: the objective-level KL/cross-entropy uniqueness results we currently use are formalized
separately in `Mettapedia/ProbabilityTheory/KnuthSkilling/Theorem.lean`. Connecting
this operator-level interface to those objective-level theorems requires fixing a concrete
constraint language (as in Shore–Johnson: expected-value constraints) and formalizing the
operator→objective derivation (their Theorem I / Appendix). The constraint language is introduced
in `Mettapedia/ProbabilityTheory/KnuthSkilling/Constraints.lean`, and the resulting
assumption bundle for the SJ→KL pipeline is packaged in
`Mettapedia/ProbabilityTheory/KnuthSkilling/PathC.lean`.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Inference

open Classical Finset BigOperators

open Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropy
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Proof

/-! ## Basic operations on finite distributions -/

namespace ProbDist

variable {n : ℕ}

/-- Permute a finite distribution by relabeling indices. -/
noncomputable def permute (σ : Equiv.Perm (Fin n)) (P : ProbDist n) : ProbDist n where
  p := fun i => P.p (σ⁻¹ i)
  nonneg := fun i => P.nonneg _
  sum_one := by
    classical
    -- Reindex the finite sum by the permutation.
    calc
      (∑ i : Fin n, P.p (σ⁻¹ i)) = ∑ i : Fin n, P.p i := by
        simpa using (Equiv.sum_comp (σ⁻¹) (fun i : Fin n => P.p i))
      _ = 1 := P.sum_one

theorem permute_apply (σ : Equiv.Perm (Fin n)) (P : ProbDist n) (i : Fin n) :
    (permute σ P).p i = P.p (σ⁻¹ i) := rfl

end ProbDist

namespace ProbDist

variable {n m : ℕ}

/-- Disjoint-union / two-block mixture of distributions on `Fin n` and `Fin m`.

This is the “subset independence” analogue of the product distribution `⊗`: it builds a
distribution on `Fin (n+m)` by weighting the left block by `w` and the right block by `1-w`.
-/
noncomputable def twoBlock (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (P₁ : ProbDist n) (P₂ : ProbDist m) : ProbDist (n + m) where
  p := fun i =>
    match (finSumFinEquiv (m := n) (n := m)).symm i with
    | Sum.inl i₁ => w * P₁.p i₁
    | Sum.inr i₂ => (1 - w) * P₂.p i₂
  nonneg := by
    intro i
    cases h : (finSumFinEquiv (m := n) (n := m)).symm i with
    | inl i₁ =>
        simpa [h] using mul_nonneg hw0 (P₁.nonneg i₁)
    | inr i₂ =>
        have hw' : 0 ≤ 1 - w := sub_nonneg.mpr hw1
        simpa [h] using mul_nonneg hw' (P₂.nonneg i₂)
  sum_one := by
    classical
    -- Reindex by the sum-equivalence and split the sum over `Fin n ⊕ Fin m`.
    have hsum :
        (∑ i : Fin (n + m),
            match (finSumFinEquiv (m := n) (n := m)).symm i with
            | Sum.inl i₁ => w * P₁.p i₁
            | Sum.inr i₂ => (1 - w) * P₂.p i₂) =
          ∑ s : Fin n ⊕ Fin m,
            (match s with
              | Sum.inl i₁ => w * P₁.p i₁
              | Sum.inr i₂ => (1 - w) * P₂.p i₂) := by
      -- Reindex the finite sum by the equivalence `Fin (n+m) ≃ Fin n ⊕ Fin m`.
      let e : Fin (n + m) ≃ Fin n ⊕ Fin m := (finSumFinEquiv (m := n) (n := m)).symm
      let g : Fin n ⊕ Fin m → ℝ := fun s =>
        match s with
        | Sum.inl i₁ => w * P₁.p i₁
        | Sum.inr i₂ => (1 - w) * P₂.p i₂
      -- Now `Equiv.sum_comp e g` is exactly the desired equality.
      simpa [e, g] using (Equiv.sum_comp e g)
    rw [hsum]
    -- Now split the sum over the two summands.
    simp [Fintype.sum_sum_type]
    have hleft :
        (∑ i : Fin n, w * P₁.p i) = w * ∑ i : Fin n, P₁.p i := by
      -- Pull out the constant `w` from the finite sum.
      change (Finset.univ.sum fun i : Fin n => w * P₁.p i) =
        w * (Finset.univ.sum fun i : Fin n => P₁.p i)
      simpa using
        (Finset.mul_sum (s := (Finset.univ : Finset (Fin n))) (a := w) (f := fun i => P₁.p i)).symm
    have hright :
        (∑ i : Fin m, (1 - w) * P₂.p i) = (1 - w) * ∑ i : Fin m, P₂.p i := by
      change (Finset.univ.sum fun i : Fin m => (1 - w) * P₂.p i) =
        (1 - w) * (Finset.univ.sum fun i : Fin m => P₂.p i)
      simpa using
        (Finset.mul_sum (s := (Finset.univ : Finset (Fin m))) (a := (1 - w)) (f := fun i => P₂.p i)).symm
    -- Finish using `∑ P₁ = 1` and `∑ P₂ = 1`.
    calc
      (∑ i : Fin n, w * P₁.p i) + (∑ i : Fin m, (1 - w) * P₂.p i)
          = w * 1 + (1 - w) * 1 := by simp [hleft, hright, P₁.sum_one, P₂.sum_one]
      _ = 1 := by ring

end ProbDist

/-! ## Product marginals -/

namespace ProbDistProd

variable {n m : ℕ}

/-- Left marginal of a distribution on `Fin n × Fin m`. -/
noncomputable def marginalLeft (P : ProbDistProd n m) : ProbDist n where
  p := fun i => ∑ j : Fin m, P.p (i, j)
  nonneg := by
    intro i
    exact Finset.sum_nonneg (fun j _ => P.nonneg (i, j))
  sum_one := by
    classical
    -- `∑ i (∑ j P(i,j)) = ∑ (i,j) P(i,j) = 1`.
    simpa [Fintype.sum_prod_type] using P.sum_one

/-- Right marginal of a distribution on `Fin n × Fin m`. -/
noncomputable def marginalRight (P : ProbDistProd n m) : ProbDist m where
  p := fun j => ∑ i : Fin n, P.p (i, j)
  nonneg := by
    intro j
    exact Finset.sum_nonneg (fun i _ => P.nonneg (i, j))
  sum_one := by
    classical
    -- `∑ j (∑ i P(i,j)) = ∑ (i,j) P(i,j) = 1`, by swapping the order of summation.
    calc
      (∑ j : Fin m, ∑ i : Fin n, P.p (i, j))
          = ∑ ji : Fin m × Fin n, P.p (ji.2, ji.1) := by
              -- This is just `Fintype.sum_prod_type` for the function `ji ↦ P.p (ji.2, ji.1)`.
              have h :
                  (∑ ji : Fin m × Fin n, P.p (ji.2, ji.1)) =
                    ∑ j : Fin m, ∑ i : Fin n, P.p (i, j) := by
                simp [Fintype.sum_prod_type]
              exact h.symm
      _ = ∑ ij : Fin n × Fin m, P.p ij := by
            -- Reindex via `Equiv.prodComm`.
            simpa using (Equiv.sum_comp (Equiv.prodComm (Fin m) (Fin n))
              (fun ij : Fin n × Fin m => P.p ij))
      _ = 1 := P.sum_one

end ProbDistProd

/-! ## Constraint sets and basic constructors -/

/-- A constraint set is just a set of admissible posteriors. -/
abbrev ConstraintSet (n : ℕ) := Set (ProbDist n)

/-- A constraint set on a product space `Fin n × Fin m`. -/
abbrev ConstraintSetProd (n m : ℕ) := Set (ProbDistProd n m)

namespace ConstraintSet

variable {n : ℕ}

/-- Relabel constraints by permuting the state labels. -/
def permute (σ : Equiv.Perm (Fin n)) (C : ConstraintSet n) : ConstraintSet n :=
  {Q | ProbDist.permute σ Q ∈ C}

end ConstraintSet

namespace ConstraintSet

variable {n m : ℕ}

/-- Two-block constraint constructor: admissible posteriors are built by mixing admissible block
posteriors with a fixed block-mass `w`. -/
def twoBlock (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (C₁ : ConstraintSet n) (C₂ : ConstraintSet m) :
    ConstraintSet (n + m) :=
  {Q | ∃ q₁ ∈ C₁, ∃ q₂ ∈ C₂, Q = ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 q₁ q₂}

end ConstraintSet

namespace ConstraintSetProd

variable {n m : ℕ}

/-- Product constraint: constrain the left and right marginals independently. -/
def product (C₁ : ConstraintSet n) (C₂ : ConstraintSet m) : ConstraintSetProd n m :=
  {Q | ProbDistProd.marginalLeft Q ∈ C₁ ∧ ProbDistProd.marginalRight Q ∈ C₂}

end ConstraintSetProd

/-! ## Shore–Johnson inference methods and axioms -/

/-- An inference method: relation between a prior, admissible posteriors, and an inferred posterior.

We use a relation (not a function) so that **uniqueness** can be stated as an axiom (SJ1). -/
structure InferenceMethod where
  Infer : ∀ {n : ℕ}, ProbDist n → ConstraintSet n → ProbDist n → Prop
  InferProd : ∀ {n m : ℕ}, ProbDistProd n m → ConstraintSetProd n m → ProbDistProd n m → Prop

/-- Shore–Johnson axioms (discrete).

This is intentionally an interface: it does not commit to any specific constraint language, only to
the *structural* invariance/independence requirements.
-/
structure ShoreJohnsonAxioms (I : InferenceMethod) : Prop where
  /-- SJ1 (Uniqueness): unique inferred posterior for every prior and constraint set. -/
  unique :
    ∀ {n : ℕ} (p : ProbDist n) (C : ConstraintSet n), ∃! q : ProbDist n, I.Infer p C q

  /-- SJ1 (Uniqueness) on product spaces. -/
  uniqueProd :
    ∀ {n m : ℕ} (p : ProbDistProd n m) (C : ConstraintSetProd n m), ∃! q : ProbDistProd n m, I.InferProd p C q

  /-- Feasibility: inferred posteriors lie in the constraint set. -/
  feasible :
    ∀ {n : ℕ} {p : ProbDist n} {C : ConstraintSet n} {q : ProbDist n}, I.Infer p C q → q ∈ C

  /-- Feasibility on product spaces. -/
  feasibleProd :
    ∀ {n m : ℕ} {p : ProbDistProd n m} {C : ConstraintSetProd n m} {q : ProbDistProd n m},
      I.InferProd p C q → q ∈ C

  /-- SJ2 (Permutation invariance): relabeling the state space commutes with inference. -/
  perm_invariant :
    ∀ {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : ProbDist n) (C : ConstraintSet n) (q : ProbDist n),
      I.Infer p C q → I.Infer (ProbDist.permute σ p) (ConstraintSet.permute σ C) (ProbDist.permute σ q)

  /-- SJ4 / Axiom III (System independence): independent constraints on each factor imply a product posterior. -/
  system_independent :
    ∀ {n m : ℕ} (p₁ : ProbDist n) (p₂ : ProbDist m)
      (C₁ : ConstraintSet n) (C₂ : ConstraintSet m)
      (q₁ : ProbDist n) (q₂ : ProbDist m) (q : ProbDistProd n m),
      I.Infer p₁ C₁ q₁ →
      I.Infer p₂ C₂ q₂ →
      I.InferProd (p₁ ⊗ p₂) (ConstraintSetProd.product C₁ C₂) q →
      q = (q₁ ⊗ q₂)

  /-- SJ3 / Axiom IV (Subset independence), two-block disjoint-union form.

If the “information” decomposes by disjoint subsets (here: `Fin n` and `Fin m` inside
`Fin (n+m)`), and we additionally fix the block masses via the mixture weight `w`, then inference
commutes with building the combined distribution.

This statement is intentionally **constraint-language agnostic**: constraints are modeled as
sets of admissible posteriors, and `ConstraintSet.twoBlock` is the canonical constructor for
“separate constraints on each block + fixed block mass”.
-/
  subset_independent_twoBlock :
    ∀ {n m : ℕ} (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
      (p₁ : ProbDist n) (p₂ : ProbDist m)
      (C₁ : ConstraintSet n) (C₂ : ConstraintSet m)
      (q₁ : ProbDist n) (q₂ : ProbDist m) (q : ProbDist (n + m)),
      I.Infer p₁ C₁ q₁ →
      I.Infer p₂ C₂ q₂ →
      I.Infer (ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 p₁ p₂)
        (ConstraintSet.twoBlock (n := n) (m := m) w hw0 hw1 C₁ C₂) q →
      q = ProbDist.twoBlock (n := n) (m := m) w hw0 hw1 q₁ q₂

end Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Inference
