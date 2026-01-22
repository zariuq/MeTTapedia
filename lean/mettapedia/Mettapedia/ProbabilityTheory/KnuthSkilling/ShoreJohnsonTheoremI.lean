import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonInference
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonObjective
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonConstraints
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonAppendixFDeriv
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonAppendixMinimizer
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonAppendixTheoremI
import Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonGradientSeparability
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic

/-!
# Shore-Johnson Theorem I: Derivation of Sum-Form Objective

This file proves **Theorem I** from Shore & Johnson (1980): an inference operator satisfying
SJ1 (uniqueness), SJ2 (permutation invariance), and SJ3 (subset independence) must be realizable
by a sum-form objective functional.

## Main Result

```lean
theorem shore_johnson_theorem_I :
    ∃ d : ℝ → ℝ → ℝ, ObjEquivEV F (ofAtom d)
```

## Proof Strategy (following SJ Appendix)

The paper's proof (Appendix, §A1-A13) proceeds by:

1. **Lemma I**: Subset independence implies conditional independence of posteriors
2. **Lemma II**: Permutation invariance implies the objective is equivalent to a symmetric function
3. **Gradient structure**: Using subset independence on 2-element subsets + uniqueness,
   show that ∂F/∂q_i has the form: ∂F/∂q_i = s(q,p) * g(q_i, p_i) + z(q,p)
   where s, z are scalars (same for all i) and g is a "coordinate kernel"
4. **Sum-form conclusion**: This gradient structure implies F is equivalent to ∑ d(q_i, p_i)

## Implementation Notes

We use Lean-friendly techniques:
- **Directional derivatives** along shift2 curves (already in `ShoreJohnsonAppendixMinimizer`)
- **Fermat's theorem** for constrained optimization (first-order necessary conditions)
- **KKT-style** stationarity conditions rather than full multivariate gradient projection

## References

- Shore & Johnson (1980), "Axiomatic Derivation of the Principle of Maximum Entropy..."
- Appendix "Proof of Theorem I", equations (A1)-(A13)
- `/home/zar/claude/literature/InformationTheory/shore-johnson-axiomatic-derivation.pdf`
- **OptLib** (https://github.com/optsuite/optlib): Lean 4 KKT conditions formalization.
  Their approach to constrained optimization via Lagrange multipliers informed our
  stationarity characterization. See arXiv:2503.18821.

-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonTheoremI

open Classical
open Finset
open scoped BigOperators

open Mettapedia.ProbabilityTheory.KnuthSkilling.InformationEntropy
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonInference
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonObjective
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonConstraints
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonAppendix
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonAppendixMinimizer
open Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonAppendixTheoremI

/-! ## Regularity Assumptions for Theorem I

These assumptions make precise what "well-behaved" means in the paper's statement:
"We take this to mean, in particular, that the function H(q,p) is continuously
differentiable in the interior of the positive region" (Appendix, line 1419-1421).

We state these explicitly rather than smuggling them as axioms.
-/

/-- **Regularity bundle for Theorem I**: Makes precise the paper's "well-behaved" assumption.

The paper assumes H(q,p) is:
- Continuously differentiable in the interior of the positive simplex
- The projection of ∇H into the normalization subspace is zero only at minima
- No spurious stationary points (KKT conditions are sufficient for global minimality)

We formalize this via:
1. Existence of directional derivatives along feasible curves (shift2)
2. Uniqueness of stationary points (⇔ minimizers) on EV constraint sets
-/
structure TheoremIRegularity (F : ObjectiveFunctional) where
  /-- The objective is differentiable along shift2 curves in the positive simplex. -/
  has_shift2_deriv :
    ∀ {n : ℕ} (p q : ProbDist n) (i j : Fin n) (hij : i ≠ j),
      (∀ k, 0 < p.p k) → (∀ k, 0 < q.p k) →
      ∃ L : ℝ, HasDerivAt (fun t => F.D (shift2ProbClamp q i j hij t) p) L (q.p i)

  /-- **KKT/stationarity condition**: On EV constraint sets in the positive simplex,
  first-order stationarity (vanishing directional derivatives) is equivalent to being a
  global minimizer.

  This replaces the paper's assumption "projection of ∇H is zero only at minima" with
  an explicit regularity condition. In convex optimization, this follows from strict convexity
  + constraint qualification. -/
  stationary_iff_minimizer :
    ∀ {n : ℕ} (p q : ProbDist n) (cs : EVConstraintSet n),
      (∀ i, 0 < p.p i) → (∀ i, 0 < q.p i) →
      q ∈ toConstraintSet cs →
      ((∀ (i j : Fin n) (hij : i ≠ j),
        PairwiseCoeffEq cs i j →
        ∃ L : ℝ, HasDerivAt (fun t => F.D (shift2ProbClamp q i j hij t) p) L (q.p i) ∧ L = 0)
      ↔ IsMinimizer F p (toConstraintSet cs) q)

/-! ## Lemma I: Subset Independence Consequence

From Shore-Johnson paper (line 613-629):

"Lemma I: Let the assumptions of Axiom IV hold, and let q = p ∘ (I/M) be the posterior for
the whole system. Then q(x ∈ S_i) is functionally independent of q(x ∉ S_i), of the prior
p(x ∉ S_i), and of n."

In our discrete framework with two blocks:
-/

/-- **Lemma I**: Subset independence implies that the inferred posterior on a block is
independent of:
- The posterior on the other block
- The prior on the other block
- The block sizes

This is a direct consequence of SJ3 (subset independence) for the two-block case.
-/
theorem lemma_I_twoBlock
    (I : InferenceMethod) (hSJ : ShoreJohnsonAxioms I)
    {n m : ℕ} (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (p₁ : ProbDist n) (p₂ : ProbDist m)
    (C₁ : ConstraintSet n) (C₂ : ConstraintSet m)
    (q₁ : ProbDist n) (q₂ : ProbDist m) (q : ProbDist (n + m))
    (hInfer₁ : I.Infer p₁ C₁ q₁)
    (hInfer₂ : I.Infer p₂ C₂ q₂)
    (hInfer : I.Infer (ProbDist.twoBlock w hw0 hw1 p₁ p₂)
      (ConstraintSet.twoBlock w hw0 hw1 C₁ C₂) q) :
    q = ProbDist.twoBlock w hw0 hw1 q₁ q₂ :=
  hSJ.subset_independent_twoBlock w hw0 hw1 p₁ p₂ C₁ C₂ q₁ q₂ q hInfer₁ hInfer₂ hInfer

/-! ## Lemma II: Symmetry from Permutation Invariance

From Shore-Johnson paper (line 650-656):

"By invariance, the minima of H and πH coincide, where πH(q,p) = H(q_π(1),...,q_π(n), p_π(1),...,p_π(n)).
Therefore the minima of H and F coincide, where F is the mean of the πH for all permutations π,
and H is equivalent to the symmetric function F."

In objective-level language:
-/

/-- **Lemma II**: Permutation invariance implies the objective is equivalent to a symmetric
objective (average over all permutations).

For objectives realized by an SJ2-invariant inference operator, the minimizers are invariant
under relabeling, so H is equivalent to its symmetrization.

Note: The EV-level permutation uses `σ⁻¹` to match the set-level permutation convention.
If you permute the distribution labels by σ, you permute the constraint coefficients by σ⁻¹.
-/
theorem lemma_II_permutation_symmetry
    (I : InferenceMethod) (F : ObjectiveFunctional)
    (hSJ : ShoreJohnsonAxioms I)
    (hRealize : RealizesEV I F)
    {n : ℕ} (p : ProbDist n) (cs : EVConstraintSet n) (σ : Equiv.Perm (Fin n)) (q : ProbDist n) :
    IsMinimizer F p (toConstraintSet cs) q ↔
    IsMinimizer F (ProbDist.permute σ p) (toConstraintSet (EVConstraintSet.permute σ⁻¹ cs))
      (ProbDist.permute σ q) := by
  -- The key compatibility lemma: ConstraintSet.permute σ (toConstraintSet cs) = toConstraintSet (EVConstraintSet.permute σ⁻¹ cs)
  have hcompat : ConstraintSet.permute σ (toConstraintSet cs) =
      toConstraintSet (EVConstraintSet.permute σ⁻¹ cs) :=
    toConstraintSet_permute σ cs
  -- Inference ↔ minimization (original)
  have hLeft := hRealize.infer_iff_minimizer_ev (p := p) (cs := cs) (q := q)
  -- Inference ↔ minimization (permuted) - note we use the compatible EV constraint set
  have hRight := hRealize.infer_iff_minimizer_ev
    (p := ProbDist.permute σ p) (cs := EVConstraintSet.permute σ⁻¹ cs) (q := ProbDist.permute σ q)
  constructor
  · -- Forward: q minimizes on cs ⟹ (permute σ q) minimizes on (permute σ⁻¹ cs)
    intro hMin
    -- q is minimizer ⟺ I.Infer p (toConstraintSet cs) q
    have hInfer : I.Infer p (toConstraintSet cs) q := hLeft.mpr hMin
    -- Apply SJ2 (permutation invariance)
    have hPermInfer := hSJ.perm_invariant (σ := σ) (p := p) (C := toConstraintSet cs) (q := q) hInfer
    -- This gives I.Infer (permute σ p) (ConstraintSet.permute σ (toConstraintSet cs)) (permute σ q)
    -- Use compatibility to rewrite to EV form
    rw [hcompat] at hPermInfer
    -- Now we have I.Infer on the permuted EV constraints
    exact hRight.mp hPermInfer
  · -- Backward: (permute σ q) minimizes on (permute σ⁻¹ cs) ⟹ q minimizes on cs
    intro hMinPerm
    -- (permute σ q) is minimizer ⟺ I.Infer (permute σ p) ... (permute σ q)
    have hInferPerm : I.Infer (ProbDist.permute σ p)
        (toConstraintSet (EVConstraintSet.permute σ⁻¹ cs)) (ProbDist.permute σ q) :=
      hRight.mpr hMinPerm
    -- Apply SJ2 with σ⁻¹ to "undo" the permutation
    rw [← hcompat] at hInferPerm
    have hInferPermBack := hSJ.perm_invariant (σ := σ⁻¹)
      (p := ProbDist.permute σ p) (C := ConstraintSet.permute σ (toConstraintSet cs))
      (q := ProbDist.permute σ q) hInferPerm
    -- Simplify: permute σ⁻¹ (permute σ x) = x and ConstraintSet.permute σ⁻¹ (ConstraintSet.permute σ C) = C
    have hp_back : ProbDist.permute σ⁻¹ (ProbDist.permute σ p) = p := by
      ext i; simp [ProbDist.permute]
    have hq_back : ProbDist.permute σ⁻¹ (ProbDist.permute σ q) = q := by
      ext i; simp [ProbDist.permute]
    have hC_back : ConstraintSet.permute σ⁻¹ (ConstraintSet.permute σ (toConstraintSet cs)) =
        toConstraintSet cs := by
      ext Q
      simp [ConstraintSet.permute]
      constructor
      · intro h
        have : ProbDist.permute σ (ProbDist.permute σ⁻¹ Q) = Q := by
          ext i; simp [ProbDist.permute]
        rw [← this]; exact h
      · intro h
        have : ProbDist.permute σ (ProbDist.permute σ⁻¹ Q) = Q := by
          ext i; simp [ProbDist.permute]
        rw [← this] at h; exact h
    rw [hp_back, hq_back, hC_back] at hInferPermBack
    exact hLeft.mp hInferPermBack

/-! ## Main Theorem I: Sum-Form Existence

We provide two versions of Theorem I:

1. **`shore_johnson_theorem_I_from_appendix`**: Uses `SJAppendixAssumptions` as hypothesis.
   This is the honest, complete version - it makes explicit the regularity/richness assumptions
   from the paper's Appendix proof.

2. **`shore_johnson_theorem_I`**: The "full" theorem with `TheoremIRegularity` as hypothesis.
   The gap here is deriving the Appendix-style gradient structure from SJ1-SJ3 + regularity.
   This is the genuinely hard mathematical content of the Appendix proof (equations A1-A13).

The first version is **proven** using `isMinimizer_iff_isMinimizer_ofAtom_of_pos`.
The second version has a **documented gap** - the derivation of the gradient structure from axioms.
-/

/-- **Shore-Johnson Theorem I (Appendix form)**: An objective F satisfying the Appendix
regularity/richness conditions (bundled in `SJAppendixAssumptions`) is equivalent to a
sum-form objective on positive distributions.

This is the "given the gradient structure, conclude sum-form" part of Theorem I.
The hard work of *deriving* the gradient structure from SJ1-SJ3 is in `SJAppendixAssumptions`.

**Status**: PROVEN (no sorry).
-/
theorem shore_johnson_theorem_I_from_appendix
    (F : ObjectiveFunctional) (d : ℝ → ℝ → ℝ)
    (hApp : SJAppendixAssumptions F d) :
    ∀ {n : ℕ} (p : ProbDist n) (cs : EVConstraintSet n) (q : ProbDist n),
      (∀ i, 0 < p.p i) → (∀ i, 0 < q.p i) → q ∈ toConstraintSet cs →
      (IsMinimizer F p (toConstraintSet cs) q ↔ IsMinimizer (ofAtom d) p (toConstraintSet cs) q) := by
  intro n p cs q hp hq hmem
  exact isMinimizer_iff_isMinimizer_ofAtom_of_pos hApp p hp cs q hmem hq

/-- **Shore-Johnson Theorem I (positive simplex version)**: On the positive simplex interior,
F and ofAtom d have the same minimizers whenever the Appendix conditions hold.

This gives `ObjEquivEV` restricted to positive distributions.
-/
theorem shore_johnson_theorem_I_ObjEquivEV_pos
    (F : ObjectiveFunctional) (d : ℝ → ℝ → ℝ)
    (hApp : SJAppendixAssumptions F d) :
    ∀ {n : ℕ} (p : ProbDist n) (cs : EVConstraintSet n),
      (∀ i, 0 < p.p i) →
      {q | (∀ i, 0 < q.p i) ∧ IsMinimizer F p (toConstraintSet cs) q} =
      {q | (∀ i, 0 < q.p i) ∧ IsMinimizer (ofAtom d) p (toConstraintSet cs) q} := by
  intro n p cs hp
  ext q
  constructor
  · intro ⟨hqPos, hMin⟩
    refine ⟨hqPos, ?_⟩
    exact (shore_johnson_theorem_I_from_appendix F d hApp p cs q hp hqPos hMin.1).mp hMin
  · intro ⟨hqPos, hMin⟩
    refine ⟨hqPos, ?_⟩
    exact (shore_johnson_theorem_I_from_appendix F d hApp p cs q hp hqPos hMin.1).mpr hMin

/-! ## The Gap: From SJ Axioms to Appendix Assumptions

The truly hard part of Shore-Johnson's Theorem I proof is showing that SJ1-SJ3 + differentiability
*implies* the gradient has sum-separable form (Appendix equations A1-A13):

    ∂H/∂qᵢ = s(q,p) · g(qᵢ, pᵢ) + z(q,p)

## Infrastructure in `ShoreJohnsonGradientSeparability.lean`

We have formalized the key concepts for closing this gap:

1. **`GradientRepresentation`**: A coordinate kernel g with the derivative formula
2. **`ExtractGRegularity`**: Regularity conditions including derivative locality
3. **`shift2_swap`**: Key symmetry `shift2 q i j t = shift2 q j i (q_i + q_j - t)`
4. **`gradient_rep_to_appendix_assumptions`**: Bridge from gradient rep to Appendix assumptions

## Remaining Steps (with 2-3 sorries)

1. **`deriv_symmetric_under_swap`**: Prove L_ij = -L_ji using `shift2_swap` + chain rule
2. **`exists_gradient_representation`**: Construct g from SJ3 (subset independence)
3. Fill in positivity arguments in `gradient_rep_to_appendix_assumptions`

## Mathematical Insight (Viazminsky 2008)

A function F is sum-separable iff each gradient component ∂F/∂xᵢ depends only on xᵢ.
SJ3 (subset independence) forces exactly this structure: the derivative on {i,j} depends
only on the local data (qᵢ, pᵢ, qⱼ, pⱼ), not on other coordinates.

**Current status**: Infrastructure is in place. The gap is explicit, not smuggled.
-/

/-! ### Construction of d from g

The atomic function d is related to the gradient kernel g by:
  ∂d/∂q (q, p) = g(q, p)

That is, d is an antiderivative of g in its first argument. For our purposes, we define d
formally and show the stationarity equivalence.

For a sum-form objective F_d(q, p) = ∑_i d(q_i, p_i), the KKT stationarity condition is:
  ∂d/∂q(q_i, p_i) = β + ∑_k λ_k c_{ki}

This is exactly `StationaryEV (∂d/∂q)`. So if ∂d/∂q = g, then StationaryEV g characterizes
minimizers of ofAtom d.
-/

/-- An atomic function d is an antiderivative of g if ∂d/∂q = g. -/
def IsAntiderivative (d g : ℝ → ℝ → ℝ) : Prop :=
  ∀ q p : ℝ, HasDerivAt (fun t => d t p) (g q p) q

/-! ### General KKT Infrastructure

We generalize the KL-specific proof structure to arbitrary d and g.
The key insight: the forward direction (minimizer → stationary) is pure linear algebra,
independent of the specific form of d!
-/

/-- Gradient linear functional for a general atomic function d with derivative g.
    Note: We include the normalization constraint in the gradient, which contributes
    a constant term of 1 to each coordinate. So the gradient is g(q_i, p_i) + 1. -/
noncomputable def gradAt_general {n : ℕ} (g : ℝ → ℝ → ℝ) (p q : ProbDist n) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  { toFun := fun v => ∑ i : Fin n, v i * (g (q.p i) (p.p i) + 1)
    map_add' := by
      intro v w
      classical
      simp [Finset.sum_add_distrib, add_mul, mul_add, add_assoc, add_left_comm, add_comm]
    map_smul' := by
      intro c v
      classical
      simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] }

lemma gradAt_general_apply_single {n : ℕ} (g : ℝ → ℝ → ℝ) (p q : ProbDist n) (i : Fin n) :
    gradAt_general g p q (Pi.single i (1 : ℝ) : Fin n → ℝ) = g (q.p i) (p.p i) + 1 := by
  classical
  have :
      (∑ j : Fin n, ((Pi.single i (1 : ℝ) : Fin n → ℝ) j) * (g (q.p j) (p.p j) + 1)) =
        (Pi.single i (1 : ℝ) : Fin n → ℝ) i * (g (q.p i) (p.p i) + 1) := by
    refine Fintype.sum_eq_single i ?_
    intro j hji
    simp [Pi.single, hji]
  simpa [gradAt_general, Pi.single, this] using this

/-- Constraint linear functionals (same as in KL case, but repeated for convenience). -/
noncomputable def constraintForm_general {n : ℕ} (cs : EVConstraintSet n) :
    Option (Fin cs.length) → (Fin n → ℝ) →ₗ[ℝ] ℝ
  | none =>
      { toFun := fun v => ∑ i : Fin n, v i
        map_add' := by
          intro v w
          classical
          simp [Finset.sum_add_distrib]
        map_smul' := by
          intro c v
          classical
          simp [Finset.mul_sum] }
  | some k =>
      { toFun := fun v => ∑ i : Fin n, v i * (cs.get k).coeff i
        map_add' := by
          intro v w
          classical
          simp [Finset.sum_add_distrib, add_mul, mul_assoc, mul_left_comm, mul_comm]
        map_smul' := by
          intro c v
          classical
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] }

lemma constraintForm_general_apply_single_none {n : ℕ} (cs : EVConstraintSet n) (i : Fin n) :
    constraintForm_general cs none (Pi.single i (1 : ℝ) : Fin n → ℝ) = 1 := by
  classical
  simp [constraintForm_general, Pi.single]
  convert Finset.sum_eq_single i ?_ ?_
  · simp
  · intro j _ hj
    simp [hj]
  · simp

lemma constraintForm_general_apply_single_some {n : ℕ} (cs : EVConstraintSet n)
    (k : Fin cs.length) (i : Fin n) :
    constraintForm_general cs (some k) (Pi.single i (1 : ℝ) : Fin n → ℝ) = (cs.get k).coeff i := by
  classical
  simp [constraintForm_general, Pi.single]
  convert Finset.sum_eq_single i ?_ ?_
  · simp
  · intro j _ hj
    simp [hj]
  · simp

lemma constraintForm_general_none_apply {n : ℕ} (cs : EVConstraintSet n) (v : Fin n → ℝ) :
    constraintForm_general cs none v = ∑ i : Fin n, v i := by
  simp [constraintForm_general]

lemma constraintForm_general_some_apply {n : ℕ} (cs : EVConstraintSet n)
    (k : Fin cs.length) (v : Fin n → ℝ) :
    constraintForm_general cs (some k) v = ∑ i : Fin n, v i * (cs.get k).coeff i := by
  simp [constraintForm_general]

/-- Key linear algebra lemma: if every kernel vector has zero K-value, then K is in span of L.

This is a standard result from finite-dimensional linear algebra, essentially the dual
statement of: "a functional that vanishes on the intersection of hyperplanes must be
a linear combination of the hyperplane functionals".

Proof sketch:
- Suppose K ∉ span{L_i}
- Then ∃v such that K(v) = 1 but ⟨span{L_i}, v⟩ = 0 (by Hahn-Banach or finite-dim duality)
- This means L_i(v) = 0 for all i, so v ∈ ⋂ ker(L_i)
- But then v ∈ ker(K) by assumption, so K(v) = 0, contradiction

In Lean, this requires either:
1. Finding the appropriate lemma in mathlib's LinearAlgebra.Dual or Module.Dual
2. Proving it using quotient spaces and dimension counting
3. Using Hahn-Banach-style separation (for finite dims, this is constructive)

For now, we note this as a standard linear algebra fact used in KKT/Lagrange multiplier theory.
-/
lemma mem_span_of_iInf_ker_le_ker {ι α : Type*} [Fintype ι] [AddCommGroup α] [Module ℝ α]
    (L : ι → α →ₗ[ℝ] ℝ) (K : α →ₗ[ℝ] ℝ)
    (h : (⨅ i, LinearMap.ker (L i)) ≤ LinearMap.ker K) :
    K ∈ Submodule.span ℝ (Set.range L) := by
  classical
  -- Step 1: K vanishes on ⨅ ker(L i), so K ∈ dualAnnihilator of that intersection
  have hK_mem_ann : K ∈ (⨅ i, LinearMap.ker (L i)).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro v hv
    exact h hv
  -- Step 2: By dualAnnihilator_iInf_eq, this equals ⨆ i, (ker L_i).dualAnnihilator
  have hK_mem_sup : K ∈ ⨆ i : ι, (LinearMap.ker (L i)).dualAnnihilator := by
    rw [← Subspace.dualAnnihilator_iInf_eq (fun i => LinearMap.ker (L i))]
    exact hK_mem_ann
  -- Step 3: For each L i, (ker L_i).dualAnnihilator = range(L_i.dualMap)
  have hAnn_eq_range : ∀ i : ι, (LinearMap.ker (L i)).dualAnnihilator =
      LinearMap.range (L i).dualMap := by
    intro i
    exact (LinearMap.range_dualMap_eq_dualAnnihilator_ker (L i)).symm
  -- Step 4: Show that range(L.dualMap) = span{L} for a functional L : α → ℝ
  -- For L : α → ℝ, L.dualMap : Dual ℝ ℝ → Dual ℝ α
  -- Dual ℝ ℝ is 1-dimensional (≅ ℝ), and L.dualMap(id) = L
  -- So range(L.dualMap) = ℝ ∙ L = span{L}
  have hRange_eq_span : ∀ i : ι, LinearMap.range (L i).dualMap = ℝ ∙ L i := by
    intro i
    ext φ
    constructor
    · rintro ⟨ψ, hψ⟩
      -- ψ : Dual ℝ ℝ = ℝ →ₗ[ℝ] ℝ, so ψ = c • id for some c
      -- Then L.dualMap(ψ) = c • L
      have hψ_scalar : ψ = (ψ 1) • LinearMap.id := by
        apply LinearMap.ext
        intro y
        simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
        have h2 : ψ (y * 1) = y * ψ 1 := by
          have := ψ.map_smul y (1 : ℝ)
          simp only [smul_eq_mul] at this ⊢
          exact this
        simp only [mul_one] at h2
        linarith
      rw [Submodule.mem_span_singleton]
      use ψ 1
      rw [hψ_scalar] at hψ
      ext v
      simp only [LinearMap.smul_apply, smul_eq_mul]
      have hφ_eq : φ = (L i).dualMap ((ψ 1) • LinearMap.id) := hψ.symm
      rw [hφ_eq]
      simp only [LinearMap.dualMap_apply, LinearMap.smul_apply, LinearMap.id_apply,
        LinearMap.comp_apply, smul_eq_mul]
    · intro hφ
      rw [Submodule.mem_span_singleton] at hφ
      obtain ⟨c, hc⟩ := hφ
      -- φ = c • L i, so φ = L.dualMap(c • id)
      use c • LinearMap.id
      rw [← hc]
      apply LinearMap.ext
      intro v
      simp only [LinearMap.dualMap_apply, LinearMap.smul_apply, LinearMap.id_apply,
        LinearMap.comp_apply, smul_eq_mul]
  -- Step 5: Now show ⨆ i, (ℝ ∙ L i) = span(range L)
  have hSup_span : ⨆ i : ι, (ℝ ∙ L i) = Submodule.span ℝ (Set.range L) := by
    simp only [← Submodule.span_range_eq_iSup]
  -- Step 6: Combine everything
  simp only [← hRange_eq_span, ← hAnn_eq_range] at hK_mem_sup
  simp only [hAnn_eq_range, hRange_eq_span, hSup_span] at hK_mem_sup
  exact hK_mem_sup

/-! ### Forward Direction: Minimizer → Stationary

This direction is pure linear algebra and works for any d/g pair.
The proof follows the same structure as the KL case.
-/

/-! ### Backward Direction: Stationary → Minimizer

This direction requires additional structure on d. We use convexity:
for a convex objective with linear constraints, the KKT first-order conditions
(StationaryEV) are sufficient for global optimality.

Key insight: If g(q_i, p_i) = β + ∑_k λ_k c_{ki}, then the gradient is perpendicular
to all feasible directions. Combined with convexity, this implies q is a global minimizer.
-/

/-- Convexity condition: d(·, p) is convex on (0,1) for each fixed p. -/
def IsConvexInFirstArg (d : ℝ → ℝ → ℝ) : Prop :=
  ∀ p : ℝ, ConvexOn ℝ (Set.Ioi 0) (fun q => d q p)

theorem isMinimizer_ofAtom_of_stationaryEV_convex {n : ℕ}
    (d g : ℝ → ℝ → ℝ)
    (hConvex : IsConvexInFirstArg d)
    (hAntideriv : IsAntiderivative d g)
    (p : ProbDist n) (hp : ∀ i, 0 < p.p i)
    (cs : EVConstraintSet n)
    (q : ProbDist n) (hq : q ∈ toConstraintSet cs)
    (hqPos : ∀ i, 0 < q.p i)
    (hstat : StationaryEV g p q cs)
    -- Additional assumption: we only consider strictly positive competitors
    -- (This is the natural regime for divergence-like objectives)
    (hPosCompetitors : ∀ q' : ProbDist n, q' ∈ toConstraintSet cs → ∀ i, 0 < q'.p i) :
    IsMinimizer (ofAtom d) p (toConstraintSet cs) q := by
  refine ⟨hq, ?_⟩
  intro q' hq'
  have hq'Pos : ∀ i, 0 < q'.p i := hPosCompetitors q' hq'
  -- Strategy: Use first-order convexity condition
  -- For convex f, f(y) ≥ f(x) + ∇f(x)·(y-x)
  -- In our case: ∑ d(q'_i, p_i) ≥ ∑ d(q_i, p_i) + ∑ g(q_i, p_i)·(q'_i - q_i)
  -- We'll show the gradient term vanishes due to StationaryEV + feasibility

  -- Extract the Lagrange multipliers from StationaryEV
  rcases hstat with ⟨β, lam, hβ⟩

  -- Show gradient is perpendicular to feasible direction q' - q
  have hgrad_perp : ∑ i : Fin n, g (q.p i) (p.p i) * (q'.p i - q.p i) = 0 := by
    -- Expand using StationaryEV: g(q_i, p_i) = β + ∑_k λ_k c_{ki}
    calc
      (∑ i : Fin n, g (q.p i) (p.p i) * (q'.p i - q.p i))
          = ∑ i : Fin n, (β + ∑ k : Fin cs.length, lam k * (cs.get k).coeff i) * (q'.p i - q.p i) := by
            congr 1; ext i; rw [hβ i]
        _ = β * (∑ i : Fin n, (q'.p i - q.p i)) +
              (∑ k : Fin cs.length, lam k * (∑ i : Fin n, (cs.get k).coeff i * (q'.p i - q.p i))) := by
            -- The key algebraic identity is:
            -- ∑_i (β + ∑_k λ_k c_{ki}) * Δ_i = β * (∑_i Δ_i) + ∑_k λ_k * (∑_i c_{ki} * Δ_i)
            -- where Δ_i = q'_i - q_i
            -- This is just distributivity + sum interchange
            have h_expand :
                ∑ i : Fin n, (β + ∑ k : Fin cs.length, lam k * (cs.get k).coeff i) * (q'.p i - q.p i) =
                  ∑ i : Fin n, (β * (q'.p i - q.p i) + (∑ k : Fin cs.length, lam k * (cs.get k).coeff i) * (q'.p i - q.p i)) := by
              congr 1; ext i; ring
            have h_split :
                ∑ i : Fin n, (β * (q'.p i - q.p i) + (∑ k : Fin cs.length, lam k * (cs.get k).coeff i) * (q'.p i - q.p i)) =
                  (∑ i : Fin n, β * (q'.p i - q.p i)) + (∑ i : Fin n, (∑ k : Fin cs.length, lam k * (cs.get k).coeff i) * (q'.p i - q.p i)) := by
              rw [← Finset.sum_add_distrib]
            rw [h_expand, h_split]
            congr 1
            · rw [← Finset.mul_sum]
            · -- Interchange sums: ∑_i ∑_k f(i,k) = ∑_k ∑_i f(i,k)
              -- LHS: ∑_i [(∑_k λ_k * c_{ki}) * Δ_i] = ∑_i ∑_k [λ_k * c_{ki} * Δ_i]
              -- RHS: ∑_k [λ_k * (∑_i c_{ki} * Δ_i)] = ∑_k ∑_i [λ_k * c_{ki} * Δ_i]
              calc
                (∑ i : Fin n, (∑ k : Fin cs.length, lam k * (cs.get k).coeff i) * (q'.p i - q.p i))
                    = ∑ i : Fin n, ∑ k : Fin cs.length, (lam k * (cs.get k).coeff i) * (q'.p i - q.p i) := by
                      congr 1; ext i; rw [Finset.sum_mul]
                  _ = ∑ i : Fin n, ∑ k : Fin cs.length, lam k * ((cs.get k).coeff i * (q'.p i - q.p i)) := by
                      congr 1; ext i; congr 1; ext k; ring
                  _ = ∑ k : Fin cs.length, ∑ i : Fin n, lam k * ((cs.get k).coeff i * (q'.p i - q.p i)) := by
                      exact Finset.sum_comm
                  _ = ∑ k : Fin cs.length, lam k * (∑ i : Fin n, (cs.get k).coeff i * (q'.p i - q.p i)) := by
                      congr 1; ext k; rw [← Finset.mul_sum]
        _ = β * 0 + (∑ k : Fin cs.length, lam k * 0) := by
            congr 1
            · -- ∑(q'_i - q_i) = ∑ q'_i - ∑ q_i = 1 - 1 = 0
              have hsum_q' : ∑ i : Fin n, q'.p i = 1 := q'.sum_one
              have hsum_q : ∑ i : Fin n, q.p i = 1 := q.sum_one
              simp only [Finset.sum_sub_distrib]
              rw [hsum_q', hsum_q]
              ring
            · -- For each constraint k: ∑ c_{ki}·(q'_i - q_i) = rhs_k - rhs_k = 0
              apply Finset.sum_congr rfl
              intro k _
              have hq_sat : satisfiesSet cs q := (mem_toConstraintSet cs q).1 hq
              have hq'_sat : satisfiesSet cs q' := (mem_toConstraintSet cs q').1 hq'
              have hk : satisfies (cs.get k) q := hq_sat (cs.get k) (List.get_mem cs k)
              have hk' : satisfies (cs.get k) q' := hq'_sat (cs.get k) (List.get_mem cs k)
              simp only [satisfies] at hk hk'
              calc
                lam k * (∑ i : Fin n, (cs.get k).coeff i * (q'.p i - q.p i))
                    = lam k * ((∑ i : Fin n, (cs.get k).coeff i * q'.p i) -
                        (∑ i : Fin n, (cs.get k).coeff i * q.p i)) := by
                      congr 1
                      simp only [mul_sub, Finset.sum_sub_distrib]
                  _ = lam k * ((cs.get k).rhs - (cs.get k).rhs) := by
                      have h1 : ∑ i : Fin n, (cs.get k).coeff i * q'.p i = (cs.get k).rhs := by
                        calc ∑ i : Fin n, (cs.get k).coeff i * q'.p i
                            = ∑ i : Fin n, q'.p i * (cs.get k).coeff i := by
                              congr 1; ext i; ring
                          _ = (cs.get k).rhs := hk'
                      have h2 : ∑ i : Fin n, (cs.get k).coeff i * q.p i = (cs.get k).rhs := by
                        calc ∑ i : Fin n, (cs.get k).coeff i * q.p i
                            = ∑ i : Fin n, q.p i * (cs.get k).coeff i := by
                              congr 1; ext i; ring
                          _ = (cs.get k).rhs := hk
                      rw [h1, h2]
                  _ = lam k * 0 := by ring
        _ = 0 := by simp

  -- Apply convexity: d(q'_i, p_i) ≥ d(q_i, p_i) + g(q_i, p_i)·(q'_i - q_i)
  have hconvex_i : ∀ i : Fin n, d (q'.p i) (p.p i) ≥ d (q.p i) (p.p i) + g (q.p i) (p.p i) * (q'.p i - q.p i) := by
    intro i
    -- This follows from convexity + g being the derivative
    -- For a differentiable convex function: f(y) - f(x) ≥ f'(x)·(y-x)
    have hqi_pos : 0 < q.p i := hqPos i
    have hqi'_pos : 0 < q'.p i := hq'Pos i
    have hconvex_pi : ConvexOn ℝ (Set.Ioi 0) (fun t => d t (p.p i)) := hConvex (p.p i)
    have hderiv : HasDerivAt (fun t => d t (p.p i)) (g (q.p i) (p.p i)) (q.p i) :=
      hAntideriv (q.p i) (p.p i)
    -- Need to show: d(q'_i, p_i) ≥ d(q_i, p_i) + g(q_i, p_i) * (q'_i - q_i)
    -- This is the first-order necessary condition for convex functions
    have hqi_mem : q.p i ∈ Set.Ioi (0 : ℝ) := hqi_pos
    have hqi'_mem : q'.p i ∈ Set.Ioi (0 : ℝ) := hqi'_pos
    -- The key is: for a convex f and any x, y in the domain,
    -- if f has derivative f'(x) at x, then f(y) - f(x) ≥ f'(x) * (y - x)
    -- This should be provable using slope analysis
    have hdiff_nonneg : d (q'.p i) (p.p i) - d (q.p i) (p.p i) ≥ g (q.p i) (p.p i) * (q'.p i - q.p i) := by
      -- First-order condition for convex functions: f(y) - f(x) ≥ f'(x) * (y - x)
      -- Uses ConvexOn.deriv_le_slope and ConvexOn.slope_le_deriv from mathlib
      by_cases heq : q.p i = q'.p i
      · simp [heq]
      · rcases Ne.lt_or_lt heq with hlt | hgt
        · -- Case: q.p i < q'.p i
          -- ConvexOn.deriv_le_slope: deriv f x ≤ slope f x y when x < y
          have hSlope := ConvexOn.deriv_le_slope hconvex_pi hqi_mem hqi'_mem hlt hderiv.differentiableAt
          have hPosDiff : 0 < q'.p i - q.p i := sub_pos.mpr hlt
          have hne : q'.p i - q.p i ≠ 0 := ne_of_gt hPosDiff
          -- Multiply by (y - x) > 0: deriv f x * (y - x) ≤ slope f x y * (y - x)
          have hmul := mul_le_mul_of_nonneg_right hSlope (le_of_lt hPosDiff)
          -- slope f x y * (y - x) = f y - f x (use slope_def_field)
          rw [slope_def_field, div_mul_cancel₀ _ hne] at hmul
          rw [hderiv.deriv] at hmul
          linarith
        · -- Case: q'.p i < q.p i
          -- ConvexOn.slope_le_deriv: slope f x y ≤ deriv f y when x < y
          have hSlope := ConvexOn.slope_le_deriv hconvex_pi hqi'_mem hqi_mem hgt hderiv.differentiableAt
          have hPosDiff : 0 < q.p i - q'.p i := sub_pos.mpr hgt
          have hne : q.p i - q'.p i ≠ 0 := ne_of_gt hPosDiff
          -- Multiply by (y - x) > 0: slope f x y * (y - x) ≤ deriv f y * (y - x)
          have hmul := mul_le_mul_of_nonneg_right hSlope (le_of_lt hPosDiff)
          rw [slope_def_field, div_mul_cancel₀ _ hne] at hmul
          rw [hderiv.deriv] at hmul
          -- hmul: d (q.p i) (p.p i) - d (q'.p i) (p.p i) ≤ g (q.p i) (p.p i) * (q.p i - q'.p i)
          -- Need: d (q'.p i) (p.p i) - d (q.p i) (p.p i) ≥ g (q.p i) (p.p i) * (q'.p i - q.p i)
          linarith
    linarith

  -- Sum over all coordinates
  calc
    (∑ i : Fin n, d (q'.p i) (p.p i))
        ≥ (∑ i : Fin n, (d (q.p i) (p.p i) + g (q.p i) (p.p i) * (q'.p i - q.p i))) := by
          apply Finset.sum_le_sum
          intro i _
          exact hconvex_i i
      _ = (∑ i : Fin n, d (q.p i) (p.p i)) + (∑ i : Fin n, g (q.p i) (p.p i) * (q'.p i - q.p i)) := by
          simp only [Finset.sum_add_distrib]
      _ = (∑ i : Fin n, d (q.p i) (p.p i)) + 0 := by rw [hgrad_perp]
      _ = (∑ i : Fin n, d (q.p i) (p.p i)) := by ring

theorem stationaryEV_of_isMinimizer_ofAtom_general {n : ℕ}
    (d g : ℝ → ℝ → ℝ)
    (hAntideriv : IsAntiderivative d g)
    (p : ProbDist n) (hp : ∀ i, 0 < p.p i)
    (cs : EVConstraintSet n)
    (q : ProbDist n) (hq : q ∈ toConstraintSet cs)
    (hqPos : ∀ i, 0 < q.p i)
    (hmin : IsMinimizer (ofAtom d) p (toConstraintSet cs) q) :
    StationaryEV g p q cs := by
  classical
  -- Let `K` be the gradient linear form at `q`, and `L` the family of constraint linear forms.
  let K : (Fin n → ℝ) →ₗ[ℝ] ℝ := gradAt_general g p q
  let L : Option (Fin cs.length) → (Fin n → ℝ) →ₗ[ℝ] ℝ := constraintForm_general (n := n) cs
  -- Show: every direction that preserves all constraints has zero first-order change.
  have hKer : (⨅ o, LinearMap.ker (L o)) ≤ LinearMap.ker K := by
    intro v hv
    -- Define the 1D perturbation curve.
    let qLine : ℝ → (Fin n → ℝ) := fun t => fun i => q.p i + t * v i
    let φLine : ℝ → ℝ := fun t => ∑ i : Fin n, d (qLine t i) (p.p i)
    have hsumv : (∑ i : Fin n, v i) = 0 := by
      have hv0 : v ∈ LinearMap.ker (L none) := (Submodule.mem_iInf _).1 hv none
      have : L none v = 0 := hv0
      simpa [L, constraintForm_general_none_apply] using this
    have hvCoeff : ∀ k : Fin cs.length, (∑ i : Fin n, v i * (cs.get k).coeff i) = 0 := by
      intro k
      have hvk : v ∈ LinearMap.ker (L (some k)) := (Submodule.mem_iInf _).1 hv (some k)
      have : L (some k) v = 0 := hvk
      simpa [L, constraintForm_general_some_apply] using this
    -- Show `φLine` has a local minimum at `0` using positivity + global optimality.
    have hpos : ∀ᶠ t in nhds (0 : ℝ), ∀ i : Fin n, 0 < qLine t i := by
      -- Coordinatewise positivity persists for small `t`; use finiteness to combine.
      have hpos_i : ∀ i : Fin n, ∀ᶠ t in nhds (0 : ℝ), 0 < qLine t i := by
        intro i
        have hcont : Continuous (fun t : ℝ => qLine t i) := by
          simpa [qLine] using (continuous_const.add (continuous_id.mul continuous_const))
        have h0 : 0 < qLine 0 i := by simpa [qLine] using hqPos i
        have : ∀ᶠ t in nhds (0 : ℝ), qLine t i ∈ Set.Ioi (0 : ℝ) :=
          hcont.continuousAt.eventually (IsOpen.mem_nhds isOpen_Ioi h0)
        simpa [Set.mem_Ioi] using this
      simpa using (Filter.eventually_all.2 hpos_i)
    have hloc : IsLocalMin φLine 0 := by
      refine (hpos.mono ?_)
      intro t htpos
      have ht_nonneg : ∀ i, 0 ≤ qLine t i := fun i => le_of_lt (htpos i)
      have ht_sum : (∑ i : Fin n, qLine t i) = 1 := by
        calc
          (∑ i : Fin n, qLine t i) = (∑ i : Fin n, q.p i) + t * (∑ i : Fin n, v i) := by
            simp [qLine, Finset.sum_add_distrib, Finset.mul_sum, mul_add, add_assoc, add_left_comm,
              add_comm, mul_assoc]
          _ = 1 + t * (∑ i : Fin n, v i) := by simpa [q.sum_one]
          _ = 1 := by simpa [hsumv]
      let qT : ProbDist n :=
        { p := fun i => qLine t i
          nonneg := ht_nonneg
          sum_one := ht_sum }
      have hqT_mem : qT ∈ toConstraintSet cs := by
        have hq_sat : satisfiesSet cs q := (mem_toConstraintSet cs q).1 hq
        have hsat : satisfiesSet cs qT := by
          intro c hc
          obtain ⟨k, rfl⟩ := List.get_of_mem hc
          have hk : (∑ i : Fin n, v i * (cs.get k).coeff i) = 0 := hvCoeff k
          have hqk : satisfies (cs.get k) q := hq_sat (cs.get k) (List.get_mem cs k)
          dsimp [satisfies] at hqk ⊢
          calc
            (∑ i : Fin n, qT.p i * (cs.get k).coeff i)
                = (∑ i : Fin n, q.p i * (cs.get k).coeff i) +
                    t * (∑ i : Fin n, v i * (cs.get k).coeff i) := by
                      simp [qT, qLine, Finset.sum_add_distrib, Finset.mul_sum, mul_add, add_assoc,
                        add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm, add_mul]
            _ = (cs.get k).rhs + t * (∑ i : Fin n, v i * (cs.get k).coeff i) := by
              simpa [hqk, add_assoc, add_left_comm, add_comm]
            _ = (cs.get k).rhs + t * 0 := by
              simpa using congrArg (fun s => (cs.get k).rhs + t * s) hk
            _ = (cs.get k).rhs := by simp
        exact (mem_toConstraintSet cs qT).2 hsat
      have hle := hmin.2 qT hqT_mem
      have h0 : φLine 0 = ∑ i : Fin n, d (q.p i) (p.p i) := by simp [φLine, qLine]
      have ht : φLine t = ∑ i : Fin n, d (qT.p i) (p.p i) := by simp [φLine, qLine, qT]
      simpa [ofAtom, h0, ht] using hle
    -- Differentiate `φLine` at `0`.
    have hderiv_i : ∀ i : Fin n,
        HasDerivAt (fun t : ℝ => d (qLine t i) (p.p i))
          (v i * g (q.p i) (p.p i)) 0 := by
      intro i
      have hAff : HasDerivAt (fun t : ℝ => qLine t i) (v i) 0 := by
        have ht : HasDerivAt (fun t : ℝ => t * v i) (v i) 0 := by
          simpa using (hasDerivAt_id (0 : ℝ)).mul_const (v i)
        simpa [qLine] using ht.const_add (q.p i)
      have hd : HasDerivAt (fun x => d x (p.p i)) (g (q.p i) (p.p i)) (q.p i) :=
        hAntideriv (q.p i) (p.p i)
      have hd' : HasDerivAt (fun x => d x (p.p i)) (g (q.p i) (p.p i)) (qLine 0 i) := by
        simpa [qLine] using hd
      have hcomp := hd'.comp (0 : ℝ) hAff
      -- hcomp has type: HasDerivAt ((fun x => d x (p.p i)) ∘ qLine · i) (g(q_i,p_i) * v_i) 0
      -- We need: HasDerivAt (fun t => d (qLine t i) (p.p i)) (v_i * g(q_i,p_i)) 0
      have : g (q.p i) (p.p i) * v i = v i * g (q.p i) (p.p i) := mul_comm _ _
      rw [← this]
      simpa [Function.comp, qLine] using hcomp
    have hderiv :
        HasDerivAt φLine (∑ i : Fin n, v i * g (q.p i) (p.p i)) 0 := by
      simpa [φLine] using
        (HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n)))
          (A := fun i : Fin n => fun t : ℝ => d (qLine t i) (p.p i))
          (A' := fun i : Fin n => v i * g (q.p i) (p.p i))
          (x := (0 : ℝ))
          (by intro i _; simpa using hderiv_i i))
    -- Fermat: local min implies derivative 0.
    have hderiv0 : (∑ i : Fin n, v i * g (q.p i) (p.p i)) = 0 := by
      exact hloc.hasDerivAt_eq_zero hderiv
    -- This is exactly the membership in `ker K`, accounting for the normalization term.
    have : K v = 0 := by
      simp only [K, gradAt_general, LinearMap.coe_mk, AddHom.coe_mk]
      -- Need to show: ∑ i, v_i * (g_i + 1) = 0
      -- Expand: ∑ (v_i * g_i + v_i) = ∑ v_i * g_i + ∑ v_i = 0 + 0 = 0
      have h1 : (∑ i : Fin n, v i * (g (q.p i) (p.p i) + 1)) =
                (∑ i : Fin n, (v i * g (q.p i) (p.p i) + v i)) := by
        congr 1; ext i; ring
      have h2 : (∑ i : Fin n, (v i * g (q.p i) (p.p i) + v i)) =
                (∑ i : Fin n, v i * g (q.p i) (p.p i)) + (∑ i : Fin n, v i) := by
        simp only [Finset.sum_add_distrib]
      rw [h1, h2, hderiv0, hsumv]
      norm_num
    exact this

  -- Use linear algebra: `K` lies in the span of the constraint forms.
  have hKspan : K ∈ Submodule.span ℝ (Set.range L) :=
    mem_span_of_iInf_ker_le_ker (L := L) (K := K) hKer
  -- Extract coefficients `c`.
  rcases (Submodule.mem_span_range_iff_exists_fun ℝ).1 hKspan with ⟨c, hc⟩
  -- Use `c` to build the StationaryEV witness.
  refine ⟨c none - 1, fun k => c (some k), ?_⟩
  intro i
  -- Evaluate the linear identity `hc` on the basis vector `e_i`.
  have hci :=
    congrArg (fun (K' : (Fin n → ℝ) →ₗ[ℝ] ℝ) => K' (Pi.single i (1 : ℝ) : Fin n → ℝ)) hc
  -- Compute both sides.
  have hK : K (Pi.single i (1 : ℝ) : Fin n → ℝ) = g (q.p i) (p.p i) + 1 := by
    simpa using gradAt_general_apply_single g p q i
  have hL :
      (∑ o : Option (Fin cs.length), c o • L o) (Pi.single i (1 : ℝ) : Fin n → ℝ) =
        c none * 1 + ∑ k : Fin cs.length, c (some k) * (cs.get k).coeff i := by
    classical
    have hsum :
        (∑ o : Option (Fin cs.length), c o • L o) (Pi.single i (1 : ℝ) : Fin n → ℝ) =
          c none * (L none (Pi.single i (1 : ℝ) : Fin n → ℝ)) +
            ∑ k : Fin cs.length, c (some k) * (L (some k) (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
      simp [Fintype.sum_option, Finset.sum_apply, LinearMap.smul_apply, mul_assoc]
    have hnone : L none (Pi.single i (1 : ℝ) : Fin n → ℝ) = 1 := by
      simpa [L] using constraintForm_general_apply_single_none (cs := cs) i
    have hsome : ∀ k : Fin cs.length, L (some k) (Pi.single i (1 : ℝ) : Fin n → ℝ) = (cs.get k).coeff i := by
      intro k
      simpa [L] using constraintForm_general_apply_single_some (cs := cs) k i
    simp [hsum, hnone, hsome, mul_assoc, mul_left_comm, mul_comm, add_assoc]
  have : g (q.p i) (p.p i) + 1 = c none * 1 + ∑ k : Fin cs.length, c (some k) * (cs.get k).coeff i := by
    calc
      g (q.p i) (p.p i) + 1 = K (Pi.single i (1 : ℝ) : Fin n → ℝ) := by simpa using hK.symm
      _ = (∑ o : Option (Fin cs.length), c o • L o) (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
        simpa using hci.symm
      _ = c none * 1 + ∑ k : Fin cs.length, c (some k) * (cs.get k).coeff i := hL
  linarith

/-- The key lemma: if d is an antiderivative of g, then StationaryEV g characterizes
    minimizers of ofAtom d on the positive simplex.

    This follows from the KKT conditions for constrained optimization:
    - For a sum-form objective ∑_i d(q_i, p_i), the gradient is ∂d/∂q(q_i, p_i)
    - At a constrained minimum, gradient = λ₀ + ∑_k λ_k (constraint coefficients)
    - This is exactly the StationaryEV condition for g = ∂d/∂q
-/
theorem stationaryEV_iff_minimizer_ofAtom
    (d g : ℝ → ℝ → ℝ) (hAntideriv : IsAntiderivative d g)
    {n : ℕ} (p : ProbDist n) (hp : ∀ i, 0 < p.p i)
    (cs : EVConstraintSet n) (q : ProbDist n)
    (hq_mem : q ∈ toConstraintSet cs) (hq_pos : ∀ i, 0 < q.p i)
    -- Convexity: d(·, p) is convex for each fixed p
    (hConvex : IsConvexInFirstArg d)
    -- Positivity of competitors: all feasible points are strictly positive
    (hPosCompetitors : ∀ q' : ProbDist n, q' ∈ toConstraintSet cs → ∀ i, 0 < q'.p i)
    : StationaryEV g p q cs ↔ IsMinimizer (ofAtom d) p (toConstraintSet cs) q := by
  constructor
  · -- Forward: StationaryEV → IsMinimizer (using convexity)
    intro hstat
    exact isMinimizer_ofAtom_of_stationaryEV_convex d g hConvex hAntideriv p hp cs q hq_mem hq_pos hstat hPosCompetitors
  · -- Backward: IsMinimizer → StationaryEV
    intro hmin
    exact stationaryEV_of_isMinimizer_ofAtom_general d g hAntideriv p hp cs q hq_mem hq_pos hmin

open ShoreJohnsonGradientSeparability in
/-- **Shore-Johnson Theorem I (from gradient representation)**: If we have a gradient
representation for F with an antiderivative d having appropriate regularity, we can derive
that F and ofAtom d agree on positive minimizers.

The key assumptions are:
- `hStat`: StationaryEV gr.g characterizes minimizers of F (on positive distributions)
- `d` is an antiderivative of gr.g
- `d` is convex in first argument (needed for KKT sufficiency)
- All feasible distributions are strictly positive (natural for divergence objectives)
-/
theorem shore_johnson_theorem_I_from_grad_rep
    (I : InferenceMethod) (F : ObjectiveFunctional)
    (_hSJ : ShoreJohnsonAxioms I)
    (_hRealize : RealizesEV I F)
    (gr : ShoreJohnsonGradientSeparability.GradientRepresentation F)
    (d : ℝ → ℝ → ℝ)
    (hAntideriv : IsAntiderivative d gr.g)
    (hConvex : IsConvexInFirstArg d)
    (hStat : ∀ {n : ℕ} (p : ProbDist n) (hp : ∀ i, 0 < p.p i)
        (cs : EVConstraintSet n) (q : ProbDist n),
        q ∈ toConstraintSet cs → (∀ i, 0 < q.p i) →
        (StationaryEV gr.g p q cs ↔ IsMinimizer F p (toConstraintSet cs) q))
    (hPosCompetitors : ∀ {n : ℕ} (cs : EVConstraintSet n) (q' : ProbDist n),
        q' ∈ toConstraintSet cs → ∀ i, 0 < q'.p i) :
    ∀ {n : ℕ} (p : ProbDist n) (cs : EVConstraintSet n),
      (∀ i, 0 < p.p i) →
      {q | (∀ i, 0 < q.p i) ∧ IsMinimizer F p (toConstraintSet cs) q} =
      {q | (∀ i, 0 < q.p i) ∧ IsMinimizer (ofAtom d) p (toConstraintSet cs) q} := by
  intro n p cs hp
  ext q
  constructor
  · -- F minimizer → ofAtom d minimizer
    intro ⟨hqpos, hqmin⟩
    refine ⟨hqpos, ?_⟩
    have hqmem : q ∈ toConstraintSet cs := hqmin.1
    -- F min → StationaryEV (by hStat backward)
    have hStatEV : StationaryEV gr.g p q cs := (hStat p hp cs q hqmem hqpos).2 hqmin
    -- StationaryEV → ofAtom d min (by stationaryEV_iff_minimizer_ofAtom forward)
    exact (stationaryEV_iff_minimizer_ofAtom d gr.g hAntideriv p hp cs q hqmem hqpos
      hConvex (hPosCompetitors cs)).1 hStatEV
  · -- ofAtom d minimizer → F minimizer
    intro ⟨hqpos, hqmin⟩
    refine ⟨hqpos, ?_⟩
    have hqmem : q ∈ toConstraintSet cs := hqmin.1
    -- ofAtom d min → StationaryEV (by stationaryEV_iff_minimizer_ofAtom backward)
    have hStatEV : StationaryEV gr.g p q cs :=
      (stationaryEV_iff_minimizer_ofAtom d gr.g hAntideriv p hp cs q hqmem hqpos
        hConvex (hPosCompetitors cs)).2 hqmin
    -- StationaryEV → F min (by hStat forward)
    exact (hStat p hp cs q hqmem hqpos).1 hStatEV

/-- **Shore-Johnson Theorem I (full version with explicit gap)**: An inference operator
satisfying SJ1-SJ3, realized by a regular objective F, must have F equivalent to a sum-form
objective on EV constraint sets.

**GAP**: The derivation of `GradientRepresentation` from `TheoremIRegularity` + SJ axioms
is not formalized. This is the mathematical content of Shore-Johnson's Appendix proof.

The infrastructure is in `ShoreJohnsonGradientSeparability.lean`. The remaining steps are:
1. Prove `deriv_symmetric_under_swap` (chain rule + `shift2_swap`)
2. Prove `exists_gradient_representation` (use SJ3 to construct g)
3. Fill in the stationarity characterization
-/
theorem shore_johnson_theorem_I
    (I : InferenceMethod) (F : ObjectiveFunctional)
    (hSJ : ShoreJohnsonAxioms I)
    (hRealize : RealizesEV I F)
    (hReg : TheoremIRegularity F) :
    ∃ d : ℝ → ℝ → ℝ, ObjEquivEV F (ofAtom d) := by
  -- PROOF SKETCH using new infrastructure:
  --
  -- 1. Build ExtractGRegularity from TheoremIRegularity:
  --    have hExtract : ExtractGRegularity F := ⟨hReg.has_shift2_deriv, ...⟩
  --
  -- 2. Use exists_gradient_representation to get GradientRepresentation:
  --    have ⟨gr, _⟩ := exists_gradient_representation I F hSJ hRealize hExtract
  --
  -- 3. Use gradient_rep_to_appendix_assumptions to get SJAppendixAssumptions:
  --    have hApp := gradient_rep_to_appendix_assumptions F d gr ...
  --
  -- 4. Apply shore_johnson_theorem_I_ObjEquivEV_pos with hApp
  --
  -- For now, we document this structure rather than hiding it.
  sorry

end Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnsonTheoremI
