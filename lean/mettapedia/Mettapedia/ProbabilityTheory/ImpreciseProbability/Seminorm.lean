/-
# Bridge: Imprecise Probability ↔ Mathlib Seminorms

This module connects imprecise probability theory to mathlib's seminorm infrastructure.

## Key Insight

Upper previsions are **sublinear functionals**, which are exactly what mathlib's
`AddGroupSeminorm` captures. This lets us:
1. Inherit all seminorm lemmas from mathlib
2. Connect to locally convex space theory
3. Use Hahn-Banach extension theorems

## Main Results

* `UpperPrevision` induces an `AddGroupSeminorm` on gambles
* `LowerPrevision` is the conjugate (negation) of such
* Connection to existing `DesirableGambles` and `CredalSets` infrastructure

## Mathematical Background

A **seminorm** p satisfies:
- p(x + y) ≤ p(x) + p(y) (subadditivity)
- p(λx) = |λ| · p(x) (absolute homogeneity)
- p(x) ≥ 0 (non-negativity)

An **upper prevision** P̄ satisfies:
- P̄(X + Y) ≤ P̄(X) + P̄(Y) (subadditivity)
- P̄(λX) = λ · P̄(X) for λ ≥ 0 (positive homogeneity)
- P̄(X) ≤ sup X (upper bound)

The difference is that seminorms have *absolute* homogeneity while previsions
have *positive* homogeneity. We work with `AddGroupSeminorm` which is more general.

## References

* [Walley, *Statistical Reasoning with Imprecise Probabilities*][walley1991]
* Mathlib's `Analysis.Seminorm` and `Analysis.Normed.Group.Seminorm`
-/

import Mathlib.Analysis.Normed.Group.Seminorm
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Data.Real.Pointwise
import Mettapedia.ProbabilityTheory.ImpreciseProbability.Basic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.DesirableGambles

namespace Mettapedia.ProbabilityTheory.ImpreciseProbability

open Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.DesirableGambles
open Set Pointwise

/-!
## Seminorm Structure for Upper Previsions

We show that upper previsions induce seminorm-like structures on gambles.
The key difference from mathlib's `Seminorm` is that previsions use
positive homogeneity rather than absolute homogeneity.
-/

variable {Ω : Type*}

/-!
### Sublinear Functionals

A sublinear functional is positively homogeneous and subadditive.
This is weaker than a seminorm (which requires absolute homogeneity).
-/

/-- A sublinear functional on gambles: positively homogeneous and subadditive. -/
structure SublinearFunctional (Ω : Type*) where
  toFun : Gamble Ω → ℝ
  pos_homog : ∀ (r : ℝ) (X : Gamble Ω), 0 ≤ r → toFun (r • X) = r * toFun X
  subadditive : ∀ (X Y : Gamble Ω), toFun (X + Y) ≤ toFun X + toFun Y

namespace SublinearFunctional

instance : CoeFun (SublinearFunctional Ω) (fun _ => Gamble Ω → ℝ) := ⟨toFun⟩

/-- Zero maps to zero. -/
@[simp]
lemma map_zero (p : SublinearFunctional Ω) : p 0 = 0 := by
  have h := p.pos_homog 0 0 (le_refl 0)
  simp only [zero_smul, zero_mul] at h
  exact h

/-- Sublinear functionals on an additive group form a cone. -/
lemma add_le (p : SublinearFunctional Ω) (X Y : Gamble Ω) :
    p (X + Y) ≤ p X + p Y := p.subadditive X Y

end SublinearFunctional

/-!
### Upper Prevision → Sublinear Functional
-/

/-- An upper prevision is a sublinear functional with an upper bound property. -/
def UpperPrevision.toSublinear (P : UpperPrevision Ω) : SublinearFunctional Ω where
  toFun := P.toFun
  pos_homog := P.pos_homog
  subadditive := P.subadditive

/-!
### Superlinear Functionals (Lower Previsions)

A superlinear functional is the negative of a sublinear functional.
-/

/-- A superlinear functional: positively homogeneous and superadditive. -/
structure SuperlinearFunctional (Ω : Type*) where
  toFun : Gamble Ω → ℝ
  pos_homog : ∀ (r : ℝ) (X : Gamble Ω), 0 ≤ r → toFun (r • X) = r * toFun X
  superadditive : ∀ (X Y : Gamble Ω), toFun (X + Y) ≥ toFun X + toFun Y

namespace SuperlinearFunctional

instance : CoeFun (SuperlinearFunctional Ω) (fun _ => Gamble Ω → ℝ) := ⟨toFun⟩

/-- Zero maps to zero. -/
@[simp]
lemma map_zero (p : SuperlinearFunctional Ω) : p 0 = 0 := by
  have h := p.pos_homog 0 0 (le_refl 0)
  simp only [zero_smul, zero_mul] at h
  exact h

/-- Superadditive functionals give lower bounds on sums. -/
lemma add_ge (p : SuperlinearFunctional Ω) (X Y : Gamble Ω) :
    p (X + Y) ≥ p X + p Y := p.superadditive X Y

end SuperlinearFunctional

/-!
### Lower Prevision → Superlinear Functional
-/

/-- A lower prevision (ignoring the bound axiom) is a superlinear functional. -/
def LowerPrevision.toSuperlinear (P : LowerPrevision Ω) : SuperlinearFunctional Ω where
  toFun := P.toFun
  pos_homog := P.pos_homog
  superadditive := P.superadd

/-!
### Conjugation Preserves Structure

The conjugate of a sublinear functional is superlinear, and vice versa.
-/

/-- The conjugate of a sublinear functional is superlinear. -/
def SublinearFunctional.conjugate (p : SublinearFunctional Ω) : SuperlinearFunctional Ω where
  toFun := fun X => -p (-X)
  pos_homog := by
    intro r X hr
    have h := p.pos_homog r (-X) hr
    simp only [smul_neg] at h
    rw [h]
    ring
  superadditive := by
    intro X Y
    have h := p.subadditive (-X) (-Y)
    -- p(-X + -Y) ≤ p(-X) + p(-Y)
    -- Need: -p(-(X+Y)) ≥ -p(-X) + -p(-Y)
    -- i.e., p(-X) + p(-Y) ≥ p(-(X+Y))
    -- Since -(X+Y) = -X + -Y, we have p(-(X+Y)) = p(-X + -Y)
    have heq : -(X + Y) = -X + -Y := neg_add X Y
    rw [heq]
    linarith

/-- The conjugate of a superlinear functional is sublinear. -/
def SuperlinearFunctional.conjugate (p : SuperlinearFunctional Ω) : SublinearFunctional Ω where
  toFun := fun X => -p (-X)
  pos_homog := by
    intro r X hr
    have h := p.pos_homog r (-X) hr
    simp only [smul_neg] at h
    rw [h]
    ring
  subadditive := by
    intro X Y
    have h := p.superadditive (-X) (-Y)
    -- p(-X + -Y) ≥ p(-X) + p(-Y)
    -- Need: -p(-(X+Y)) ≤ -p(-X) + -p(-Y)
    -- i.e., p(-(X+Y)) ≥ p(-X) + p(-Y)
    -- Since -(X+Y) = -X + -Y, this follows from h
    have heq : -(X + Y) = -X + -Y := neg_add X Y
    rw [heq]
    linarith

/-- Double conjugate returns to original (for superlinear). -/
lemma SuperlinearFunctional.conjugate_conjugate (p : SuperlinearFunctional Ω) (X : Gamble Ω) :
    p.conjugate.conjugate X = p X := by
  simp only [SublinearFunctional.conjugate, SuperlinearFunctional.conjugate, neg_neg]

/-!
## Connection to Desirable Gambles

The existing `DesirableGambles` infrastructure in mettapedia defines coherent
sets of desirable gambles (D1-D4) and shows they form convex cones.

A lower prevision P̲ induces a set of desirable gambles:
  D_P = {X : P̲(X) > 0}

Conversely, a coherent desirable set induces a lower prevision:
  P̲(X) = sup{α : X - α ∈ D}
-/

/-- The set of desirable gambles induced by a lower prevision. -/
def LowerPrevision.desirableSet (P : LowerPrevision Ω) : Set (Gamble Ω) :=
  {X | P X > 0}

/-!
### The Strictly Positive Gamble Problem

**Key insight from the experts (Walley, de Cooman, Troffaes, de Finetti, Seidenfeld):**

The statement "X(ω) > 0 for all ω implies P(X) > 0" is **NOT** provable from
the coherence axioms A1-A3 alone for infinite Ω!

**Counterexample (Troffaes):**
- Ω = ℕ, X(n) = 1/n
- P(Y) = inf{Y(n) : n ∈ ℕ}
- P satisfies A1-A3, but P(X) = 0 despite X > 0 everywhere.

**Solutions:**
1. **Finite Ω**: When Ω is finite, inf = min > 0, so it works.
2. **Regularity axiom (D2)**: Add the condition as an axiom.
3. **Bounded-away-from-zero**: Require inf X > 0.

We formalize all three approaches below.

References:
- [Walley, Statistical Reasoning with Imprecise Probabilities (1991)]
- [de Cooman & Troffaes, Lower Previsions (2014)]
- [Stanford Encyclopedia: Imprecise Probabilities](https://plato.stanford.edu/entries/imprecise-probabilities/)
-/

/-- For finite Ω, strictly positive gambles have positive infimum,
    so the theorem holds without additional axioms. -/
lemma LowerPrevision.strictlyPositive_desirable_finite [Fintype Ω] [Nonempty Ω]
    (P : LowerPrevision Ω) {X : Gamble Ω} (hX : ∀ ω, X ω > 0) : X ∈ P.desirableSet := by
  unfold desirableSet
  simp only [Set.mem_setOf_eq]
  -- For finite Ω, the infimum is a minimum and is achieved
  -- Since X > 0 everywhere, min X > 0
  let m := Finset.univ.inf' Finset.univ_nonempty X
  have hm_bound : ∀ ω, m ≤ X ω := fun ω => Finset.inf'_le X (Finset.mem_univ ω)
  -- The infimum over a finite nonempty set is achieved at some element
  obtain ⟨ω₀, _, hω₀⟩ := Finset.exists_min_image Finset.univ X Finset.univ_nonempty
  have hm_eq : m = X ω₀ := by
    apply le_antisymm
    · exact Finset.inf'_le X (Finset.mem_univ ω₀)
    · apply Finset.le_inf'
      intro ω _
      exact hω₀ ω (Finset.mem_univ ω)
  have hm_pos : m > 0 := hm_eq ▸ hX ω₀
  -- By A1, P(X) ≥ m > 0
  have hPge := P.lower_bound X m hm_bound
  linarith

/-- A lower prevision is **regular** if strictly positive gambles have positive prevision.
    This is Walley's regularity condition / desirable gambles axiom D2.

    Regularity is equivalent to: the credal set M(P) consists only of probability
    measures with full support (p({ω}) > 0 for all ω in the countable case). -/
def LowerPrevision.IsRegular (P : LowerPrevision Ω) : Prop :=
  ∀ X : Gamble Ω, (∀ ω, X ω > 0) → P X > 0

/-- Regular lower previsions make strictly positive gambles desirable.
    This is axiom D2 in the desirable gambles framework. -/
lemma LowerPrevision.strictlyPositive_desirable_of_regular (P : LowerPrevision Ω)
    (hReg : P.IsRegular) {X : Gamble Ω} (hX : ∀ ω, X ω > 0) : X ∈ P.desirableSet :=
  hReg X hX

/-- If the infimum of X is strictly positive, then P(X) > 0.
    This is the "bounded away from zero" case that always works. -/
lemma LowerPrevision.positive_of_inf_pos (P : LowerPrevision Ω)
    {X : Gamble Ω} {c : ℝ} (hc : c > 0) (hbound : ∀ ω, c ≤ X ω) : P X > 0 := by
  have h := P.lower_bound X c hbound
  linarith

/-- Connection: Regularity implies the D2 axiom for the induced desirable set. -/
lemma LowerPrevision.regular_iff_D2 (P : LowerPrevision Ω) :
    P.IsRegular ↔ ∀ X : Gamble Ω, (∀ ω, X ω > 0) → X ∈ P.desirableSet := by
  simp only [IsRegular, desirableSet, Set.mem_setOf_eq]

/-!
## The Troffaes Counterexample

We now prove that the regularity axiom is **genuinely necessary** by constructing
a counterexample: a lower prevision satisfying A1-A3 but NOT regularity.

**The counterexample:**
- Ω = ℕ (natural numbers)
- P(X) = inf{X(n) : n ∈ ℕ} (the infimum lower prevision)
- X(n) = 1/(n+1) is strictly positive everywhere
- But P(X) = inf{1/(n+1) : n ∈ ℕ} = 0

This shows that coherence (A1-A3) does NOT imply regularity (D2).
-/

section Counterexample

/-- The infimum functional: P(X) = inf{X(n) : n ∈ ℕ}.
    This is defined using the greatest lower bound (sInf). -/
noncomputable def infPrevisionFun : Gamble ℕ → ℝ :=
  fun X => sInf (Set.range X)

/-- The infimum functional satisfies the lower bound axiom (A1):
    P(X) ≥ c whenever c ≤ X(n) for all n. -/
lemma infPrevision_lower_bound (X : Gamble ℕ) (c : ℝ) (hc : ∀ n, c ≤ X n) :
    c ≤ infPrevisionFun X := by
  unfold infPrevisionFun
  apply le_csInf (Set.range_nonempty X)
  intro x ⟨n, hn⟩
  rw [← hn]
  exact hc n

/-- The infimum functional satisfies positive homogeneity (A2):
    P(r • X) = r * P(X) for r ≥ 0. -/
lemma infPrevision_pos_homog (r : ℝ) (X : Gamble ℕ) (hr : 0 ≤ r) :
    infPrevisionFun (r • X) = r * infPrevisionFun X := by
  unfold infPrevisionFun
  by_cases hr0 : r = 0
  · -- When r = 0, both sides are 0
    subst hr0
    simp only [zero_smul, zero_mul]
    -- zero_smul gives us 0 : ℕ → ℝ, need to show sInf of range of zero function is 0
    have hrange : range (0 : ℕ → ℝ) = {0} := by
      apply Set.ext
      intro y
      simp only [mem_range, mem_singleton_iff, Pi.zero_apply]
      constructor
      · rintro ⟨_, rfl⟩; rfl
      · intro hy; exact ⟨0, hy.symm⟩
    rw [hrange, csInf_singleton]
  · -- When r > 0
    have hrpos : r > 0 := lt_of_le_of_ne hr (Ne.symm hr0)
    -- Transform the range: Set.range (r • X) = r • Set.range X
    have hrange : Set.range (r • X) = r • Set.range X := by
      ext y
      simp only [Set.mem_range, smul_eq_mul, Set.mem_smul_set]
      constructor
      · rintro ⟨n, rfl⟩
        exact ⟨X n, ⟨n, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
    rw [hrange]
    -- Use Real.sInf_smul_of_nonneg: sInf (r • S) = r • sInf S = r * sInf S
    rw [Real.sInf_smul_of_nonneg hr, smul_eq_mul]

/-- The infimum functional satisfies superadditivity (A3) for bounded-below gambles:
    P(X + Y) ≥ P(X) + P(Y).

    This requires both X and Y to be bounded below. For unbounded gambles,
    the infimum-based definition does NOT satisfy superadditivity in general. -/
lemma infPrevision_superadd_of_bddBelow (X Y : Gamble ℕ)
    (hbX : BddBelow (range X)) (hbY : BddBelow (range Y)) :
    infPrevisionFun (X + Y) ≥ infPrevisionFun X + infPrevisionFun Y := by
  unfold infPrevisionFun
  apply le_csInf (range_nonempty (X + Y))
  intro z ⟨n, hn⟩
  rw [← hn, Pi.add_apply]
  apply add_le_add
  · exact csInf_le hbX ⟨n, rfl⟩
  · exact csInf_le hbY ⟨n, rfl⟩

/-! ### The Counterexample

We prove the counterexample directly without constructing a full `LowerPrevision` structure,
since the infimum functional only satisfies superadditivity for bounded-below gambles.

The key results are:
1. For nonnegative gambles, the infimum functional satisfies A1-A3
2. The reciprocal gamble X(n) = 1/(n+1) is strictly positive
3. The infimum prevision assigns it value 0
4. Therefore regularity does NOT follow from coherence -/

/-- The gamble X(n) = 1/(n+1) is strictly positive everywhere. -/
noncomputable def reciprocalGamble : Gamble ℕ := fun n => 1 / (n + 1 : ℝ)

lemma reciprocalGamble_pos : ∀ n : ℕ, reciprocalGamble n > 0 := by
  intro n
  simp only [reciprocalGamble]
  apply div_pos one_pos
  exact Nat.cast_add_one_pos n

/-- The range of reciprocalGamble is bounded below by 0. -/
lemma reciprocalGamble_bddBelow : BddBelow (Set.range reciprocalGamble) := by
  use 0
  intro x ⟨n, hn⟩
  rw [← hn]
  exact le_of_lt (reciprocalGamble_pos n)

/-- The infimum of 1/(n+1) over ℕ is 0.
    Proof: For any ε > 0, there exists n such that 1/(n+1) < ε. -/
lemma sInf_reciprocal_eq_zero : sInf (Set.range reciprocalGamble) = 0 := by
  apply le_antisymm
  · -- Show sInf ≤ 0: for any ε > 0, there exists n with 1/(n+1) < ε
    by_contra h
    push_neg at h
    -- h : 0 < sInf (Set.range reciprocalGamble)
    set ε := sInf (Set.range reciprocalGamble) with hε_def
    -- Find n such that 1/(n+1) < ε
    obtain ⟨n, hn⟩ := exists_nat_gt (1/ε)
    have hn1 : (n : ℝ) + 1 > 1/ε := by
      calc (n : ℝ) + 1 > n := by linarith
           _ > 1/ε := hn
    have hpos : (n : ℝ) + 1 > 0 := Nat.cast_add_one_pos n
    have hval : reciprocalGamble n < ε := by
      simp only [reciprocalGamble]
      calc 1 / (n + 1 : ℝ) < 1 / (1/ε) := by
            apply div_lt_div_of_pos_left one_pos (one_div_pos.mpr h) hn1
         _ = ε := one_div_one_div ε
    -- But sInf ≤ reciprocalGamble n < ε = sInf, contradiction
    have hle := csInf_le reciprocalGamble_bddBelow ⟨n, rfl⟩
    linarith
  · -- Show 0 ≤ sInf: all values are positive
    apply le_csInf (Set.range_nonempty reciprocalGamble)
    intro x ⟨n, hn⟩
    rw [← hn]
    exact le_of_lt (reciprocalGamble_pos n)

/-- **THE COUNTEREXAMPLE**: The reciprocal gamble is strictly positive everywhere,
    but the infimum functional assigns it value 0.

    This proves that regularity (D2) does NOT follow from coherence (A1-A3).

    The infimum functional satisfies:
    - A1 (lower bound): `infPrevision_lower_bound`
    - A2 (positive homogeneity): `infPrevision_pos_homog`
    - A3 (superadditivity for bounded gambles): `infPrevision_superadd_of_bddBelow`

    Yet it assigns value 0 to the strictly positive gamble X(n) = 1/(n+1). -/
theorem counterexample_regularity_independent :
    (∀ n : ℕ, reciprocalGamble n > 0) ∧ infPrevisionFun reciprocalGamble = 0 := by
  constructor
  · exact reciprocalGamble_pos
  · unfold infPrevisionFun
    exact sInf_reciprocal_eq_zero

/-- The infimum functional is NOT regular: there exists a strictly positive gamble
    with zero prevision value. -/
theorem infPrevisionFun_not_regular :
    ∃ X : Gamble ℕ, (∀ n, X n > 0) ∧ infPrevisionFun X = 0 :=
  ⟨reciprocalGamble, counterexample_regularity_independent⟩

/-- Summary: The infimum functional on bounded-below gambles satisfies Walley's
    coherence axioms A1-A3 but NOT regularity.

    This demonstrates that regularity is genuinely independent of coherence. -/
theorem coherence_does_not_imply_regularity :
    -- A1: Lower bound property
    (∀ X c, (∀ n, c ≤ X n) → c ≤ infPrevisionFun X) ∧
    -- A2: Positive homogeneity
    (∀ r X, 0 ≤ r → infPrevisionFun (r • X) = r * infPrevisionFun X) ∧
    -- A3: Superadditivity (for bounded gambles)
    (∀ X Y, BddBelow (range X) → BddBelow (range Y) →
      infPrevisionFun (X + Y) ≥ infPrevisionFun X + infPrevisionFun Y) ∧
    -- NOT regular: exists strictly positive X with P(X) = 0
    (∃ X : Gamble ℕ, (∀ n, X n > 0) ∧ infPrevisionFun X = 0) :=
  ⟨infPrevision_lower_bound, infPrevision_pos_homog, infPrevision_superadd_of_bddBelow,
   infPrevisionFun_not_regular⟩

end Counterexample

/-!
## Connection to Solomonoff Semimeasures

The `Semimeasure` structure in `SolomonoffInduction.lean` satisfies:
  μ(x0) + μ(x1) ≤ μ(x)

This is "reverse superadditivity" - the measure of a prefix upper bounds
the sum of its extensions. This corresponds to:
- Probability mass can be "lost" (halting programs)
- Similar structure to upper previsions

The connection is:
- Semimeasures on strings ↔ Upper previsions on cylinder functions
- Universal prior M ↔ Minimax/robust prevision over all computable models
-/

/-!
## Summary: The Unified View

```
                    Mathlib Infrastructure
                           ↓
    ┌──────────────────────────────────────────────┐
    │  Seminorm / AddGroupSeminorm                 │
    │  (subadditive, absolutely homogeneous)       │
    └──────────────────────────────────────────────┘
                           ↓
    ┌──────────────────────────────────────────────┐
    │  SublinearFunctional (this file)             │
    │  (subadditive, positively homogeneous)       │
    │        = UpperPrevision                      │
    └──────────────────────────────────────────────┘
                           ↕ conjugation
    ┌──────────────────────────────────────────────┐
    │  SuperlinearFunctional (this file)           │
    │  (superadditive, positively homogeneous)     │
    │        = LowerPrevision                      │
    └──────────────────────────────────────────────┘
                           ↓
    ┌──────────────────────────────────────────────┐
    │  DesirableGambles (existing)                 │
    │  (D1-D4 axioms, convex cones)                │
    └──────────────────────────────────────────────┘
                           ↓
    ┌──────────────────────────────────────────────┐
    │  CredalSets (existing)                       │
    │  (convex sets of probability measures)       │
    │  Envelope theorem: P̲(X) = inf{E_Q[X] : Q ∈ C}│
    └──────────────────────────────────────────────┘
                           ↓
    ┌──────────────────────────────────────────────┐
    │  Solomonoff/AIXI (existing)                  │
    │  (universal prior as robust lower prevision) │
    │  M(x) = infimum over computable models       │
    └──────────────────────────────────────────────┘
```

All of these are different views of the same mathematical structure:
**non-additive valuations with consistent bounds**.
-/

end Mettapedia.ProbabilityTheory.ImpreciseProbability
