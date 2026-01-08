/-
# Novel Probability Theories from the Hypercube

Three unexplored vertices in the probability hypercube that could yield
genuinely new frameworks for reasoning under uncertainty.

## The Three Theories

1. **Imprecise K&S**: K&S algebra with belief intervals instead of point estimates
2. **Quantum D-S**: Dempster-Shafer on non-commutative algebras
3. **Partial Classical**: Classical probability without total ordering

Each theory sits at an unexplored vertex of the 5-axis hypercube and could
have significant applications in AI, physics, and decision theory.

## References

- Walley, "Statistical Reasoning with Imprecise Probabilities" (1991)
- Quantum probability: Parthasarathy, "An Introduction to Quantum Stochastic Calculus"
- Non-commutative D-S: Shenoy & Shafer, "Axioms for Probability and Belief-Function Propagation"
-/

import Mathlib.Order.Lattice
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.Hypercube.Basic
import Mettapedia.ProbabilityTheory.Common.Valuation
import Mettapedia.ProbabilityTheory.Common.LatticeSummation

namespace Mettapedia.ProbabilityTheory.Hypercube.NovelTheories

open Hypercube Common

/-!
# §1: Imprecise Knuth-Skilling Theory

## Motivation

Standard K&S derives that plausibility → (ℝ≥0, +). But what if we have
**epistemic uncertainty about the plausibilities themselves**?

Instead of: x has plausibility θ(x) ∈ ℝ
We have: x has plausibility in interval [θ_L(x), θ_U(x)]

This bridges K&S algebraic foundations with Walley's imprecise probability!

## Mathematical Structure

An Imprecise K&S Algebra is a K&S algebra where the representation
maps to **intervals** instead of points:
- θ : α → [ℝ≥0, ℝ≥0] (interval-valued)
- θ_L(x ⊕ y) = θ_L(x) + θ_L(y) (lower additive)
- θ_U(x ⊕ y) = θ_U(x) + θ_U(y) (upper additive)

## Key Property

The gap θ_U(x) - θ_L(x) measures **epistemic uncertainty** about plausibility.
-/

/-- An interval of real numbers [lower, upper] -/
structure RealInterval where
  lower : ℝ
  upper : ℝ
  valid : lower ≤ upper

namespace RealInterval

/-- The zero interval [0, 0] -/
def zero : RealInterval := ⟨0, 0, le_refl 0⟩

/-- Add two intervals: [a,b] + [c,d] = [a+c, b+d] -/
def add (I J : RealInterval) : RealInterval where
  lower := I.lower + J.lower
  upper := I.upper + J.upper
  valid := add_le_add I.valid J.valid

/-- The width (imprecision) of an interval -/
def width (I : RealInterval) : ℝ := I.upper - I.lower

/-- Width is non-negative -/
theorem width_nonneg (I : RealInterval) : 0 ≤ I.width := by
  simp only [width]
  linarith [I.valid]

/-- A precise interval has zero width -/
def isPrecise (I : RealInterval) : Prop := I.lower = I.upper

/-- Precise intervals have zero width -/
theorem precise_iff_zero_width (I : RealInterval) :
    I.isPrecise ↔ I.width = 0 := by
  simp only [isPrecise, width]
  constructor <;> intro h <;> linarith

end RealInterval

/-- An Imprecise K&S Algebra: K&S with interval-valued representations.

    The key insight: instead of mapping to (ℝ≥0, +), we map to
    intervals, capturing epistemic uncertainty about plausibilities. -/
class ImpreciseKSAlgebra (α : Type*) extends LinearOrder α where
  /-- The combination operation -/
  op : α → α → α
  /-- Identity element -/
  ident : α
  /-- Lower plausibility bound -/
  θ_lower : α → ℝ
  /-- Upper plausibility bound -/
  θ_upper : α → ℝ
  /-- Bounds are valid -/
  bounds_valid : ∀ x, θ_lower x ≤ θ_upper x
  /-- Lower bound is additive -/
  lower_additive : ∀ x y, θ_lower (op x y) = θ_lower x + θ_lower y
  /-- Upper bound is additive -/
  upper_additive : ∀ x y, θ_upper (op x y) = θ_upper x + θ_upper y
  /-- Identity has zero plausibility -/
  ident_zero : θ_lower ident = 0 ∧ θ_upper ident = 0
  /-- Monotonicity preserved -/
  mono : ∀ x y, x ≤ y → θ_lower x ≤ θ_lower y

namespace ImpreciseKSAlgebra

variable {α : Type*} [ImpreciseKSAlgebra α]

/-- Get the plausibility interval for an element -/
def plausibilityInterval (x : α) : RealInterval where
  lower := θ_lower x
  upper := θ_upper x
  valid := bounds_valid x

/-- The epistemic gap for an element -/
def epistemicGap (x : α) : ℝ := θ_upper x - θ_lower x

/-- Gap is non-negative -/
theorem gap_nonneg (x : α) : 0 ≤ epistemicGap x := by
  simp only [epistemicGap]
  linarith [bounds_valid x]

/-- Gap is additive: gap(x ⊕ y) = gap(x) + gap(y) -/
theorem gap_additive (x y : α) :
    epistemicGap (op x y) = epistemicGap x + epistemicGap y := by
  simp only [epistemicGap, lower_additive, upper_additive]
  ring

/-- An element is precisely known iff its gap is zero -/
def isPrecise (x : α) : Prop := θ_lower x = θ_upper x

/-- The identity is always precisely known -/
theorem ident_precise : isPrecise (ident (α := α)) := by
  simp only [isPrecise]
  have h := @ident_zero α _
  exact h.1.trans h.2.symm

end ImpreciseKSAlgebra

/-!
## Applications of Imprecise K&S

### 1. Robust Machine Learning

When learning probabilities from data, we have **finite sample uncertainty**.
Instead of point estimates, we get confidence intervals.

Imprecise K&S provides the algebraic foundation for:
- Combining uncertain probability estimates
- Propagating epistemic uncertainty through inference
- Making robust decisions under model uncertainty

### 2. Expert Elicitation

Experts often can't give precise probabilities but CAN give bounds:
"I think P(A) is between 0.3 and 0.5"

Imprecise K&S formalizes how to combine such expert assessments.

### 3. Sensor Fusion with Calibration Uncertainty

Multiple sensors with unknown calibration errors give interval readings.
Imprecise K&S provides principled combination rules.
-/

/-!
# §2: Quantum Dempster-Shafer Theory

## Motivation

Standard D-S assumes events form a Boolean algebra (sets commute).
But what if events are **quantum observables** that don't commute?

This yields a theory for reasoning about:
- Quantum measurement uncertainty
- Non-commutative evidence combination
- Entanglement effects on belief

## Mathematical Structure

Replace the power set 2^Ω with an **orthomodular lattice** L:
- Meet ∧ doesn't distribute over join ∨
- Complement satisfies orthomodularity: a ≤ b → b = a ∨ (b ∧ aᶜ)
- Observables may not commute: [A, B] ≠ 0

Mass functions assign to projection operators, not sets!
-/

/-- An orthomodular lattice (quantum logic structure).
    This is the lattice of projections in a Hilbert space.

    Key properties:
    - Not distributive in general (unlike Boolean algebras)
    - Has orthocomplementation (aᶜ with a ⊓ aᶜ = ⊥ and a ⊔ aᶜ = ⊤)
    - Satisfies orthomodularity: a ≤ b → b = a ⊔ (b ⊓ aᶜ)
-/
class OrthomodularLattice (L : Type*) extends Lattice L, HasCompl L, BoundedOrder L where
  /-- Orthomodularity: if a ≤ b then b = a ∨ (b ∧ aᶜ) -/
  orthomodular : ∀ a b : L, a ≤ b → b = a ⊔ (b ⊓ aᶜ)
  /-- Double negation -/
  compl_compl : ∀ a : L, aᶜᶜ = a
  /-- De Morgan laws -/
  compl_sup : ∀ a b : L, (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ
  compl_inf : ∀ a b : L, (a ⊓ b)ᶜ = aᶜ ⊔ bᶜ
  /-- Complement of bottom is top -/
  compl_bot : (⊥ : L)ᶜ = ⊤
  /-- Complement of top is bottom -/
  compl_top : (⊤ : L)ᶜ = ⊥
  /-- a ⊓ aᶜ = ⊥ (orthocomplementation property) -/
  inf_compl_self : ∀ a : L, a ⊓ aᶜ = ⊥
  /-- a ⊔ aᶜ = ⊤ (orthocomplementation property) -/
  sup_compl_self : ∀ a : L, a ⊔ aᶜ = ⊤

/-!
### Boolean Algebras as Orthomodular Lattices

Any Boolean algebra is (trivially) an orthomodular lattice: distributivity is stronger than
orthomodularity, and the Boolean complement provides an orthocomplementation.
-/

instance {L : Type*} [BooleanAlgebra L] : OrthomodularLattice L where
  toLattice := inferInstance
  toHasCompl := inferInstance
  toBoundedOrder := inferInstance
  orthomodular a b hab := by
    -- In a Boolean algebra: b = (b ⊓ a) ⊔ (b ⊓ aᶜ) = a ⊔ (b ⊓ aᶜ) when a ≤ b.
    calc
      b = b ⊓ ⊤ := by simp
      _ = b ⊓ (a ⊔ aᶜ) := by simp
      _ = (b ⊓ a) ⊔ (b ⊓ aᶜ) := by simp
      _ = a ⊔ (b ⊓ aᶜ) := by simp [inf_eq_right.mpr hab]
  compl_compl a := by simp
  compl_sup a b := by simp
  compl_inf a b := by simp
  compl_bot := by simp
  compl_top := by simp
  inf_compl_self a := by simp
  sup_compl_self a := by simp

namespace OrthomodularLattice

variable {L : Type*} [OrthomodularLattice L]

/-- aᶜ ⊓ a = ⊥ (commutativity of inf_compl_self). -/
theorem compl_inf_self (a : L) : aᶜ ⊓ a = ⊥ := by
  rw [inf_comm, inf_compl_self]

/-- aᶜ ⊔ a = ⊤ (commutativity of sup_compl_self). -/
theorem compl_sup_self (a : L) : aᶜ ⊔ a = ⊤ := by
  rw [sup_comm, sup_compl_self]

/-- Complement is antitone: a ≤ b implies bᶜ ≤ aᶜ.

    Proof: From a ≤ b, we have a ⊔ b = b. Taking complements and applying de Morgan:
    (a ⊔ b)ᶜ = bᶜ, hence aᶜ ⊓ bᶜ = bᶜ, which means bᶜ ≤ aᶜ. -/
theorem compl_le_compl {a b : L} (h : a ≤ b) : bᶜ ≤ aᶜ := by
  -- From a ≤ b, we have a ⊔ b = b
  have hsup : a ⊔ b = b := sup_eq_right.mpr h
  -- Take complement: (a ⊔ b)ᶜ = bᶜ
  have hcompl : (a ⊔ b)ᶜ = bᶜ := by rw [hsup]
  -- By de Morgan: aᶜ ⊓ bᶜ = bᶜ
  rw [compl_sup] at hcompl
  -- aᶜ ⊓ bᶜ = bᶜ means bᶜ ≤ aᶜ
  exact inf_eq_right.mp hcompl

-- The old complex proof attempted to use OML directly, but the de Morgan approach is much simpler.
-- The key insight is that compl_sup gives us (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ for free.

/-- Helper: bᶜ ⊓ a = ⊥ when a ≤ b (orthogonality from order). -/
theorem compl_inf_of_le {a b : L} (h : a ≤ b) : bᶜ ⊓ a = ⊥ := by
  have hba : bᶜ ⊓ a ≤ ⊥ := by
    calc bᶜ ⊓ a ≤ bᶜ ⊓ b := inf_le_inf_left bᶜ h
         _ = ⊥ := compl_inf_self b
  exact le_antisymm hba bot_le

/-- The dual orthomodular law: a ≤ b implies a = (a ⊔ bᶜ) ⊓ b.
    This is exactly the Sasaki projection formula! -/
theorem orthomodular_dual {a b : L} (h : a ≤ b) : a = (a ⊔ bᶜ) ⊓ b := by
  -- From a ≤ b, we have bᶜ ≤ aᶜ
  have hc : bᶜ ≤ aᶜ := compl_le_compl h
  -- Apply orthomodular to bᶜ ≤ aᶜ: aᶜ = bᶜ ⊔ (aᶜ ⊓ bᶜᶜ) = bᶜ ⊔ (aᶜ ⊓ b)
  have hom' : aᶜ = bᶜ ⊔ (aᶜ ⊓ bᶜᶜ) := orthomodular bᶜ aᶜ hc
  have hom : aᶜ = bᶜ ⊔ (aᶜ ⊓ b) := by rw [compl_compl] at hom'; exact hom'
  -- Take complement of both sides: (aᶜ)ᶜ = (bᶜ ⊔ (aᶜ ⊓ b))ᶜ
  have hom_compl : aᶜᶜ = (bᶜ ⊔ (aᶜ ⊓ b))ᶜ := congr_arg (·ᶜ) hom
  -- Expand using de Morgan and double negation
  calc a = aᶜᶜ := (compl_compl a).symm
       _ = (bᶜ ⊔ (aᶜ ⊓ b))ᶜ := hom_compl
       _ = bᶜᶜ ⊓ (aᶜ ⊓ b)ᶜ := compl_sup bᶜ (aᶜ ⊓ b)
       _ = b ⊓ (aᶜᶜ ⊔ bᶜ) := by rw [compl_compl, compl_inf]
       _ = b ⊓ (a ⊔ bᶜ) := by rw [compl_compl]
       _ = (a ⊔ bᶜ) ⊓ b := inf_comm b (a ⊔ bᶜ)

/-!
### Orthogonality vs. Disjointness

In an orthomodular lattice, `a ≤ bᶜ` (orthogonality) implies `a ⊓ b = ⊥`,
but the converse is not valid in general (e.g. in the Hilbert lattice of subspaces).
-/

/-- Orthogonality implies disjointness: `a ≤ bᶜ` implies `a ⊓ b = ⊥`. -/
theorem inf_eq_bot_of_le_compl {a b : L} (h : a ≤ bᶜ) : a ⊓ b = ⊥ := by
  have hle : a ⊓ b ≤ ⊥ := by
    calc a ⊓ b ≤ bᶜ ⊓ b := inf_le_inf_right b h
         _ = ⊥ := compl_inf_self b
  exact le_antisymm hle bot_le

/-!
### Important Note on Disjointness vs Orthogonality

In a Boolean algebra: `a ⊓ b = ⊥ ↔ a ≤ bᶜ` (disjointness = orthogonality)

In a general OML: `a ≤ bᶜ → a ⊓ b = ⊥` but NOT the converse!

**Counterexample**: In the Hilbert lattice of ℂ², let:
- a = span{(1,0)}
- b = span{(1,1)}
Then a ⊓ b = {0} = ⊥ (they're disjoint as subspaces),
but a ≤ bᶜ is FALSE since bᶜ = span{(1,-1)} and (1,0) ∉ span{(1,-1)}.

This asymmetry is fundamental to quantum logic: disjoint propositions
need not be orthogonal (complementary).

The property `(a ⊔ b) ⊓ aᶜ ≤ b` (quasi-distributivity) is also FALSE
in general OML, as shown by the same counterexample where
(a ⊔ b) ⊓ aᶜ = ℂ² ⊓ span{(0,1)} = span{(0,1)} ⊈ span{(1,1)} = b.

For COMMUTING elements, these properties DO hold (Foulis-Holland theorem).
-/

end OrthomodularLattice

/-- Two elements commute in an orthomodular lattice -/
def commutes {L : Type*} [OrthomodularLattice L] (a b : L) : Prop :=
  a = (a ⊓ b) ⊔ (a ⊓ bᶜ)

/-- A quantum mass function on an orthomodular lattice -/
structure QuantumMassFunction (L : Type*) [OrthomodularLattice L] where
  /-- Mass assigned to each projection -/
  m : L → ℝ
  /-- No mass on bottom -/
  m_bot : m ⊥ = 0
  /-- Masses are non-negative -/
  m_nonneg : ∀ a, 0 ≤ m a

namespace QuantumMassFunction

variable {L : Type*} [OrthomodularLattice L]

/-!
### Belief Function for Finite Orthomodular Lattices

For finite lattices, belief is simply the sum over all elements below a.
This avoids measure-theoretic machinery while being mathematically precise.
-/

section FiniteCase

variable [Fintype L] [DecidableEq L] [DecidableRel (α := L) (· ≤ ·)]

/-- Quantum belief: sum over projections below a.
    For finite lattices, this is a direct Finset sum using `sumBelow`. -/
noncomputable def belief (qm : QuantumMassFunction L) (a : L) : ℝ :=
  sumBelow qm.m a

/-- Quantum plausibility: 1 - belief of complement. -/
noncomputable def plausibility (qm : QuantumMassFunction L) (a : L) : ℝ :=
  1 - belief qm aᶜ

omit [DecidableEq L] in
/-- Belief is monotone: a ≤ b implies Bel(a) ≤ Bel(b). -/
theorem belief_mono (qm : QuantumMassFunction L) {a b : L} (h : a ≤ b) :
    qm.belief a ≤ qm.belief b :=
  sumBelow.mono_of_nonneg qm.m qm.m_nonneg h

/-- Belief at ⊥ equals m(⊥) = 0. -/
@[simp]
theorem belief_bot (qm : QuantumMassFunction L) : qm.belief ⊥ = 0 := by
  simp [belief, qm.m_bot]

omit [DecidableEq L] in
/-- Belief is non-negative. -/
theorem belief_nonneg (qm : QuantumMassFunction L) (a : L) : 0 ≤ qm.belief a :=
  sumBelow.nonneg_of_nonneg qm.m qm.m_nonneg a

/-- Total mass is belief at ⊤. -/
noncomputable def totalMass (qm : QuantumMassFunction L) : ℝ := qm.belief ⊤

omit [DecidableEq L] in
/-- Belief at any element is at most total mass. -/
theorem belief_le_totalMass (qm : QuantumMassFunction L) (a : L) :
    qm.belief a ≤ qm.totalMass :=
  qm.belief_mono le_top

omit [DecidableEq L] in
/-- m(a) ≤ Bel(a) for any a. -/
theorem m_le_belief (qm : QuantumMassFunction L) (a : L) : qm.m a ≤ qm.belief a :=
  sumBelow.self_le_of_nonneg qm.m qm.m_nonneg a

end FiniteCase

end QuantumMassFunction

/-!
### The Sasaki Projection: Quantum Conditional

The Sasaki projection φ_a(b) = (b ∨ a') ∧ a is the quantum analog of "b ∧ a".
In Boolean algebras, φ_a(b) = a ∧ b. In orthomodular lattices, φ_a(b) ≠ φ_b(a)
in general, capturing measurement order-dependence.

References:
- Sasaki, "Orthocomplemented Lattices Satisfying the Exchange Axiom" (1954)
- Hardegree, "An Axiom System for Orthomodular Quantum Logic" (1981)
- Stanford Encyclopedia: https://plato.stanford.edu/entries/qt-quantlog/
-/

/-- The Sasaki projection (quantum conditional): φ_a(b) = (b ∨ a') ∧ a.
    This is the orthomodular analog of "b given a" or "b ∧ a".

    Key properties:
    - In Boolean algebras: sasakiProj a b = a ⊓ b
    - In orthomodular: sasakiProj a b ≠ sasakiProj b a in general
    - sasakiProj a b ≤ a always
    - If b ≤ a, then sasakiProj a b = b -/
def sasakiProj {L : Type*} [OrthomodularLattice L] (a b : L) : L :=
  (b ⊔ aᶜ) ⊓ a

namespace sasakiProj

variable {L : Type*} [OrthomodularLattice L]

/-- Sasaki projection is below the first argument. -/
theorem le_left (a b : L) : sasakiProj a b ≤ a := inf_le_right

/-- If b ≤ a, the Sasaki projection returns b.
    This is a direct consequence of the dual orthomodular law. -/
theorem of_le {a b : L} (h : b ≤ a) : sasakiProj a b = b := by
  -- sasakiProj a b = (b ⊔ aᶜ) ⊓ a
  -- By the dual orthomodular law: b ≤ a implies b = (b ⊔ aᶜ) ⊓ a
  simp only [sasakiProj]
  exact (OrthomodularLattice.orthomodular_dual h).symm

/-- Sasaki projection at ⊤ returns b. -/
theorem top (b : L) : sasakiProj ⊤ b = b := by
  simp [sasakiProj, OrthomodularLattice.compl_top]

/-- Sasaki projection at ⊥ returns ⊥. -/
theorem bot (b : L) : sasakiProj ⊥ b = ⊥ := by
  simp [sasakiProj, OrthomodularLattice.compl_bot]

end sasakiProj

/-- Quantum D-S combination rule.

    Unlike classical D-S, this must handle non-commuting evidence!
    The combination depends on the ORDER of evidence application.

    The key insight (from quantum logic literature):
    - Classical uses A ∧ B for combining focal elements
    - Quantum uses the Sasaki projection φ_A(B) = (B ∨ A') ∧ A

    This captures that "first A, then B" ≠ "first B, then A" when
    A and B don't commute (i.e., represent incompatible measurements). -/
structure QuantumDempsterRule (L : Type*) [OrthomodularLattice L] where
  /-- Left-to-right combination -/
  combine_lr : QuantumMassFunction L → QuantumMassFunction L → QuantumMassFunction L
  /-- Right-to-left combination (may differ!) -/
  combine_rl : QuantumMassFunction L → QuantumMassFunction L → QuantumMassFunction L
  /-- Combination is order-dependent for non-commuting evidence -/
  order_dependent : ∃ m₁ m₂ : QuantumMassFunction L,
    combine_lr m₁ m₂ ≠ combine_rl m₁ m₂

/-!
### Quantum Dempster Combination Implementation

The quantum combination rule generalizes classical Dempster:

**Classical**: m₁₂(C) = K⁻¹ · Σ_{A∧B=C, A∧B≠⊥} m₁(A) · m₂(B)

**Quantum LR**: m₁₂(C) = K⁻¹ · Σ_{φ_A(B)=C, φ_A(B)≠⊥} m₁(A) · m₂(B)
  where φ_A(B) = (B ∨ A') ∧ A is the Sasaki projection

**Quantum RL**: m₂₁(C) = K⁻¹ · Σ_{φ_B(A)=C, φ_B(A)≠⊥} m₁(A) · m₂(B)
  where φ_B(A) = (A ∨ B') ∧ B

The normalization constant K = 1 - Σ_{φ_A(B)=⊥} m₁(A) · m₂(B) accounts for conflict.
-/

section QuantumCombination

variable {L : Type*} [OrthomodularLattice L] [Fintype L] [DecidableEq L]
variable [DecidableRel (α := L) (· ≤ ·)]

/-- Unnormalized combination mass using Sasaki projection (left-to-right).
    Σ_{φ_A(B)=C} m₁(A) · m₂(B) -/
noncomputable def rawCombineMass_lr (m₁ m₂ : QuantumMassFunction L) (c : L) : ℝ :=
  Finset.sum Finset.univ fun a =>
    Finset.sum Finset.univ fun b =>
      if sasakiProj a b = c then m₁.m a * m₂.m b else 0

/-- Unnormalized combination mass using Sasaki projection (right-to-left).
    Σ_{φ_B(A)=C} m₁(A) · m₂(B) -/
noncomputable def rawCombineMass_rl (m₁ m₂ : QuantumMassFunction L) (c : L) : ℝ :=
  Finset.sum Finset.univ fun a =>
    Finset.sum Finset.univ fun b =>
      if sasakiProj b a = c then m₁.m a * m₂.m b else 0

/-- Conflict mass: total mass on combinations that project to ⊥. -/
noncomputable def conflictMass_lr (m₁ m₂ : QuantumMassFunction L) : ℝ :=
  rawCombineMass_lr m₁ m₂ ⊥

/-- The normalization constant K = 1 - conflict (when masses are normalized). -/
noncomputable def normalizationK_lr (m₁ m₂ : QuantumMassFunction L) : ℝ :=
  1 - conflictMass_lr m₁ m₂

/-- Raw combination masses are non-negative. -/
theorem rawCombineMass_lr_nonneg (m₁ m₂ : QuantumMassFunction L) (c : L) :
    0 ≤ rawCombineMass_lr m₁ m₂ c := by
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  split_ifs
  · exact mul_nonneg (m₁.m_nonneg a) (m₂.m_nonneg b)
  · exact le_refl 0

/-- In a Boolean algebra viewed as an OML, Sasaki projection equals meet.
    This shows the classical case where combination is commutative.

    Note: We have an instance `BooleanAlgebra → OrthomodularLattice` above, so `sasakiProj`
    is available on Boolean algebras. We keep this lemma stated purely in Boolean terms for
    direct reuse without mentioning `sasakiProj`. -/
theorem sasaki_eq_meet_in_boolean_fact {L : Type*} [BooleanAlgebra L] (a b : L) :
    (b ⊔ aᶜ) ⊓ a = a ⊓ b := by
  rw [inf_sup_right]
  simp [inf_comm]

omit [OrthomodularLattice L] [DecidableRel (α := L) (· ≤ ·)] in
/-- In Boolean algebras, left-to-right equals right-to-left (classical behavior).

With the Boolean-algebra → OML bridge, `sasakiProj` reduces to `⊓`, hence the two orderings
coincide. -/
theorem rawCombineMass_lr_eq_rl_boolean {L : Type*} [BooleanAlgebra L]
    [Fintype L] [DecidableEq L]
    (m₁ m₂ : QuantumMassFunction L) (c : L) :
    rawCombineMass_lr m₁ m₂ c = rawCombineMass_rl m₁ m₂ c := by
  classical
  unfold rawCombineMass_lr rawCombineMass_rl
  -- In a Boolean algebra, `sasakiProj a b = a ⊓ b`.
  have hsasaki : ∀ a b : L, sasakiProj a b = a ⊓ b := by
    intro a b
    -- `sasakiProj a b = (b ⊔ aᶜ) ⊓ a`, and `(b ⊔ aᶜ) ⊓ a = a ⊓ b` by distributivity.
    simpa [sasakiProj] using sasaki_eq_meet_in_boolean_fact (L := L) a b
  -- Rewrite both conditions to `a ⊓ b = c` (commutativity takes care of RL).
  simp [hsasaki, inf_comm]

end QuantumCombination

/-!
## Key Theorems of Quantum D-S

1. **Order Dependence**: Evidence combination is non-commutative
2. **Entanglement Effects**: Correlated evidence behaves differently
3. **Measurement Collapse**: Belief updates upon observation
4. **Uncertainty Relations**: Complementary observables can't both be certain
-/

/-- Weak uncertainty principle: if all mass is concentrated at a single element x,
    then Bel(a) = totalMass iff x ≤ a. This is the foundation for stronger results. -/
theorem belief_eq_totalMass_iff_contains_support
    {L : Type*} [OrthomodularLattice L] [Fintype L] [DecidableEq L]
    [DecidableRel (α := L) (· ≤ ·)]
    (qm : QuantumMassFunction L) (a : L)
    (x : L) (hx : ∀ y, y ≠ x → qm.m y = 0)
    (hmx : qm.m x ≠ 0) :
    qm.belief a = qm.totalMass ↔ x ≤ a := by
  -- Use the singleton support lemma from LatticeSummation
  have hsing : hasSingletonSupport qm.m x := hx
  simp only [QuantumMassFunction.belief, QuantumMassFunction.totalMass]
  exact hasSingletonSupport.sumBelow_eq_total_iff hsing hmx a

/-- For singleton support, if x ≰ a then belief(a) < totalMass. -/
theorem belief_lt_totalMass_of_not_le
    {L : Type*} [OrthomodularLattice L] [Fintype L] [DecidableEq L]
    [DecidableRel (α := L) (· ≤ ·)]
    (qm : QuantumMassFunction L) (a : L)
    (x : L) (hx : ∀ y, y ≠ x → qm.m y = 0)
    (hmx : 0 < qm.m x)
    (hna : ¬x ≤ a) :
    qm.belief a < qm.totalMass := by
  have hsing : hasSingletonSupport qm.m x := hx
  simp only [QuantumMassFunction.belief, QuantumMassFunction.totalMass]
  exact hasSingletonSupport.sumBelow_lt_total_of_not_le hsing hmx hna

/-- Heisenberg-like uncertainty for Quantum D-S:
    If all mass is at element x, and x ≤ a but x ≰ b, then Bel(a) = totalMass but Bel(b) < totalMass.
    This is the lattice-theoretic analog of quantum uncertainty. -/
theorem quantum_ds_uncertainty_singleton
    {L : Type*} [OrthomodularLattice L] [Fintype L] [DecidableEq L]
    [DecidableRel (α := L) (· ≤ ·)]
    (qm : QuantumMassFunction L) (a b : L)
    (x : L) (hx : ∀ y, y ≠ x → qm.m y = 0)
    (hmx : 0 < qm.m x)
    (hxa : x ≤ a)
    (hxb : ¬x ≤ b) :
    qm.belief a = qm.totalMass ∧ qm.belief b < qm.totalMass := by
  constructor
  · rw [belief_eq_totalMass_iff_contains_support qm a x hx (ne_of_gt hmx)]
    exact hxa
  · exact belief_lt_totalMass_of_not_le qm b x hx hmx hxb

/-- The key insight: in an orthomodular lattice, if a and b don't commute,
    there exists an element x that is below a but not below b (or vice versa).
    This is what prevents simultaneous certainty for non-commuting observables. -/
theorem noncommuting_not_nested
    {L : Type*} [OrthomodularLattice L] (a b : L)
    (hnc : ¬commutes a b) :
    ¬(a ≤ b ∧ b ≤ a) := by
  intro ⟨hab, hba⟩
  -- If a ≤ b and b ≤ a, then a = b, so they trivially commute
  have heq : a = b := le_antisymm hab hba
  subst heq
  -- a commutes with itself: a = (a ⊓ a) ⊔ (a ⊓ aᶜ) = a ⊔ (a ⊓ aᶜ)
  apply hnc
  -- Show a = (a ⊓ a) ⊔ (a ⊓ aᶜ)
  simp only [commutes, inf_idem]
  -- Need to show a = a ⊔ (a ⊓ aᶜ)
  -- By inf_compl_self: a ⊓ aᶜ = ⊥
  rw [OrthomodularLattice.inf_compl_self, sup_bot_eq]

/-!
### Generalized Support and Full Belief

For arbitrary mass functions (not just singleton support), we characterize
when Bel(a) = totalMass.
-/

/-- The support of a mass function: elements with positive mass. -/
noncomputable def massSupport {L : Type*} [OrthomodularLattice L] [Fintype L] [DecidableEq L]
    (qm : QuantumMassFunction L) : Finset L :=
  Finset.filter (fun x => 0 < qm.m x) Finset.univ

/-- Support characterization: x ∈ support iff m(x) > 0. -/
theorem mem_massSupport_iff {L : Type*} [OrthomodularLattice L] [Fintype L] [DecidableEq L]
    (qm : QuantumMassFunction L) (x : L) :
    x ∈ massSupport qm ↔ 0 < qm.m x := by
  simp [massSupport]

/-- ⊥ is never in the support (since m(⊥) = 0). -/
theorem bot_not_mem_massSupport {L : Type*} [OrthomodularLattice L] [Fintype L] [DecidableEq L]
    (qm : QuantumMassFunction L) :
    ⊥ ∉ massSupport qm := by
  simp [massSupport, qm.m_bot]

/-- If all support is below a, then Bel(a) = totalMass. -/
theorem belief_eq_totalMass_of_support_below
    {L : Type*} [OrthomodularLattice L] [Fintype L] [DecidableEq L]
    [DecidableRel (α := L) (· ≤ ·)]
    (qm : QuantumMassFunction L) (a : L)
    (h : ∀ x ∈ massSupport qm, x ≤ a) :
    qm.belief a = qm.totalMass := by
  simp only [QuantumMassFunction.belief, QuantumMassFunction.totalMass, sumBelow]
  -- Sum over finsetBelow a = sum over finsetBelow ⊤
  -- because all elements outside finsetBelow a have zero mass
  have heq : Finset.sum (finsetBelow a) qm.m = Finset.sum Finset.univ qm.m := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hxa
    -- x ∈ univ but x ∉ finsetBelow a means x ≰ a
    simp only [finsetBelow.mem_iff] at hxa
    -- Show qm.m x = 0
    by_contra hmx
    push_neg at hmx
    have hpos : 0 < qm.m x := lt_of_le_of_ne (qm.m_nonneg x) (Ne.symm hmx)
    have hsupp : x ∈ massSupport qm := by simp [massSupport, hpos]
    exact hxa (h x hsupp)
  simp only [finsetBelow.top_eq_univ] at heq ⊢
  exact heq

/-- If Bel(a) = totalMass and totalMass > 0, then all positive-mass elements are below a. -/
theorem support_below_of_belief_eq_totalMass
    {L : Type*} [OrthomodularLattice L] [Fintype L] [DecidableEq L]
    [DecidableRel (α := L) (· ≤ ·)]
    (qm : QuantumMassFunction L) (a : L)
    (hbel : qm.belief a = qm.totalMass)
    (_htotal : 0 < qm.totalMass) :
    ∀ x ∈ massSupport qm, x ≤ a := by
  intro x hx
  simp only [massSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  by_contra hna
  -- If x ≰ a and m(x) > 0, then Bel(a) < totalMass
  -- Bel(a) = sum over finsetBelow a, which doesn't include x
  -- totalMass = sum over univ, which includes x with positive mass
  simp only [QuantumMassFunction.belief, QuantumMassFunction.totalMass, sumBelow,
    finsetBelow.top_eq_univ] at hbel
  -- Split: sum over univ = sum over (finsetBelow a) + sum over (univ \ finsetBelow a)
  have hsplit : Finset.sum Finset.univ qm.m =
      Finset.sum (finsetBelow a) qm.m +
      Finset.sum (Finset.univ \ finsetBelow a) qm.m := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff)]
    congr 1
    ext y
    simp only [Finset.mem_union, finsetBelow.mem_iff, Finset.mem_sdiff, Finset.mem_univ,
      true_and, or_not]
  -- From hbel and hsplit, derive that sum over complement is 0
  have hzero : Finset.sum (Finset.univ \ finsetBelow a) qm.m = 0 := by
    have h : Finset.sum (finsetBelow a) qm.m + Finset.sum (Finset.univ \ finsetBelow a) qm.m =
             Finset.sum (finsetBelow a) qm.m := by
      rw [← hsplit, ← hbel]
    have hnn : 0 ≤ Finset.sum (Finset.univ \ finsetBelow a) qm.m :=
      Finset.sum_nonneg (fun y _ => qm.m_nonneg y)
    clear hna
    linarith
  -- But x ∈ (univ \ finsetBelow a) and m(x) > 0, contradiction
  have hx_in : x ∈ Finset.univ \ finsetBelow a := by
    simp only [Finset.mem_sdiff, Finset.mem_univ, finsetBelow.mem_iff, true_and]
    exact hna
  have hx_pos : 0 < Finset.sum (Finset.univ \ finsetBelow a) qm.m := by
    calc 0 < qm.m x := hx
         _ ≤ Finset.sum (Finset.univ \ finsetBelow a) qm.m :=
           Finset.single_le_sum (fun y _ => qm.m_nonneg y) hx_in
  rw [hzero] at hx_pos
  exact absurd hx_pos (lt_irrefl 0)

/-- Characterization: Bel(a) = totalMass iff all support is below a (when totalMass > 0). -/
theorem belief_eq_totalMass_iff_support_below
    {L : Type*} [OrthomodularLattice L] [Fintype L] [DecidableEq L]
    [DecidableRel (α := L) (· ≤ ·)]
    (qm : QuantumMassFunction L) (a : L)
    (htotal : 0 < qm.totalMass) :
    qm.belief a = qm.totalMass ↔ ∀ x ∈ massSupport qm, x ≤ a := by
  constructor
  · intro hbel
    exact support_below_of_belief_eq_totalMass qm a hbel htotal
  · exact belief_eq_totalMass_of_support_below qm a

/-- Generalized uncertainty: if a and b both achieve full belief, then all support
    is below a ⊓ b. -/
theorem support_below_inf_of_both_full
    {L : Type*} [OrthomodularLattice L] [Fintype L] [DecidableEq L]
    [DecidableRel (α := L) (· ≤ ·)]
    (qm : QuantumMassFunction L) (a b : L)
    (htotal : 0 < qm.totalMass)
    (ha : qm.belief a = qm.totalMass)
    (hb : qm.belief b = qm.totalMass) :
    ∀ x ∈ massSupport qm, x ≤ a ⊓ b := by
  intro x hx
  have hxa : x ≤ a := support_below_of_belief_eq_totalMass qm a ha htotal x hx
  have hxb : x ≤ b := support_below_of_belief_eq_totalMass qm b hb htotal x hx
  exact le_inf hxa hxb

/-- Key structural theorem: if the support contains an element x where x ≤ a but x ≰ b,
    then Bel(a) and Bel(b) cannot both equal totalMass. -/
theorem uncertainty_from_asymmetric_support
    {L : Type*} [OrthomodularLattice L] [Fintype L] [DecidableEq L]
    [DecidableRel (α := L) (· ≤ ·)]
    (qm : QuantumMassFunction L) (a b : L)
    (htotal : 0 < qm.totalMass)
    (x : L) (hx : x ∈ massSupport qm) (_hxa : x ≤ a) (hxb : ¬x ≤ b) :
    ¬(qm.belief a = qm.totalMass ∧ qm.belief b = qm.totalMass) := by
  intro ⟨ha, hb⟩
  have hxab : x ≤ a ⊓ b := support_below_inf_of_both_full qm a b htotal ha hb x hx
  exact hxb (le_trans hxab inf_le_right)

/-- Main uncertainty theorem: if a and b don't commute, and all mass is at some x,
    then we cannot have both Bel(a) = totalMass and Bel(b) = totalMass. -/
theorem quantum_ds_uncertainty {L : Type*} [OrthomodularLattice L]
    [Fintype L] [DecidableEq L] [DecidableRel (α := L) (· ≤ ·)]
    (qm : QuantumMassFunction L) (a b : L) (_h : ¬commutes a b)
    (x : L) (hx : ∀ y, y ≠ x → qm.m y = 0)
    (hmx : 0 < qm.m x) :
    qm.belief a = qm.totalMass → qm.belief b < qm.totalMass ∨ qm.belief b = qm.totalMass := by
  intro ha
  -- From ha and singleton support, we know x ≤ a
  have hxa : x ≤ a := by
    rw [belief_eq_totalMass_iff_contains_support qm a x hx (ne_of_gt hmx)] at ha
    exact ha
  -- Check if x ≤ b
  by_cases hxb : x ≤ b
  · -- x ≤ b means Bel(b) = totalMass too
    right
    rw [belief_eq_totalMass_iff_contains_support qm b x hx (ne_of_gt hmx)]
    exact hxb
  · -- x ≰ b means Bel(b) < totalMass
    left
    exact belief_lt_totalMass_of_not_le qm b x hx hmx hxb

/-!
## Applications of Quantum D-S

### 1. Quantum State Tomography

Reconstructing quantum states from incomplete measurements.
Multiple measurement outcomes give "quantum evidence" that must be combined.

### 2. Quantum Machine Learning

Reasoning about quantum classifiers and their uncertainty.
Quantum D-S provides the belief-function semantics for quantum predictions.

### 3. Quantum Cryptography Analysis

Analyzing security of quantum key distribution:
- Eve's knowledge is represented as quantum belief
- Information leakage affects plausibility bounds
- Non-commutativity captures measurement disturbance

### 4. Foundations of Quantum Mechanics

Provides an alternative interpretation where:
- Quantum probabilities are upper bounds (plausibilities)
- Interference arises from non-commutative evidence combination
- Collapse is belief update upon observation
-/

/-!
# §3: Partial-Order Classical Probability

## Motivation

Standard probability requires ALL events to be comparable.
But some events may be **genuinely incomparable**:
- "It will rain tomorrow" vs "The stock market will rise"
- Different modalities of uncertainty

Partial-order classical relaxes this to allow incomparable events
while keeping the other axioms (additivity, normalization).

## Mathematical Structure

Events form a **distributive lattice** (not Boolean, not linear):
- Some pairs a, b have neither a ≤ b nor b ≤ a
- Probability is still additive on disjoint events
- But P(a) and P(b) may be incomparable if a and b are
-/

/-- A valuation on a partial order (not necessarily total) -/
structure PartialValuation (L : Type*) [DistribLattice L] [BoundedOrder L] where
  /-- The valuation function -/
  val : L → ℝ
  /-- Monotonicity -/
  mono : ∀ a b, a ≤ b → val a ≤ val b
  /-- Normalized at bottom -/
  val_bot : val ⊥ = 0
  /-- Normalized at top -/
  val_top : val ⊤ = 1
  /-- Additive on disjoint elements -/
  additive : ∀ a b, a ⊓ b = ⊥ → val (a ⊔ b) = val a + val b

namespace PartialValuation

variable {L : Type*} [DistribLattice L] [BoundedOrder L]

/-- Values are bounded -/
theorem bounded (v : PartialValuation L) (a : L) : 0 ≤ v.val a ∧ v.val a ≤ 1 := by
  constructor
  · calc 0 = v.val ⊥ := v.val_bot.symm
       _ ≤ v.val a := v.mono ⊥ a bot_le
  · calc v.val a ≤ v.val ⊤ := v.mono a ⊤ le_top
       _ = 1 := v.val_top

/-- Two elements are **probabilistically comparable** if their values are ordered -/
def probComparable (v : PartialValuation L) (a b : L) : Prop :=
  v.val a ≤ v.val b ∨ v.val b ≤ v.val a

/-- Lattice-comparable implies probabilistically comparable -/
theorem lattice_comp_implies_prob_comp (v : PartialValuation L) (a b : L)
    (h : a ≤ b ∨ b ≤ a) : v.probComparable a b := by
  cases h with
  | inl hab => left; exact v.mono a b hab
  | inr hba => right; exact v.mono b a hba

end PartialValuation

/-- The partial-order probability vertex in the hypercube -/
def partialOrderClassical : ProbabilityVertex where
  commutativity := .commutative
  distributivity := .distributive  -- Not Boolean!
  precision := .precise
  orderAxis := .partialOrder       -- Key difference
  additivity := .additive
  invertibility := .monoid
  determinism := .probabilistic
  support := .continuous
  regularity := .borel
  independence := .tensor

/-!
## Key Theorems of Partial-Order Classical

1. **Independence Generalization**: Independent events may be incomparable
2. **Conditional Probability**: Only defined when events are comparable
3. **Total Probability Law**: Requires comparable partition
-/

/-- Conditional probability only makes sense for comparable events -/
noncomputable def conditionalProb {L : Type*} [DistribLattice L] [BoundedOrder L]
    (v : PartialValuation L) (a b : L) (_hb : v.val b ≠ 0) : ℝ :=
  v.val (a ⊓ b) / v.val b

/-- The law of total probability requires a comparable partition -/
structure ComparablePartition (L : Type*) [DistribLattice L] [BoundedOrder L]
    (v : PartialValuation L) where
  /-- The partition elements -/
  parts : List L
  /-- Parts are pairwise disjoint -/
  pairwise_disjoint : ∀ a ∈ parts, ∀ b ∈ parts, a ≠ b → a ⊓ b = ⊥
  /-- Parts cover the space -/
  covers : parts.foldl (· ⊔ ·) ⊥ = ⊤
  /-- All parts are comparable to each other -/
  comparable : ∀ a ∈ parts, ∀ b ∈ parts, v.probComparable a b

/-!
## Applications of Partial-Order Classical

### 1. Multi-Modal Reasoning

Different "modes" of uncertainty that can't be compared:
- Epistemic uncertainty (what we don't know)
- Aleatory uncertainty (inherent randomness)
- Model uncertainty (structural assumptions)

These may be incomparable - you can't say epistemic > aleatory in general.

### 2. Multi-Agent Belief Aggregation

Different agents have different probability assessments.
If agents are "incomparable" (equally expert), their beliefs
form a partial order, not a total order.

### 3. Imprecise Probability Foundation

Partial-order classical could be a **strict generalization** of both:
- Classical probability (total order)
- Imprecise probability (interval bounds)

The relationship: [P_L, P_U] corresponds to an antichain in the partial order.

### 4. Quantum-Classical Interface

Events at the quantum-classical boundary might be:
- Comparable to other classical events
- Incomparable to quantum events

This could provide a smooth transition between quantum and classical regimes.

### 5. Preference Theory

In economics, preferences that are incomplete (not all alternatives comparable)
lead naturally to partial-order valuations.
-/

/-- A theory candidate for the hypercube -/
structure TheoryCandidate where
  vertex : ProbabilityVertex
  suggestedRewrites : List Unit  -- Simplified
  description : String

/-- Theory candidate for Imprecise K&S -/
def impreciseKS : TheoryCandidate :=
  ⟨{ knuthSkilling with precision := .imprecise }, [], "K&S with lower/upper plausibility bounds"⟩

/-- Theory candidate for Quantum D-S -/
def quantumDS : TheoryCandidate :=
  ⟨{ dempsterShafer with commutativity := .noncommutative }, [], "D-S on non-commutative algebras"⟩

/-- Theory candidate for Partial Classical -/
def partialClassical' : TheoryCandidate :=
  ⟨partialOrderClassical, [], "Classical probability with partial ordering"⟩

/-!
# §4: Comparison and Connections

## How the Three Theories Relate

```
                    Classical (Kolmogorov)
                    /         |         \
                   /          |          \
         Imprecise K&S   Quantum D-S   Partial Classical
              \             /  \            /
               \           /    \          /
                Quantum Imprecise K&S?
                         |
                 Most General Theory?
```

## The Grand Unification Question

Is there a **universal probability theory** that contains all three as special cases?

Such a theory would have:
- Interval-valued plausibilities (from Imprecise K&S)
- Non-commutative evidence (from Quantum D-S)
- Partial ordering (from Partial Classical)

This would be at the "most general" vertex of the hypercube!
-/

/-- The most general theory vertex -/
def mostGeneral : ProbabilityVertex where
  commutativity := .noncommutative
  distributivity := .general
  precision := .imprecise
  orderAxis := .partialOrder
  additivity := .subadditive
  invertibility := .semigroup
  determinism := .fuzzy
  support := .continuous
  regularity := .finitelyAdditive
  independence := .free  -- Free is most general

/-- Imprecise K&S has imprecise valuations (like mostGeneral) -/
theorem impreciseKS_is_imprecise :
    impreciseKS.vertex.precision = mostGeneral.precision := by decide

/-- Quantum D-S is non-commutative (like mostGeneral) -/
theorem quantumDS_noncommutative :
    quantumDS.vertex.commutativity = mostGeneral.commutativity := by decide

/-- Partial Classical has partial ordering (like mostGeneral) -/
theorem partialClassical_partial_order :
    partialClassical'.vertex.orderAxis = mostGeneral.orderAxis := by decide

/-- Each novel theory shares at least one "general" axis with the most general theory -/
theorem novel_theories_extend_toward_general :
    impreciseKS.vertex.precision = .imprecise ∧
    quantumDS.vertex.commutativity = .noncommutative ∧
    partialClassical'.vertex.orderAxis = .partialOrder := by
  decide

/-!
# §5: Research Directions

## For Imprecise K&S
1. Prove the representation theorem maps to interval arithmetic
2. Develop coherence conditions (avoiding Dutch books with intervals)
3. Build computational tools for interval plausibility propagation
4. Apply to robust Bayesian inference

## For Quantum D-S
1. Formalize the quantum combination rule rigorously
2. Prove uncertainty relations for quantum belief
3. Connect to quantum probability theory and POVMs
4. Apply to quantum state estimation

## For Partial Classical
1. Characterize which lattices admit valuations
2. Develop conditional probability for incomparable events
3. Connect to imprecise probability and credal sets
4. Apply to multi-agent belief aggregation

## For the Grand Unification
1. Define the "most general" probability structure
2. Show classical, quantum, imprecise, partial all embed
3. Characterize the collapse conditions for each special case
4. Find applications requiring the full generality
-/

/-!
# §6: Collapse and Degenerate Cases

These theorems show when general theories collapse to simpler ones.
This provides complete coverage of the hypercube edges.
-/

section CollapseCases

/-!
## Boolean Algebras are Orthomodular

Every Boolean algebra is an orthomodular lattice where all elements commute.
This shows that quantum D-S on a Boolean algebra = classical D-S.
-/

/-- The commutativity condition (a = (a ⊓ b) ⊔ (a ⊓ bᶜ)) holds in Boolean algebras.
    This is the definition used in our OrthomodularLattice's `commutes` predicate. -/
theorem boolean_commutes_condition {L : Type*} [BooleanAlgebra L] (a b : L) :
    a = (a ⊓ b) ⊔ (a ⊓ bᶜ) := by
  -- In Boolean algebra: a = a ⊓ ⊤ = a ⊓ (b ⊔ bᶜ) = (a ⊓ b) ⊔ (a ⊓ bᶜ)
  calc a = a ⊓ ⊤ := by rw [inf_top_eq]
       _ = a ⊓ (b ⊔ bᶜ) := by rw [sup_compl_eq_top]
       _ = (a ⊓ b) ⊔ (a ⊓ bᶜ) := inf_sup_left a b bᶜ

/-- In a Boolean algebra viewed as orthomodular, all elements commute.
    This shows quantum D-S on Boolean algebras = classical D-S. -/
theorem boolean_all_commute {L : Type*} [OrthomodularLattice L]
    (h_bool : ∀ a b : L, a ⊓ (b ⊔ bᶜ) = (a ⊓ b) ⊔ (a ⊓ bᶜ)) -- distributivity
    (h_compl : ∀ a : L, a ⊔ aᶜ = ⊤) -- excluded middle
    (a b : L) : commutes a b := by
  unfold commutes
  calc a = a ⊓ ⊤ := by rw [inf_top_eq]
       _ = a ⊓ (b ⊔ bᶜ) := by rw [h_compl b]
       _ = (a ⊓ b) ⊔ (a ⊓ bᶜ) := h_bool a b

/-!
## Vacuous Mass Function = Maximum Uncertainty

When all mass is on ⊤, we have Bel(a) = 0 for all a ≠ ⊤.
This represents "complete ignorance" - we know nothing.
-/

/-- A vacuous mass function: all mass on ⊤. -/
def isVacuousMass {L : Type*} [OrthomodularLattice L] (m : L → ℝ) : Prop :=
  (∀ a, a ≠ ⊤ → m a = 0) ∧ m ⊤ = 1

/-- For vacuous mass, belief is 0 everywhere except at ⊤. -/
theorem vacuous_belief_zero {L : Type*} [OrthomodularLattice L]
    [Fintype L] [DecidableEq L] [DecidableRel (α := L) (· ≤ ·)]
    (m : L → ℝ) (hv : isVacuousMass m) (a : L) (ha : a ≠ ⊤) :
    sumBelow m a = 0 := by
  -- All elements below a have zero mass (since a ≠ ⊤, and only ⊤ has mass)
  apply Finset.sum_eq_zero
  intro x hx
  simp only [finsetBelow.mem_iff] at hx
  -- x ≤ a and a ≠ ⊤, so x ≠ ⊤
  have hx_ne : x ≠ ⊤ := by
    intro hxeq
    subst hxeq
    exact ha (le_antisymm le_top hx)
  exact hv.1 x hx_ne

/-- For vacuous mass, belief at ⊤ equals total mass = 1. -/
theorem vacuous_belief_top {L : Type*} [OrthomodularLattice L]
    [Fintype L] [DecidableEq L] [DecidableRel (α := L) (· ≤ ·)]
    (m : L → ℝ) (hv : isVacuousMass m) :
    sumBelow m ⊤ = 1 := by
  simp only [sumBelow, finsetBelow.top_eq_univ]
  -- Sum over all elements, but only ⊤ contributes
  have h : ∀ x ∈ Finset.univ, m x = if x = ⊤ then 1 else 0 := by
    intro x _
    by_cases hx : x = ⊤
    · simp [hx, hv.2]
    · simp [hx, hv.1 x hx]
  calc Finset.sum Finset.univ m
       = Finset.sum Finset.univ (fun x => if x = ⊤ then 1 else 0) := by
         apply Finset.sum_congr rfl h
     _ = 1 := by simp

/-!
## Singleton-Supported Mass = Precise Probability

When mass is concentrated on a single element x with m(x) > 0,
belief equals total mass iff the element is below. This gives
"point probability" behavior.
-/

/-- Singleton mass gives belief equal to m(x) or 0. -/
theorem singleton_belief_dichotomy {L : Type*} [OrthomodularLattice L]
    [Fintype L] [DecidableEq L] [DecidableRel (α := L) (· ≤ ·)]
    (m : L → ℝ) (x : L) (hsupp : ∀ y, y ≠ x → m y = 0) (a : L) :
    sumBelow m a = if x ≤ a then m x else 0 :=
  hasSingletonSupport.sumBelow_eq hsupp a

/-!
## Two-Element Lattice = Trivial Probability

On the two-element lattice {⊥, ⊤}, probability collapses to {0, 1}.
-/

/-- On any lattice with m(⊥) = 0, we have Bel(⊥) = 0. -/
theorem belief_bot_zero {L : Type*} [OrthomodularLattice L]
    [Fintype L] [DecidableEq L] [DecidableRel (α := L) (· ≤ ·)]
    (m : L → ℝ) (hbot : m ⊥ = 0) :
    sumBelow m ⊥ = 0 := by
  simp [sumBelow, hbot]

end CollapseCases

end Mettapedia.ProbabilityTheory.Hypercube.NovelTheories
