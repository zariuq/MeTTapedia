/-
# Unified Uncertainty Theory

A single framework that captures Classical, Cox, K&S, Dempster-Shafer, and Quantum
probability as special cases of a parametrized structure.

## The Key Abstraction

ALL uncertainty theories share this structure:
1. A **lattice** of propositions/events (with varying properties)
2. A **valuation** assigning "plausibility" to propositions
3. **Combination rules** for composing evidence

The differences are captured by TYPE PARAMETERS:
- Lattice structure: Boolean vs Distributive vs Orthomodular
- Precision: Single valuation vs Lower/Upper pair
- Commutativity: Whether operations commute

## Benefits of Unification

1. **Prove once, use everywhere**: Theorems about the general structure
   automatically apply to all instantiations
2. **Clear axiom comparison**: See exactly which axioms distinguish theories
3. **Morphisms for free**: Specialization/generalization relationships emerge
4. **New theories**: The framework suggests unexplored vertices!
-/

import Mathlib.Order.Lattice
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.Hypercube.Basic

namespace Mettapedia.ProbabilityTheory.Hypercube.UnifiedTheory

open Hypercube

/-!
## §1: The Core Abstraction - Uncertainty Algebra

This captures the common structure of ALL uncertainty theories.
-/

/-- An uncertainty algebra over a lattice L with real-valued lower/upper bounds.
    This is the unified structure that captures all probability theories. -/
structure UncertaintyAlgebra (L : Type*) [Lattice L] [BoundedOrder L] where
  /-- The lower valuation (= belief, = probability for precise theories) -/
  lower : L → ℝ
  /-- The upper valuation (= plausibility, = lower for precise theories) -/
  upper : L → ℝ
  /-- Lower ≤ Upper always -/
  lower_le_upper : ∀ a, lower a ≤ upper a
  /-- Monotonicity of lower -/
  lower_mono : ∀ a b, a ≤ b → lower a ≤ lower b
  /-- Normalization: ⊥ → 0 -/
  lower_bot : lower ⊥ = 0
  /-- Normalization: ⊤ → 1 -/
  upper_top : upper ⊤ = 1

namespace UncertaintyAlgebra

variable {L : Type*} [Lattice L] [BoundedOrder L]

/-- A theory is **precise** if lower = upper everywhere. -/
def IsPrecise (U : UncertaintyAlgebra L) : Prop := ∀ a, U.lower a = U.upper a

/-- The imprecision gap at a proposition. -/
def gap (U : UncertaintyAlgebra L) (a : L) : ℝ := U.upper a - U.lower a

/-- Gap is always non-negative. -/
theorem gap_nonneg (U : UncertaintyAlgebra L) (a : L) : 0 ≤ U.gap a := by
  simp only [gap]
  linarith [U.lower_le_upper a]

/-- For precise theories, gap is zero everywhere. -/
theorem precise_gap_zero (U : UncertaintyAlgebra L) (hU : U.IsPrecise) (a : L) :
    U.gap a = 0 := by
  simp only [gap, hU a, sub_self]

/-- Lower valuation of ⊥ is minimal. -/
theorem lower_bot_minimal (U : UncertaintyAlgebra L) (a : L) :
    U.lower ⊥ ≤ U.lower a := by
  apply U.lower_mono
  exact bot_le

/-- Lower valuation of ⊤ is maximal. -/
theorem lower_top_maximal (U : UncertaintyAlgebra L) (a : L) :
    U.lower a ≤ U.lower ⊤ := by
  apply U.lower_mono
  exact le_top

end UncertaintyAlgebra

/-!
## §2: Specific Theory Structures

Each probability theory is captured as a structure with appropriate constraints.
-/

/-- Classical (Kolmogorov) probability: Boolean lattice, precise, additive. -/
structure KolmogorovProbability (L : Type*) [BooleanAlgebra L] where
  /-- The probability measure -/
  P : L → ℝ
  /-- Normalization -/
  P_bot : P ⊥ = 0
  P_top : P ⊤ = 1
  /-- Monotonicity -/
  P_mono : ∀ a b, a ≤ b → P a ≤ P b
  /-- Additivity for disjoint -/
  P_additive : ∀ a b, a ⊓ b = ⊥ → P (a ⊔ b) = P a + P b

/-- Dempster-Shafer belief function: imprecise (Bel ≤ Pl). -/
structure BeliefFunction (L : Type*) [BooleanAlgebra L] where
  /-- Belief (lower probability) -/
  Bel : L → ℝ
  /-- Plausibility (upper probability) -/
  Pl : L → ℝ
  /-- Normalization -/
  Bel_bot : Bel ⊥ = 0
  Bel_top : Bel ⊤ = 1
  /-- Bel ≤ Pl always -/
  Bel_le_Pl : ∀ a, Bel a ≤ Pl a
  /-- Duality -/
  Pl_dual : ∀ a, Pl a = 1 - Bel aᶜ
  /-- Monotonicity -/
  Bel_mono : ∀ a b, a ≤ b → Bel a ≤ Bel b

/-- K&S probability: derived from associativity + Archimedean. -/
structure KSProbability (L : Type*) [DistribLattice L] [BoundedOrder L] [LinearOrder L] where
  /-- The combination operation -/
  op : L → L → L
  /-- Identity -/
  ident : L
  /-- Associativity -/
  assoc : ∀ x y z, op (op x y) z = op x (op y z)
  /-- Identity laws -/
  ident_right : ∀ x, op x ident = x
  ident_left : ∀ x, op ident x = x
  /-- Strict monotonicity -/
  strictMono_left : ∀ y, StrictMono (fun x => op x y)
  strictMono_right : ∀ x, StrictMono (fun y => op x y)
  /-- Archimedean -/
  archimedean : ∀ x y, ident < x → ∃ n : ℕ, y < Nat.iterate (op x) n x
  /-- Positivity -/
  ident_le : ∀ x, ident ≤ x

/-!
## §3: Embeddings into the Unified Framework

Each specific theory embeds into UncertaintyAlgebra.
-/

/-- Kolmogorov probability → UncertaintyAlgebra (precise). -/
def KolmogorovProbability.toUA {L : Type*} [BooleanAlgebra L]
    (K : KolmogorovProbability L) : UncertaintyAlgebra L where
  lower := K.P
  upper := K.P  -- Precise!
  lower_le_upper := fun _ => le_refl _
  lower_mono := K.P_mono
  lower_bot := K.P_bot
  upper_top := K.P_top

/-- Kolmogorov is precise. -/
theorem KolmogorovProbability.isPrecise {L : Type*} [BooleanAlgebra L]
    (K : KolmogorovProbability L) : K.toUA.IsPrecise :=
  fun _ => rfl

/-- Belief function → UncertaintyAlgebra (imprecise). -/
def BeliefFunction.toUA {L : Type*} [BooleanAlgebra L]
    (B : BeliefFunction L) : UncertaintyAlgebra L where
  lower := B.Bel
  upper := B.Pl
  lower_le_upper := B.Bel_le_Pl
  lower_mono := B.Bel_mono
  lower_bot := B.Bel_bot
  upper_top := by
    rw [B.Pl_dual]
    simp [B.Bel_bot]

/-!
## §4: Universal Theorems

These hold for ALL uncertainty theories.
-/

section UniversalTheorems

variable {L : Type*} [Lattice L] [BoundedOrder L]
variable (U : UncertaintyAlgebra L)

/-- Lower valuation is bounded in [0, upper(⊤)]. -/
theorem lower_bounded (a : L) : U.lower ⊥ ≤ U.lower a ∧ U.lower a ≤ U.lower ⊤ :=
  ⟨U.lower_bot_minimal a, U.lower_top_maximal a⟩

/-- Monotonicity preserves ordering for lower. -/
theorem lower_ordered (a b : L) (hab : a ≤ b) : U.lower a ≤ U.lower b :=
  U.lower_mono a b hab

end UniversalTheorems

/-!
## §5: The Specialization Hierarchy

Different theories form a partial order by "adding axioms".
-/

/-- Theory T₁ specializes T₂ if T₁ has more structure (more axioms). -/
def Specializes (V₁ V₂ : ProbabilityVertex) : Prop :=
  -- Commutative specializes non-commutative
  (V₁.commutativity = .commutative ∨ V₂.commutativity = .noncommutative) ∧
  -- Precise specializes imprecise
  (V₁.precision = .precise ∨ V₂.precision = .imprecise) ∧
  -- Total order specializes partial order
  (V₁.orderAxis = .totalOrder ∨ V₂.orderAxis = .partialOrder)

/-- Kolmogorov specializes D-S. -/
theorem kolmogorov_specializes_ds : Specializes kolmogorov dempsterShafer := by
  constructor
  · left; rfl
  constructor
  · left; rfl
  · left; rfl

/-- Kolmogorov specializes Quantum. -/
theorem kolmogorov_specializes_quantum : Specializes kolmogorov quantum := by
  constructor
  · left; rfl
  constructor
  · left; rfl
  · left; rfl

/-- K&S and Cox are equivalent in the hypercube. -/
theorem ks_equiv_cox : Specializes knuthSkilling cox ∧ Specializes cox knuthSkilling := by
  constructor
  · -- K&S specializes Cox
    constructor
    · left; rfl
    · constructor
      · left; rfl
      · left; rfl
  · -- Cox specializes K&S
    constructor
    · left; rfl
    · constructor
      · left; rfl
      · left; rfl

/-!
## §6: Practical Refactoring: Common Lemma Library

The hypercube framework suggests factoring out these common components:
-/

/-- Common monotonicity lemma: works for any uncertainty theory. -/
theorem common_mono {L : Type*} [Lattice L] [BoundedOrder L]
    (f : L → ℝ) (hf : ∀ a b, a ≤ b → f a ≤ f b) (a b : L) (hab : a ≤ b) :
    f a ≤ f b := hf a b hab

/-- Common normalization lemma: f(⊥) = 0 and f(⊤) = 1 implies 0 ≤ f(a) ≤ 1
    for monotone f. -/
theorem common_bounds {L : Type*} [Lattice L] [BoundedOrder L]
    (f : L → ℝ) (hf_mono : ∀ a b, a ≤ b → f a ≤ f b)
    (hf_bot : f ⊥ = 0) (hf_top : f ⊤ = 1) (a : L) :
    0 ≤ f a ∧ f a ≤ 1 := by
  constructor
  · calc 0 = f ⊥ := hf_bot.symm
       _ ≤ f a := hf_mono ⊥ a bot_le
  · calc f a ≤ f ⊤ := hf_mono a ⊤ le_top
       _ = 1 := hf_top

/-!
## §7: Summary - How This Helps

### Immediate Benefits

1. **Shared lemmas**: `common_mono`, `common_bounds`, etc. work everywhere
2. **Type-safe parametrization**: Can't accidentally mix incompatible theories
3. **Clear axiom comparison**: Visible what distinguishes each theory

### Suggested Refactoring for Existing Code

1. **Factor out**: Create `Mettapedia/ProbabilityTheory/Common/` with:
   - `Monotonicity.lean`: Shared monotonicity lemmas
   - `Bounds.lean`: Normalization and bound lemmas
   - `Lattice.lean`: Common lattice operations

2. **Parameterize proofs**: Rewrite key theorems in terms of `UncertaintyAlgebra`

3. **Unify combination rules**: All theories have some combination rule:
   - Classical: multiplication P(A)P(B|A)
   - D-S: Dempster's rule
   - K&S: the ⊕ operation
   - Quantum: tensor product
   All can be abstracted!

### The K&S Question Clarified

The hypercube shows that K&S is "natural" because:
- It DERIVES commutativity (doesn't assume it)
- Uses weaker lattice structure than Cox
- But requires LinearOrder (stronger than D-S)

The "central question" about K&S is: does the representation theorem
PROOF actually need commutativity, or does commutativity emerge from
associativity + Archimedean + LinearOrder?
-/

end Mettapedia.ProbabilityTheory.Hypercube.UnifiedTheory
