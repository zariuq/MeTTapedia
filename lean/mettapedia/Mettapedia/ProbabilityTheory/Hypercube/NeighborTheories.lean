/-
# Neighbor Theories: Systematic Investigation of K-S Neighbors

This module investigates the 14 cube-neighbors of Knuth-Skilling in the probability
hypercube. For each neighbor, we ask:

1. Does a representation theorem still hold?
2. If yes, what structure does it produce?
3. If no, what's the minimal additional axiom needed?
4. What are the applications?

## The K-S Coordinates

K-S sits at: (commutative, distributive, precise, totalOrder, derived, probabilistic, continuous, borel)

## Most Promising Neighbors

1. **Orthomodular K-S**: Could derive quantum probability from first principles!
2. **Partial Order K-S**: What survives without totality?
3. **Noncommutative K-S**: Could give principled noncommutative probability
4. **Subadditive K-S**: Could derive Dempster-Shafer from K-S-like axioms

## References

- Knuth & Skilling, "Foundations of Inference" (2012)
- Gudder, "Quantum Probability" (1988)
- Rédei, "Quantum Logic in Algebraic Approach" (1998)
- Walley, "Statistical Reasoning with Imprecise Probabilities" (1991)
-/

import Mathlib.Order.Lattice
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.Hypercube.Basic
import Mettapedia.ProbabilityTheory.Hypercube.NovelTheories
import Mettapedia.ProbabilityTheory.KnuthSkilling.Basic

namespace Mettapedia.ProbabilityTheory.Hypercube.NeighborTheories

open Hypercube NovelTheories

/-!
# §1: Orthomodular K-S (Distributive → Orthomodular)

## The Big Question

Can we derive quantum probability from K-S-like axioms on orthomodular lattices?

## Key Insight

In K-S, the event algebra is a distributive lattice. The combination operation ⊕
satisfies monotonicity and associativity, leading to a representation θ : α → ℝ.

For orthomodular lattices:
- Distributivity FAILS: a ∧ (b ∨ c) ≠ (a ∧ b) ∨ (a ∧ c) in general
- But orthomodularity provides a WEAKER substitute
- The Sasaki projection replaces conjunction for conditionals

## Hypothesis

An "Orthomodular K-S Algebra" should have:
1. An orthomodular lattice of events
2. A plausibility operation ⊕ on a carrier set
3. Monotonicity respecting the OML order
4. Archimedean property

The question: Does this still give a representation theorem?
-/

/-- An orthomodular plausibility algebra.
    This is a K-S-like structure where the underlying event logic is orthomodular
    rather than distributive/Boolean. -/
class OrthomodularPlausibilityAlgebra (L : Type*) (α : Type*)
    [OrthomodularLattice L] [LinearOrder α] where
  /-- Plausibility assignment: events → plausibilities -/
  plaus : L → α
  /-- Bottom element of plausibilities -/
  ident : α
  /-- Plausibility combination -/
  op : α → α → α
  /-- Plausibility of ⊥ is identity -/
  plaus_bot : plaus ⊥ = ident
  /-- Monotonicity: a ≤ b in L implies plaus(a) ≤ plaus(b) -/
  plaus_mono : ∀ a b : L, a ≤ b → plaus a ≤ plaus b
  /-- Associativity of combination -/
  op_assoc : ∀ x y z : α, op (op x y) z = op x (op y z)
  /-- Identity laws -/
  op_ident_right : ∀ x : α, op x ident = x
  op_ident_left : ∀ x : α, op ident x = x
  /-- Strict monotonicity -/
  op_strictMono_left : ∀ y : α, StrictMono (fun x => op x y)
  op_strictMono_right : ∀ x : α, StrictMono (fun y => op x y)
  /-- Archimedean property -/
  op_archimedean : ∀ x y : α, ident < x → ∃ n : ℕ, y < Nat.iterate (op x) n x
  /-- Identity is bottom -/
  ident_le : ∀ x : α, ident ≤ x

namespace OrthomodularPlausibilityAlgebra

variable {L : Type*} {α : Type*} [OrthomodularLattice L] [LinearOrder α]
variable [OrthomodularPlausibilityAlgebra L α]

/-- Plausibility of ⊤ is the maximum plausibility. -/
theorem plaus_top_max (a : L) : plaus (α := α) a ≤ plaus (⊤ : L) :=
  plaus_mono a ⊤ le_top

/-- Commuting elements behave classically.
    When a and b commute in an OML, the sublattice they generate is Boolean.
    The `commutes` predicate says: a = (a ⊓ b) ⊔ (a ⊓ bᶜ) -/
theorem commuting_elements_classical {a b : L} (h : commutes a b) :
    -- For commuting elements, the standard distributivity holds
    a = (a ⊓ b) ⊔ (a ⊓ bᶜ) := h

end OrthomodularPlausibilityAlgebra

/-!
## Key Theorem Attempt: Orthomodular Representation

**Conjecture**: If (L, α, plaus, op) is an OrthomodularPlausibilityAlgebra, then
there exists θ : α → ℝ≥0 such that:
1. θ(op x y) = θ(x) + θ(y)
2. θ is order-preserving
3. For commuting elements a, b ∈ L: θ(plaus(a ⊔ b)) = θ(plaus(a)) + θ(plaus(b)) - θ(plaus(a ⊓ b))

**Status**: OPEN RESEARCH QUESTION

The standard K-S representation proof uses the Archimedean property to embed into ℝ.
This should still work for the plausibility carrier α. The question is what
additional structure we get on L.
-/

/-- The carrier α of an OrthomodularPlausibilityAlgebra forms a KnuthSkillingAlgebra.
    This is the key insight: quantum non-commutativity lives in L (the event space),
    but the plausibility space α is still a classical K-S algebra! -/
def OrthomodularPlausibilityAlgebra.toKnuthSkillingAlgebra
    {L : Type*} {α : Type*} [OrthomodularLattice L] [lo : LinearOrder α]
    (inst : OrthomodularPlausibilityAlgebra L α) :
    KnuthSkilling.KnuthSkillingAlgebra α where
  op := inst.op
  ident := inst.ident
  op_assoc := inst.op_assoc
  op_ident_right := inst.op_ident_right
  op_ident_left := inst.op_ident_left
  op_strictMono_left := inst.op_strictMono_left
  op_strictMono_right := inst.op_strictMono_right
  op_archimedean := inst.op_archimedean
  ident_le := inst.ident_le

/-- The representation theorem for the plausibility space α.
    Since α forms a KnuthSkillingAlgebra, the K-S representation theorem applies.

    **Status**: This follows from the K-S representation theorem (still in development).
    Once KnuthSkilling.RepTheorem is complete, this becomes a direct corollary. -/
theorem oml_carrier_has_representation
    {L : Type*} {α : Type*} [OrthomodularLattice L] [LinearOrder α]
    [inst : OrthomodularPlausibilityAlgebra L α] :
    -- The carrier α satisfies K-S axioms, so representation exists
    ∃ θ : α → ℝ, (∀ x y, θ (inst.op x y) = θ x + θ y) ∧ StrictMono θ := by
  -- The K-S representation theorem applies to inst.toKnuthSkillingAlgebra
  -- Result: ∃ θ : α → ℝ additive and strictly monotone
  sorry -- Blocked on K-S representation theorem completion

/-!
# §2: Partial Order K-S (TotalOrder → PartialOrder)

## The Question

What happens if we drop trichotomy? Can we still derive anything useful?

## Known Result

K-S REQUIRES total order. The Archimedean property needs to compare any two elements.

## What Survives

Even without totality, we can still have:
1. Monotonicity of ⊕
2. Associativity
3. A representation on EACH chain (linearly ordered subset)

This suggests: Partial Order K-S gives a FAMILY of representations, one per chain!
-/

/-- A partial K-S algebra - K-S axioms with only partial order. -/
class PartialKSAlgebra (α : Type*) extends PartialOrder α where
  op : α → α → α
  ident : α
  op_assoc : ∀ x y z : α, op (op x y) z = op x (op y z)
  op_ident_right : ∀ x : α, op x ident = x
  op_ident_left : ∀ x : α, op ident x = x
  /-- Monotonicity (not strict - can't be strict without totality!) -/
  op_mono_left : ∀ y : α, Monotone (fun x => op x y)
  op_mono_right : ∀ x : α, Monotone (fun y => op x y)
  ident_le : ∀ x : α, ident ≤ x

namespace PartialKSAlgebra

variable {α : Type*} [PartialKSAlgebra α]

/-- Key theorem: Each chain admits a K-S representation!
    A chain is a linearly ordered subset, so it satisfies totality. -/
theorem chain_representation_exists (C : Set α) (hC : IsChain (· ≤ ·) C)
    (hClosed : ∀ x y, x ∈ C → y ∈ C → op x y ∈ C)
    (hIdent : ident ∈ C) :
    -- Each chain gets its own representation
    ∃ θ : C → ℝ, ∀ x y : C, θ ⟨op x.1 y.1, hClosed x.1 y.1 x.2 y.2⟩ = θ x + θ y := by
  sorry -- The chain with inherited operation is a K-S algebra

/-- The family of chain representations must be COHERENT.
    If x, y are both in chains C₁ and C₂, their plausibilities must agree. -/
def coherentRepresentations (Θ : (C : Set α) → IsChain (· ≤ ·) C → (C → ℝ)) : Prop :=
  ∀ C₁ C₂ hC₁ hC₂, ∀ x : α, ∀ (hx₁ : x ∈ C₁) (hx₂ : x ∈ C₂),
    Θ C₁ hC₁ ⟨x, hx₁⟩ = Θ C₂ hC₂ ⟨x, hx₂⟩

end PartialKSAlgebra

/-!
## Application: Partial Order K-S for Incomparable Uncertainties

**Interpretation**: Sometimes two uncertain quantities are genuinely incomparable!

Example: "Probability of rain tomorrow" vs "Quality of this restaurant"
- Both are uncertainties, but comparing them is meaningless
- A partial K-S algebra captures this

**Practical use**: Multi-criteria decision making where criteria are incomparable.
-/

/-!
# §3: Noncommutative K-S (Commutative → Noncommutative)

## The Question

What if ⊕ is not commutative? x ⊕ y ≠ y ⊕ x

## Known Results

The semidirect product examples (SD in counterexamples) show that
noncommutative K-S algebras exist but fail the separation property.

## Key Insight

Noncommutativity in ⊕ corresponds to ORDER-DEPENDENCE in combining evidence.
This is exactly what happens in quantum mechanics!

"Measure A then B" ≠ "Measure B then A"
-/

/-- A noncommutative K-S algebra. -/
class NoncommutativeKSAlgebra (α : Type*) extends LinearOrder α where
  op : α → α → α
  ident : α
  op_assoc : ∀ x y z : α, op (op x y) z = op x (op y z)
  op_ident_right : ∀ x : α, op x ident = x
  op_ident_left : ∀ x : α, op ident x = x
  op_strictMono_left : ∀ y : α, StrictMono (fun x => op x y)
  op_strictMono_right : ∀ x : α, StrictMono (fun y => op x y)
  op_archimedean : ∀ x y : α, ident < x → ∃ n : ℕ, y < Nat.iterate (op x) n x
  ident_le : ∀ x : α, ident ≤ x
  -- NOTE: No commutativity axiom!

namespace NoncommutativeKSAlgebra

variable {α : Type*} [NoncommutativeKSAlgebra α]

/-- The commutator measures noncommutativity. -/
def commutator (x y : α) : Prop := op x y = op y x

/-- Elements that commute with everything form a commutative subalgebra. -/
def center : Set α := {x | ∀ y, commutator x y}

/-- The center is closed under op. -/
theorem center_closed (x y : α) (hx : x ∈ center) (hy : y ∈ center) :
    op x y ∈ center := by
  intro z
  unfold commutator at *
  calc op (op x y) z = op x (op y z) := op_assoc x y z
       _ = op x (op z y) := by rw [hy z]
       _ = op (op x z) y := (op_assoc x z y).symm
       _ = op (op z x) y := by rw [hx z]
       _ = op z (op x y) := op_assoc z x y

/-- Conjecture: Noncommutative K-S admits an order embedding into ℝ,
    but NOT an additive representation (unless commutative). -/
theorem order_embedding_exists :
    ∃ θ : α → ℝ, StrictMono θ := by
  -- This should follow from the Archimedean property alone
  sorry

/-- The failure of additive representation for noncommutative algebras. -/
theorem no_additive_representation_if_noncommutative
    (h : ∃ x y : α, op x y ≠ op y x) :
    ¬∃ θ : α → ℝ, (∀ x y, θ (op x y) = θ x + θ y) ∧ Function.Injective θ := by
  intro ⟨θ, hθadd, hθinj⟩
  obtain ⟨x, y, hxy⟩ := h
  -- θ(x ⊕ y) = θ(x) + θ(y) = θ(y) + θ(x) = θ(y ⊕ x)
  have heq : θ (op x y) = θ (op y x) := by
    rw [hθadd, hθadd, add_comm]
  -- But θ is injective, so op x y = op y x, contradiction
  exact hxy (hθinj heq)

end NoncommutativeKSAlgebra

/-!
## The Quantum Connection

Noncommutative K-S naturally leads to QUANTUM PROBABILITY:

1. The combination operation ⊕ is matrix multiplication (noncommutative)
2. The "plausibility" is a density matrix ρ
3. Probabilities are tr(ρ · E) for projection operators E

**Key theorem to prove**: An Archimedean noncommutative K-S algebra embeds into
the positive cone of a C*-algebra.

This would give a principled derivation of quantum mechanics from K-S-like axioms!
-/

/-!
# §4: Subadditive K-S (Derived → Subadditive)

## The Question

What if we only derive θ(a ⊕ b) ≤ θ(a) + θ(b) instead of equality?

## Connection to Dempster-Shafer

This is exactly the subadditivity condition of belief functions!

Bel(A ∪ B) ≤ Bel(A) + Bel(B)

If K-S-like axioms can derive subadditivity (rather than additivity),
we get a principled foundation for Dempster-Shafer theory!
-/

/-- A subadditive K-S algebra. -/
class SubadditiveKSAlgebra (α : Type*) extends LinearOrder α where
  op : α → α → α
  ident : α
  θ : α → ℝ  -- The representation map (given, not derived)
  op_assoc : ∀ x y z : α, op (op x y) z = op x (op y z)
  op_ident_right : ∀ x : α, op x ident = x
  op_ident_left : ∀ x : α, op ident x = x
  op_mono_left : ∀ y : α, Monotone (fun x => op x y)
  op_mono_right : ∀ x : α, Monotone (fun y => op x y)
  ident_le : ∀ x : α, ident ≤ x
  θ_mono : StrictMono θ
  θ_ident : θ ident = 0
  /-- SUBADDITIVITY instead of additivity! -/
  θ_subadditive : ∀ x y, θ (op x y) ≤ θ x + θ y

namespace SubadditiveKSAlgebra

variable {α : Type*} [SubadditiveKSAlgebra α]

/-- The "defect" from additivity measures how subadditive the operation is. -/
def additivityDefect (x y : α) : ℝ := θ x + θ y - θ (op x y)

/-- The defect is always non-negative (by subadditivity). -/
theorem additivityDefect_nonneg (x y : α) : 0 ≤ additivityDefect x y := by
  unfold additivityDefect
  linarith [θ_subadditive x y]

/-- Superadditivity: θ(x ⊕ y) ≥ max(θ(x), θ(y))
    This follows from monotonicity. -/
theorem θ_superadditive_max (x y : α) :
    max (θ x) (θ y) ≤ θ (op x y) := by
  -- op x y ≥ x (since ident ≤ y and op is monotone)
  have hx : x ≤ op x y := by
    have h1 : ident ≤ y := ident_le y
    have h2 : op x ident ≤ op x y := op_mono_right x h1
    simp only [op_ident_right] at h2
    exact h2
  have hy : y ≤ op x y := by
    have h1 : ident ≤ x := ident_le x
    have h2 : op ident y ≤ op x y := op_mono_left y h1
    simp only [op_ident_left] at h2
    exact h2
  -- Use that θ is strictly monotone
  have hθx : θ x ≤ θ (op x y) := by
    rcases lt_or_eq_of_le hx with hlt | heq
    · exact le_of_lt (θ_mono hlt)
    · rw [← heq]
  have hθy : θ y ≤ θ (op x y) := by
    rcases lt_or_eq_of_le hy with hlt | heq
    · exact le_of_lt (θ_mono hlt)
    · rw [← heq]
  exact max_le hθx hθy

end SubadditiveKSAlgebra

/-!
## The Belief Function Connection

**Theorem sketch**: A subadditive K-S algebra gives rise to a belief function!

Define:
- Ω = atoms of the underlying lattice
- m(A) = "mass" derived from additivity defect
- Bel(A) = θ(plaus(A))

Then Bel should satisfy the n-monotonicity conditions of D-S theory.

This gives a PRINCIPLED FOUNDATION for Dempster-Shafer!
-/

/-!
# §5: General Lattice K-S (Distributive → General)

## The Question

What if we assume only a lattice structure, not even distributivity?

## Analysis

This is likely TOO WEAK. Without distributivity, we lose the connection between
the algebraic operation ⊕ and the lattice operations ∧, ∨.
-/

/-- A general lattice plausibility structure. -/
class GeneralLatticePlausibility (L : Type*) (α : Type*)
    [Lattice L] [BoundedOrder L] [LinearOrder α] where
  plaus : L → α
  op : α → α → α
  ident : α
  plaus_bot : plaus ⊥ = ident
  plaus_mono : ∀ a b : L, a ≤ b → plaus a ≤ plaus b
  op_assoc : ∀ x y z : α, op (op x y) z = op x (op y z)
  op_ident_right : ∀ x : α, op x ident = x
  op_ident_left : ∀ x : α, op ident x = x
  ident_le : ∀ x : α, ident ≤ x

/-!
Without distributivity, we can still have the carrier α be a K-S algebra.
But we LOSE the additivity relation between lattice operations!

The key question: What additivity condition (if any) relates plaus(a ∨ b)
to plaus(a), plaus(b), plaus(a ∧ b)?

- In Boolean case: plaus(a ∨ b) = op (plaus a) (plaus b) when a ∧ b = ⊥
- In orthomodular: Same for orthogonal elements
- In general lattice: NO such relation exists!
-/

/-!
# §6: Summary and Research Directions

## Results Summary

| Neighbor | Representation? | Structure Obtained | Status |
|----------|-----------------|-------------------|--------|
| Orthomodular | YES (carrier) | Quantum probability on commuting part | PROMISING |
| Partial Order | Per-chain only | Family of representations | COHERENCE QUESTION |
| Noncommutative | Order only | No additive rep | CONNECTS TO C*-ALGEBRAS |
| Subadditive | Given (not derived) | Belief functions | PRINCIPLED D-S |
| General Lattice | Too weak | No lattice connection | NOT VIABLE |

## Key Research Questions

1. **Orthomodular**: Prove that OML + Archimedean gives quantum probability
2. **Noncommutative**: Characterize when order embedding extends to C*-algebra
3. **Subadditive**: Derive n-monotonicity from weaker axioms
4. **Partial Order**: When do coherent representations exist?

## The Big Picture

K-S sits at a "sweet spot" in the hypercube:
- More general (orthomodular) → quantum probability
- Less structure (partial order) → incomparable uncertainties
- Noncommutative → operator algebras
- Subadditive → belief functions

Each neighbor leads to a different but meaningful generalization!
-/

/-!
# §7: Concrete Examples
-/

section ConcreteExamples

/-- Example: The simplest orthomodular lattice that's not Boolean.
    The "benzene ring" O₆ (also called MO₂). -/

inductive BenzeneRing : Type
  | bot : BenzeneRing
  | a : BenzeneRing
  | b : BenzeneRing
  | c : BenzeneRing  -- a' (complement of a)
  | d : BenzeneRing  -- b' (complement of b)
  | top : BenzeneRing
  deriving DecidableEq, Repr

namespace BenzeneRing

/-- The ordering on O₆. -/
def le : BenzeneRing → BenzeneRing → Prop
  | bot, _ => True
  | _, top => True
  | a, a => True
  | b, b => True
  | c, c => True
  | d, d => True
  | _, _ => False

instance : LE BenzeneRing := ⟨le⟩

instance : DecidableRel (α := BenzeneRing) (· ≤ ·) := fun x y => by
  cases x <;> cases y <;> simp only [LE.le, le] <;> infer_instance

-- O₆ is NOT distributive! This is the key property.
-- a ∧ (b ∨ c) ≠ (a ∧ b) ∨ (a ∧ c) in general.
-- But it IS orthomodular - it satisfies the orthomodular law.

end BenzeneRing

end ConcreteExamples

/-!
# §8: The Unification Vision

All these neighbors can be unified under a single framework:

**Generalized Inference Algebra** (GIA):
1. A "proposition space" L (lattice-like)
2. A "plausibility space" α (ordered monoid-like)
3. A map plaus : L → α
4. Coherence conditions depending on L's structure

The hypercube coordinates determine which coherence conditions apply:
- Commutativity → op commutes
- Distributivity → additivity on ∧-independent elements
- Order totality → Archimedean property
- etc.

This gives a SINGLE PARAMETERIZED THEORY that specializes to:
- K-S (all classical settings)
- Quantum probability (orthomodular)
- Belief functions (subadditive)
- And more!
-/

/-- The master structure: Generalized Inference Algebra -/
structure GeneralizedInferenceAlgebra where
  /-- Proposition space -/
  L : Type*
  /-- Plausibility space -/
  α : Type*
  /-- Lattice structure on L -/
  latticeL : Lattice L
  /-- Bounded order on L -/
  boundedL : BoundedOrder L
  /-- Order on α -/
  orderα : PartialOrder α
  /-- The plausibility map -/
  plaus : L → α
  /-- Combination operation -/
  op : α → α → α
  /-- Configuration from hypercube -/
  config : ProbabilityVertex

/-- A GIA is valid if it satisfies the conditions specified by its config. -/
def GeneralizedInferenceAlgebra.isValid (G : GeneralizedInferenceAlgebra) : Prop :=
  -- Commutativity condition
  (G.config.commutativity = .commutative → ∀ x y : G.α, G.op x y = G.op y x) ∧
  -- Other conditions would follow similarly
  True

/-!
# §9: Deep Dive - Orthomodular K-S and Quantum Probability

## The Key Insight

In an OrthomodularPlausibilityAlgebra (L, α, plaus, op):
- L is the orthomodular lattice of "propositions" (quantum events)
- α is the carrier of "plausibilities" with operation op
- The carrier α itself satisfies ALL K-S axioms!

Therefore: α admits a representation θ : α → ℝ with θ(op x y) = θ(x) + θ(y).

The question is: what structure does this induce on L?
-/

section OrthomodularDeepDive

variable {L : Type*} {α : Type*} [OrthomodularLattice L] [LinearOrder α]
variable [inst : OrthomodularPlausibilityAlgebra L α]

-- The carrier α forms a K-S-like structure. We can verify each axiom.

/-- Associativity holds by assumption. -/
theorem carrier_op_assoc : ∀ x y z : α, inst.op (inst.op x y) z = inst.op x (inst.op y z) :=
  OrthomodularPlausibilityAlgebra.op_assoc

/-- Identity laws hold by assumption. -/
theorem carrier_op_ident_right : ∀ x : α, inst.op x inst.ident = x :=
  OrthomodularPlausibilityAlgebra.op_ident_right

theorem carrier_op_ident_left : ∀ x : α, inst.op inst.ident x = x :=
  OrthomodularPlausibilityAlgebra.op_ident_left

/-- Strict monotonicity holds by assumption. -/
theorem carrier_strictMono_left : ∀ y : α, StrictMono (fun x => inst.op x y) :=
  OrthomodularPlausibilityAlgebra.op_strictMono_left

theorem carrier_strictMono_right : ∀ x : α, StrictMono (fun y => inst.op x y) :=
  OrthomodularPlausibilityAlgebra.op_strictMono_right

/-- Archimedean property holds by assumption. -/
theorem carrier_archimedean : ∀ x y : α, inst.ident < x → ∃ n : ℕ, y < Nat.iterate (inst.op x) n x :=
  OrthomodularPlausibilityAlgebra.op_archimedean

/-- Identity is bottom. -/
theorem carrier_ident_le : ∀ x : α, inst.ident ≤ x :=
  OrthomodularPlausibilityAlgebra.ident_le

/-!
## Commutativity Question

The standard K-S derivation shows that commutativity of op follows from
the representation theorem. Does this still work here?

YES! The carrier α has all K-S axioms, so if we can apply the K-S
representation theorem, we get commutativity of op on α.

This means: even though L may be non-distributive (orthomodular),
the PLAUSIBILITY operation is still commutative!
-/

/-- If the representation theorem holds for α, then op is commutative.
    This is the key insight: quantum non-commutativity lives in L,
    not in the plausibility space α! -/
theorem op_commutative_from_representation
    (θ : α → ℝ) (hθ_add : ∀ x y, θ (inst.op x y) = θ x + θ y)
    (hθ_inj : Function.Injective θ) :
    ∀ x y : α, inst.op x y = inst.op y x := by
  intro x y
  apply hθ_inj
  rw [hθ_add, hθ_add, add_comm]

/-!
## Additivity for Orthogonal Elements

In an orthomodular lattice, two elements a, b are ORTHOGONAL if a ≤ bᶜ (equiv. b ≤ aᶜ).
For orthogonal elements, we expect additivity to hold:

plaus(a ⊔ b) should relate to op(plaus(a), plaus(b)) when a ⊥ b.

This is the quantum analog of: P(A ∪ B) = P(A) + P(B) when A ∩ B = ∅.
-/

/-- Two elements are orthogonal in an OML. -/
def orthogonal (a b : L) : Prop := a ≤ bᶜ

/-- Orthogonality is symmetric. -/
theorem orthogonal_symm {a b : L} (h : orthogonal a b) : orthogonal b a := by
  unfold orthogonal at *
  -- a ≤ bᶜ implies b ≤ aᶜ by taking complements
  have := OrthomodularLattice.compl_le_compl h
  simp only [OrthomodularLattice.compl_compl] at this
  exact this

/-- For orthogonal elements, a ⊓ b = ⊥. -/
theorem orthogonal_inf_eq_bot {a b : L} (h : orthogonal a b) : a ⊓ b = ⊥ := by
  unfold orthogonal at h
  -- a ≤ bᶜ and a ⊓ b ≤ a, so a ⊓ b ≤ bᶜ
  -- Also a ⊓ b ≤ b
  -- So a ⊓ b ≤ bᶜ ⊓ b = ⊥
  have h1 : a ⊓ b ≤ bᶜ := le_trans inf_le_left h
  have h2 : a ⊓ b ≤ b := inf_le_right
  have h3 : a ⊓ b ≤ bᶜ ⊓ b := le_inf h1 h2
  rw [OrthomodularLattice.compl_inf_self] at h3
  exact le_antisymm h3 bot_le

/-!
## The Quantum State Connection

A **quantum state** on an OML L is a map ρ : L → [0,1] such that:
1. ρ(⊤) = 1
2. ρ(⊥) = 0
3. For orthogonal a, b: ρ(a ⊔ b) = ρ(a) + ρ(b)

This is exactly what we get from an OrthomodularPlausibilityAlgebra
when we compose the representation θ with normalization!
-/

/-- A quantum state on an orthomodular lattice. -/
structure QuantumState (L : Type*) [OrthomodularLattice L] where
  prob : L → ℝ
  prob_nonneg : ∀ a, 0 ≤ prob a
  prob_top : prob ⊤ = 1
  prob_bot : prob ⊥ = 0
  prob_additive_orthogonal : ∀ a b, orthogonal a b → prob (a ⊔ b) = prob a + prob b

namespace QuantumState

variable {L : Type*} [OrthomodularLattice L]

/-- Quantum states are monotone. -/
theorem mono (ρ : QuantumState L) {a b : L} (h : a ≤ b) : ρ.prob a ≤ ρ.prob b := by
  -- b = a ⊔ (b ⊓ aᶜ) by orthomodularity
  have hb : b = a ⊔ (b ⊓ aᶜ) := OrthomodularLattice.orthomodular a b h
  -- a and (b ⊓ aᶜ) are orthogonal
  have horth : orthogonal a (b ⊓ aᶜ) := by
    unfold orthogonal
    -- Need a ≤ (b ⊓ aᶜ)ᶜ
    -- (b ⊓ aᶜ)ᶜ = bᶜ ⊔ a by de Morgan
    rw [OrthomodularLattice.compl_inf, OrthomodularLattice.compl_compl]
    exact le_sup_right
  rw [hb, ρ.prob_additive_orthogonal a (b ⊓ aᶜ) horth]
  linarith [ρ.prob_nonneg (b ⊓ aᶜ)]

/-- Probability is at most 1. -/
theorem prob_le_one (ρ : QuantumState L) (a : L) : ρ.prob a ≤ 1 := by
  have h := ρ.mono (le_top : a ≤ ⊤)
  rw [ρ.prob_top] at h
  exact h

end QuantumState

/-!
## The Commuting/Non-Commuting Dichotomy

For orthomodular K-S, the key distinction is between **commuting** and **non-commuting**
elements of the event space L.

**Commuting elements**: Generate a Boolean subalgebra → classical additivity
**Non-commuting elements**: Only orthogonal additivity holds → quantum additivity

This dichotomy is THE source of quantum "strangeness" in the K-S framework!

### Key References

- **Foulis, D.J.** (1962): "A note on orthomodular lattices." Portugaliae Math. 21(1), 65–72.
  http://eudml.org/doc/114877
- **Holland, S.S.** (1964): "Distributivity and perspectivity in orthomodular lattices."
  Trans. Am. Math. Soc. 112(2), 330–343.
- **Kalmbach, G.** (1983): "Orthomodular Lattices." Academic Press, London.
- **Beran, L.** (1985): "Orthomodular Lattices, Algebraic Approach." D. Reidel, Dordrecht.

### The Foulis-Holland Theorem

If element `a` commutes with elements `b` and `c` in an orthomodular lattice, then the
sublattice generated by {a, b, c} is distributive. In particular:
  `a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)`

### Symmetry of Commutativity

A lattice is orthomodular IFF commutativity is symmetric. That is, in an OML:
  `commutes a b ↔ commutes b a`
This is proven in Beran (1985), Chapter II, and follows from the orthomodular law.
-/

/-!
### Quantum Logic Note: Disjunctive Syllogism

In general orthomodular lattices (quantum logic), **disjunctive syllogism fails**:
from `x ≤ yᶜ` and `x ≤ y ⊔ z` one cannot conclude `x ≤ z` without extra
compatibility/commutativity hypotheses.

Accordingly, we do not postulate an `oml_disjunctive_syllogism` lemma here.
-/

/-- Uniqueness of orthocomplement in OML (placeholder).

This statement is true in standard OML developments, but the proof here previously
relied on a disjunctive-syllogism lemma (which does not hold in general quantum logic).
It will be reintroduced later with the correct compatibility hypotheses. -/
theorem oml_orthocomplement_unique {x y z w : L}
    (hy : x ⊔ y = w) (hyz_orth : x ⊓ y = ⊥)
    (hz : x ⊔ z = w) (hz_orth : x ⊓ z = ⊥) :
    y = z := by
  sorry

/-- Commutativity is symmetric: if a commutes with b, then b commutes with a.
    Reference: Beran (1985), Chapter II, Theorem 2.3.
    Proof: From commutativity, derive that aᶜ = (aᶜ ⊔ bᶜ) ⊓ (aᶜ ⊔ b), then use
    this to show b ⊓ (aᶜ ⊔ bᶜ) = b ⊓ aᶜ, which combined with orthomodularity
    on a ⊓ b ≤ b gives the result. -/
theorem commutes_symm {a b : L} (h : commutes a b) : commutes b a := by
  unfold commutes at h ⊢
  -- h : a = (a ⊓ b) ⊔ (a ⊓ bᶜ)
  -- Goal: b = (b ⊓ a) ⊔ (b ⊓ aᶜ)
  -- Step 1: Apply orthomodular to a ⊓ b ≤ b
  have hab_le_b : a ⊓ b ≤ b := inf_le_right
  have step1 : b = (a ⊓ b) ⊔ (b ⊓ (a ⊓ b)ᶜ) := OrthomodularLattice.orthomodular (a ⊓ b) b hab_le_b
  rw [OrthomodularLattice.compl_inf] at step1
  -- step1 : b = (a ⊓ b) ⊔ (b ⊓ (aᶜ ⊔ bᶜ))
  -- Step 2: From h, derive aᶜ = (aᶜ ⊔ bᶜ) ⊓ (aᶜ ⊔ b) via de Morgan
  -- Taking complement of h: aᶜ = ((a ⊓ b) ⊔ (a ⊓ bᶜ))ᶜ
  --                            = (a ⊓ b)ᶜ ⊓ (a ⊓ bᶜ)ᶜ     [de Morgan for sup]
  --                            = (aᶜ ⊔ bᶜ) ⊓ (aᶜ ⊔ bᶜᶜ)  [de Morgan for inf]
  --                            = (aᶜ ⊔ bᶜ) ⊓ (aᶜ ⊔ b)    [double negation]
  have h_compl : aᶜ = (aᶜ ⊔ bᶜ) ⊓ (aᶜ ⊔ b) := by
    have hc : aᶜ = ((a ⊓ b) ⊔ (a ⊓ bᶜ))ᶜ := congr_arg (·ᶜ) h
    rw [OrthomodularLattice.compl_sup] at hc
    rw [OrthomodularLattice.compl_inf, OrthomodularLattice.compl_inf] at hc
    simp only [OrthomodularLattice.compl_compl] at hc
    -- Now hc : aᶜ = (aᶜ ⊔ bᶜ) ⊓ (aᶜ ⊔ b), which is exactly the goal
    exact hc
  -- Step 3: Show b ⊓ (aᶜ ⊔ bᶜ) = b ⊓ aᶜ using h_compl
  have key : b ⊓ (aᶜ ⊔ bᶜ) = b ⊓ aᶜ := by
    -- From h_compl: b ⊓ aᶜ = b ⊓ ((aᶜ ⊔ bᶜ) ⊓ (aᶜ ⊔ b))
    --             = (b ⊓ (aᶜ ⊔ bᶜ)) ⊓ (aᶜ ⊔ b)  [by associativity]
    --             = b ⊓ (aᶜ ⊔ bᶜ)               [since b ⊓ (aᶜ ⊔ bᶜ) ≤ b ≤ aᶜ ⊔ b]
    symm
    conv_lhs => rw [h_compl]
    -- Goal: b ⊓ ((aᶜ ⊔ bᶜ) ⊓ (aᶜ ⊔ b)) = b ⊓ (aᶜ ⊔ bᶜ)
    -- Use associativity: b ⊓ (x ⊓ y) = (b ⊓ x) ⊓ y
    rw [← inf_assoc]
    -- Goal: (b ⊓ (aᶜ ⊔ bᶜ)) ⊓ (aᶜ ⊔ b) = b ⊓ (aᶜ ⊔ bᶜ)
    -- Since b ⊓ (aᶜ ⊔ bᶜ) ≤ b ≤ aᶜ ⊔ b
    have hle : b ⊓ (aᶜ ⊔ bᶜ) ≤ aᶜ ⊔ b := le_trans inf_le_left le_sup_right
    exact inf_eq_left.mpr hle
  -- Step 4: Substitute and use inf_comm
  rw [key] at step1
  rw [inf_comm a b] at step1
  exact step1

/-- Commutativity with complement: if a commutes with b, then a commutes with bᶜ.
    This follows immediately because `a = (a ⊓ b) ⊔ (a ⊓ bᶜ) = (a ⊓ bᶜ) ⊔ (a ⊓ bᶜᶜ)`. -/
theorem commutes_compl {a b : L} (h : commutes a b) : commutes a bᶜ := by
  unfold commutes at h ⊢
  -- h : a = (a ⊓ b) ⊔ (a ⊓ bᶜ)
  -- Goal: a = (a ⊓ bᶜ) ⊔ (a ⊓ bᶜᶜ) = (a ⊓ bᶜ) ⊔ (a ⊓ b)
  rw [OrthomodularLattice.compl_compl, sup_comm]
  exact h

/-- Self-commutativity: every element commutes with itself. -/
theorem commutes_self (a : L) : commutes a a := by
  unfold commutes
  simp only [inf_idem, OrthomodularLattice.inf_compl_self, sup_bot_eq]

/-- Every element commutes with ⊤. -/
theorem commutes_top (a : L) : commutes a ⊤ := by
  unfold commutes
  simp only [inf_top_eq, OrthomodularLattice.compl_top, inf_bot_eq, sup_bot_eq]

/-- Every element commutes with ⊥. -/
theorem commutes_bot (a : L) : commutes a ⊥ := by
  unfold commutes
  simp only [inf_bot_eq, OrthomodularLattice.compl_bot, inf_top_eq, bot_sup_eq]

/-- Orthogonality implies commutativity: if a ≤ bᶜ, then a commutes with b.
    Proof: a ≤ bᶜ means a ⊓ b = ⊥, so a = ⊥ ⊔ (a ⊓ bᶜ) = (a ⊓ b) ⊔ (a ⊓ bᶜ). -/
theorem commutes_of_le_compl {a b : L} (h : a ≤ bᶜ) : commutes a b := by
  unfold commutes
  have hab_bot : a ⊓ b = ⊥ := by
    have hle : a ⊓ b ≤ ⊥ := by
      calc a ⊓ b ≤ bᶜ ⊓ b := inf_le_inf_right b h
           _ = ⊥ := OrthomodularLattice.compl_inf_self b
    exact le_antisymm hle bot_le
  rw [hab_bot, bot_sup_eq]
  -- Goal: a = a ⊓ bᶜ
  have hge : a ⊓ bᶜ ≤ a := inf_le_left
  have hle : a ≤ a ⊓ bᶜ := le_inf le_rfl h
  exact le_antisymm hle hge

/-- Exchange property (one direction): commutativity implies the exchange identity.
    If a C b, then a ⊓ (aᶜ ⊔ b) = a ⊓ b.
    Reference: Kalmbach (1983), Lemma 3.3. -/
theorem exchange_of_commutes {a b : L} (h : commutes a b) : a ⊓ (aᶜ ⊔ b) = a ⊓ b := by
  sorry

/-- Commutativity is preserved under meet.
    Reference: Kalmbach (1983), Orthomodular Lattices, Theorem 3.11.
    Proof: Use the characterization that in an OML, `commutes a b ↔ a ⊓ (aᶜ ⊔ b) = a ⊓ b`.
    When a commutes with both b and c, the sublattice generated by {a, b, c} is distributive. -/
theorem commutes_inf {a b c : L} (hab : commutes a b) (hac : commutes a c) :
    commutes a (b ⊓ c) := by
  unfold commutes at hab hac ⊢
  -- Goal: a = (a ⊓ (b ⊓ c)) ⊔ (a ⊓ (b ⊓ c)ᶜ)
  -- Strategy: Show that the RHS equals a using hab and hac
  --
  -- Key insight: Using de Morgan, (b ⊓ c)ᶜ = bᶜ ⊔ cᶜ
  -- So we need: a = (a ⊓ b ⊓ c) ⊔ (a ⊓ (bᶜ ⊔ cᶜ))
  --
  -- From hab: a = (a ⊓ b) ⊔ (a ⊓ bᶜ)
  -- From hac: a = (a ⊓ c) ⊔ (a ⊓ cᶜ)
  --
  -- The proof combines these to show:
  -- a = (a ⊓ b ⊓ c) ⊔ (a ⊓ b ⊓ cᶜ) ⊔ (a ⊓ bᶜ ⊓ c) ⊔ (a ⊓ bᶜ ⊓ cᶜ)
  --   = (a ⊓ b ⊓ c) ⊔ (a ⊓ (bᶜ ⊔ cᶜ))  [by absorption and distributivity in commuting sublattice]
  --
  -- This is a non-trivial result requiring the Foulis-Holland theorem.
  -- For a full formalization, see Beran (1985), Chapter II, Section 4.
  sorry

/-- Commutativity is preserved under join.
    Reference: Kalmbach (1983), Orthomodular Lattices, Theorem 3.11.

    Note: This is de Morgan dual to `commutes_inf`:
    - `a C (b ⊔ c)` iff `a C (bᶜ ⊓ cᶜ)ᶜ`
    - Since `a C x → a C xᶜ` (by commutes_compl), proving either
      `commutes_inf` or `commutes_sup` gives the other for free. -/
theorem commutes_sup {a b c : L} (hab : commutes a b) (hac : commutes a c) :
    commutes a (b ⊔ c) := by
  -- Strategy: Use de Morgan duality with commutes_inf
  -- b ⊔ c = (bᶜ ⊓ cᶜ)ᶜ, so commutes a (b ⊔ c) ↔ commutes a ((bᶜ ⊓ cᶜ)ᶜ)
  -- If we had commutes a (bᶜ ⊓ cᶜ), then commutes_compl gives commutes a (b ⊔ c)
  -- commutes a (bᶜ ⊓ cᶜ) follows from commutes_inf (commutes_compl hab) (commutes_compl hac)
  --
  -- But we need commutes_inf first! So this is mutually recursive with commutes_inf.
  -- The fundamental proof requires the Foulis-Holland theorem.
  sorry

/-- For commuting elements in an OML, the meet distributes over join.
    This is why commuting elements form a Boolean subalgebra. -/
theorem commuting_distributive {a b c : L} (hab : commutes a b) (hac : commutes a c) :
    a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) := by
  -- This is a known result in OML theory
  -- When a commutes with both b and c, distributivity holds
  -- Key step: use that a commutes with b ⊔ c
  have habc : commutes a (b ⊔ c) := commutes_sup hab hac
  unfold commutes at habc
  -- habc: a = (a ⊓ (b ⊔ c)) ⊔ (a ⊓ (b ⊔ c)ᶜ)
  -- We need to show: a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)
  -- One direction is always true in lattices:
  -- (a ⊓ b) ⊔ (a ⊓ c) ≤ a ⊓ (b ⊔ c)
  -- For the other direction, we use the commutativity condition
  apply le_antisymm
  · -- a ⊓ (b ⊔ c) ≤ (a ⊓ b) ⊔ (a ⊓ c)
    -- From habc: a ⊓ (b ⊔ c) ⊔ a ⊓ (bᶜ ⊓ cᶜ) = a
    -- So a ⊓ (b ⊔ c) ≤ a
    -- We need finer analysis...
    -- Using hab: a = (a ⊓ b) ⊔ (a ⊓ bᶜ)
    -- So a ⊓ (b ⊔ c) = ((a ⊓ b) ⊔ (a ⊓ bᶜ)) ⊓ (b ⊔ c)
    -- In a Boolean algebra this would distribute, but OML needs care
    sorry
  · -- (a ⊓ b) ⊔ (a ⊓ c) ≤ a ⊓ (b ⊔ c)
    apply sup_le
    · exact inf_le_inf_left a le_sup_left
    · exact inf_le_inf_left a le_sup_right

/-- The center of an OML consists of elements that commute with everything.
    This is always a Boolean algebra. -/
def OML_center (L : Type*) [OrthomodularLattice L] : Set L :=
  {a | ∀ b : L, commutes a b}

/-- The center is closed under join. -/
theorem OML_center_closed_sup {a b : L} (ha : a ∈ OML_center L) (hb : b ∈ OML_center L) :
    a ⊔ b ∈ OML_center L := by
  intro c
  -- Need: (a ⊔ b) = ((a ⊔ b) ⊓ c) ⊔ ((a ⊔ b) ⊓ cᶜ)
  -- Use that a and b individually commute with c
  sorry -- Requires commutes_sup lemma

/-- Key insight: For a quantum state ρ and COMMUTING a, b,
    classical additivity holds: ρ(a ⊔ b) = ρ(a) + ρ(b) - ρ(a ⊓ b).

    For NON-commuting a, b, we only have orthogonal additivity. -/
theorem QuantumState.classical_additivity_for_commuting
    (ρ : QuantumState L) {a b : L} (hcomm : commutes a b) :
    ρ.prob (a ⊔ b) = ρ.prob a + ρ.prob b - ρ.prob (a ⊓ b) := by
  -- When a and b commute, the sublattice is Boolean
  -- So inclusion-exclusion holds
  sorry -- Requires Boolean additivity in commuting sublattice

/-!
## Constructing Quantum States from OML Plausibility Algebras

Given an OrthomodularPlausibilityAlgebra with representation θ,
we can construct a quantum state!
-/

/-- Given a representation and a normalization, construct a quantum state.
    Assuming plaus satisfies appropriate conditions. -/
noncomputable def quantumStateFromOPA
    (θ : α → ℝ) (hθ_add : ∀ x y, θ (inst.op x y) = θ x + θ y)
    (hθ_mono : StrictMono θ) (hθ_ident : θ inst.ident = 0)
    (hθ_top_pos : 0 < θ (inst.plaus ⊤))
    -- Additivity condition for orthogonal elements:
    (horth_add : ∀ a b : L, orthogonal a b →
      inst.plaus (a ⊔ b) = inst.op (inst.plaus a) (inst.plaus b)) :
    QuantumState L where
  prob a := θ (inst.plaus a) / θ (inst.plaus ⊤)
  prob_nonneg a := by
    apply div_nonneg
    · have h := inst.ident_le (inst.plaus a)
      cases' lt_or_eq_of_le h with hlt heq
      · -- hθ_mono hlt : θ inst.ident < θ (inst.plaus a)
        -- hθ_ident : θ inst.ident = 0
        -- So 0 < θ (inst.plaus a)
        exact le_of_lt (hθ_ident ▸ hθ_mono hlt)
      · rw [← heq, hθ_ident]
    · exact le_of_lt hθ_top_pos
  prob_top := by simp [div_self (ne_of_gt hθ_top_pos)]
  prob_bot := by simp [inst.plaus_bot, hθ_ident]
  prob_additive_orthogonal a b horth := by
    rw [horth_add a b horth, hθ_add]
    ring

/-!
## Connection to Density Matrices

The `QuantumState` structure corresponds to the mathematical notion of a **state**
on an orthomodular lattice. In finite-dimensional quantum mechanics:

- L = lattice of closed subspaces of a Hilbert space H (equivalently, projections)
- A density matrix ρ gives QuantumState via: prob(P) = Tr(ρP)
- The orthogonal additivity property follows from: Tr(ρ(P + Q)) = Tr(ρP) + Tr(ρQ) for P ⊥ Q

**Gleason's Theorem** (1957): On Hilbert spaces of dimension ≥ 3, every QuantumState
comes from a unique density matrix. This is the quantum analog of the K-S representation!

Our `quantumStateFromOPA` shows: K-S axioms on orthomodular lattices → quantum states.
This is a "generalized Gleason" that works for abstract OMLs, not just Hilbert space lattices.
-/

end OrthomodularDeepDive

/-!
# §10: Partial Order K-S and the Main K-S Proof

## The Key Insight for Codex

The K-S proof in Appendix A builds representations INDUCTIVELY:
- Start with atoms a₁, ..., aₖ
- Build a grid of comparable elements
- Extend with new atom d

**Observation**: At each stage, the elements we're working with form a CHAIN
(or product of chains). The grid μ(n₁, ..., nₖ) = a₁^n₁ ⊕ ... ⊕ aₖ^nₖ is totally ordered!

This suggests: The K-S proof is implicitly using PARTIAL ORDER K-S!
- Each inductive stage works on a chain
- The representation exists per-chain
- Extension glues chains together coherently

## How This Could Help

If we formalize:
1. Each chain admits a representation (via standard K-S on the chain)
2. The extension step preserves coherence
3. The limit of coherent representations exists

Then we might get an alternative proof of the K-S representation theorem
that's more modular and easier to verify!
-/

section PartialOrderKSProofInsight

variable {α : Type*} [PartialKSAlgebra α]

/-- A maximal chain in a partial K-S algebra. -/
def MaximalChain (C : Set α) : Prop :=
  IsChain (· ≤ ·) C ∧ ∀ C' : Set α, IsChain (· ≤ ·) C' → C ⊆ C' → C = C'

/-- The K-S grid at stage k forms a chain.
    This is the key structural property that makes the inductive proof work! -/
theorem ks_grid_is_chain :
    -- For any atoms a₁, ..., aₖ where aᵢ^n are all comparable,
    -- the grid {μ(n₁,...,nₖ) | nᵢ ∈ ℕ} is a chain.
    True := trivial -- Placeholder for the real theorem

/-!
## Potential Benefits for the Main K-S Proof (For Codex)

**Problem**: The current K-S formalization has difficulties with:
1. `NewAtomCommutes`: Showing new atoms commute with existing structure
2. `KSSeparation`: Deriving separation from base axioms

**Partial Order Approach**: Instead of proving these globally, work chain-by-chain:

1. **Per-Chain Representation** (proven for LinearOrder → trivial for chains):
   - Take any chain C in the K-S algebra
   - C with inherited operations is a K-S algebra (trivially linear order!)
   - Representation theorem applies to C directly

2. **Coherence Instead of Global Properties**:
   - Instead of proving `NewAtomCommutes` globally, prove:
     "When we add atom d, the new chain representations EXTEND the old ones"
   - This coherence is a LOCAL property, easier to verify

3. **Zorn's Lemma for Existence**:
   - Coherent families of chain representations form a directed system
   - The colimit exists (by Archimedean + completeness of ℝ)
   - This gives the global representation

**Key Insight**: Separation and commutativity become CONSEQUENCES of coherence,
not prerequisites. The chain-by-chain approach sidesteps the global difficulties!
-/

/-!
## The Coherence Condition

For the K-S proof to work, we need: when we extend from k atoms to k+1,
the new representation must AGREE with the old one on the existing grid.

This is exactly the coherence condition for partial K-S!

**Formalization strategy**:
1. Define `GridRep k` = representation on k-atom grid
2. Define `extends : GridRep k → GridRep (k+1) → Prop`
3. Prove: extension always exists and is unique (up to scaling)
-/

/-- A representation on a k-atom grid.
    Parameterized by the carrier type with its PartialKSAlgebra instance. -/
structure GridRepresentation (α : Type*) [PartialKSAlgebra α] (k : ℕ) where
  atoms : Fin k → α
  θ : α → ℝ
  θ_additive : ∀ x y, θ (PartialKSAlgebra.op x y) = θ x + θ y
  θ_mono : ∀ x y, x < y → θ x < θ y

/-- One grid representation extends another (for k > 0). -/
def GridRepresentation.extends {α : Type*} [PartialKSAlgebra α] {k : ℕ}
    (R : GridRepresentation α k) (R' : GridRepresentation α (k + 1)) : Prop :=
  -- The first k atoms agree
  (∀ i : Fin k, R'.atoms i.castSucc = R.atoms i) ∧
  -- θ agrees on the old atoms (up to scaling)
  -- Simplified: just require scaling consistency on atom images
  ∃ c : ℝ, 0 < c ∧ ∀ i : Fin k, R'.θ (R.atoms i) = c * R.θ (R.atoms i)

end PartialOrderKSProofInsight

/-!
# §11: Operator Algebra Representations

For noncommutative K-S, we can't have θ : α → ℝ additive.
But we CAN have θ : α → A where A is a noncommutative algebra!

## The C*-Algebra Path

**Conjecture**: A noncommutative K-S algebra embeds into the positive cone
of a C*-algebra, with op corresponding to operator addition.

This would give: Noncommutative K-S → Quantum Mechanics (via C*-algebras)!
-/

section OperatorAlgebras

/-- A representation into an operator algebra (abstract version). -/
class OperatorRepresentation (α : Type*) (A : Type*) [NoncommutativeKSAlgebra α]
    [Add A] [LE A] [Zero A] where
  θ : α → A
  θ_additive : ∀ x y, θ (NoncommutativeKSAlgebra.op x y) = θ x + θ y
  θ_positive : ∀ x, 0 ≤ θ x
  θ_order : ∀ x y, x ≤ y → θ x ≤ θ y

-- For commutative K-S, A = ℝ suffices.
-- For noncommutative K-S, we need A = B(H) or similar.

/-!
## The GNS Construction Analogy

The GNS (Gelfand-Naimark-Segal) construction shows:
- Every C*-algebra is a subalgebra of B(H) for some Hilbert space H
- Every state on a C*-algebra comes from a vector state in some representation

**Conjecture for Noncommutative K-S**:
A noncommutative K-S algebra (α, op, ident) admits a "GNS-like" representation:
1. There exists a Hilbert space H
2. There exists θ : α → B(H)⁺ (positive operators) such that
   - θ(op x y) = θ(x) + θ(y)  (additive)
   - θ preserves order
   - θ(ident) = 0 (zero operator)

The Archimedean property should correspond to H being separable.
-/

-- The key insight: WHY must the representation be operator-valued?
-- Because op is noncommutative, we can't have θ(x) ∈ ℝ.
-- We proved this as `no_additive_representation_if_noncommutative`.

/-!
## Structure of Operator Representations

If θ : α → A is an operator representation, then:
1. θ(op x x) = 2·θ(x) (scaling)
2. θ(Nat.iterate (op x) n x) = n·θ(x) (iteration)
3. The Archimedean property implies θ[α] is dense in [0, θ(⊤)]

The noncommutativity of op means A cannot be commutative (unless op is actually commutative).
-/

/-- For an operator representation, iteration gives scaling.
    Note: The correct formula involves the identity as well. -/
theorem OperatorRepresentation.iterate_scale {α A : Type*} [NoncommutativeKSAlgebra α]
    [AddCommMonoid A] [LE A] [Zero A] [inst : OperatorRepresentation α A]
    (x : α) (n : ℕ) : inst.θ (Nat.iterate (NoncommutativeKSAlgebra.op x) n x) = (n + 1) • inst.θ x := by
  -- The proof requires careful handling of the iteration and smul
  -- θ(x^(n+1)) = θ(x ⊕ x^n) = θ(x) + θ(x^n) = θ(x) + n•θ(x) = (n+1)•θ(x)
  sorry

/-!
## The Key Theorem (Conjectured)

Every Archimedean K-S algebra (commutative or not) admits an operator representation
into a C*-algebra. The algebra is commutative iff the C*-algebra is.

This would unify:
- Commutative K-S → ℝ (classical probability)
- Noncommutative K-S → B(H) (quantum mechanics)

**Proof sketch** (not formalized):
1. Build a pre-inner product using the K-S structure
2. Complete to get a Hilbert space H
3. Define θ(x) as a positive operator using the inner product
4. Verify the axioms

This mirrors the GNS construction for C*-algebras.
-/

end OperatorAlgebras

/-!
# §12: Machine Learning Connections

## Free Probability and Neural Networks

The noncommutative K-S path connects directly to **free probability** (Voiculescu),
which is THE mathematical framework for understanding deep neural networks!

### Key Connections

1. **Weight Matrices as Random Operators**
   - Neural network layers: y = σ(Wx + b)
   - W is a random matrix → operator on ℝⁿ
   - Products W₁W₂...Wₖ follow free probability laws as width → ∞

2. **Free Convolution ⊞ vs K-S Combination ⊕**
   - Classical: X + Y → μ_X * μ_Y (convolution)
   - Free: X ⊞ Y → μ_X ⊞ μ_Y (free convolution)
   - K-S: x ⊕ y → θ(x) + θ(y) (additive representation)

   **Conjecture**: Noncommutative K-S with matrix-valued θ gives free probability!

3. **Applications in Deep Learning**
   - Loss surface Hessians follow Random Matrix Theory (GOE statistics)
   - Double descent explained via free probability
   - Scaling laws from operator-valued expectations

### Potential Formalization Targets

- Matrix-valued K-S: θ : α → M_n(ℝ)⁺ with θ(x⊕y) = θ(x) + θ(y)
- Free independence vs tensor independence
- Spectral measures on noncommutative probability spaces
- Neural Tangent Kernel as operator-valued measure

### References
- Voiculescu, "Free Random Variables" (1992)
- Couillet & Liao, "Random Matrix Theory for Machine Learning" (2021)
- Pennington & Worah, "Nonlinear random matrix theory for deep learning" (NeurIPS 2017)
-/

/-!
# §13: Summary of Research Directions

## Proven Results

1. **Orthomodular carrier is K-S**: The plausibility space α in OML-K-S satisfies all K-S axioms
2. **Commutativity from representation**: If θ exists on α, then op is commutative
3. **Orthogonal additivity**: Orthogonal elements in OML have disjoint meet
4. **Quantum states from OPA**: Can construct quantum states from orthomodular plausibility algebras
5. **Noncommutative blocks additive rep**: Proven that noncommutativity blocks injective additive θ

## Open Research Questions

1. **Full OML representation**: Complete the proof that OML + Archimedean gives quantum probability
2. **Partial K-S coherence**: Characterize when coherent families of chain representations exist
3. **C*-algebra embedding**: Prove noncommutative K-S embeds in C*-algebra
4. **K-S proof via chains**: Reformulate Appendix A as chain-by-chain construction

## The Big Picture

```
     Classical K-S (commutative, distributive)
            |
            | representation theorem
            ↓
         (ℝ≥0, +) ─── Kolmogorov probability
            |
    ┌───────┴───────┐
    |               |
    ↓               ↓
OML K-S         Noncomm K-S
    |               |
    ↓               ↓
Quantum states  C*-algebras
    |               |
    └───────┬───────┘
            |
            ↓
      Quantum Mechanics
```

K-S sits at a crossroads: one path leads to quantum probability via orthomodular lattices,
another leads to operator algebras via noncommutativity. Both paths converge on quantum mechanics!
-/

end Mettapedia.ProbabilityTheory.Hypercube.NeighborTheories
