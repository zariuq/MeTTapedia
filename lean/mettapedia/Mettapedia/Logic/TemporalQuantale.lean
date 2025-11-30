
/-!
# Temporal Quantales

This file formalizes the algebraic structure underlying Temporal Probabilistic Logic Networks,
lifting the boolean skeleton in `PLNTemporal.lean` to a quantale-valued setting.

## Mathematical Foundation

A **Temporal Quantale** is a commutative quantale Q equipped with a group action φ : T → (Q → Q)
such that each φ_t is a **quantale automorphism** (invertible, preserves *, ⊤, ⊥, ⊔, ≤).

**Key Insight**: Since T is an additive group, φ_t has an inverse φ_{-t}, making it an
automorphism. Automorphisms preserve residuation (implication), which guarantees:
- Temporal transitivity: (a ⇨ φ_{t₁} b) * φ_{t₁}(b ⇨ φ_{t₂} c) ≤ (a ⇨ φ_{t₁+t₂} c)
- This is proven WITHOUT additional axioms!

## Connection to PLN

In PLN, the quantale Q represents "evidence values" or "truth values":
- Elements of Q are <s, c> pairs (strength, confidence)
- Product (*) represents conjunction under independence
- Residuation (⇨) represents implication strength
- Time shift (φ_t) is typically the identity on values (concepts are stable,
  predictions carry uncertainty in the implication, not in the shift)

## References

[1] Geisweiller, N., Yusuf, H. (2023). "Probabilistic Logic Networks for Temporal
    and Procedural Reasoning". Lecture Notes in Computer Science, vol 13869.
[2] Goertzel, B. "Weakness and Its Quantale: Plausibility Theory from First Principles"
[3] Rosenthal, K. "Quantales and their Applications"
-/

open Mettapedia.Algebra.QuantaleWeakness

universe u v

variable {Q : Type u} {T : Type v}

/-! ## The Temporal Quantale Class

A temporal quantale extends a commutative quantale with a time-indexed family of automorphisms.
The key property is that shift forms a **group action** by **automorphisms**.
-/

/--
A temporal quantale is a commutative quantale Q with a time group T and a shift operation
that acts as a group homomorphism T → Aut(Q).

**Axioms**:
1. Group action: shift 0 = id, shift (t + t') = shift t ∘ shift t'
2. Quantale homomorphism: shift t preserves *, ⊥, ⊤, and ⊔
3. (Automatic) Since T is a group, shift t is invertible (shift (-t)), hence an automorphism
-/
class TemporalQuantale (Q : Type u) (T : Type v)
    [CommSemigroup Q] [CompleteLattice Q] [IsCommQuantale Q] [AddCommGroup T] where
  /-- Time shift operator -/
  shift : T → Q → Q

  /-- Group action: identity -/
  shift_zero : ∀ a, shift 0 a = a

  /-- Group action: composition -/
  shift_add : ∀ t t' a, shift (t + t') a = shift t (shift t' a)

  /-- Quantale homomorphism: preserves product (conjunction) -/
  shift_mul : ∀ t a b, shift t (a * b) = shift t a * shift t b

  /-- Lattice homomorphism: preserves suprema (critical for quantale structure!) -/
  shift_sSup : ∀ t (S : Set Q), shift t (sSup S) = ⨆ s ∈ S, shift t s

  /-- Lattice homomorphism: preserves bottom -/
  shift_bot : ∀ t, shift t ⊥ = ⊥

  /-- Lattice homomorphism: preserves top -/
  shift_top : ∀ t, shift t ⊤ = ⊤

namespace TemporalQuantale

variable [CommSemigroup Q] [CompleteLattice Q] [IsCommQuantale Q] [AddCommGroup T]
variable [TemporalQuantale Q T]

/-! ## Basic Properties of Shift

These follow directly from the axioms.
-/

/-- Shift preserves binary suprema -/
theorem shift_sup (t : T) (a b : Q) : shift t (a ⊔ b) = shift t a ⊔ shift t b := by
  have h1 : a ⊔ b = sSup {a, b} := sSup_pair.symm
  rw [h1, shift_sSup]
  -- Goal: ⨆ s ∈ {a, b}, shift t s = shift t a ⊔ shift t b
  apply le_antisymm
  · apply iSup_le
    intro s
    apply iSup_le
    intro hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  · apply sup_le
    · apply le_iSup_of_le a
      apply le_iSup_of_le (Set.mem_insert a {b})
      exact le_refl _
    · apply le_iSup_of_le b
      apply le_iSup_of_le (Set.mem_insert_of_mem a (Set.mem_singleton b))
      exact le_refl _

/-- Shift is monotone (follows from sSup preservation) -/
theorem shift_mono (t : T) : Monotone (shift (Q := Q) t) := by
  intro a b hab
  -- a ≤ b ↔ a ⊔ b = b
  rw [← sup_eq_right]
  rw [← shift_sup, sup_eq_right.mpr hab]

/-- Shift by negative time is the inverse -/
theorem shift_neg (t : T) (a : Q) : shift (-t) (shift t a) = a := by
  rw [← shift_add, neg_add_cancel, shift_zero]

/-- Shift by negative time is the inverse (other direction) -/
theorem shift_neg' (t : T) (a : Q) : shift t (shift (-t) a) = a := by
  rw [← shift_add, add_neg_cancel, shift_zero]

/-- Shift is injective -/
theorem shift_injective (t : T) : Function.Injective (shift (Q := Q) t) := by
  intro a b h
  have := congrArg (shift (-t)) h
  simp only [shift_neg] at this
  exact this

/-- Shift is surjective -/
theorem shift_surjective (t : T) : Function.Surjective (shift (Q := Q) t) := by
  intro b
  exact ⟨shift (-t) b, shift_neg' t b⟩

/-- Shift is bijective -/
theorem shift_bijective (t : T) : Function.Bijective (shift (Q := Q) t) :=
  ⟨shift_injective t, shift_surjective t⟩

/-! ## Derived Temporal Operators

These match the definitions in PLNTemporal.lean but operate on quantale values.
-/

/-- Lag: bring past to present (shift by -t) -/
def lag (a : Q) (t : T) : Q := shift (-t) a

/-- Lead: bring future to present (shift by t) -/
def lead (a : Q) (t : T) : Q := shift t a

/-- Sequential AND: a now AND b at time t -/
def seqAnd (a b : Q) (t : T) : Q := a * shift t b

/-- Sequential OR: a now OR b at time t (using lattice join) -/
def seqOr (a b : Q) (t : T) : Q := a ⊔ shift t b

/-- Predictive Implication: "if a now, then b at time t"
Uses left residuation from QuantaleWeakness.lean -/
noncomputable def predImpl (a b : Q) (t : T) : Q := leftResiduate a (shift t b)

/-! ## Inverse Laws for Lag/Lead -/

theorem lag_lead_inv (a : Q) (t : T) : lag (lead a t) t = a := by
  simp [lag, lead, shift_neg]

theorem lead_lag_inv (a : Q) (t : T) : lead (lag a t) t = a := by
  simp [lag, lead, shift_neg']

/-! ## The Key Theorem: Shift Preserves Residuation

Since shift t is an automorphism (invertible quantale homomorphism),
it preserves residuation. This is the mathematical core that makes
temporal transitivity work.

**Proof Strategy**: Use the Galois connection characterization of residuation.
For any x: x ≤ φ(a ⇨ b) ⟺ x ≤ φ(a) ⇨ φ(b), where φ = shift t.
-/

/--
Shift preserves residuation: φ_t(a ⇨ b) = φ_t(a) ⇨ φ_t(b)

This follows from shift being an automorphism (bijective homomorphism).
-/
theorem shift_residuate (t : T) (a b : Q) :
    shift t (leftResiduate a b) = leftResiduate (shift t a) (shift t b) := by
  -- We prove equality by showing mutual ≤
  apply le_antisymm
  -- Direction 1: shift t (a ⇨ b) ≤ shift t a ⇨ shift t b
  · -- Use Galois connection: z ≤ (x ⇨ y) ⟺ z * x ≤ y
    rw [← residuate_galois]
    -- Need: shift t (a ⇨ b) * shift t a ≤ shift t b
    rw [← shift_mul]
    apply shift_mono
    -- Need: (a ⇨ b) * a ≤ b, which is modus ponens
    exact modusPonens_left a b
  -- Direction 2: shift t a ⇨ shift t b ≤ shift t (a ⇨ b)
  · -- Key insight: since shift t is bijective, x ≤ y ⟺ shift (-t) x ≤ shift (-t) y
    -- So we apply shift (-t) to both sides
    suffices h : shift (-t) (leftResiduate (shift t a) (shift t b)) ≤ leftResiduate a b by
      have := shift_mono t h
      simp only [shift_neg'] at this
      exact this
    -- Now prove: shift (-t) (shift t a ⇨ shift t b) ≤ a ⇨ b
    rw [← residuate_galois]
    -- Need: shift (-t) (shift t a ⇨ shift t b) * a ≤ b
    -- Use: shift (-t) (x * y) = shift (-t) x * shift (-t) y
    have key : shift (-t) (leftResiduate (shift t a) (shift t b)) * a
             = shift (-t) (leftResiduate (shift t a) (shift t b) * shift t a) := by
      rw [shift_mul, shift_neg]
    rw [key]
    -- Now: shift (-t) ((shift t a ⇨ shift t b) * shift t a) ≤ b
    -- By modus ponens: (shift t a ⇨ shift t b) * shift t a ≤ shift t b
    -- So shift (-t) of LHS ≤ shift (-t) of RHS = b
    calc shift (-t) (leftResiduate (shift t a) (shift t b) * shift t a)
        ≤ shift (-t) (shift t b) := shift_mono (-t) (modusPonens_left (shift t a) (shift t b))
      _ = b := shift_neg t b

/-! ## Temporal Transitivity

The main theorem: chaining predictive implications works correctly.

If (a ⇨ φ_{t₁} b) holds and (b ⇨ φ_{t₂} c) holds (shifted by t₁),
then (a ⇨ φ_{t₁+t₂} c) holds.

This is the quantale version of "If A implies B at time t₁, and B implies C at time t₂,
then A implies C at time t₁+t₂."
-/

/--
**Temporal Transitivity Theorem**

(a ⇨ shift t₁ b) * shift t₁ (b ⇨ shift t₂ c) ≤ (a ⇨ shift (t₁+t₂) c)

This is the core inference rule for chaining temporal implications in PLN.
-/
theorem temporal_transitivity (a b c : Q) (t₁ t₂ : T) :
    predImpl a b t₁ * shift t₁ (predImpl b c t₂) ≤ predImpl a c (t₁ + t₂) := by
  unfold predImpl
  -- Goal: (a ⇨ shift t₁ b) * shift t₁ (b ⇨ shift t₂ c) ≤ a ⇨ shift (t₁+t₂) c

  -- Step 1: Use shift_residuate to transform the middle term
  rw [shift_residuate]
  -- Now: (a ⇨ shift t₁ b) * (shift t₁ b ⇨ shift t₁ (shift t₂ c)) ≤ a ⇨ shift (t₁+t₂) c

  -- Step 2: Simplify shift t₁ (shift t₂ c) = shift (t₁+t₂) c using shift_add
  -- shift_add: shift (t + t') a = shift t (shift t' a)
  -- So (shift_add t₁ t₂ c).symm gives: shift t₁ (shift t₂ c) = shift (t₁ + t₂) c
  have h_comp : shift t₁ (shift t₂ c) = shift (t₁ + t₂) c := (shift_add t₁ t₂ c).symm
  rw [h_comp]
  -- Now: (a ⇨ shift t₁ b) * (shift t₁ b ⇨ shift (t₁+t₂) c) ≤ a ⇨ shift (t₁+t₂) c

  -- Step 3: Use Galois connection to convert goal
  rw [← residuate_galois]
  -- Goal: (a ⇨ shift t₁ b) * (shift t₁ b ⇨ shift (t₁+t₂) c) * a ≤ shift (t₁+t₂) c

  -- Step 4: Rearrange and apply modus ponens twice
  -- First, use commutativity to get (a ⇨ shift t₁ b) * a together
  have step1 : leftResiduate a (shift t₁ b) * leftResiduate (shift t₁ b) (shift (t₁ + t₂) c) * a
             = (leftResiduate a (shift t₁ b) * a) * leftResiduate (shift t₁ b) (shift (t₁ + t₂) c) := by
    rw [mul_assoc, mul_comm (leftResiduate (shift t₁ b) (shift (t₁ + t₂) c)) a, ← mul_assoc]
  rw [step1]
  -- Now: (a ⇨ shift t₁ b) * a * (shift t₁ b ⇨ shift (t₁+t₂) c) ≤ shift (t₁+t₂) c
  -- By modus ponens: (a ⇨ shift t₁ b) * a ≤ shift t₁ b
  have mp1 := modusPonens_left a (shift t₁ b)
  have step2 : (leftResiduate a (shift t₁ b) * a) * leftResiduate (shift t₁ b) (shift (t₁ + t₂) c)
             ≤ (shift t₁ b) * leftResiduate (shift t₁ b) (shift (t₁ + t₂) c) :=
    mul_le_mul_right' mp1 _
  -- By modus ponens again: (shift t₁ b ⇨ shift (t₁+t₂) c) * shift t₁ b ≤ shift (t₁+t₂) c
  have mp2 := modusPonens_left (shift t₁ b) (shift (t₁ + t₂) c)
  have step3 : (shift t₁ b) * leftResiduate (shift t₁ b) (shift (t₁ + t₂) c)
             ≤ shift (t₁ + t₂) c := by
    rw [mul_comm]
    exact mp2
  exact le_trans step2 step3

/-! ## Temporal Modus Ponens

A simpler case: if a holds and (a ⇨ shift t b) holds, then (shift t b) holds.
-/

theorem temporal_modus_ponens (a b : Q) (t : T) :
    a * predImpl a b t ≤ shift t b := by
  unfold predImpl
  rw [mul_comm]
  exact modusPonens_left a (shift t b)

/-! ## Distributivity of Shift over Temporal Operators -/

theorem shift_seqAnd (t s : T) (a b : Q) :
    shift s (seqAnd a b t) = seqAnd (shift s a) (shift s b) t := by
  simp only [seqAnd, shift_mul]
  congr 1
  -- Goal: shift s (shift t b) = shift t (shift s b)
  rw [← shift_add, ← shift_add, add_comm]

theorem shift_predImpl (t s : T) (a b : Q) :
    shift s (predImpl a b t) = predImpl (shift s a) (shift s b) t := by
  simp only [predImpl, shift_residuate]
  congr 1
  -- Goal: shift s (shift t b) = shift t (shift s b)
  rw [← shift_add, ← shift_add, add_comm]

end TemporalQuantale

/-! ## Example: The Identity Temporal Quantale

When time shifts are identity maps, we get the "static" quantale where
temporal operators reduce to their non-temporal versions.

This is the degenerate case where all times are equivalent.
-/

section IdentityExample

variable {Q : Type*} [CommSemigroup Q] [CompleteLattice Q] [IsCommQuantale Q]

/-- The trivial temporal quantale where shift is always the identity.
This represents a "timeless" logic where past, present, and future are equivalent. -/
def TemporalQuantale.identity : TemporalQuantale Q ℤ where
  shift _ a := a
  shift_zero _ := rfl
  shift_add _ _ _ := rfl
  shift_mul _ _ _ := rfl
  shift_sSup _ S := by
    -- Goal: sSup S = ⨆ s ∈ S, s
    apply le_antisymm
    · apply sSup_le
      intro a ha
      exact le_iSup₂_of_le a ha (le_refl _)
    · apply iSup_le
      intro s
      apply iSup_le
      intro hs
      exact le_sSup hs
  shift_bot _ := rfl
  shift_top _ := rfl

end IdentityExample

/-! ## Idealized Probabilistic Model (Sketch)

In PLN, truth values are <s, c> pairs where:
- s = strength (probability)
- c = confidence

**The Quantale Structure (Idealized)**:
- Product: <s₁, c₁> * <s₂, c₂> = <s₁·s₂, c₁·c₂>  (independence assumption)
- Order: <s₁, c₁> ≤ <s₂, c₂> ⟺ s₁ ≤ s₂ (strength ordering)
- Supremum: pointwise on strength
- Bottom: <0, 1> (certain falsehood)
- Top: <1, 1> (certain truth)

**The Temporal Shift**:
- shift t <s, c> = <s, c>  (identity!)

**Why identity?**
In Temporal PLN, concepts are stable. "A cat" at time t has the same truth value
as "A cat" at time t+1. The uncertainty lies in *predictions* (the implication
links), not in the concepts themselves.

This means:
- seqAnd a b t = a * b  (just conjunction, time is a label)
- predImpl a b t = a ⇨ b  (just implication, time appears in the formula)

The actual "temporal decay" happens when computing the truth value of
(PredictiveImplication T P Q), which uses different PLN formulas than
standard implication, incorporating time-based discounting.

This is why the *abstract* formalization uses identity shift: it captures
the algebraic structure correctly. The *probabilistic semantics* handles
time-dependent confidence separately in the truth value formulas.
-/

/-! ## Connection to PLNTemporal.lean

The boolean skeleton in `PLNTemporal.lean` is recovered when Q = Prop:
- shift t P = P  (propositions don't change over time)
- seqAnd P Q t = P ∧ Q  (just conjunction)
- predImpl P Q t = P → Q  (just implication)

The quantale version lifts this to graded truth values while preserving
the same algebraic laws.

## Future Work

1. **Probabilistic Instance**: Define `instance : TemporalQuantale TruthValue ℝ`
   where TruthValue is (s, c) pairs with PLN operations

2. **Confidence Decay**: Model time-dependent confidence decay in the
   truth value formulas (separate from the algebraic shift)

3. **Event Calculus**: Layer for reasoning about events, states, and actions
   built on top of temporal quantales
-/
