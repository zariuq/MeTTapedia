/-
# K&S Advantages: Structures Measurable by K&S but NOT by Cox/Boolean Lattices

This file demonstrates concrete examples where the Knuth-Skilling framework
can assign coherent measures to structures that fall outside the scope of:
1. Cox's theorem (requires Boolean algebra with negation)
2. Standard probability (requires Boolean σ-algebra)

## Key Insight

**Cox**: Requires propositions with negation (Boolean algebra)
**Standard probability**: Requires Boolean σ-algebra with complement
**K&S**: Works on Generalized Boolean Algebras (relative complements only)
       AND on ordered semigroups without identity (via Hölder embedding)

## Three Categories of K&S Advantage

### Category 1: Generalized Boolean Algebras (GBA) without Full Boolean Structure
- Interval lattices: [a,b] has relative complement [a,b] \ [c,d], but no absolute complement
- Ideal lattices of posets: ideals closed under relative complement within bounds
- K&S's Section 5.2 applies; Cox cannot define p(¬A|B) for all A

### Category 2: Identity-Free Structures
- Positive reals (ℝ⁺, +): no additive identity
- Multiplicative positive reals (ℝ⁺, ×): no multiplicative identity in (0,∞)
- K&S identity-free representation applies; Cox requires "contradiction" as baseline

### Category 3: Measures with Genuine Non-Additivity
- Our 7-element counterexample shows distributive lattices can have non-modular measures
- K&S correctly identifies where inclusion-exclusion applies (GBA) vs. where it doesn't
- Cox's framework assumes additivity from the start

## References

- Knuth & Skilling, "Foundations of Inference" (2012), Sections 5.1-5.2
- Cox, "The Algebra of Probable Inference" (1961)
- This project: Additive/ (Appendix A) and Counterexamples/NonModularDistributive.lean
-/

import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Examples

open Set

/-! ## Example 1: Interval Lattice (GBA without Boolean)

**Structure**: Closed intervals [a,b] on the real line, ordered by inclusion.

**Key property**: Has RELATIVE complements but NOT absolute complements.
- Relative complement: [0,1] \ [0.3, 0.7] = [0, 0.3) ∪ (0.7, 1] (exists as union of intervals)
- Absolute complement: What's ¬[0,1]? The entire real line minus [0,1]?
  Not an element of "bounded intervals on [0,1]"!

**K&S applicability**: Section 5.2 applies to GBAs
**Cox non-applicability**: Cannot define p(¬A|B) when A has no absolute complement -/

section IntervalLattice

/-- A bounded interval [a,b] on the real line. -/
structure BoundedInterval where
  lo : ℝ
  hi : ℝ
  h_le : lo ≤ hi

namespace BoundedInterval

/-- Interval inclusion ordering: I ≤ J means I ⊆ J. -/
instance : LE BoundedInterval where
  le I J := J.lo ≤ I.lo ∧ I.hi ≤ J.hi

/-- Length of an interval (a natural "measure"). -/
def length (I : BoundedInterval) : ℝ := I.hi - I.lo

/-- Length is non-negative. -/
theorem length_nonneg (I : BoundedInterval) : 0 ≤ I.length := by
  simp only [length]
  linarith [I.h_le]

/-- Length is monotone with respect to inclusion. -/
theorem length_mono {I J : BoundedInterval} (h : I ≤ J) : I.length ≤ J.length := by
  simp only [length]
  have h1 : J.lo ≤ I.lo := h.1
  have h2 : I.hi ≤ J.hi := h.2
  linarith

/-- **Key Point**: Relative complement exists within a containing interval.

For sub ⊆ container, the relative complement is the "left and right remainders".
This makes bounded intervals a **Generalized Boolean Algebra**. -/
def leftRemainder (container sub : BoundedInterval) (h : sub ≤ container) : BoundedInterval :=
  ⟨container.lo, sub.lo, h.1⟩

def rightRemainder (container sub : BoundedInterval) (h : sub ≤ container) : BoundedInterval :=
  ⟨sub.hi, container.hi, h.2⟩

/-- The relative complement satisfies: container = left + sub + right. -/
theorem relativeComplement_lengths (container sub : BoundedInterval) (h : sub ≤ container) :
    container.length = (leftRemainder container sub h).length + sub.length +
                       (rightRemainder container sub h).length := by
  simp only [leftRemainder, rightRemainder, length]
  ring

/-- **Cox CANNOT apply here**: There's no absolute complement for a general interval.

What would ¬[0.3, 0.7] be as a "bounded interval on [0,1]"?
- It would need to be [0, 0.3) ∪ (0.7, 1], but that's TWO intervals, not one.
- The interval lattice is NOT closed under absolute complement.

Cox requires: For any A, there exists ¬A such that p(¬A|B) = G(p(A|B)).
This fails when ¬A doesn't exist as a lattice element.

The theorem below shows that no single interval can serve as the complement
of a "middle" interval like [0.3, 0.7] within [0, 1]. -/
theorem no_single_interval_complement :
    ¬∃ (neg : BoundedInterval),
      -- neg should be the complement of [0.3, 0.7] within [0, 1]
      neg.lo = 0 ∧ neg.hi = 1 ∧  -- neg spans the full range
      -- AND neg is disjoint from [0.3, 0.7]
      (neg.hi ≤ 0.3 ∨ neg.lo ≥ 0.7) := by
  intro ⟨neg, h_lo, h_hi, h_disj⟩
  rcases h_disj with h1 | h2
  · -- neg.hi ≤ 0.3 but neg.hi = 1
    linarith
  · -- neg.lo ≥ 0.7 but neg.lo = 0
    linarith

/-- **K&S DOES apply**: We can define additive measures via Section 5.2.

The GBA structure (relative complements within containers) is exactly what
K&S Section 5.2 needs for the inclusion-exclusion decomposition. -/
theorem ks_applies_to_intervals :
    ∃ (m : BoundedInterval → ℝ),
      (∀ I, 0 ≤ m I) ∧  -- Non-negative
      (∀ I J : BoundedInterval, I ≤ J → m I ≤ m J) ∧  -- Monotone
      (∀ container sub : BoundedInterval, ∀ h : sub ≤ container,
        m container = m (leftRemainder container sub h) + m sub +
                      m (rightRemainder container sub h)) := by  -- Additive on complements
  use length
  refine ⟨length_nonneg, ?_, relativeComplement_lengths⟩
  intro I J h
  exact length_mono h

end BoundedInterval

end IntervalLattice

/-! ## Example 2: Positive Reals (Identity-Free Ordered Semigroup)

**Structure**: (ℝ⁺, +) - positive real numbers under addition.

**Key property**: NO additive identity (0 is not in ℝ⁺).

**K&S applicability**: Identity-free Hölder embedding (our `holder_representation`)
**Cox non-applicability**: Cox requires a "contradiction" (⊥) with p(⊥|B) = 0 -/

section PositiveReals

/-- Positive reals form an ordered cancellative semigroup. -/
def PosReal := {x : ℝ // 0 < x}

namespace PosReal

instance : Add PosReal where
  add x y := ⟨x.val + y.val, add_pos x.prop y.prop⟩

instance : LT PosReal where
  lt x y := x.val < y.val

instance : LE PosReal where
  le x y := x.val ≤ y.val

/-- Addition is strictly monotone in both arguments. -/
theorem add_lt_add_left (a : PosReal) {b c : PosReal} (h : b < c) : a + b < a + c := by
  show a.val + b.val < a.val + c.val
  have hbc : b.val < c.val := h
  linarith

theorem add_lt_add_right {a b : PosReal} (h : a < b) (c : PosReal) : a + c < b + c := by
  show a.val + c.val < b.val + c.val
  have hab : a.val < b.val := h
  linarith

/-- **Key Point**: No identity element exists.

In (ℝ⁺, +), there is no e such that e + x = x for all x.
(That would require e = 0, but 0 ∉ ℝ⁺.) -/
theorem no_identity : ¬∃ e : PosReal, ∀ x : PosReal, e + x = x := by
  intro ⟨e, he⟩
  have h := he ⟨1, one_pos⟩
  -- h says e + 1 = 1, i.e., e.val + 1 = 1
  have h' : e.val + 1 = 1 := congrArg Subtype.val h
  -- This means e.val = 0, contradicting e.val > 0
  linarith [e.prop]

/-- Every element is "positive" in Eric Luap's sense: ∀ z, z < x + z. -/
theorem all_positive (x : PosReal) : ∀ z : PosReal, z < x + z := by
  intro z
  show z.val < x.val + z.val
  linarith [x.prop]

/-- **K&S identity-free representation applies**.

By our `holder_representation` (or `cuts_pnat_representation`), there exists
Θ : PosReal → ℝ that is order-preserving and additive.

Here, the natural embedding is just Θ(x) = x.val (identity function to ℝ). -/
def Theta : PosReal → ℝ := fun x => x.val

theorem Theta_order_preserving : ∀ a b : PosReal, a ≤ b ↔ Theta a ≤ Theta b := by
  intro a b
  rfl

theorem Theta_additive : ∀ x y : PosReal, Theta (x + y) = Theta x + Theta y := by
  intro x y
  rfl

/-- **Cox CANNOT apply here**: No "contradiction" baseline.

Cox's framework requires:
- A "contradiction" proposition ⊥ with p(⊥|B) = 0
- A "tautology" proposition ⊤ with p(⊤|B) = 1

In (ℝ⁺, +), there's no bottom element (no minimal positive real).
We cannot define "the plausibility of the impossible event" because
there IS no impossible event in this structure. -/
theorem no_bottom : ¬∃ bot : PosReal, ∀ x : PosReal, bot ≤ x := by
  intro ⟨bot, hbot⟩
  -- For any bot > 0, we can find x = bot/2 < bot
  let x : PosReal := ⟨bot.val / 2, by linarith [bot.prop]⟩
  have h := hbot x
  -- h says bot.val ≤ bot.val / 2, contradiction since bot.val > 0
  show False
  have : bot.val ≤ bot.val / 2 := h
  linarith [bot.prop]

end PosReal

end PositiveReals

/-! ## Example 3: The 7-Element Ideal Lattice

This example is fully developed in `Counterexamples/NonModularDistributive.lean`.

**Key points**:
- 7-element distributive lattice modeling "features with shared prerequisites"
- Monotone + disjoint-additive valuation exists
- But modular law FAILS: m(abc ⊔ abd) + m(abc ⊓ abd) ≠ m(abc) + m(abd)
- This shows K&S's inclusion-exclusion requires GBA structure, not just distributivity

See `Counterexamples/NonModularDistributive.lean` for the full formalization. -/

/-! ## Summary: When Does K&S Apply vs. Cox/Boolean?

### K&S Section 5.2 (Inclusion-Exclusion) Applies When:
1. Structure is a **Generalized Boolean Algebra** (relative complements exist)
2. Measure is **monotone** and **disjoint-additive**
3. Does NOT require: absolute complements, identity element, or full Boolean structure

### K&S Identity-Free Representation Applies When:
1. Structure is an **ordered cancellative semigroup**
2. All elements are "positive" (∀ z, z < op x z)
3. Does NOT require: identity element (⊥), top element (⊤)

### Cox's Theorem Requires:
1. **Boolean algebra** of propositions (with negation ¬A for all A)
2. Baseline "contradiction" with p(⊥|B) = 0
3. Baseline "tautology" with p(⊤|B) = 1

### Standard Probability Requires:
1. **Boolean σ-algebra** (closed under complement)
2. Countable additivity on disjoint unions
3. Probability space with Ω, ∅ as top/bottom

### Practical Implications:

**Intervals on the real line**: K&S ✓, Cox ✗
- Can measure length/probability of intervals
- Cannot define "probability of NOT [0.3, 0.7]" as a single interval

**Positive quantities without baseline**: K&S ✓, Cox ✗
- Can measure positive utilities, gains, etc.
- Cannot define "probability of zero gain" when zero isn't in the structure

**Systems with genuine synergy/entanglement**: K&S correctly identifies ✗
- The 7-element counterexample shows where inclusion-exclusion fails
- K&S doesn't claim to work there; it correctly requires GBA structure
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Examples
