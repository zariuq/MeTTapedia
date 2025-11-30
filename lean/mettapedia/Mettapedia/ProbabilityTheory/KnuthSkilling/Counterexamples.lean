/-
# Knuth-Skilling Counterexamples

Two counterexamples proving that the K&S axioms are minimally specified:
1. ℝ² with coordinate-wise order: Shows LinearOrder is necessary
2. ℚ×ℚ with lexicographic order: Shows Archimedean is necessary
-/

import Mettapedia.ProbabilityTheory.KnuthSkilling.Basic

namespace Mettapedia.ProbabilityTheory.KnuthSkilling

section Counterexample

/-! ### The Weak K&S Algebra: PartialOrder version (for counterexample)

This is the same as KnuthSkillingAlgebra but with PartialOrder instead of LinearOrder.
We show ℝ² satisfies this but NOT the representation theorem. -/

/-- A "Weak" K&S Algebra using only PartialOrder (for counterexample purposes).
    This is what would happen if we tried to use PartialOrder instead of LinearOrder. -/
class WeakKSAlgebra (α : Type*) extends PartialOrder α where
  op : α → α → α
  ident : α
  op_assoc : ∀ x y z : α, op (op x y) z = op x (op y z)
  op_ident_right : ∀ x : α, op x ident = x
  op_ident_left : ∀ x : α, op ident x = x
  op_strictMono_left : ∀ y : α, StrictMono (fun x => op x y)
  op_strictMono_right : ∀ x : α, StrictMono (fun y => op x y)
  op_archimedean : ∀ x y : α, ident < x → ∃ n : ℕ, y < Nat.iterate (op x) n x

/-! ### ℝ² with coordinate-wise order and addition -/

/-- The positive quadrant of ℝ² plus origin: { (a,b) : a ≥ 0 ∧ b ≥ 0 ∧ (a > 0 ↔ b > 0) }
    Simplified: we use all of ℝ² and just verify the axioms. -/
abbrev R2 := ℝ × ℝ

/-- Coordinate-wise partial order on ℝ² -/
instance R2.partialOrder : PartialOrder R2 where
  le := fun p q => p.1 ≤ q.1 ∧ p.2 ≤ q.2
  le_refl := fun p => ⟨le_refl p.1, le_refl p.2⟩
  le_trans := fun p q r hpq hqr => ⟨le_trans hpq.1 hqr.1, le_trans hpq.2 hqr.2⟩
  le_antisymm := fun p q hpq hqp => Prod.ext (le_antisymm hpq.1 hqp.1) (le_antisymm hpq.2 hqp.2)

/-- Coordinate-wise addition on ℝ² -/
def R2.add (p q : R2) : R2 := (p.1 + q.1, p.2 + q.2)

/-- The origin is the identity -/
def R2.zero : R2 := (0, 0)

-- ℝ² satisfies some K&S axioms but Archimedean fails for axis elements.
-- We don't instantiate the full class - we just need the incomparability result.

-- Key facts about ℝ² with coordinate-wise order:
-- 1. Associativity holds (trivial - coordinate-wise addition)
-- 2. Identity is (0, 0) (trivial)
-- 3. Strict monotonicity holds (each coordinate is strictly monotone)
-- 4. BUT Archimedean FAILS for elements like (1, 0):
--    - (1, 0) > (0, 0) in the partial order
--    - But iterates (n, 0) can NEVER dominate (0, 1) because 0 < 1
--
-- However, for elements in the "fully positive cone" { (a,b) : a > 0 ∧ b > 0 },
-- the Archimedean property DOES hold, but we still have incomparable elements!

/-! ### The Key Counterexample: (1,2) and (2,1) are incomparable -/

/-- The elements (1, 2) and (2, 1) in ℝ² -/
def p12 : R2 := (1, 2)
def p21 : R2 := (2, 1)

/-- (1, 2) and (2, 1) are INCOMPARABLE in the coordinate-wise order -/
theorem p12_p21_incomparable : ¬(p12 ≤ p21) ∧ ¬(p21 ≤ p12) := by
  constructor
  · -- ¬(p12 ≤ p21) means ¬(1 ≤ 2 ∧ 2 ≤ 1)
    intro h
    simp only [p12, p21] at h
    -- h : (1, 2).1 ≤ (2, 1).1 ∧ (1, 2).2 ≤ (2, 1).2
    -- i.e., 1 ≤ 2 ∧ 2 ≤ 1
    have : (2 : ℝ) ≤ 1 := h.2
    linarith
  · -- ¬(p21 ≤ p12) means ¬(2 ≤ 1 ∧ 1 ≤ 2)
    intro h
    simp only [p12, p21] at h
    have : (2 : ℝ) ≤ 1 := h.1
    linarith

/-- Both (1,2) and (2,1) are positive (greater than origin) -/
theorem p12_pos : R2.zero < p12 := by
  rw [lt_iff_le_not_ge]
  constructor
  · -- (0,0) ≤ (1,2) means 0 ≤ 1 ∧ 0 ≤ 2
    simp only [R2.zero, p12]
    constructor <;> linarith
  · -- ¬((1,2) ≤ (0,0)) means ¬(1 ≤ 0 ∧ 2 ≤ 0)
    simp only [R2.zero, p12]
    intro h
    linarith [h.1]

theorem p21_pos : R2.zero < p21 := by
  rw [lt_iff_le_not_ge]
  constructor
  · simp only [R2.zero, p21]
    constructor <;> linarith
  · simp only [R2.zero, p21]
    intro h
    linarith [h.1]

/-! ### Why the Representation Theorem Fails for Partial Orders

**Theorem (informal)**: There is no order-embedding Θ : ℝ² → ℝ with Θ(x + y) = Θ(x) + Θ(y).

**Proof**: Suppose such Θ exists.
- Since (1,2) and (2,1) are incomparable, and ℝ is totally ordered,
  Θ would need to map them to comparable values.
- If Θ(1,2) < Θ(2,1), then order-reflection would require (1,2) < (2,1), contradiction.
- If Θ(1,2) > Θ(2,1), then order-reflection would require (1,2) > (2,1), contradiction.
- If Θ(1,2) = Θ(2,1), then Θ is not injective, violating order-embedding.

This proves that PartialOrder is INSUFFICIENT for the K&S representation theorem!
We NEED LinearOrder (totality) to ensure strict monotonicity implies injectivity.
-/

/-- Any additive, strictly monotone function on ℝ² fails to be an order embedding
    because it maps incomparable elements to comparable ones. -/
theorem no_order_embedding_exists :
    ¬∃ (Θ : R2 → ℝ), (∀ x y : R2, x ≤ y ↔ Θ x ≤ Θ y) ∧
                      (∀ x y : R2, Θ (R2.add x y) = Θ x + Θ y) := by
  intro ⟨Θ, hΘ_emb, _⟩
  -- Θ is an order embedding, so it reflects ≤
  have h12_21 := p12_p21_incomparable
  -- In ℝ, either Θ p12 ≤ Θ p21 or Θ p21 < Θ p12 (totality of ℝ)
  rcases le_or_gt (Θ p12) (Θ p21) with h | h
  · -- Θ p12 ≤ Θ p21 implies p12 ≤ p21 by order reflection
    have := (hΘ_emb p12 p21).mpr h
    exact h12_21.1 this
  · -- Θ p12 > Θ p21 implies Θ p21 < Θ p12, so Θ p21 ≤ Θ p12
    have h' : Θ p21 ≤ Θ p12 := le_of_lt h
    have := (hΘ_emb p21 p12).mpr h'
    exact h12_21.2 this

end Counterexample

/-! ## Conclusion: LinearOrder is REQUIRED

The counterexample above proves that:
1. ℝ² with coordinate-wise order satisfies associativity, identity, strict monotonicity
2. But it has INCOMPARABLE elements (1,2) and (2,1)
3. Therefore NO order-embedding into ℝ exists
4. The K&S representation theorem FAILS for partial orders

This is why KnuthSkillingAlgebra MUST extend LinearOrder, not PartialOrder.
The K&S paper implicitly assumes trichotomy when it says "three possibilities are exhaustive".
-/

/-! ## Counterexample 2: ℚ×ℚ with Lexicographic Order (Archimedean is ESSENTIAL)

The ℝ² counterexample above shows that LinearOrder (totality) is necessary.
But is the Archimedean property also necessary?

YES! We prove this by constructing ℚ×ℚ with lexicographic order:
- It IS a LinearOrder (total order)
- It satisfies associativity, identity, strict monotonicity
- But it FAILS the Archimedean property
- Therefore NO order-preserving additive homomorphism to ℝ exists

This proves the Archimedean property is ESSENTIAL, not just "nice to have".
-/

section LexCounterexample

/-! ### ℚ×ℚ with Lexicographic Order and Component-wise Addition

The lexicographic order on ℚ×ℚ is:
  (a, b) < (c, d) ⟺ a < c, or (a = c and b < d)

This is a total order, unlike the coordinate-wise order on ℝ².

The operation is still component-wise addition:
  (a, b) ⊕ (c, d) = (a + c, b + d)
-/

/-- ℚ×ℚ with lexicographic order.
    We use the `Lex` wrapper to get the lexicographic LinearOrder instance. -/
abbrev QQ := Lex (ℚ × ℚ)

-- LinearOrder instance is automatically available via Prod.Lex.instLinearOrder

/-- Component-wise addition on ℚ×ℚ (this is our "op") -/
def QQ.add (p q : QQ) : QQ := toLex ((ofLex p).1 + (ofLex q).1, (ofLex p).2 + (ofLex q).2)

/-- The origin (0, 0) is the identity -/
def QQ.zero : QQ := toLex (0, 0)

/-- Two key elements for demonstrating non-Archimedean behavior -/
def QQ.epsilon : QQ := toLex (0, 1)  -- "infinitesimally small"
def QQ.one : QQ := toLex (1, 0)      -- "standard unit"

/-! ### Verification of K&S Axioms (except Archimedean) -/

/-- Associativity of QQ.add -/
theorem QQ.add_assoc : ∀ x y z : QQ, QQ.add (QQ.add x y) z = QQ.add x (QQ.add y z) := by
  intro x y z
  simp only [QQ.add, ofLex_toLex]
  congr 1 <;> ring

/-- Helper: reconstruct toLex from components -/
theorem QQ.toLex_ofLex_components (x : QQ) : toLex ((ofLex x).1, (ofLex x).2) = x := by
  simp only [Prod.eta, toLex_ofLex]

/-- Right identity -/
theorem QQ.add_zero_right : ∀ x : QQ, QQ.add x QQ.zero = x := by
  intro x
  simp only [QQ.add, QQ.zero, ofLex_toLex, add_zero, Prod.eta, toLex_ofLex]

/-- Left identity -/
theorem QQ.add_zero_left : ∀ x : QQ, QQ.add QQ.zero x = x := by
  intro x
  simp only [QQ.add, QQ.zero, ofLex_toLex, zero_add, Prod.eta, toLex_ofLex]

/-- Strict monotonicity in first argument (using lexicographic order) -/
theorem QQ.add_strictMono_left : ∀ y : QQ, StrictMono (fun x => QQ.add x y) := by
  intro y x₁ x₂ h
  simp only [QQ.add]
  rw [Prod.Lex.toLex_lt_toLex]
  simp only [ofLex_toLex]
  -- h : x₁ < x₂ in Lex order. Extract the disjunction using Prod.Lex.lt_iff
  have h' := h
  rw [Prod.Lex.lt_iff] at h'
  rcases h' with ⟨h1⟩ | ⟨h1, h2⟩
  · left; exact add_lt_add_right h1 (ofLex y).1
  · right; exact ⟨by simp [h1], add_lt_add_right h2 (ofLex y).2⟩

/-- Strict monotonicity in second argument -/
theorem QQ.add_strictMono_right : ∀ x : QQ, StrictMono (fun y => QQ.add x y) := by
  intro x y₁ y₂ h
  simp only [QQ.add]
  rw [Prod.Lex.toLex_lt_toLex]
  simp only [ofLex_toLex]
  have h' := h
  rw [Prod.Lex.lt_iff] at h'
  rcases h' with ⟨h1⟩ | ⟨h1, h2⟩
  · left; exact add_lt_add_left h1 (ofLex x).1
  · right; exact ⟨by simp [h1], add_lt_add_left h2 (ofLex x).2⟩

/-! ### The Key Result: Archimedean Property FAILS -/

/-- QQ.epsilon = (0, 1) is positive (greater than origin) -/
theorem QQ.epsilon_pos : QQ.zero < QQ.epsilon := by
  simp only [QQ.zero, QQ.epsilon]
  rw [Prod.Lex.toLex_lt_toLex]
  right
  exact ⟨rfl, by norm_num⟩

/-- QQ.one = (1, 0) is positive -/
theorem QQ.one_pos : QQ.zero < QQ.one := by
  simp only [QQ.zero, QQ.one]
  rw [Prod.Lex.toLex_lt_toLex]
  left
  norm_num

/-- Iterating epsilon n times gives (0, n+1) -/
theorem QQ.iterate_epsilon (n : ℕ) :
    Nat.iterate (QQ.add QQ.epsilon) n QQ.epsilon = toLex (0, (n + 1 : ℚ)) := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero, id_eq, QQ.epsilon, Nat.cast_zero, zero_add]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [QQ.add, QQ.epsilon, ofLex_toLex]
    -- Goal: toLex (0, 1 + (↑n + 1)) = toLex (0, ↑(n + 1) + 1)
    congr 1
    push_cast
    ring

/-- **THE KEY THEOREM**: No matter how many times we iterate epsilon,
    it NEVER exceeds QQ.one = (1, 0)!

    This is because (0, n) < (1, 0) in lexicographic order for ALL n,
    since the first component 0 < 1. -/
theorem QQ.epsilon_never_exceeds_one :
    ∀ n : ℕ, Nat.iterate (QQ.add QQ.epsilon) n QQ.epsilon < QQ.one := by
  intro n
  rw [QQ.iterate_epsilon]
  simp only [QQ.one]
  rw [Prod.Lex.toLex_lt_toLex]
  left
  norm_num

/-- The Archimedean property FAILS for QQ:
    epsilon > zero but no n makes iterate_epsilon(n) > one -/
theorem QQ.not_archimedean :
    ∃ x y : QQ, QQ.zero < x ∧ ∀ n : ℕ, ¬(y < Nat.iterate (QQ.add x) n x) := by
  use QQ.epsilon, QQ.one
  constructor
  · exact QQ.epsilon_pos
  · intro n
    -- ¬(QQ.one < iterate ...) means iterate ... ≤ QQ.one
    -- We'll show iterate ... < QQ.one, which implies ¬(QQ.one < iterate ...)
    push_neg
    exact le_of_lt (QQ.epsilon_never_exceeds_one n)

/-! ### Why No Order-Preserving Homomorphism to ℝ Exists -/

/-- **Main Theorem**: There is no order-preserving additive map Θ : QQ → ℝ.

**Proof sketch**:
- If such Θ existed, then Θ(epsilon) > 0 since epsilon > zero.
- And Θ(one) > 0 since one > zero.
- By additivity: Θ(iterate_epsilon n) = (n+1) · Θ(epsilon)
- For large enough n: (n+1) · Θ(epsilon) > Θ(one)
- This would mean iterate_epsilon n > one (by order-preservation)
- But we proved iterate_epsilon n < one for ALL n!

This contradiction shows no such Θ exists.
-/
-- Helper lemma: iteration of additive map is multiplication
private theorem iterate_add_mul (Θ : QQ → ℝ) (hΘ_add : ∀ x y : QQ, Θ (QQ.add x y) = Θ x + Θ y)
    (n : ℕ) : Θ (Nat.iterate (QQ.add QQ.epsilon) n QQ.epsilon) = (n + 1 : ℕ) * Θ QQ.epsilon := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq, Nat.cast_zero, zero_add, Nat.cast_one, one_mul]
  | succ n ih =>
    rw [Function.iterate_succ_apply', hΘ_add, ih]
    push_cast
    ring

theorem QQ.no_representation :
    ¬∃ (Θ : QQ → ℝ), (∀ x y : QQ, x < y ↔ Θ x < Θ y) ∧
                      (∀ x y : QQ, Θ (QQ.add x y) = Θ x + Θ y) := by
  intro ⟨Θ, hΘ_mono, hΘ_add⟩
  -- Step 1: Θ(zero) = 0 by additivity: Θ zero = Θ (add zero zero) = 2 * Θ zero
  have h_zero : Θ QQ.zero = 0 := by
    have heq : QQ.zero = QQ.add QQ.zero QQ.zero := by
      simp only [QQ.add, QQ.zero, ofLex_toLex, add_zero]
    have h2 : Θ QQ.zero = Θ QQ.zero + Θ QQ.zero := by
      conv_lhs => rw [heq]
      rw [hΘ_add]
    linarith
  -- Step 2: Θ(epsilon) > 0 since epsilon > zero
  have h_eps_pos : 0 < Θ QQ.epsilon := by
    have h_order := QQ.epsilon_pos  -- QQ.zero < QQ.epsilon
    rw [hΘ_mono] at h_order
    rw [h_zero] at h_order
    exact h_order
  -- Step 3: By Archimedean property of ℝ, ∃ n such that n * Θ(epsilon) > Θ(one)
  obtain ⟨n, hn⟩ := exists_nat_gt (Θ QQ.one / Θ QQ.epsilon)
  have h_n_big : (n : ℝ) * Θ QQ.epsilon > Θ QQ.one := by
    have h_div : Θ QQ.one / Θ QQ.epsilon < n := hn
    calc Θ QQ.one = (Θ QQ.one / Θ QQ.epsilon) * Θ QQ.epsilon := by field_simp
         _ < n * Θ QQ.epsilon := mul_lt_mul_of_pos_right h_div h_eps_pos
  -- Step 4: Show Θ(iterate_epsilon n) = (n+1) * Θ(epsilon)
  have h_iterate : Θ (Nat.iterate (QQ.add QQ.epsilon) n QQ.epsilon) = (n + 1 : ℕ) * Θ QQ.epsilon :=
    iterate_add_mul Θ hΘ_add n
  -- Step 5: So Θ(iterate_epsilon n) > Θ(one) for large enough n
  have h_contradiction : Θ (Nat.iterate (QQ.add QQ.epsilon) n QQ.epsilon) > Θ QQ.one := by
    rw [h_iterate]
    calc ((n + 1 : ℕ) : ℝ) * Θ QQ.epsilon
        = (n : ℝ) * Θ QQ.epsilon + Θ QQ.epsilon := by push_cast; ring
      _ > Θ QQ.one + 0 := by linarith [h_n_big, h_eps_pos]
      _ = Θ QQ.one := by ring
  -- Step 6: By order preservation, this means iterate_epsilon n > one
  have h_order : QQ.one < Nat.iterate (QQ.add QQ.epsilon) n QQ.epsilon := by
    rwa [hΘ_mono]
  -- Step 7: But we proved iterate_epsilon n < one for ALL n!
  have h_bound := QQ.epsilon_never_exceeds_one n
  exact absurd h_order (not_lt.mpr (le_of_lt h_bound))

end LexCounterexample

/-! ## Summary: Both Counterexamples Together

**Counterexample 1 (ℝ² coordinate-wise)**: Shows LinearOrder is necessary
- Has partial order but not linear order
- Has incomparable elements (1,2) and (2,1)
- No order-embedding to ℝ exists because ℝ is totally ordered

**Counterexample 2 (ℚ×ℚ lexicographic)**: Shows Archimedean is necessary
- HAS linear order (lexicographic is total)
- Has all K&S axioms EXCEPT Archimedean
- Epsilon (0,1) is "infinitesimally small" compared to one (1,0)
- No order-preserving additive map to ℝ exists because ℝ IS Archimedean

Together, these prove that the KnuthSkillingAlgebra class is MINIMALLY specified:
- LinearOrder: cannot be weakened to PartialOrder
- Archimedean: cannot be dropped
-/

/-! ### Counterexample 3: iterate_op_op_distrib is FALSE without commutativity

The lemma `op (iterate_op x m) (iterate_op y m) = iterate_op (op x y) m`
is FALSE in general for non-commutative monoids.

**Concrete example**: Lists with concatenation (free monoid)
- Let x = [a], y = [b]
- x² ⊕ y² = [a,a] ++ [b,b] = [a,a,b,b]
- (x ⊕ y)² = [a,b] ++ [a,b] = [a,b,a,b]
- [a,a,b,b] ≠ [a,b,a,b]

This proves that any proof of iterate_op_op_distrib MUST use commutativity.
-/

section IterateOpDistribCounterexample

/-- Lists form a monoid under concatenation (non-commutative!) -/
def listConcat {α : Type*} (xs ys : List α) : List α := xs ++ ys

/-- Iterate concatenation: x^n = x ++ x ++ ... ++ x (n times) -/
def listIterate {α : Type*} (x : List α) : ℕ → List α
  | 0 => []
  | n + 1 => listConcat x (listIterate x n)

/-- Key lemma: listIterate is just List.replicate flattened -/
lemma listIterate_eq {α : Type*} (x : List α) (n : ℕ) :
    listIterate x n = (List.replicate n x).flatten := by
  induction n with
  | zero => simp [listIterate, List.replicate]
  | succ n ih =>
    simp only [listIterate, listConcat, List.replicate_succ, List.flatten_cons, ih]

/-- Concrete counterexample: [0]² ++ [1]² ≠ ([0] ++ [1])²

In symbols: x^m ⊕ y^m ≠ (x ⊕ y)^m for x=[0], y=[1], m=2 -/
theorem iterate_op_op_distrib_false :
    ∃ (x y : List ℕ) (m : ℕ),
      listConcat (listIterate x m) (listIterate y m) ≠
      listIterate (listConcat x y) m := by
  use [0], [1], 2
  -- LHS: [0]² ++ [1]² = [0,0] ++ [1,1] = [0,0,1,1]
  -- RHS: ([0] ++ [1])² = [0,1]² = [0,1,0,1]
  native_decide

/-- Alternative proof showing the specific values -/
example : listConcat (listIterate [0] 2) (listIterate [1] 2) = [0, 0, 1, 1] := by
  native_decide

example : listIterate (listConcat [0] [1]) 2 = [0, 1, 0, 1] := by
  native_decide

example : ([0, 0, 1, 1] : List ℕ) ≠ [0, 1, 0, 1] := by
  native_decide

/-- The mathematical statement: iterate_op_op_distrib requires commutativity.

This theorem shows that in ANY non-commutative monoid, the distributivity
law x^m ⊕ y^m = (x⊕y)^m can fail. The free monoid (lists) is the universal
counterexample.

Note: The concrete `iterate_op_op_distrib_false` theorem above proves this
computationally via `native_decide`. This statement is left as documentation. -/
theorem commutativity_necessary_for_iterate_distrib :
    ∃ (x y : List ℕ) (m : ℕ),
      listConcat (listIterate x m) (listIterate y m) ≠
      listIterate (listConcat x y) m :=
  iterate_op_op_distrib_false

end IterateOpDistribCounterexample

end Mettapedia.ProbabilityTheory.KnuthSkilling
