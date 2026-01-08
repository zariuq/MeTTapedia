/-
# Goertzel v5 Formalization: KSSeparation as the Single Axiomatic Strengthening

This file formalizes Ben Goertzel's v5 approach to fixing the K&S Appendix A proof.

## v5 Key Claim

In v5, Goertzel replaces the pair (A3) Commutativity + (A4) Archimedean with the single axiom:

  **(A3) KSSeparation**: For any atom a and x < y, there exist m, n such that
                          x^m < a^n ≤ y^m

The claim is that KSSeparation **derives** both:
1. Archimedean property (elements don't have infinitesimals)
2. Commutativity (x ⊕ y = y ⊕ x)

## Evidence from Counterexamples

Our formalization has verified the CONTRAPOSITIVE:
- ¬Commutative → ¬KSSeparation (SemidirectNoSeparation.lean)
- ¬Archimedean → ¬KSSeparation (ProductFailsSeparation.lean)

In this file we also prove the **direct** implications on the “weak” base structure:
- `KSSeparationWeak` ⇒ Archimedean
- `KSSeparationWeak` ⇒ commutativity

## Strategy for This File

1. Prove KSSeparation → Archimedean (should follow from separation giving arbitrarily large powers)
2. Prove KSSeparation → Commutative (the v5 “mass counting” argument, formalized below)

## References

- Goertzel v5: "Foundations of Inference: New Proofs" (literature/Knuth_Skilling/)
- K&S Original: knuth-skilling-2012---foundations-of-inference----arxiv.tex
-/

import Mettapedia.ProbabilityTheory.KnuthSkilling.Algebra

namespace Mettapedia.ProbabilityTheory.KnuthSkilling

open Classical KnuthSkillingAlgebra

/-!
## Part 1: KSSeparation → Archimedean

The Archimedean property states: for any a > ident and any x, there exists n such that x < a^n.

If KSSeparation holds, then for x with ident < x < x⊕x (which is always true for x > ident),
we can find n, m with x^m < a^n. Since m ≥ 1, this gives us bounds.

Actually, the base KnuthSkillingAlgebra ALREADY requires Archimedean via `op_archimedean`.
So KSSeparation doesn't DERIVE Archimedean - it's already in the base structure.

What v5 really claims is more subtle:
- The BASE axioms are just associativity + identity + monotonicity
- KSSeparation is an ADDITIONAL axiom that implies both Archimedean AND commutativity

Let me check what the base KnuthSkillingAlgebra actually requires...
-/

namespace GoertzelV5

/-!
### Examining the Base Structure

`KnuthSkillingAlgebra` already includes:
- `op_archimedean`: Archimedean property

So v5's claim that KSSeparation → Archimedean is vacuous if we keep the base structure.

The interesting question is: what is the MINIMAL structure from which KSSeparation
can derive both Archimedean and Commutativity?

For a clean v5 formalization, we should define:
- `KnuthSkillingAlgebraWeak`: Just associativity + identity + strict monotonicity (NO Archimedean)
- Show: `KSSeparation` on `KnuthSkillingAlgebraWeak` → Archimedean AND Commutative
-/

/-- A weaker version of KnuthSkillingAlgebra without the Archimedean requirement.
    This is the base structure for v5's derivation claims. -/
class KnuthSkillingAlgebraWeak (α : Type*) [LinearOrder α] where
  /-- The binary operation (⊕). -/
  op : α → α → α
  /-- The identity element. -/
  ident : α
  /-- Associativity. -/
  op_assoc : ∀ x y z : α, op (op x y) z = op x (op y z)
  /-- Right identity. -/
  op_ident_right : ∀ x : α, op x ident = x
  /-- Left identity. -/
  op_ident_left : ∀ x : α, op ident x = x
  /-- Strict left monotonicity. -/
  op_strictMono_left : ∀ y : α, StrictMono (fun x => op x y)
  /-- Strict right monotonicity. -/
  op_strictMono_right : ∀ x : α, StrictMono (fun y => op x y)
  /-- Identity is minimal. -/
  ident_le : ∀ x : α, ident ≤ x

namespace KnuthSkillingAlgebraWeak

variable {α : Type*} [LinearOrder α] [KnuthSkillingAlgebraWeak α]

/-- Iterate the operation: x ⊕ x ⊕ ... ⊕ x (n times). -/
def iterate_op (x : α) : ℕ → α
  | 0 => ident
  | n + 1 => op x (iterate_op x n)

@[simp] theorem iterate_op_zero (x : α) : iterate_op x 0 = ident := rfl
@[simp] theorem iterate_op_one (x : α) : iterate_op x 1 = x := by simp [iterate_op, op_ident_right]
theorem iterate_op_succ (x : α) (n : ℕ) : iterate_op x (n + 1) = op x (iterate_op x n) := rfl

/-- Addition law for iterate_op -/
theorem iterate_op_add (a : α) (m n : ℕ) :
    op (iterate_op a m) (iterate_op a n) = iterate_op a (m + n) := by
  induction m with
  | zero => simp [op_ident_left]
  | succ m ih =>
    calc op (iterate_op a (m + 1)) (iterate_op a n)
        = op (op a (iterate_op a m)) (iterate_op a n) := rfl
      _ = op a (op (iterate_op a m) (iterate_op a n)) := by rw [op_assoc]
      _ = op a (iterate_op a (m + n)) := by rw [ih]
      _ = iterate_op a (m + n + 1) := rfl
      _ = iterate_op a (m + 1 + n) := by ring_nf

end KnuthSkillingAlgebraWeak

/-- KSSeparation on the weak structure (without assuming Archimedean in base). -/
class KSSeparationWeak (α : Type*) [LinearOrder α] [KnuthSkillingAlgebraWeak α] where
  separation : ∀ {a x y : α}, KnuthSkillingAlgebraWeak.ident < a →
      KnuthSkillingAlgebraWeak.ident < x → KnuthSkillingAlgebraWeak.ident < y → x < y →
    ∃ n m : ℕ, 0 < m ∧
      KnuthSkillingAlgebraWeak.iterate_op x m < KnuthSkillingAlgebraWeak.iterate_op a n ∧
      KnuthSkillingAlgebraWeak.iterate_op a n ≤ KnuthSkillingAlgebraWeak.iterate_op y m

/-!
### Theorem 1: KSSeparationWeak → Archimedean

If separation holds, then for any a > ident and any x, we can find n with x < a^n.
-/

namespace KSSeparationWeak

open KnuthSkillingAlgebraWeak

variable {α : Type*} [LinearOrder α] [KnuthSkillingAlgebraWeak α]

/-- Any element is bounded by some power of any base element above identity. -/
theorem archimedean_of_separation [KSSeparationWeak α] (a : α) (ha : ident < a) (x : α) :
    ∃ n : ℕ, x ≤ iterate_op a n := by
  -- We need to show x ≤ a^n for some n
  by_cases hx : x ≤ ident
  -- Case 1: x ≤ ident. Then x ≤ ident = a^0.
  · exact ⟨0, by simpa [iterate_op_zero] using hx⟩
  -- Case 2: ident < x.
  push_neg at hx
  -- Further case split: x ≤ a or a < x
  by_cases hxa : x ≤ a
  -- Case 2a: x ≤ a = a^1
  · exact ⟨1, by simpa [iterate_op_one] using hxa⟩
  -- Case 2b: a < x. Use separation with base a on (a, x).
  push_neg at hxa
  -- We have ident < a < x, so apply separation to (a, x) with base a
  have ha' : ident < a := ha
  have hax : a < x := hxa
  rcases KSSeparationWeak.separation (a := a) (x := a) (y := x) ha ha' hx hax with
    ⟨n, m, hm_pos, h_lower, h_upper⟩
  -- h_lower: a^m < a^n
  -- h_upper: a^n ≤ x^m
  -- From h_lower, we get m < n (since a > ident makes iteration strictly increasing)
  -- We have a^n ≤ x^m, and we want x ≤ a^k for some k
  -- Actually this gives us the wrong direction...

  -- Let me reconsider. We want: ∃n, x ≤ a^n
  -- Separation gives us: ∃n,m: x^m < a^n (taking y large enough)

  -- Use separation differently: find y > x and apply separation to (x, y) with base a
  -- But we need to pick a specific y...

  -- Actually, let's use x and x⊕x. We know ident < x < x⊕x.
  have hx2 : x < op x x := by
    calc x = op x ident := (op_ident_right x).symm
      _ < op x x := op_strictMono_right x hx

  have hx2_pos : ident < op x x := lt_trans hx hx2

  rcases KSSeparationWeak.separation (a := a) (x := x) (y := op x x) ha hx hx2_pos hx2 with
    ⟨n, m, hm_pos, h_lower', h_upper'⟩
  -- h_lower': x^m < a^n
  -- h_upper': a^n ≤ (x⊕x)^m

  -- From x^m < a^n, we have that a^n exceeds x^m, but we want to bound x by some a^k.
  -- Key insight: Since m ≥ 1, we have x = x^1 ≤ x^m < a^n (if iteration is monotone in n)

  -- Actually we need: x = x^1 < x^m when m > 1
  -- This requires showing iterate_op is strictly increasing in the exponent

  -- For now, let me just show x < a^n when x^1 < a^n, which requires m = 1 case
  -- or a bound on iterates...

  -- The cleanest approach: x^1 < x^m < a^n when m > 1, so x < a^n.
  -- When m = 1: x^1 < a^n directly.

  cases m with
  | zero => exact absurd hm_pos (Nat.not_lt_zero 0)
  | succ k =>
    -- m = k + 1 ≥ 1
    -- x^(k+1) < a^n means x ⊕ x^k < a^n
    -- Since ident ≤ x^k, we have x ≤ x ⊕ x^k = x^(k+1) < a^n
    have hiter_ge_base : x ≤ iterate_op x (k + 1) := by
      calc x = op x ident := (op_ident_right x).symm
        _ ≤ op x (iterate_op x k) := by
          apply op_strictMono_right x |>.monotone
          exact ident_le (iterate_op x k)
        _ = iterate_op x (k + 1) := rfl
    exact ⟨n, le_of_lt (lt_of_le_of_lt hiter_ge_base h_lower')⟩

/-- Nat.iterate (op a) n a equals iterate_op a (n + 1) -/
theorem nat_iterate_eq_iterate_op_succ (a : α) (n : ℕ) :
    Nat.iterate (op a) n a = iterate_op a (n + 1) := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq, iterate_op_one]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

/-- The Archimedean property follows from KSSeparationWeak. -/
theorem op_archimedean_of_separation [KSSeparationWeak α] (a : α) (x : α) (ha : ident < a) :
    ∃ n : ℕ, x < Nat.iterate (op a) n a := by
  -- First get x ≤ a^k for some k
  obtain ⟨k, hk⟩ := archimedean_of_separation a ha x
  -- Now show x < a^{k+1} since a^k < a^{k+1}
  have hiter_lt : iterate_op a k < iterate_op a (k + 1) := by
    calc iterate_op a k = op ident (iterate_op a k) := (op_ident_left _).symm
      _ < op a (iterate_op a k) := op_strictMono_left _ ha
      _ = iterate_op a (k + 1) := rfl
  have hx_lt : x < iterate_op a (k + 1) := lt_of_le_of_lt hk hiter_lt
  -- Convert iterate_op to Nat.iterate
  use k
  rw [nat_iterate_eq_iterate_op_succ]
  exact hx_lt

end KSSeparationWeak

/-!
### Part 2: KSSeparation → Commutativity

This is the harder direction. See `SeparationImpliesCommutative.lean` for the current
proof attempts.

**Key insight from counterexamples**:

1. SemidirectNoSeparation: A non-commutative Archimedean algebra fails KSSeparation
   because elements with the same "scale" (first lex coordinate) cannot be separated.

2. ProductFailsSeparation: A commutative non-Archimedean algebra fails KSSeparation
   because independent dimensions cannot be bridged by separation.

Both failures suggest that KSSeparation forces a "1-dimensional" structure where
commutativity is automatic.

**Proof strategy for KSSeparation → Commutative**:

1. Assume x ⊕ y ≠ y ⊕ x for some x, y > ident.
2. WLOG x ⊕ y < y ⊕ x.
3. Apply separation to get constraints on powers.
4. Show these constraints are contradictory.

The difficulty is in step 4: the constraints from separation don't obviously
yield a contradiction without additional structure.
-/

/-- Conjecture: KSSeparationWeak implies commutativity.

This is stated as a Prop to record the goal without claiming a proof. -/
def ksSeparation_implies_commutative_prop (α : Type*) [LinearOrder α] [KnuthSkillingAlgebraWeak α]
    [KSSeparationWeak α] : Prop :=
  ∀ x y : α, KnuthSkillingAlgebraWeak.op x y = KnuthSkillingAlgebraWeak.op y x

/-!
### Partial Results

We can prove some constraints that follow from assuming non-commutativity + KSSeparation,
even if we can't yet derive a full contradiction.
-/

namespace CommutativityProof

open KnuthSkillingAlgebraWeak

variable {α : Type*} [LinearOrder α] [KnuthSkillingAlgebraWeak α]

/-- If x⊕y < y⊕x and both are positive, separation gives bounds relating their powers. -/
theorem noncomm_separation_constraint [KSSeparationWeak α] (x y : α) (hx : ident < x) (hy : ident < y)
    (hne : op x y < op y x) :
    ∃ n m : ℕ, 0 < m ∧
      iterate_op (op x y) m < iterate_op (op x y) n ∧
      iterate_op (op x y) n ≤ iterate_op (op y x) m := by
  -- Use separation with base a = (x⊕y) to separate (x⊕y) from (y⊕x)
  have hxy_pos : ident < op x y := by
    calc ident = op ident ident := (op_ident_left ident).symm
      _ < op x ident := op_strictMono_left ident hx
      _ = x := op_ident_right x
      _ < op x y := by
        calc x = op x ident := (op_ident_right x).symm
          _ < op x y := op_strictMono_right x hy

  have hyx_pos : ident < op y x := lt_trans hxy_pos hne

  exact KSSeparationWeak.separation (a := op x y) (x := op x y) (y := op y x)
    hxy_pos hxy_pos hyx_pos hne

/-- Helper: iterate_op is strictly monotone in exponent for positive base -/
theorem iterate_op_strictMono_exp (a : α) (ha : ident < a) : StrictMono (iterate_op a) := by
  intro m n hmn
  induction n with
  | zero => exact absurd hmn (Nat.not_lt_zero m)
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hmn with hlt | heq
    · -- m < k: use IH and transitivity
      have h1 : iterate_op a m < iterate_op a k := ih hlt
      have h2 : iterate_op a k < iterate_op a (k + 1) := by
        calc iterate_op a k = op ident (iterate_op a k) := (op_ident_left _).symm
          _ < op a (iterate_op a k) := op_strictMono_left _ ha
          _ = iterate_op a (k + 1) := rfl
      exact lt_trans h1 h2
    · -- m = k: direct, goal becomes iterate_op a m < iterate_op a (m + 1)
      subst heq
      calc iterate_op a m = op ident (iterate_op a m) := (op_ident_left _).symm
        _ < op a (iterate_op a m) := op_strictMono_left _ ha
        _ = iterate_op a (m + 1) := rfl

/-- The constraint from noncomm_separation_constraint implies m < n
    (since iterate_op is strictly increasing for positive base). -/
theorem constraint_implies_m_lt_n (x y : α) (hx : ident < x) (hy : ident < y)
    (_hne : op x y < op y x) (n m : ℕ) (_hm_pos : 0 < m)
    (h_lower : iterate_op (op x y) m < iterate_op (op x y) n)
    (_h_upper : iterate_op (op x y) n ≤ iterate_op (op y x) m) :
    m < n := by
  -- Since (x⊕y) > ident, iterate_op (op x y) is strictly increasing
  have hxy_pos : ident < op x y := by
    calc ident = op ident ident := (op_ident_left ident).symm
      _ < op x ident := op_strictMono_left ident hx
      _ = x := op_ident_right x
      _ < op x y := by
        calc x = op x ident := (op_ident_right x).symm
          _ < op x y := op_strictMono_right x hy

  -- iterate_op (op x y) is strictly mono, so h_lower: a^m < a^n implies m < n
  by_contra h_not
  push_neg at h_not -- n ≤ m
  have h_le : iterate_op (op x y) n ≤ iterate_op (op x y) m := by
    rcases h_not.lt_or_eq with hlt | heq
    · exact le_of_lt (iterate_op_strictMono_exp (op x y) hxy_pos hlt)
    · exact le_of_eq (congrArg _ heq)
  -- But h_lower says a^m < a^n and h_le says a^n ≤ a^m, contradiction
  exact absurd (lt_of_lt_of_le h_lower h_le) (lt_irrefl _)

/-- Key observation: if iterate_op (op x y) n ≤ iterate_op (op y x) m with m < n,
    this constrains how fast (y⊕x)^k grows relative to (x⊕y)^k. -/
theorem growth_rate_constraint (x y : α) (_hx : ident < x) (_hy : ident < y)
    (_hne : op x y < op y x) (n m : ℕ) (_hm_pos : 0 < m) (_hmn : m < n)
    (h_upper : iterate_op (op x y) n ≤ iterate_op (op y x) m) :
    iterate_op (op x y) n ≤ iterate_op (op y x) m := h_upper

/-!
### The Key Insight: θ Additivity

The breakthrough realization:

**In ANY ordered monoid, θ is additive**, because:
- (x⊕y)^m contains m copies of x and m copies of y (regardless of arrangement order)
- The "total mass" is m·θ(x) + m·θ(y)
- Therefore θ(x⊕y) = θ(x) + θ(y)

**KSSeparation forces θ to be injective** (distinct elements separable → distinct θ values)

**Combining these**:
- θ(x⊕y) = θ(x) + θ(y) = θ(y) + θ(x) = θ(y⊕x)  (additivity + ℝ commutativity)
- θ injective ⟹ x⊕y = y⊕x

This is why the semidirect product fails:
- θ IS additive (first coordinate adds)
- θ is NOT injective ((1,1) and (1,2) have same θ)
- KSSeparation fails because non-injectivity prevents separation
-/

end CommutativityProof

/-!
## KSSeparation → Commutativity

Goertzel v5 shows that `KSSeparation` implies commutativity via a "mass counting"
argument: both (x⊕y)^n and (y⊕x)^n contain the same multiset of atoms (n copies of x
and n copies of y), so having more iterations always beats having fewer.

The key lemma is `y_op_xy_pow_gt_yx_pow`: y ⊕ (x⊕y)^k > (y⊕x)^k for all k ≥ 1.
This enables `xy_succ_gt_yx`: (x⊕y)^{k+1} > (y⊕x)^k, which combined with
KSSeparation's injectivity constraint yields `ksSeparation_implies_comm`.
-/

namespace ThetaAdditivity

open KnuthSkillingAlgebraWeak

variable {α : Type*} [LinearOrder α] [KnuthSkillingAlgebraWeak α]

/-!
### The Mass Counting Argument

The conceptual idea is that both (x⊕y)^m and (y⊕x)^m contain exactly m copies of x
and m copies of y, so they should have the same "growth rate" θ. This intuition guides
our formal proof, but we bypass defining θ explicitly: instead, we directly prove that
(x⊕y)^n > (y⊕x)^m when n > m, using associativity to reorganize atoms.
-/

/-- Helper: iterate_op is strictly monotone in base for positive iterations -/
theorem iterate_op_strictMono_base (m : ℕ) (hm : 0 < m) (x y : α) (hxy : x < y) :
    iterate_op x m < iterate_op y m := by
  cases m with
  | zero => omega
  | succ n =>
    induction n with
    | zero =>
      simp only [Nat.zero_add, iterate_op_one]
      exact hxy
    | succ n ih =>
      have hm_pos : 0 < n + 1 := Nat.succ_pos n
      calc iterate_op x (n + 1 + 1)
          = op x (iterate_op x (n + 1)) := rfl
        _ < op x (iterate_op y (n + 1)) := op_strictMono_right x (ih hm_pos)
        _ < op y (iterate_op y (n + 1)) := op_strictMono_left (iterate_op y (n + 1)) hxy
        _ = iterate_op y (n + 1 + 1) := rfl

/-- (x⊕y)^m lies between bounds determined by x^m and y^m.
    This captures that the "mass" of (x⊕y)^m is determined by x and y. -/
theorem iterate_op_xy_bounds (x y : α) (hx : ident < x) (hy : ident < y) (m : ℕ) (hm : 0 < m) :
    iterate_op x m < iterate_op (op x y) m ∧ iterate_op y m < iterate_op (op x y) m := by
  have hxy : x < op x y := by
    calc x = op x ident := (op_ident_right x).symm
      _ < op x y := op_strictMono_right x hy
  have hyx : y < op x y := by
    calc y = op ident y := (op_ident_left y).symm
      _ < op x y := op_strictMono_left y hx
  constructor
  · exact iterate_op_strictMono_base m hm x (op x y) hxy
  · exact iterate_op_strictMono_base m hm y (op x y) hyx

/-!
### The Core "More Atoms = Larger" Lemma

This is the key structural result: (x⊕y)^n > (y⊕x)^m when n > m.

The proof uses associativity to show that (x⊕y)^n contains "more positive stuff"
than (y⊕x)^m, regardless of how the elements are arranged.
-/

/-- Base case: (x⊕y)^2 > (y⊕x)^1

Proof:
  iterate_op (op x y) 2 = (x⊕y) ⊕ (x⊕y) [by iterate_op def]
  Using associativity and monotonicity, show this exceeds y⊕x.
-/
theorem xy_sq_gt_yx (x y : α) (hx : ident < x) (hy : ident < y) :
    iterate_op (op x y) 2 > iterate_op (op y x) 1 := by
  -- iterate_op (op x y) 2 = (x⊕y) ⊕ iterate_op (op x y) 1 = (x⊕y) ⊕ (x⊕y)
  have h_expand : iterate_op (op x y) 2 = op (op x y) (iterate_op (op x y) 1) := rfl
  rw [iterate_op_one] at h_expand
  -- So iterate_op (op x y) 2 = (x⊕y) ⊕ (x⊕y)
  -- By assoc: (x⊕y) ⊕ (x⊕y) = x ⊕ (y ⊕ (x ⊕ y))
  have h2 : op (op x y) (op x y) = op x (op y (op x y)) := by rw [op_assoc x y (op x y)]
  -- y ⊕ (x ⊕ y) = (y ⊕ x) ⊕ y by associativity
  have h3 : op y (op x y) = op (op y x) y := by rw [op_assoc y x y]
  -- (y ⊕ x) ⊕ y > y ⊕ x by right monotonicity (since y > ident)
  have h4 : op (op y x) y > op y x := by
    calc op (op y x) y > op (op y x) ident := op_strictMono_right (op y x) hy
      _ = op y x := op_ident_right (op y x)
  -- x ⊕ ((y ⊕ x) ⊕ y) > x ⊕ (y ⊕ x) by right mono
  have h5 : op x (op (op y x) y) > op x (op y x) := op_strictMono_right x h4
  -- x ⊕ (y ⊕ x) > y ⊕ x by left mono (since x > ident)
  have h6 : op x (op y x) > op y x := by
    calc op x (op y x) > op ident (op y x) := op_strictMono_left (op y x) hx
      _ = op y x := op_ident_left (op y x)
  -- Chain
  rw [h_expand]
  calc op (op x y) (op x y)
      = op x (op y (op x y)) := h2
    _ = op x (op (op y x) y) := by rw [h3]
    _ > op x (op y x) := h5
    _ > op y x := h6
    _ = iterate_op (op y x) 1 := (iterate_op_one (op y x)).symm

/-- Key intermediate lemma: y ⊕ (x⊕y)^k > (y⊕x)^k for all k ≥ 1

This is proved by induction using associativity:
- Base k=1: y ⊕ (x⊕y) = (y⊕x) ⊕ y > y⊕x
- Inductive step uses restructuring via associativity
-/
theorem y_op_xy_pow_gt_yx_pow (x y : α) (_hx : ident < x) (hy : ident < y)
    (k : ℕ) (hk : k ≥ 1) :
    op y (iterate_op (op x y) k) > iterate_op (op y x) k := by
  induction k with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      -- Base case k = 1: y ⊕ (x⊕y)^1 = y ⊕ (x⊕y) > y⊕x
      simp only [iterate_op_one]
      -- y ⊕ (x⊕y) = (y⊕x) ⊕ y by associativity
      have h1 : op y (op x y) = op (op y x) y := by rw [op_assoc y x y]
      rw [h1]
      -- (y⊕x) ⊕ y > (y⊕x) ⊕ ident = y⊕x
      calc op (op y x) y > op (op y x) ident := op_strictMono_right (op y x) hy
        _ = op y x := op_ident_right (op y x)
    | succ m =>
      -- Induction step: k = m + 2
      -- IH: op y (iterate_op (op x y) (m + 1)) > iterate_op (op y x) (m + 1)
      have ih_applied : op y (iterate_op (op x y) (m + 1)) > iterate_op (op y x) (m + 1) :=
        ih (Nat.le_add_left 1 m)

      -- Key: Use associativity to restructure y ⊕ (x⊕y)^{m+2}
      -- y ⊕ ((x⊕y) ⊕ (x⊕y)^{m+1}) = (y ⊕ (x⊕y)) ⊕ (x⊕y)^{m+1}  [by assoc]
      -- = ((y⊕x) ⊕ y) ⊕ (x⊕y)^{m+1}  [by assoc on y ⊕ (x⊕y)]
      -- = (y⊕x) ⊕ (y ⊕ (x⊕y)^{m+1})  [by assoc in reverse]

      have assoc1 : op y (op (op x y) (iterate_op (op x y) (m + 1))) =
          op (op y (op x y)) (iterate_op (op x y) (m + 1)) := by
        rw [op_assoc y (op x y) (iterate_op (op x y) (m + 1))]

      have assoc2 : op y (op x y) = op (op y x) y := by rw [op_assoc y x y]

      have assoc3 : op (op (op y x) y) (iterate_op (op x y) (m + 1)) =
          op (op y x) (op y (iterate_op (op x y) (m + 1))) := by
        rw [op_assoc (op y x) y (iterate_op (op x y) (m + 1))]

      calc op y (iterate_op (op x y) (m + 2))
          = op y (op (op x y) (iterate_op (op x y) (m + 1))) := rfl
        _ = op (op y (op x y)) (iterate_op (op x y) (m + 1)) := assoc1
        _ = op (op (op y x) y) (iterate_op (op x y) (m + 1)) := by rw [assoc2]
        _ = op (op y x) (op y (iterate_op (op x y) (m + 1))) := assoc3
        _ > op (op y x) (iterate_op (op y x) (m + 1)) := op_strictMono_right (op y x) ih_applied
        _ = iterate_op (op y x) (m + 2) := rfl

/-- Generalization: (x⊕y)^{k+1} > (y⊕x)^k for all k ≥ 1

Uses y_op_xy_pow_gt_yx_pow and transitivity.
-/
theorem xy_succ_gt_yx (x y : α) (hx : ident < x) (hy : ident < y) (k : ℕ) (hk : k ≥ 1) :
    iterate_op (op x y) (k + 1) > iterate_op (op y x) k := by
  -- (x⊕y)^{k+1} = (x⊕y) ⊕ (x⊕y)^k = x ⊕ (y ⊕ (x⊕y)^k) by associativity
  have assoc : op (op x y) (iterate_op (op x y) k) =
      op x (op y (iterate_op (op x y) k)) := by
    rw [op_assoc x y (iterate_op (op x y) k)]

  -- y ⊕ (x⊕y)^k > (y⊕x)^k by the intermediate lemma
  have h1 : op y (iterate_op (op x y) k) > iterate_op (op y x) k :=
    y_op_xy_pow_gt_yx_pow x y hx hy k hk

  -- x ⊕ (y ⊕ (x⊕y)^k) > x ⊕ (y⊕x)^k by right monotonicity
  have h2 : op x (op y (iterate_op (op x y) k)) > op x (iterate_op (op y x) k) :=
    op_strictMono_right x h1

  -- x ⊕ (y⊕x)^k > (y⊕x)^k by left monotonicity
  have h3 : op x (iterate_op (op y x) k) > iterate_op (op y x) k := by
    calc op x (iterate_op (op y x) k)
        > op ident (iterate_op (op y x) k) := op_strictMono_left _ hx
      _ = iterate_op (op y x) k := op_ident_left _

  calc iterate_op (op x y) (k + 1)
      = op (op x y) (iterate_op (op x y) k) := rfl
    _ = op x (op y (iterate_op (op x y) k)) := assoc
    _ > op x (iterate_op (op y x) k) := h2
    _ > iterate_op (op y x) k := h3

/-- The main comparison lemma: for n > m ≥ 1, (x⊕y)^n > (y⊕x)^m

This is the "mass counting" result formalized: more copies of positive atoms
always yield a strictly larger result, regardless of arrangement.
-/
theorem xy_pow_gt_yx_pow (x y : α) (hx : ident < x) (hy : ident < y)
    (n m : ℕ) (hm : m ≥ 1) (hnm : n > m) :
    iterate_op (op x y) n > iterate_op (op y x) m := by
  -- The proof uses:
  -- 1. (x⊕y)^{k+1} > (y⊕x)^k for all k ≥ 1 (from xy_succ_gt_yx)
  -- 2. iterate_op is strictly increasing in exponent
  -- 3. Chain: (x⊕y)^n > (x⊕y)^{m+1} > (y⊕x)^m when n > m

  have hxy_pos : ident < op x y := by
    calc ident < x := hx
      _ = op x ident := (op_ident_right x).symm
      _ < op x y := op_strictMono_right x hy

  cases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hnm) with
  | inl h_n_gt_m_plus_1 =>
    -- n > m + 1, so n ≥ m + 2
    -- (x⊕y)^n > (x⊕y)^{m+1} > (y⊕x)^m
    have h1 : iterate_op (op x y) n > iterate_op (op x y) (m + 1) :=
      CommutativityProof.iterate_op_strictMono_exp (op x y) hxy_pos h_n_gt_m_plus_1
    have h2 : iterate_op (op x y) (m + 1) > iterate_op (op y x) m :=
      xy_succ_gt_yx x y hx hy m hm
    exact lt_trans h2 h1
  | inr h_n_eq_m_plus_1 =>
    -- n = m + 1 (note: h_n_eq_m_plus_1 : m.succ = n, i.e., m + 1 = n)
    rw [← h_n_eq_m_plus_1]
    exact xy_succ_gt_yx x y hx hy m hm

/-!
### Step 3: KSSeparation implies θ is injective
-/

variable [KSSeparationWeak α]

/-- KSSeparation implies that distinct elements have distinct growth rates (θ values).

If x ≠ y, then either x < y or y < x. WLOG x < y.
By separation, we can find n, m with x^m < a^n ≤ y^m.
This means θ(x) < n/m ≤ θ(y), so θ(x) < θ(y). -/
theorem theta_injective (a x y : α) (ha : ident < a) (hx : ident < x) (hy : ident < y)
    (hxy : x < y) :
    ∃ n m : ℕ, 0 < m ∧ iterate_op x m < iterate_op a n ∧ iterate_op a n ≤ iterate_op y m := by
  -- This is exactly what KSSeparation gives us!
  exact KSSeparationWeak.separation ha hx hy hxy

/-!
### Step 4: The Main Theorem
-/

/-- **Main Theorem**: KSSeparation implies commutativity.

Proof Structure:
1. Assume x⊕y < y⊕x (for contradiction)
2. Apply KSSeparation to get n, m with (x⊕y)^m < (x⊕y)^n ≤ (y⊕x)^m and n > m
3. By mass counting: (x⊕y)^n > (y⊕x)^m (because n > m and both have same "atoms per unit")
4. This contradicts step 2's upper bound (x⊕y)^n ≤ (y⊕x)^m

The mass counting argument (step 3) is the key: θ(x⊕y) = θ(x) + θ(y) = θ(y⊕x),
so θ((x⊕y)^n) = n*θ(x⊕y) > m*θ(y⊕x) = θ((y⊕x)^m) when n > m.
Combined with KSSeparation making θ an order isomorphism, this gives (x⊕y)^n > (y⊕x)^m.
-/
theorem ksSeparation_implies_comm (x y : α) (hx : ident < x) (hy : ident < y) :
    op x y = op y x := by
  by_contra h_neq
  rcases lt_trichotomy (op x y) (op y x) with hlt | heq | hgt
  · -- Case: x⊕y < y⊕x
    have hxy_pos : ident < op x y := by
      calc ident < x := hx
        _ = op x ident := (op_ident_right x).symm
        _ < op x y := op_strictMono_right x hy
    have hyx_pos : ident < op y x := lt_trans hxy_pos hlt

    -- Get separation witnesses: (x⊕y)^m < (x⊕y)^n ≤ (y⊕x)^m
    rcases KSSeparationWeak.separation (a := op x y) hxy_pos hxy_pos hyx_pos hlt with
      ⟨n, m, hm_pos, h_lower, h_upper⟩

    -- From h_lower: m < n (since iteration is strictly increasing)
    have hmn : m < n :=
      CommutativityProof.iterate_op_strictMono_exp (op x y) hxy_pos |>.lt_iff_lt.mp h_lower

    -- From mass counting: (x⊕y)^n > (y⊕x)^m when n > m
    -- This is because both (x⊕y) and (y⊕x) contribute the same θ = θ(x) + θ(y),
    -- so having n copies of (x⊕y) exceeds m copies of (y⊕x) when n > m.
    have h_mass_counting : iterate_op (op x y) n > iterate_op (op y x) m :=
      xy_pow_gt_yx_pow x y hx hy n m hm_pos hmn

    -- But separation says (x⊕y)^n ≤ (y⊕x)^m
    -- This contradicts h_mass_counting!
    exact absurd h_upper (not_le_of_gt h_mass_counting)

  · exact h_neq heq

  · -- Case: x⊕y > y⊕x (symmetric to the first case)
    have hxy_pos : ident < op x y := by
      calc ident < x := hx
        _ = op x ident := (op_ident_right x).symm
        _ < op x y := op_strictMono_right x hy
    have hyx_pos : ident < op y x := by
      calc ident < y := hy
        _ = op y ident := (op_ident_right y).symm
        _ < op y x := op_strictMono_right y hx

    -- Apply separation to (y⊕x, x⊕y) with base y⊕x
    rcases KSSeparationWeak.separation (a := op y x) hyx_pos hyx_pos hxy_pos hgt with
      ⟨n, m, hm_pos, h_lower, h_upper⟩

    have hmn : m < n :=
      CommutativityProof.iterate_op_strictMono_exp (op y x) hyx_pos |>.lt_iff_lt.mp h_lower

    -- By mass counting with roles swapped: (y⊕x)^n > (x⊕y)^m
    have h_mass_counting : iterate_op (op y x) n > iterate_op (op x y) m :=
      xy_pow_gt_yx_pow y x hy hx n m hm_pos hmn

    exact absurd h_upper (not_le_of_gt h_mass_counting)

end ThetaAdditivity

/-! A convenience corollary: the v5 commutativity theorem is global (handles identity cases). -/
theorem ksSeparation_implies_commutative
    {α : Type*} [LinearOrder α] [GoertzelV5.KnuthSkillingAlgebraWeak α] [GoertzelV5.KSSeparationWeak α] :
    ∀ x y : α, GoertzelV5.KnuthSkillingAlgebraWeak.op x y = GoertzelV5.KnuthSkillingAlgebraWeak.op y x := by
  intro x y
  by_cases hx : x = GoertzelV5.KnuthSkillingAlgebraWeak.ident (α := α)
  · subst hx
    simp [GoertzelV5.KnuthSkillingAlgebraWeak.op_ident_left, GoertzelV5.KnuthSkillingAlgebraWeak.op_ident_right]
  by_cases hy : y = GoertzelV5.KnuthSkillingAlgebraWeak.ident (α := α)
  · subst hy
    simp [GoertzelV5.KnuthSkillingAlgebraWeak.op_ident_left, GoertzelV5.KnuthSkillingAlgebraWeak.op_ident_right]
  have hx_pos :
      GoertzelV5.KnuthSkillingAlgebraWeak.ident (α := α) < x :=
    lt_of_le_of_ne (GoertzelV5.KnuthSkillingAlgebraWeak.ident_le x) (Ne.symm hx)
  have hy_pos :
      GoertzelV5.KnuthSkillingAlgebraWeak.ident (α := α) < y :=
    lt_of_le_of_ne (GoertzelV5.KnuthSkillingAlgebraWeak.ident_le y) (Ne.symm hy)
  simpa using GoertzelV5.ThetaAdditivity.ksSeparation_implies_comm (α := α) (x := x) (y := y) hx_pos hy_pos

/-!
## The Semidirect Product Analysis: Why This Proof Works

**Key observation from the semidirect counterexample**:

```
Semidirect: (u,x) ⊕ (v,y) = (u+v, x + 2^u·y)

x = (1,1), y = (1,2)
x⊕y = (2,5), y⊕x = (2,4)  -- Different! (non-commutative)

But: θ(x⊕y) = 2 = θ(y⊕x)  -- Same θ! (first coordinate)

Why KSSeparation fails: Can't separate (2,4) from (2,5) because they have the same θ.
To separate, we'd need a^n with θ = 2, but then (2,4)^m = (2m, ...) and (2,5)^m = (2m, ...)
both have θ = 2m, leaving no room for a^n between them.
```

**The proof structure**:

1. **θ(x⊕y) = θ(y⊕x) always** (mass counting: same multiset of atoms)
   - This is TRUE even in non-commutative structures like the semidirect product
   - The "mass" (total θ contribution) is the same regardless of arrangement

2. **KSSeparation ⟹ θ injective** (can separate ⟹ different θ values)
   - This FAILS in the semidirect product
   - Separation requires "room" between θ values

3. **θ(x⊕y) = θ(y⊕x) + θ injective ⟹ x⊕y = y⊕x**
   - The combination gives commutativity

**Why the semidirect product fails KSSeparation**:
- θ is NOT injective: (1,1) and (1,2) have same θ = 1
- Elements with same θ can't be separated
- Non-commutativity "hides" in the non-injective part of the structure

**Why KSSeparation implies commutativity**:
- KSSeparation forces θ to be injective
- With θ injective, θ(x⊕y) = θ(y⊕x) implies x⊕y = y⊕x
-/

/-!
## Summary: What v5 Claims and What We've Proven

**v5 Claims** (both PROVEN):
- KSSeparation → Archimedean ✓ (`op_archimedean_of_separation`)
- KSSeparation → Commutative ✓ (`ksSeparation_implies_comm`)

**Proof Strategy for Commutativity**:

The key insight is "mass counting": both (x⊕y)^n and (y⊕x)^n contain the same
multiset of atoms (n copies of x and n copies of y). This means:
1. When n > m: (x⊕y)^n > (y⊕x)^m (more atoms = strictly larger)
2. KSSeparation requires: if x⊕y < y⊕x, then ∃n,m: (x⊕y)^m < (x⊕y)^n ≤ (y⊕x)^m
3. These constraints are contradictory: n > m implies (x⊕y)^n > (y⊕x)^m

**Key Lemmas**:
- `y_op_xy_pow_gt_yx_pow`: y ⊕ (x⊕y)^k > (y⊕x)^k for k ≥ 1
- `xy_succ_gt_yx`: (x⊕y)^{k+1} > (y⊕x)^k for k ≥ 1
- `xy_pow_gt_yx_pow`: (x⊕y)^n > (y⊕x)^m for n > m ≥ 1

**Supporting Evidence**:
- Contrapositive verified: ¬Commutative → ¬KSSeparation (SemidirectNoSeparation.lean)
- Contrapositive verified: ¬Archimedean → ¬KSSeparation (ProductFailsSeparation.lean)
-/

end GoertzelV5

end Mettapedia.ProbabilityTheory.KnuthSkilling
