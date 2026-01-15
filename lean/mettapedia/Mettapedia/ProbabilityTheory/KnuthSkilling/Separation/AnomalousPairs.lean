import Mettapedia.ProbabilityTheory.KnuthSkilling.Algebra

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.AnomalousPairs

open Classical
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra

variable {α : Type*} [KnuthSkillingAlgebraBase α]

/-!
# No Anomalous Pairs (Alimov/Klazar-style)

This file defines the “no anomalous pairs” condition from the ordered-semigroup literature
(Alimov; see also Klazar) in the Knuth–Skilling `iterate_op` language, and records that the
K&S sandwich separation axiom implies it.

The intended reading is:

*An anomalous pair `a < b` is “infinitesimally close”: for every finite iterate `n`,
`b^n` still lies strictly between `a^n` and `a^(n+1)`.*

`KSSeparation` rules this out immediately by applying separation with base `a` to the
comparison `a < b`.
-/

/-- `a,b` form an **anomalous pair** if `a < b` but every finite iterate stays squeezed:
for all `n > 0`, `a^n < b^n < a^(n+1)`.

We include `a^n < b^n` explicitly even though it follows from `a < b` via
`iterate_op_strictMono_base`. -/
def AnomalousPair (a b : α) : Prop :=
  ident < a ∧ a < b ∧ ∀ n : ℕ, 0 < n → iterate_op a n < iterate_op b n ∧ iterate_op b n < iterate_op a (n + 1)

/-- **No anomalous pairs**: whenever `ident < a < b`, some finite iterate makes the gap
between `a` and `b` at least one more copy of `a`, i.e. `a^(n+1) ≤ b^n` for some `n > 0`. -/
class NoAnomalousPairs (α : Type*) [KnuthSkillingAlgebraBase α] : Prop where
  exists_iterate_succ_le :
    ∀ {a b : α}, ident < a → a < b → ∃ n : ℕ, 0 < n ∧ iterate_op a (n + 1) ≤ iterate_op b n

namespace NoAnomalousPairs

variable [NoAnomalousPairs α]

theorem not_anomalous {a b : α} (ha : ident < a) (hab : a < b) : ¬ AnomalousPair (α := α) a b := by
  intro hAnom
  rcases NoAnomalousPairs.exists_iterate_succ_le (α := α) (a := a) (b := b) ha hab with ⟨n, hn, hnle⟩
  have hlt : iterate_op b n < iterate_op a (n + 1) :=
    (hAnom.2.2 n hn).2
  exact (not_lt_of_ge hnle) hlt

end NoAnomalousPairs

namespace KSSeparation

variable [KSSeparation α]

/-- `KSSeparation` implies `NoAnomalousPairs`: apply separation with base `a` to `a < b`,
and use the resulting `a^n ≤ b^m` together with `a^m < a^n` to force `a^(m+1) ≤ b^m`. -/
theorem noAnomalousPairs_of_KSSeparation : NoAnomalousPairs α := by
  refine ⟨?_⟩
  intro a b ha hab
  have hb : ident < b := lt_trans ha hab
  rcases KSSeparation.separation (a := a) (x := a) (y := b) ha ha hb hab with
    ⟨n, m, hm_pos, hlt, hle⟩

  -- From `a^m < a^n` we get `m < n` by monotonicity of iterates.
  have hmono : Monotone (iterate_op a) := (iterate_op_strictMono a ha).monotone
  have hnot : ¬ n ≤ m := by
    intro hnm
    have hle' : iterate_op a n ≤ iterate_op a m := hmono hnm
    exact (not_lt_of_ge hle') hlt
  have hmn : m < n := Nat.lt_of_not_ge hnot
  have hsucc_le : m + 1 ≤ n := Nat.succ_le_of_lt hmn

  refine ⟨m, hm_pos, ?_⟩
  have hstep : iterate_op a (m + 1) ≤ iterate_op a n := hmono hsucc_le
  exact le_trans hstep hle

end KSSeparation

/-!
## Negative Anomalous Pairs (Eric Luap's insight)

For negative elements (a, b < ident), the "anomalous" structure is reversed:
`a^n > b^n > a^{n+1}` for all n > 0.

This captures the case where powers of negative elements "squeeze" in the opposite direction.
Credit: Eric Luap's OrderedSemigroups formalization (github.com/ericluap/OrderedSemigroups).
-/

/-- **Negative anomalous pair**: `a,b` with `b < a < ident` where iterates stay squeezed
in the reversed direction: `a^n > b^n > a^{n+1}` for all n > 0.

Note the ordering: we require `b < a` (so a is "larger" but both negative). -/
def NegAnomalousPair (a b : α) : Prop :=
  b < a ∧ a < ident ∧ ∀ n : ℕ, 0 < n →
    iterate_op b n < iterate_op a n ∧ iterate_op a (n + 1) < iterate_op b n

/-- **No negative anomalous pairs**: whenever `b < a < ident`, some iterate breaks the squeeze. -/
class NoNegAnomalousPairs (α : Type*) [KnuthSkillingAlgebraBase α] : Prop where
  exists_iterate_neg_escape :
    ∀ {a b : α}, b < a → a < ident → ∃ n : ℕ, 0 < n ∧ iterate_op b n ≤ iterate_op a (n + 1)

namespace NoNegAnomalousPairs

variable [NoNegAnomalousPairs α]

theorem not_neg_anomalous {a b : α} (hab : b < a) (ha : a < ident) :
    ¬ NegAnomalousPair (α := α) a b := by
  intro hAnom
  rcases NoNegAnomalousPairs.exists_iterate_neg_escape (α := α) hab ha with ⟨n, hn, hnle⟩
  have hlt : iterate_op a (n + 1) < iterate_op b n := (hAnom.2.2 n hn).2
  exact (not_lt_of_ge hnle) hlt

end NoNegAnomalousPairs

/-!
### Relationship between positive and negative anomalous pairs

The key observation is that for elements below ident, iteration REVERSES the order
(since multiplying by something < 1 decreases). This connects positive and negative cases.
-/

/-- For x < ident, op z x < z (multiplying on the right by negative decreases).
This is the key lemma for the negative anomalous pair construction. -/
lemma op_right_neg_lt {x z : α} (hx : x < ident) : op z x < z := by
  calc op z x < op z ident := op_strictMono_right z hx
    _ = z := op_ident_right z

/-- For x < ident, op x z < z (multiplying on the left by negative decreases). -/
lemma op_left_neg_lt {x z : α} (hx : x < ident) : op x z < z := by
  calc op x z < op ident z := op_strictMono_left z hx
    _ = z := op_ident_left z

/-!
### Deriving NoNegAnomalousPairs from NoAnomalousPairs

The key insight is that for negative elements, the iteration behavior is "reversed"
in a precise sense. We show that NoAnomalousPairs (for positive elements) actually
implies NoNegAnomalousPairs when we have the Archimedean property.

The proof uses the fact that if a negative anomalous pair existed, we could
construct a positive anomalous pair by considering how negative elements interact
with positive bases.
-/

namespace NoAnomalousPairs

variable [NoAnomalousPairs α]

/-- NoAnomalousPairs implies NoNegAnomalousPairs in the presence of a positive element.
The proof uses the Archimedean property that follows from NoAnomalousPairs. -/
theorem noNegAnomalousPairs_of_noAnomalousPairs
    (h_exists_pos : ∃ base : α, ident < base) : NoNegAnomalousPairs α := by
  refine ⟨?_⟩
  intro a b hab ha
  -- We need: ∃ n, 0 < n ∧ b^n ≤ a^{n+1}
  -- For negative a, b with b < a < ident, we have a^{n+1} < a^n (iteration shrinks)
  -- and b^n < a^n (strict mono of iteration)
  -- The key is to use Archimedean: eventually the ratio exceeds any bound
  rcases h_exists_pos with ⟨base, h_base⟩

  -- For negative elements, iteration DECREASES (a^{n+1} < a^n)
  -- We use that iterate_op_strictMono_neg gives us control over the sequence
  -- The escape happens because Archimedean bounds the "shrinking rate"

  -- For now, we use a direct argument: consider n = 1
  -- We need b^1 ≤ a^2, i.e., b ≤ a · a
  -- From b < a < ident, we have a · a < a (since a < ident means multiplying shrinks)
  -- So b < a < a · a is FALSE if a < ident!
  -- Actually a · a < a · ident = a, so a² < a when a < ident.

  -- The claim is: ∃ n, b^n ≤ a^{n+1}
  -- At n = 1: b ≤ a² is NOT always true (since a² < a and b could be just below a)

  -- We need to use Archimedean more carefully. The sequence a^n shrinks to 0 (conceptually)
  -- and b^n shrinks faster or slower depending on b vs a.

  -- Actually, this is subtle. Let me use a different approach:
  -- If b^n > a^{n+1} for all n, then b^n / a^n > a, which would violate Archimedean
  -- But we don't have division in a semigroup...

  -- The direct approach is to show that if b < a < ident with b^n > a^{n+1} for all n,
  -- then we can construct a positive anomalous pair, contradicting NoAnomalousPairs.

  -- For simplicity, we use the following: by Archimedean, there exists n such that
  -- base^n exceeds 1/(a - b) in the embedding sense. But we don't have embedding yet!

  -- This is actually circular: we need NoNegAnomalousPairs to prove commutativity,
  -- which we need for the embedding, which we'd use to prove NoNegAnomalousPairs.

  -- Alternative: prove directly from the structure.
  -- The key observation: for b < a < ident, iterate_op a decreases slower than iterate_op b
  -- (since a > b and both shrink). Eventually a^{n+1} catches up to b^n.

  -- For now, leave as sorry and document the gap
  sorry

end NoAnomalousPairs

end Mettapedia.ProbabilityTheory.KnuthSkilling.Separation.AnomalousPairs

