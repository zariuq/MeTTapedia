import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Shortlex Order on Free Monoid (List Bool)

**Key Insight (GPT-5 Pro)**: Use numeric encoding to get LinearOrder for free!

Shortlex order = (length, bits) where `bits` interprets List Bool as a natural number.
This lets us use `LinearOrder.lift'` and avoid all the Lean bureaucracy.

## Main Results

- `bits : List Bool → ℕ` — Binary encoding (little-endian)
- `bits_append` — Formula for concatenation
- `LinearOrder FreeMonoid2` — Via lift, avoiding manual instance hell
- Strict monotonicity for concatenation — Both left and right (with sorries for lift' transparency)
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.FreeMonoid2Order

/-- The free monoid on two generators (List Bool). -/
abbrev FreeMonoid2 := List Bool

/-- Binary encoding of a word (little-endian: head is LSB).

    Example: [false, true, false] = 0*1 + 1*2 + 0*4 = 2
    Example: [true, true] = 1*1 + 1*2 = 3
-/
def bits : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bits bs

/-- Bits is monotone in the sense needed: same length lists with smaller bits are smaller. -/
theorem bits_strictMono_samelength {x y : List Bool} (hlen : x.length = y.length) :
    x < y → bits x < bits y := by
  intro hxy
  -- TODO: This needs enc to be defined first, then work with Prod.lex_def
  sorry

/-- Key lemma: bits of concatenation.

    This is the "shift left then add" formula that makes everything work! -/
theorem bits_append (x y : List Bool) :
    bits (x ++ y) = bits x + bits y * 2^(x.length) := by
  induction x with
  | nil => simp [bits]
  | cons b xs ih =>
    simp only [List.cons_append, bits, List.length_cons]
    rw [ih]
    ring

/-- Shortlex encoding: map word to (length, bits) with lex order. -/
def enc (w : List Bool) : Lex (ℕ × ℕ) := toLex (w.length, bits w)

/-- The encoding is injective. -/
theorem enc_injective : Function.Injective enc := by
  intro x y h
  simp [enc, toLex] at h
  obtain ⟨hlen, hbits⟩ := h
  induction x generalizing y with
  | nil =>
    cases y <;> simp_all
  | cons b xs ih =>
    cases y with
    | nil => simp_all
    | cons b' ys =>
      simp [bits] at hbits
      simp at hlen
      have hlen' : xs.length = ys.length := hlen
      -- Parity argument for heads
      have hb : b = b' := by
        have := congrArg (· % 2) hbits
        simp [Nat.add_mul_mod_self_left] at this
        cases b <;> cases b' <;> simp_all
      -- Division argument for tails
      have htail : bits xs = bits ys := by
        subst hb
        have : 2 * bits xs = 2 * bits ys := by
          cases b <;> simp_all [bits] <;> linarith
        linarith
      -- Recursion
      subst hb
      have : xs = ys := ih (by simp [hlen']) (by simp [htail])
      simp [this]

/-- **THE MONEY SHOT**: LinearOrder for FreeMonoid2 via lift!

    This gives us min_def, max_def, compare_eq_compareOfLessAndEq, etc. FOR FREE!
    No manual proofs of bureaucratic fields. -/
noncomputable instance : LinearOrder FreeMonoid2 :=
  LinearOrder.lift' enc enc_injective

/-- Concatenation on the right preserves shortlex strict order.

TODO: LinearOrder.lift' transparency issue. The lifted order x < y is NOT definitionally
equal to enc x < enc y, despite what the mathlib docs suggest. This blocks the proof.

The proof SHOULD be: extract enc x < enc y from hxy, derive enc (x++z) < enc (y++z)
using bits_append and Prod.lex_def, then convert back. But `convert` can't unify the types.

Attempted approaches:
- `show enc (x++z) < enc (y++z)` - not definitionally equal
- `convert hxy using 1` - fails to unify
- Direct simp/rw with Prod.lex_def - made no progress

Need to find the right mathlib lemma about LinearOrder.lift' or use a different instance. -/
theorem append_right_strictMono {x y : FreeMonoid2} (z : FreeMonoid2) :
    x < y → x ++ z < y ++ z := by
  sorry

/-- Concatenation on the left preserves shortlex strict order.

TODO: Same LinearOrder.lift' transparency issue as append_right_strictMono. -/
theorem append_left_strictMono {x y : FreeMonoid2} (z : FreeMonoid2) :
    x < y → z ++ x < z ++ y := by
  sorry

end Mettapedia.ProbabilityTheory.KnuthSkilling.FreeMonoid2Order
