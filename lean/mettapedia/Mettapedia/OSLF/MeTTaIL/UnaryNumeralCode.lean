import Mettapedia.OSLF.MeTTaIL.PatternCodeRecursion
import Mettapedia.OSLF.MeTTaIL.UnaryNumerals

/-!
# Unary numerals on codes

The code of the unary numeral of a number is a primitive recursive function
of the number, and it is at least the number.  So the number that a code
writes can be recovered by a search bounded by the code, and recovering it
is primitive recursive.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.PatternCode

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The code of the unary numeral of a number. -/
def unaryCode (zero succ : String) (count : ℕ) : ℕ :=
  patternCode (Pattern.unary zero succ count)

theorem unaryCode_succ (zero succ : String) (count : ℕ) :
    unaryCode zero succ (count + 1) =
      Nat.pair 2 (Nat.pair (stringCode succ)
        (Nat.succ (Nat.pair (unaryCode zero succ count) 0))) :=
  rfl

/-- The code of a numeral is a primitive recursive function of the number. -/
theorem unaryCode_primrec (zero succ : String) : Primrec (unaryCode zero succ) := by
  have step : Primrec₂ fun (_ : ℕ) (earlier : ℕ) =>
      Nat.pair 2 (Nat.pair (stringCode succ) (Nat.succ (Nat.pair earlier 0))) :=
    Primrec₂.natPair.comp (Primrec.const 2)
      (Primrec₂.natPair.comp (Primrec.const (stringCode succ))
        (Primrec.succ.comp (Primrec₂.natPair.comp Primrec.snd (Primrec.const 0))))
  refine (Primrec.nat_rec₁ (unaryCode zero succ 0) step).of_eq fun count => ?_
  induction count with
  | zero => rfl
  | succ count recurse =>
      exact congrArg
        (fun earlier => Nat.pair 2 (Nat.pair (stringCode succ) (Nat.succ (Nat.pair earlier 0))))
        recurse

/-- Distinct labels make the code of a numeral determine the number. -/
theorem unaryCode_injective {zero succ : String} (distinct : zero ≠ succ) :
    Function.Injective (unaryCode zero succ) :=
  fun _ _ same => Pattern.unary_injective distinct (patternCode_injective same)

/-- The code of a numeral is at least the number. -/
theorem le_unaryCode (zero succ : String) (count : ℕ) : count ≤ unaryCode zero succ count := by
  induction count with
  | zero => exact Nat.zero_le _
  | succ count recurse =>
      rw [unaryCode_succ]
      have inner : unaryCode zero succ count <
          Nat.succ (Nat.pair (unaryCode zero succ count) 0) :=
        Nat.lt_succ_of_le (Nat.left_le_pair _ _)
      exact Nat.succ_le_of_lt (recurse.trans_lt (inner.trans_le
        ((Nat.right_le_pair _ _).trans (lt_pair_of_pos (by decide) _).le)))

/-- The number whose unary numeral has the given code, and zero when the
code is that of no numeral. -/
def unaryCount (zero succ : String) (code : ℕ) : ℕ :=
  Nat.findGreatest (fun count => unaryCode zero succ count = code) code

/-- The count of the code of a numeral is the number. -/
theorem unaryCount_unaryCode {zero succ : String} (distinct : zero ≠ succ) (count : ℕ) :
    unaryCount zero succ (unaryCode zero succ count) = count := by
  rw [unaryCount, Nat.findGreatest_eq_iff]
  exact ⟨le_unaryCode zero succ count, fun _ => rfl,
    fun other larger _ same => absurd (unaryCode_injective distinct same) larger.ne'⟩

/-- Recovering the number from the code of its numeral is primitive
recursive. -/
theorem unaryCount_primrec (zero succ : String) : Primrec (unaryCount zero succ) :=
  Primrec.nat_findGreatest Primrec.id
    (Primrec.eq.comp ((unaryCode_primrec zero succ).comp Primrec.snd) Primrec.fst)

end Mettapedia.OSLF.MeTTaIL.PatternCode
