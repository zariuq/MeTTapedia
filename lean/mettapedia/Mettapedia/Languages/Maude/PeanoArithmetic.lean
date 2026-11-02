import Mettapedia.Languages.Maude.PeanoTermination

/-! The authored Peano equations compute natural-number addition and
multiplication. The readout identifies arbitrary numerals, independently of
the compiler and the native comparison programs. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Maude.PeanoNormalization

open PeanoEquationRules

theorem numeral_typed (context : VariableContext) (number : Nat) :
    HasSort Examples.peano.signature context (Examples.numeral "peano" number) "Nat" := by
  induction number with
  | zero => exact zero_typed context
  | succ number ih => exact successor_typed ih

theorem reduce_numeral (number : Nat) :
    reduce (Examples.numeral "peano" number) = Examples.numeral "peano" number := by
  induction number with
  | zero => exact reduce_zero
  | succ number ih =>
      simp only [Examples.numeral, String.reduceAppend, reduce_succ, ih]

theorem add_numerals (left right : Nat) :
    add (Examples.numeral "peano" left) (Examples.numeral "peano" right) =
      Examples.numeral "peano" (left + right) := by
  induction left with
  | zero =>
      simpa only [Examples.numeral, Examples.constant, String.reduceAppend, Nat.zero_add] using
        add_zero (Examples.numeral "peano" right)
  | succ left ih =>
      simp only [Examples.numeral, String.reduceAppend, add_succ, ih, Nat.succ_add]

theorem multiply_numerals (left right : Nat) :
    multiply (Examples.numeral "peano" left) (Examples.numeral "peano" right) =
      Examples.numeral "peano" (left * right) := by
  induction left with
  | zero =>
      simpa only [Examples.numeral, Examples.constant, String.reduceAppend, Nat.zero_mul] using
        multiply_zero (Examples.numeral "peano" right)
  | succ left ih =>
      change multiply (.app "peano.succ" [Examples.numeral "peano" left]) (Examples.numeral "peano" right) = _
      rw [multiply_succ, ih, add_numerals]
      rw [Nat.succ_mul, Nat.add_comm]

theorem reduce_add_numerals (left right : Nat) :
    reduce (.app "peano.add" [Examples.numeral "peano" left, Examples.numeral "peano" right]) =
      Examples.numeral "peano" (left + right) := by
  rw [reduce_add, reduce_numeral, reduce_numeral, add_numerals]

theorem reduce_multiply_numerals (left right : Nat) :
    reduce (.app "peano.mul" [Examples.numeral "peano" left, Examples.numeral "peano" right]) =
      Examples.numeral "peano" (left * right) := by
  rw [reduce_multiply, reduce_numeral, reduce_numeral, multiply_numerals]

theorem equivalent_numerals_iff (context : VariableContext) (left right : Nat) :
    Equivalent Examples.peano context "Nat" (Examples.numeral "peano" left) (Examples.numeral "peano" right) ↔
      left = right := by
  rw [equivalent_iff_reduce_eq (numeral_typed context left) (numeral_typed context right),
    reduce_numeral, reduce_numeral]
  constructor
  · intro same
    have readout := congrArg numeralValue? same
    simpa only [numeralValue?_numeral, Option.some.injEq] using readout
  · intro same
    rw [same]

end Mettapedia.Languages.Maude.PeanoNormalization
