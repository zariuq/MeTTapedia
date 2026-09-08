import Mettapedia.GSLT.Parsing.ParserProfileSemantics
import Mathlib.Tactic

/-!
# Plain-BNF lexical scalar admission

This module gives the scalar fragment of plain-BNF lexical authorities a
backend-independent meaning.  The executable PeTTa and C realizations are
separate objects and require their own preservation and reflection theorems.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfLexicalScalarSemantics

open ParserProfileSemantics

/-- Unicode scalar validity on the integer carrier used by portable grammar
data.  Negative integers and surrogate code points are not scalars. -/
def isUnicodeScalarInt (scalar : Int) : Bool :=
  decide
    (0 ≤ scalar ∧ scalar ≤ 1114111 ∧
      (scalar < 55296 ∨ 57343 < scalar))

/-- The complementary ground relation used by fail-closed validation. -/
def isNonUnicodeScalarInt (scalar : Int) : Bool :=
  !isUnicodeScalarInt scalar

theorem isUnicodeScalarInt_nat (scalar : Nat) :
    isUnicodeScalarInt scalar = isUnicodeScalar scalar := by
  simp [isUnicodeScalarInt, isUnicodeScalar]

theorem unicode_scalar_partition (scalar : Int) :
    isNonUnicodeScalarInt scalar = true ↔
      isUnicodeScalarInt scalar = false := by
  simp [isNonUnicodeScalarInt]

theorem integer_order_partition (left right : Int) :
    ¬ left < right ↔ right ≤ left := by
  omega

/-- Exact recursive invariant checked for a positive point class.  The
recursive clause is deliberately adjacent-order based, matching the portable
grammar-data traversal rather than silently sorting or deduplicating it. -/
def ScalarListWellFormed : List Int → Prop
  | [] => False
  | [scalar] => isUnicodeScalarInt scalar = true
  | left :: right :: tail =>
      isUnicodeScalarInt left = true ∧
        left < right ∧
        ScalarListWellFormed (right :: tail)

/-- Executable decision procedure for `ScalarListWellFormed`. -/
def checkScalarList : List Int → Bool
  | [] => false
  | [scalar] => isUnicodeScalarInt scalar
  | left :: right :: tail =>
      isUnicodeScalarInt left &&
        decide (left < right) &&
        checkScalarList (right :: tail)

theorem checkScalarList_eq_true_iff (scalars : List Int) :
    checkScalarList scalars = true ↔ ScalarListWellFormed scalars := by
  induction scalars with
  | nil => simp [checkScalarList, ScalarListWellFormed]
  | cons left tail ih =>
      cases tail with
      | nil => simp [checkScalarList, ScalarListWellFormed]
      | cons right rest =>
          simp [checkScalarList, ScalarListWellFormed, ih, and_assoc]

theorem accepts_unicode_boundaries :
    checkScalarList [0, 55295, 57344, 1114111] = true := by
  decide

theorem rejects_negative_scalar :
    checkScalarList [-1] = false := by
  decide

theorem rejects_surrogate_scalar :
    checkScalarList [55296] = false := by
  decide

theorem rejects_out_of_range_scalar :
    checkScalarList [1114112] = false := by
  decide

theorem rejects_duplicate_scalars :
    checkScalarList [55, 55] = false := by
  decide

theorem rejects_descending_scalars :
    checkScalarList [56, 55] = false := by
  decide

end Mettapedia.GSLT.Parsing.PlainBnfLexicalScalarSemantics
