import Mettapedia.Languages.Datalog.Comparisons
import Mathlib.Data.List.Lex

/-! Symbol order compares the decoded UTF-8 bytes lexicographically. It is
independent of symbol-table insertion order and of execution scheduling. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Datalog.SymbolOrder

def bytes (text : String) : List Nat := text.toUTF8.toList.map UInt8.toNat

def Less (left right : String) : Prop := List.Lex (· < ·) (bytes left) (bytes right)

def less (left right : String) : Bool :=
  List.lex (bytes left) (bytes right) (fun a b => decide (a < b))

theorem less_exact (left right : String) : less left right = true ↔ Less left right := by
  simp [less, Less, List.lex_eq_true_iff_lex]

theorem less_irrefl (text : String) : less text text = false := by
  simp [Bool.eq_false_iff, less_exact, Less]

theorem empty_before_nonempty {text : String} (nonempty : bytes text ≠ []) : Less "" text := by
  cases found : bytes text with
  | nil => exact False.elim (nonempty found)
  | cons head tail =>
      have empty : bytes "" = [] := by decide +kernel
      unfold Less
      rw [empty, found]
      exact .nil

theorem ascii_order : less "Z" "a" = true ∧ less "a" "Z" = false := by decide +kernel
theorem prefix_order : less "a" "aa" = true ∧ less "aa" "a" = false := by decide +kernel
theorem unicode_order : less "z" "é" = true ∧ less "é" "λ" = true ∧ less "λ" "🙂" = true := by
  decide +kernel
theorem numeric_text_is_lexical : less "10" "2" = true ∧ less "2" "10" = false := by decide +kernel

end Mettapedia.Languages.Datalog.SymbolOrder
