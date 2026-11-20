import Mathlib.Tactic

/-!
# Two readings of a source constructor named `cons` in PeTTa

A language definition may name one of its constructors `cons`. PeTTa has a list constructor of
that name: an evaluated `(cons h t)` is the cell of `h` and `t`, and a list `(f a b)` is the cell
of `f` and `(a b)`. A lowering of the language to PeTTa must say what a source term headed by
`cons` is as a PeTTa value.

* `dataTerm`: the **data reading**. Every application is the list of its constructor's name and
  its arguments, `cons` like any other.
* `cellTerm`: the **cell reading**. `cons` of two terms is PeTTa's cell of their readings.
* `dataTerm_injective`: the data reading is faithful: different terms are different values.
* `cellTerm_not_injective`: the cell reading is not. `cons(a, b(c))` and `a(b, c)` are read as
  one value, so a rule for the pattern `cons(h, t)` meets a term built by another constructor.
  Both PeTTa hosts confirm it: `(== (cons a (b c)) (a b c))` is true there.
* `dataTerm_apart`: the data reading tells those two terms apart.

So a lowering that keeps the source constructors free reads `cons` as data: a pattern for it is a
list of three whose first item is the name.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.SourceConstructorReadings

mutual
/-- A term of a source language: a constructor applied to terms. -/
inductive Term where
  | app (head : String) (args : Terms)
/-- The arguments of a constructor. -/
inductive Terms where
  | none
  | more (first : Term) (rest : Terms)
end

/-- A value of PeTTa: a symbol, the empty list, or a cell of a first item and the rest. -/
inductive Value where
  | symbol (name : String)
  | empty
  | cell (first rest : Value)
  deriving DecidableEq

mutual
/-- The data reading: a constructor without arguments is its name, an application the list of
its name and its arguments. -/
def dataTerm : Term → Value
  | .app head .none => .symbol head
  | .app head (.more first rest) => .cell (.symbol head) (.cell (dataTerm first) (dataTerms rest))
/-- The data reading of arguments: the list of their readings. -/
def dataTerms : Terms → Value
  | .none => .empty
  | .more first rest => .cell (dataTerm first) (dataTerms rest)
end

mutual
/-- The cell reading: as the data reading, except that `cons` of two terms is the cell of their
readings. -/
def cellTerm : Term → Value
  | .app head .none => .symbol head
  | .app head (.more first (.more second .none)) =>
      if head = "cons" then .cell (cellTerm first) (cellTerm second)
      else .cell (.symbol head) (.cell (cellTerm first) (.cell (cellTerm second) .empty))
  | .app head (.more first rest) => .cell (.symbol head) (.cell (cellTerm first) (cellTerms rest))
/-- The cell reading of arguments. -/
def cellTerms : Terms → Value
  | .none => .empty
  | .more first rest => .cell (cellTerm first) (cellTerms rest)
end

mutual
theorem dataTerm_injective : ∀ {s t : Term}, dataTerm s = dataTerm t → s = t
  | .app h .none, .app h' .none, same => by
      simp only [dataTerm, Value.symbol.injEq] at same
      rw [same]
  | .app h .none, .app h' (.more _ _), same => by simp [dataTerm] at same
  | .app h (.more _ _), .app h' .none, same => by simp [dataTerm] at same
  | .app h (.more a r), .app h' (.more a' r'), same => by
      simp only [dataTerm, Value.cell.injEq, Value.symbol.injEq] at same
      obtain ⟨heads, firsts, rests⟩ := same
      rw [heads, dataTerm_injective firsts, dataTerms_injective rests]
theorem dataTerms_injective : ∀ {s t : Terms}, dataTerms s = dataTerms t → s = t
  | .none, .none, _ => rfl
  | .none, .more _ _, same => by simp [dataTerms] at same
  | .more _ _, .none, same => by simp [dataTerms] at same
  | .more a r, .more a' r', same => by
      simp only [dataTerms, Value.cell.injEq] at same
      rw [dataTerm_injective same.1, dataTerms_injective same.2]
end

/-- A constant of the source language. -/
def const (name : String) : Term := .app name .none

/-- `cons(a, b(c))`. -/
def consOfTwo : Term := .app "cons" (.more (const "a") (.more (.app "b" (.more (const "c") .none)) .none))

/-- `a(b, c)`. -/
def applied : Term := .app "a" (.more (const "b") (.more (const "c") .none))

theorem two_terms : consOfTwo ≠ applied := by
  simp [consOfTwo, applied]

/-- **The cell reading is not faithful**: two different terms are read as one value. -/
theorem cellTerm_not_injective : cellTerm consOfTwo = cellTerm applied := by
  simp [consOfTwo, applied, const, cellTerm, cellTerms]

/-- The data reading tells them apart. -/
theorem dataTerm_apart : dataTerm consOfTwo ≠ dataTerm applied :=
  fun same => two_terms (dataTerm_injective same)

#print axioms dataTerm_injective
#print axioms cellTerm_not_injective

end Mettapedia.Languages.MeTTa.PeTTa.SourceConstructorReadings
