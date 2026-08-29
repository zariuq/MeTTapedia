import Mettapedia.Logic.LawsOfForm.Form

/-!
# Laws of Form: re-entry, finitely unfolded

The re-entrant form `f = ⟨f⟩` (Spencer-Brown, chapter 11; Kauffman,
*Eigenforms and quantum physics*; Kauffman, *Imaginary values*) is not a finite
form: no finite form equals a cross enclosing itself.  Its finite unfoldings
alternate in value, so the re-entrant form has no fixed Boolean value — the
"imaginary" value.  This module records both facts with a fuel-indexed
unfolding; a coalgebraic presentation is left to a separate development.
-/

namespace Mettapedia.Logic.LawsOfForm

/-- The `n`-th finite unfolding of `f = ⟨f⟩`, starting from the void. -/
def reentryUnfold : Nat → Form
  | 0 => []
  | n + 1 => [.cross (reentryUnfold n)]

theorem reentryUnfold_one : reentryUnfold 1 = mark := rfl
theorem reentryUnfold_two : reentryUnfold 2 = [.cross [.cross []]] := rfl

/-- Each unfolding negates the value of the previous one. -/
theorem reentry_alternates (n : Nat) :
    Form.markedList (reentryUnfold (n + 1)) = !Form.markedList (reentryUnfold n) := by
  simp [reentryUnfold]

/-- Hence the unfoldings never stabilize: there is no fixed value. -/
theorem reentry_no_fixed_value (n : Nat) :
    Form.markedList (reentryUnfold (n + 1)) ≠ Form.markedList (reentryUnfold n) := by
  rw [reentry_alternates]
  cases Form.markedList (reentryUnfold n) <;> decide

/-- Positive: the first two unfoldings are marked and unmarked. -/
theorem reentry_values :
    Form.markedList (reentryUnfold 1) = true ∧ Form.markedList (reentryUnfold 2) = false :=
  ⟨rfl, rfl⟩

mutual
  /-- The number of crosses in a cross (itself included). -/
  def Cross.count : Cross → Nat
    | .cross contents => Form.countList contents + 1
  /-- The number of crosses in a form. -/
  def Form.countList : List Cross → Nat
    | [] => 0
    | c :: cs => c.count + Form.countList cs
end

/-- Negative: no finite form is its own enclosure.  Re-entry is not a form. -/
theorem no_finite_reentrant_form (f : Form) : f ≠ [.cross f] := by
  intro h
  have := congrArg Form.countList h
  simp only [Form.countList, Cross.count] at this
  omega

#print axioms reentry_no_fixed_value
#print axioms no_finite_reentrant_form

end Mettapedia.Logic.LawsOfForm
