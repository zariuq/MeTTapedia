import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Core

/-!
# Evaluation and fresh-name transport of positional CMR output labels

These finite-list laws retain the value carried at each fresh occurrence.
They do not identify occurrences merely because their payloads are equal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings

universe uO uA uB

variable {O : Type uO} {A : Type uA} {B : Type uB} [DecidableEq O]

abbrev labels (old : O → A) (made : List O) (rows : List A) (o : O) : A :=
  relabel (Tm := fun _ : Unit => A) (a := ()) old made rows o

theorem map_relabel (value : A → B) (old : O → A) :
    ∀ (made : List O) (rows : List A) (o : O),
      value (labels old made rows o) = labels (fun id => value (old id)) made (rows.map value) o := by
  intro made
  induction made with
  | nil => intro rows o; rfl
  | cons head rest ih =>
    intro rows o
    cases rows with
    | nil => rfl
    | cons row later =>
      by_cases same : o = head
      · simp [relabel, same]
      · simp only [relabel, if_neg same, List.map_cons]
        exact ih later o

theorem relabel_transport (rename : Equiv.Perm O) (oldFirst oldSecond : O → A) :
    ∀ (made : List O) (rows : List A), made.length = rows.length →
      ∀ o : O, (o ∉ made → oldFirst o = oldSecond (rename o)) →
        labels oldFirst made rows o = labels oldSecond (made.map rename) rows (rename o) := by
  intro made
  induction made with
  | nil =>
    intro rows length o agrees
    have empty := List.length_eq_zero_iff.mp length.symm
    subst rows
    exact agrees (List.not_mem_nil)
  | cons head rest ih =>
    intro rows length o agrees
    cases rows with
    | nil => cases length
    | cons row later =>
      by_cases same : o = head
      · simp only [List.map_cons, relabel, same, if_pos]
      · have different : rename o ≠ rename head := fun h => same (rename.injective h)
        simp only [List.map_cons, relabel, if_neg same, if_neg different]
        exact ih later (Nat.succ.inj length) o
          (fun absent => agrees (by simpa only [List.mem_cons, not_or] using And.intro same absent))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
