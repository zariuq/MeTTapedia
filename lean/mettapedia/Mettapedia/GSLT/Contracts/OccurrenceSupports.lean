import Mettapedia.GSLT.Contracts.OccurrenceObservers
import Mathlib.Data.Set.Basic

/-!
# What the set of returned atoms can recover

Erasing occurrence identity and enumeration order leaves the support
of an answer stream. This preserves existence and completed absence.
It does not preserve the count, first answer, or a stronger readout.
This result concerns a readout of completed runs, not a claim that
replacing a store by a set preserves the transitions of a program.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.OccurrenceObservers

def support {A : Type} (trace : Trace A) : Set A :=
  { answer | answer ∈ trace.flatten }

def FromSupport (demand : Demand) : Prop :=
  ∀ {A : Type} {a b : Trace A}, support a = support b → observe demand a = observe demand b

private theorem empty_of_same_members {A : Type} (a b : List A)
    (same : ∀ x, x ∈ a ↔ x ∈ b) : a.isEmpty = b.isEmpty := by
  cases a with
  | nil =>
    cases b with
    | nil => rfl
    | cons head rest =>
      exact (List.not_mem_nil ((same head).mpr List.mem_cons_self)).elim
  | cons head rest =>
    cases b with
    | nil => exact (List.not_mem_nil ((same head).mp List.mem_cons_self)).elim
    | cons _ _ => rfl

theorem empty_of_same_support {A : Type} {a b : Trace A} (same : support a = support b) :
    a.flatten.isEmpty = b.flatten.isEmpty :=
  empty_of_same_members _ _ fun x => by
    change x ∈ support a ↔ x ∈ support b
    rw [same]

private def single : Trace Bool := [[false]]
private def doubled : Trace Bool := [[false, false]]

theorem doubling_erases_only_in_support :
    support single = support doubled ∧
      observe .count single ≠ observe .count doubled ∧
      observe .ordered single ≠ observe .ordered doubled ∧
      observe .bag single ≠ observe .bag doubled := by
  constructor
  · ext value; simp [support, single, doubled]
  · decide

private def leftFirst : Trace Bool := [[false, true]]
private def rightFirst : Trace Bool := [[true, false]]

theorem order_erases_in_support_but_not_first :
    support leftFirst = support rightFirst ∧ observe .first leftFirst ≠ observe .first rightFirst := by
  constructor
  · ext value; simp [support, leftFirst, rightFirst, or_comm]
  · decide

theorem exact_support_readouts (demand : Demand) :
    FromSupport demand ↔ demand = .presence ∨ demand = .absence := by
  constructor
  · intro recover
    cases demand with
    | presence => exact Or.inl rfl
    | absence => exact Or.inr rfl
    | count =>
      exact (doubling_erases_only_in_support.2.1 (recover doubling_erases_only_in_support.1)).elim
    | ordered =>
      exact (doubling_erases_only_in_support.2.2.1 (recover doubling_erases_only_in_support.1)).elim
    | bag =>
      exact (doubling_erases_only_in_support.2.2.2 (recover doubling_erases_only_in_support.1)).elim
    | first =>
      exact (order_erases_in_support_but_not_first.2 (recover order_erases_in_support_but_not_first.1)).elim
    | timed =>
      have same : single = doubled := recover doubling_erases_only_in_support.1
      exact (doubling_erases_only_in_support.2.1 (congrArg (observe .count) same)).elim
  · rintro (rfl | rfl) A a b same
    · exact congrArg Bool.not (empty_of_same_support same)
    · exact empty_of_same_support same

end Mettapedia.GSLT.Contracts.OccurrenceObservers
