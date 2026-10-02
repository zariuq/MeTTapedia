import Mathlib.Order.WellFounded

/-!
# The second-order encoding of accessibility

`AccCode r a` says that every predicate closed under `r`-induction holds at
`a`. It is equivalent to Lean's `Acc` (`accCode_iff_acc`), and it is how an
impredicative proposition layer expresses accessibility without an indexed
inductive family: the accessibility code of the candidate calculus is read as
`AccCode` in its consistency model.

Introduction (`AccCode.intro`) and inversion (`AccCode.inv`) hold by the
encoding alone. Every point of a measure relation is accessible
(`accCode_measure`); a reflexive point is not (`not_accCode_of_refl`).
-/

set_option autoImplicit false

namespace Mettapedia.Order

universe u

variable {α : Sort u} {r : α → α → Prop}

/-- The second-order encoding of accessibility. -/
def AccCode (r : α → α → Prop) (a : α) : Prop :=
  ∀ X : α → Prop, (∀ x, (∀ y, r y x → X y) → X x) → X a

namespace AccCode

/-- Introduction: a point whose predecessors are accessible is accessible. -/
theorem intro {a : α} (h : ∀ y, r y a → AccCode r y) : AccCode r a :=
  fun X step => step a fun y hy => h y hy X step

/-- Inversion, by the encoding at the predicate "every predecessor is
accessible". -/
theorem inv {a : α} (q : AccCode r a) : ∀ y, r y a → AccCode r y :=
  q (fun z => ∀ y, r y z → AccCode r y) fun _ ih y hy => intro (ih y hy)

/-- Accessibility passes to a smaller relation. -/
theorem mono {r' : α → α → Prop} (hr : ∀ y x, r' y x → r y x) {a : α} (q : AccCode r a) :
    AccCode r' a :=
  fun X step => q X fun x ih => step x fun y h => ih y (hr y x h)

end AccCode

theorem accCode_of_acc {a : α} (h : Acc r a) : AccCode r a := by
  induction h with
  | intro x _ ih => exact AccCode.intro ih

theorem acc_of_accCode {a : α} (h : AccCode r a) : Acc r a :=
  h (Acc r) fun x ih => Acc.intro x ih

/-- The second-order encoding is accessibility. -/
theorem accCode_iff_acc {a : α} : AccCode r a ↔ Acc r a :=
  ⟨acc_of_accCode, accCode_of_acc⟩

/-- Every point of a well-founded relation is accessible. -/
theorem accCode_of_wellFounded (wf : WellFounded r) (a : α) : AccCode r a :=
  accCode_of_acc (wf.apply a)

/-- Every point is accessible for a measure relation. -/
theorem accCode_measure (μ : α → Nat) (a : α) : AccCode (fun y x => μ y < μ x) a := by
  suffices h : ∀ n, ∀ a, μ a < n → AccCode (fun y x => μ y < μ x) a from h _ a (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro a h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
      intro a h
      exact AccCode.intro fun y hy => ih y (Nat.lt_of_lt_of_le hy (Nat.le_of_lt_succ h))

/-- A reflexive point is not accessible. -/
theorem not_accCode_of_refl {a : α} (hr : r a a) : ¬ AccCode r a := by
  intro q
  have : ∀ x : α, Acc r x → ¬ r x x := by
    intro x hx
    induction hx with
    | intro y _ ih => exact fun hyy => ih y hyy hyy
  exact this a (acc_of_accCode q) hr

end Mettapedia.Order
