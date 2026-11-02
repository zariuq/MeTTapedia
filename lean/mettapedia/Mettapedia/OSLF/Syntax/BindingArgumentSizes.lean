import Mettapedia.OSLF.Syntax.BindingArgumentSlotPositions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Typed field enumeration agrees with the existing argument-size measure

Splitting the first field from the remaining positions is an actual
equivalence. Summing child sizes over the finite typed positions gives exactly
`argsSize`. This supports descent proofs for contextual constructor imitation,
including constructors whose fields bind variables or have different sorts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ArgumentSlots

open scoped BigOperators

variable {S : Signature}

def consEquiv (first : MetaArity S) (rest : List (MetaArity S)) : Slot (first :: rest) ≃ Unit ⊕ Slot rest where
  toFun slot := match slot with
    | ⟨_, .zero⟩ => .inl ()
    | ⟨field, .succ position⟩ => .inr ⟨field, position⟩
  invFun slot := match slot with
    | .inl () => ⟨first, .zero⟩
    | .inr ⟨field, position⟩ => ⟨field, .succ position⟩
  left_inv := by
    rintro ⟨field, position⟩
    cases position <;> rfl
  right_inv := by
    intro slot
    cases slot with
    | inl marker => cases marker; rfl
    | inr slot => cases slot; rfl

theorem sum_cons (first : MetaArity S) (rest : List (MetaArity S)) (value : Slot (first :: rest) → Nat) :
    (∑ slot, value slot) = value ⟨first, .zero⟩ + ∑ slot : Slot rest, value ⟨slot.1, .succ slot.2⟩ := by
  have rearranged := Fintype.sum_equiv (consEquiv first rest) value
    (Sum.elim (fun _ : Unit => value ⟨first, .zero⟩) (fun slot : Slot rest => value ⟨slot.1, .succ slot.2⟩))
    (by rintro ⟨field, position⟩; cases position <;> rfl)
  simpa only [Fintype.sum_sum_type, Fintype.sum_unique, Sum.elim_inl, Sum.elim_inr] using rearranged

theorem sum_get : ∀ {arities : List (MetaArity S)} {Γ : Ctx S} (arguments : Args S arities Γ),
    (∑ slot : Slot arities, termSize (get arguments slot.1 slot.2)) = argsSize arguments
  | [], _, .nil => by
      apply Finset.sum_eq_zero
      intro slot _
      nomatch slot.2
  | _ :: rest, _, .cons head tail => by
      rw [sum_cons]
      simp only [get, argsSize]
      exact congrArg (Nat.add (termSize head)) (sum_get tail)

end Mettapedia.OSLF.Binding.ArgumentSlots
