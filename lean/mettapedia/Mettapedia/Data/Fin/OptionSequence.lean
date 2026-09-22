import Mathlib.Data.Fin.Basic
import Mathlib.Data.Option.Basic

/-!
# Sequencing a finite family of optional values

All entries are retained at their original indices. The operation fails if
any entry is absent; it does not require a default value or choice operator.
-/

set_option autoImplicit false

namespace Fin

universe u
variable {α : Type u}

def sequenceOption : (n : Nat) → (Fin n → Option α) → Option (Fin n → α)
  | 0, _ => some Fin.elim0
  | n + 1, values => do
      let first ← values 0
      let rest ← sequenceOption n (fun index => values index.succ)
      return Fin.cases first rest

theorem sequenceOption_sound (n : Nat) :
    ∀ {values : Fin n → Option α} {result : Fin n → α},
      sequenceOption n values = some result →
      ∀ index, values index = some (result index) := by
  induction n with
  | zero => intro values result computed index; exact Fin.elim0 index
  | succ n ih =>
      intro values result computed
      cases first : values 0 with
      | none => simp [sequenceOption, first] at computed
      | some value =>
          cases rest : sequenceOption n (fun index => values index.succ) with
          | none => simp [sequenceOption, first, rest] at computed
          | some tail =>
              simp only [sequenceOption, first, rest, bind, Option.bind, pure,
                Option.some.injEq] at computed
              subst result
              intro index
              cases index using Fin.cases with
              | zero => exact first
              | succ index => exact ih rest index

theorem sequenceOption_complete (n : Nat) :
    ∀ (values : Fin n → Option α), (∀ index, ∃ value, values index = some value) →
      ∃ result, sequenceOption n values = some result := by
  induction n with
  | zero => intro values present; exact ⟨Fin.elim0, rfl⟩
  | succ n ih =>
      intro values present
      obtain ⟨first, firstFound⟩ := present 0
      obtain ⟨rest, restFound⟩ := ih (fun index => values index.succ) (fun index => present index.succ)
      exact ⟨Fin.cases first rest, by simp [sequenceOption, firstFound, restFound]⟩

theorem sequenceOption_isSome_iff (n : Nat) (values : Fin n → Option α) :
    (sequenceOption n values).isSome = true ↔ ∀ index, (values index).isSome = true := by
  constructor
  · intro present index
    cases computed : sequenceOption n values with
    | none => simp [computed] at present
    | some result => simp [sequenceOption_sound n computed index]
  · intro present
    obtain ⟨result, computed⟩ := sequenceOption_complete n values (fun index => by
      cases entry : values index with
      | none =>
          have impossible := present index
          simp [entry] at impossible
      | some value => exact ⟨value, rfl⟩)
    simp [computed]

theorem sequenceOption_two_present :
    sequenceOption 2 (fun index => if index = 0 then some (3 : Nat) else some 7) =
      some (Fin.cases 3 (Fin.cases 7 Fin.elim0)) := by rfl

theorem sequenceOption_missing_entry :
    sequenceOption 2 (fun index => if index = 0 then some (3 : Nat) else none) = none := by
  rfl

#print axioms sequenceOption_sound
#print axioms sequenceOption_complete
#print axioms sequenceOption_isSome_iff

end Fin
