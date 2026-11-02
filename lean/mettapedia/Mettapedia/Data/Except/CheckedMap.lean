import Mathlib.Data.List.Basic

/-! Map a successful result and admit its image only when its actual
predicate holds. Existing input errors and explicit refusals remain errors. -/

set_option autoImplicit false

namespace Except

universe u v w

def checkedMap {ε : Type u} {α : Type v} {β : Type w} (input : Except ε α)
    (transform : α → β) (check : β → Bool) (refusal : ε) : Except ε β :=
  match input with
  | .error reason => .error reason
  | .ok source => if check (transform source) then .ok (transform source) else .error refusal

theorem checkedMap_ok {ε : Type u} {α : Type v} {β : Type w} {input : Except ε α}
    {transform : α → β} {check : β → Bool} {refusal : ε} {output : β}
    (built : checkedMap input transform check refusal = .ok output) :
    ∃ source, input = .ok source ∧ output = transform source ∧ check output = true := by
  cases input with
  | error reason => cases built
  | ok source =>
    change (if check (transform source) then Except.ok (transform source) else Except.error refusal) = Except.ok output at built
    cases passed : check (transform source) with
    | false => simp only [passed, Bool.false_eq_true, if_false] at built; cases built
    | true =>
      simp only [passed, if_true] at built
      have same : transform source = output := Except.ok.inj built
      exact ⟨source, rfl, same.symm, same ▸ passed⟩

#print axioms checkedMap_ok

end Except
