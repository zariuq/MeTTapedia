import Mettapedia.Logic.ConstraintTypes.PatternControls
import Mettapedia.Logic.ConstraintTypes.UnsharedParameters
import Mettapedia.Logic.ConstraintTypes.CheckCost

/-!
# Controls connecting the cost laws and unshared parameters to the checker

The structural list operator of the control model checks each element exactly
once, which is the element-wise check whose costs `CheckCost` counts. A
declaration whose first input is an unshared parameter admits exactly the calls
its waived form admits, both for an accepted and for a rejected call.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstraintTypes.CheckCostControls

open SymbolicTypes ScopedConstraints CheckingPatterns PatternControls Controls

/-- A list check is one query per element: it holds exactly when the value is a
list and every element matches. -/
theorem matches_list_iff {P : Type} (parameters : P → Closed Name Constructor typeArity)
    (element : ValueCheck P) (context : Bool) (value : Value) :
    Matches model parameters (listCheck element) context value ↔
      ∃ values, elements value = some values ∧ ∀ x ∈ values, Matches model parameters element context x := by
  rw [listCheck, matches_apply_iff]
  constructor
  · rintro ⟨branch, present, checked⟩
    cases shape : elements value with
    | none => simp [model, branches, shape] at present
    | some values =>
        have selected : branch = values.map
            (fun child => (⟨⟨0, by decide⟩, context, child⟩ :
              Query (sig := signature) (s := Kind.value) ValueOperator.list Carrier Bool)) := by
          simpa [model, branches, shape] using present
        subst branch
        refine ⟨values, rfl, fun x member => ?_⟩
        exact checked ⟨⟨0, by decide⟩, context, x⟩ (List.mem_map.2 ⟨x, member, rfl⟩)
  · rintro ⟨values, shape, checked⟩
    refine ⟨values.map (fun child => (⟨⟨0, by decide⟩, context, child⟩ :
        Query (sig := signature) (s := Kind.value) ValueOperator.list Carrier Bool)), ?_, ?_⟩
    · simp [model, branches, shape]
    · intro query member
      obtain ⟨x, xMember, rfl⟩ := List.mem_map.1 member
      exact checked x xMember

/-- An unshared first parameter beside a number input. -/
def unsharedFirst : PatternContracts.Declaration signature Nat Name Constructor typeArity .value 2 where
  input i := if i.val = 0 then ⟨.evaluate, .proper (.parameter 0)⟩ else ⟨.evaluate, .proper (.closed .number)⟩
  output := .any

def textThenNumber : Fin 2 → Value := fun i => if i.val = 0 then text "a" else number 1
def textThenText : Fin 2 → Value := fun i => if i.val = 0 then text "a" else text "b"

theorem unshared_first_accepts_any_value :
    PatternContracts.entryAccepted (PatternContracts.prepare (valueKind := Kind.value) model compiler false
      textThenNumber [unsharedFirst]) = true ∧
    PatternContracts.entryAccepted (PatternContracts.prepare (valueKind := Kind.value) model compiler false
      textThenNumber [UnsharedParameters.waive unsharedFirst 0]) = true := by cbv

theorem unshared_first_does_not_waive_other_inputs :
    PatternContracts.entryAccepted (PatternContracts.prepare (valueKind := Kind.value) model compiler false
      textThenText [unsharedFirst]) = false ∧
    PatternContracts.entryAccepted (PatternContracts.prepare (valueKind := Kind.value) model compiler false
      textThenText [UnsharedParameters.waive unsharedFirst 0]) = false := by cbv

end Mettapedia.Logic.ConstraintTypes.CheckCostControls
