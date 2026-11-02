import Mettapedia.Languages.Maude.DecidableEquality
import Mettapedia.Languages.Maude.EquationReduction

/-! A structural schema link checks every signature field, equation and rule.
Only the module's display name may differ. The checker returns an equality
witness, and that witness transports equation paths to the actual theory.
This is an IR certificate boundary, not a source parser correctness theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Maude

def Theory.named (theory : Theory) (name : String) : Theory := {theory with name := name}

mutual
  theorem Equivalent.withName {theory : Theory} {context : VariableContext} {sort : String}
      {source target : Term} (step : Equivalent theory context sort source target) (name : String) :
      Equivalent (theory.named name) context sort source target :=
    match step with
    | .refl typed => .refl typed
    | .symm step => .symm (step.withName name)
    | .trans first second => .trans (first.withName name) (second.withName name)
    | .argument frame step => .argument (theory := theory.named name) frame (step.withName name)
    | .algebra step => .algebra step
    | .equation assignment member checked left right valuation conditions =>
        .equation assignment member checked left right valuation (conditions.withName name)

  theorem Conditions.withName {theory : Theory} {context : VariableContext} {assignment : Valuation}
      {conditions : List Condition} (proved : Conditions theory context assignment conditions) (name : String) :
      Conditions (theory.named name) context assignment conditions :=
    match proved with
    | .nil assignment => .nil assignment
    | .cons first rest => .cons (first.withName name) (rest.withName name)
end

theorem EquationReduction.withName {theory : Theory} {context : VariableContext} {sort : String}
    {source target : Term} (step : EquationReduction theory context sort source target) (name : String) :
    EquationReduction (theory.named name) context sort source target := by
  induction step with
  | root assignment member checked left right valuation conditions =>
      exact .root assignment member checked left right valuation (conditions.withName name)
  | argument frame _ ih => exact .argument (theory := theory.named name) frame ih

theorem EquationPath.withName {theory : Theory} {context : VariableContext} {sort : String}
    {source target : Term} (path : EquationPath theory context sort source target) (name : String) :
    EquationPath (theory.named name) context sort source target := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step.withName name)

namespace SchemaLink

structure Witness (actual reference : Theory) : Type where
  same : actual.named reference.name = reference

def check (actual reference : Theory) : Option (Witness actual reference) :=
  if same : actual.named reference.name = reference then some ⟨same⟩ else none

theorem check_reflects (actual reference : Theory) :
    (check actual reference).isSome = true ↔ actual.named reference.name = reference := by
  by_cases same : actual.named reference.name = reference <;> simp [check, same]

theorem signature_eq {actual reference : Theory} (accepted : (check actual reference).isSome = true) :
    actual.signature = reference.signature := by
  have same := congrArg Theory.signature ((check_reflects actual reference).mp accepted)
  simpa only [Theory.named] using same

theorem equations_eq {actual reference : Theory} (accepted : (check actual reference).isSome = true) :
    actual.equations = reference.equations := by
  have same := congrArg Theory.equations ((check_reflects actual reference).mp accepted)
  simpa only [Theory.named] using same

theorem rules_eq {actual reference : Theory} (accepted : (check actual reference).isSome = true) :
    actual.rules = reference.rules := by
  have same := congrArg Theory.rules ((check_reflects actual reference).mp accepted)
  simpa only [Theory.named] using same

theorem equationPath_iff {actual reference : Theory} (accepted : (check actual reference).isSome = true)
    {context : VariableContext} {sort : String} {source target : Term} :
    EquationPath actual context sort source target ↔ EquationPath reference context sort source target := by
  have same := (check_reflects actual reference).mp accepted
  constructor
  · intro path
    simpa only [same] using path.withName reference.name
  · intro path
    rw [← same] at path
    have restored := path.withName actual.name
    simpa only [Theory.named] using restored

end SchemaLink

#print axioms Term.structuralEqual_iff
#print axioms Equivalent.withName
#print axioms SchemaLink.check_reflects
#print axioms SchemaLink.equationPath_iff

end Mettapedia.Languages.Maude
