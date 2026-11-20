import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.CheckedCalls

/-!
# The declaration actually selected by a development

The development's declaration lookup uses its first matching name; its rule
table is built from all entries. A declared-call typing theorem therefore
uses the actual lookup equation, not membership of an arbitrary definition.
Fresh package names preserve the base package's typing. Neither condition is
inferred from the declaration-time conversion check alone.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.CheckedDeclarations

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open NativeTypesOnTheStep.Computing NativeTypesOnTheStep.Computing.Definitions
open TelescopeAbstraction (applyClosed liftClosed_zero)
open AlgebraicSchema (SchemaTable)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (pkg)

theorem selected_type {dev : Development} {name : DeclName} {definition : Vectors.Checker.Definition}
    (selected : dev.find? (·.1 == name) = some (name, definition)) (rows : SchemaTable Tower.Head) :
    (devPackage dev rows).constantType name = some definition.type := by
  change (match dev.find? (·.1 == name) with
    | some (_, found) => some found.type
    | none => pkg.constantType name) = _
  rw [selected]

/-- The named constant has the supplied definition's signature only after
the actual lookup has been checked. The argument telescope is preserved by
the existing package-inclusion theorem. -/
theorem named_call_typed {dev : Development} (fresh : devFresh dev = true)
    {name : DeclName} {definition : Vectors.Checker.Definition} {compiled : Tower.Tm 0}
    (selected : dev.find? (·.1 == name) = some (name, definition))
    (checked : Checked definition 0 compiled) (rows : SchemaTable Tower.Head)
    {arguments : Sub Tower.Head definition.arity 0}
    (typedArguments : SubstMor pkg definition.telescope .nil arguments) :
    Typed (devPackage dev rows) .nil (applyClosed definition.telescope arguments (.const name))
      (subst arguments definition.result) := by
  have compiledTyped : Typed pkg .nil compiled definition.type := by
    simpa only [baseCtx, liftClosed_zero] using checked.guarantee.1
  obtain ⟨level, isUniverse, formed⟩ :=
    Derivable.presupposed CheckedCalls.setting.levels compiledTyped CtxFormed.nil
  have constantTyped : Typed (devPackage dev rows) .nil (.const name) (liftClosed definition.type) :=
    .const (selected_type selected rows) (typed_dev fresh rows formed) isUniverse
  unfold Vectors.Checker.Definition.type at constantTyped
  rw [closePi_eq_closeType] at constantTyped
  exact Typed.telescope_apply (fun index => typed_dev fresh rows (typedArguments index)) constantTyped

theorem named_native_answer {dev : Development} (fresh : devFresh dev = true)
    {name : DeclName} {definition : Vectors.Checker.Definition} {compiled : Tower.Tm 0}
    (selected : dev.find? (·.1 == name) = some (name, definition))
    (checked : Checked definition 0 compiled) (rows : SchemaTable Tower.Head)
    {arguments : Sub Tower.Head definition.arity 0}
    (typedArguments : SubstMor pkg definition.telescope .nil arguments) {value : Tower.Tm 0}
    (answered : CheckedCalls.NativeAnswer checked typedArguments value) :
    (devPackage dev rows).constantType name = some definition.type ∧
      Typed (devPackage dev rows) .nil (applyClosed definition.telescope arguments (.const name))
        (subst arguments definition.result) ∧
      Typed (devPackage dev rows) .nil value (subst arguments definition.result) :=
  ⟨selected_type selected rows, named_call_typed fresh selected checked rows typedArguments,
    typed_dev fresh rows (CheckedCalls.native_answer_keeps_type checked typedArguments answered)⟩

section Controls

open NativeTypesOnTheStep.Computing.DirectedAnswers
open TowerVectorsModel (zeroC numC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (D)

theorem addition_selected : addAppendDev.find? (·.1 == addName) = some (addName, addDef) := rfl

theorem addition_named_call_typed :
    Typed addAppendExt .nil (applyClosed addDef.telescope (addArgs zeroC zeroC) (.const addName)) numC :=
  named_call_typed addAppend_fresh addition_selected add_checked addAppendRows
    (addArgs_typed D.zero_typed D.zero_typed)

def duplicateNames : Development := [(addName, addDef), (addName, dupDef)]

/-- Membership alone selects no declaration. This control concerns lookup;
it makes no assertion that this duplicate development passes devCheck. -/
theorem membership_does_not_select_type :
    (addName, dupDef) ∈ duplicateNames ∧
      (devBase duplicateNames).constantType addName = some addDef.type ∧
      (devBase duplicateNames).constantType addName ≠ some dupDef.type := by
  constructor
  · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  constructor
  · rfl
  · decide +kernel

end Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.CheckedDeclarations

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.CheckedDeclarations.named_native_answer
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.CheckedDeclarations.membership_does_not_select_type
