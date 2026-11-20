import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NativeExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.CheckedDeclarations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ValueAnswers

/-!
# Actual declared row calls join the two native execution chains

For the checked recursive row class, the declared constant is evaluated by
the development's actual rules, through the compiled source interpreter and
its public query. The same answer is reached by the existing qualified
descriptor program. The selected declaration and fresh package names supply
the declared call and result types. The equivalence concerns data-value
observations; general normal forms, derivation multiplicity and termination
of every evaluation schedule remain separate guarantees.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.CheckedRowsNative

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open NativeTypesOnTheStep.Computing NativeTypesOnTheStep.Computing.Definitions
open TelescopeAbstraction (applyClosed)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (pkg)
open SourceLanguage SourceLanguage.Elaboration

variable {dev : Development} (built : Compiled dev)
  (D : Discipline MSig [] ()) (N : Hosting.Nodes MSig [] ()) (supply : Nat → MClosed)

include supply

theorem checked_rows_execute (ok : devCheck dev = true) (fresh : devFresh dev = true)
    {definition : Vectors.Checker.Definition} {compiled : Tower.Tm 0} {name : DeclName} {q j : Nat}
    (selected : dev.find? (·.1 == name) = some (name, definition))
    (checked : Checked definition 0 compiled)
    (reach : DirectedAnswers.RowsReach definition compiled name built.nativeRows q j)
    {arguments : Sub Tower.Head definition.arity 0}
    (typedArguments : SubstMor pkg definition.telescope .nil arguments)
    (data : DirectedAnswers.DataType (subst arguments definition.result)) :
    ∃ value, DirectedAnswers.Value value ∧
      Typed (devPackage dev built.nativeRows) .nil
        (applyClosed definition.telescope arguments (.const name)) (subst arguments definition.result) ∧
      Typed (devPackage dev built.nativeRows) .nil value (subst arguments definition.result) ∧
      NativeExecution.Answer built D N (applyClosed definition.telescope arguments (.const name)) value ∧
      CheckedCalls.NativeAnswer checked typedArguments value := by
  obtain ⟨value, isValue, typed, compiledAnswer, rowAnswer, _, _⟩ :=
    DirectedAnswers.rows_reach ok built.native checked reach typedArguments (fun _ => .refl _) data
  refine ⟨value, isValue,
    CheckedDeclarations.named_call_typed fresh selected checked built.nativeRows typedArguments,
    typed_dev fresh built.nativeRows typed,
    NativeExecution.directed_value_executes built D N supply rowAnswer.1 isValue, ?_⟩
  exact (CheckedCalls.compiled_answer_iff_native checked typedArguments value).mp compiledAnswer

theorem answer_iff_qualified (ok : devCheck dev = true)
    {definition : Vectors.Checker.Definition} {compiled : Tower.Tm 0} {name : DeclName} {q j : Nat}
    (checked : Checked definition 0 compiled)
    (reach : DirectedAnswers.RowsReach definition compiled name built.nativeRows q j)
    {arguments : Sub Tower.Head definition.arity 0}
    (typedArguments : SubstMor pkg definition.telescope .nil arguments)
    (data : DirectedAnswers.DataType (subst arguments definition.result)) (value : Tower.Tm 0) :
    NativeExecution.Answer built D N (applyClosed definition.telescope arguments (.const name)) value ↔
      CheckedCalls.NativeAnswer checked typedArguments value := by
  constructor
  · intro answered
    exact (CheckedCalls.row_answer_iff_native ok built.native checked reach typedArguments
      (fun _ => .refl _) data value).mp
        (ValueAnswers.checked_answer_is_normal built D N supply ok answered)
  · intro answered
    obtain ⟨actual, isValue, _, _, rowAnswer, unique, _⟩ :=
      DirectedAnswers.rows_reach ok built.native checked reach typedArguments (fun _ => .refl _) data
    have equal := unique value ((CheckedCalls.compiled_answer_iff_native checked typedArguments value).mpr answered)
    subst value
    exact NativeExecution.directed_value_executes built D N supply rowAnswer.1 isValue

theorem public_answer_keeps_declared_type (ok : devCheck dev = true) (fresh : devFresh dev = true)
    {definition : Vectors.Checker.Definition} {compiled : Tower.Tm 0} {name : DeclName} {q j : Nat}
    (selected : dev.find? (·.1 == name) = some (name, definition))
    (checked : Checked definition 0 compiled)
    (reach : DirectedAnswers.RowsReach definition compiled name built.nativeRows q j)
    {arguments : Sub Tower.Head definition.arity 0}
    (typedArguments : SubstMor pkg definition.telescope .nil arguments)
    (data : DirectedAnswers.DataType (subst arguments definition.result)) {value : Tower.Tm 0}
    (answered : NativeExecution.Answer built D N
      (applyClosed definition.telescope arguments (.const name)) value) :
    Typed (devPackage dev built.nativeRows) .nil value (subst arguments definition.result) :=
  (CheckedDeclarations.named_native_answer fresh selected checked built.nativeRows typedArguments
    ((answer_iff_qualified built D N supply ok checked reach typedArguments data value).mp answered)).2.2

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.CheckedRowsNative

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.CheckedRowsNative.checked_rows_execute
