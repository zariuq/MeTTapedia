import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.DirectedRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationDefinitions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationVectorProgram
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.Rows

/-!
# Checked row answers and actual directed descriptor runs

The existing checked definition compiler supplies the initial dependent state.
Its compiled call runs under the fixed fourteen-row descriptor program, with
head conversion excluded. For the independently proved `RowsReach` class, the
declared constant evaluated by its own rows and this actual target run have
the same unique answer at the source definition's computed result type.

This is an answer correspondence. It neither identifies individual row
reductions with target events nor derives strong normalization of the extended
row package. The source-language erasure and the ordinary schematic hosting
program remain separate representations. Convertible source arguments may be
read at supplied typed arguments; that premise is not an evaluation algorithm.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.CheckedCalls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open NativeTypesOnTheStep.Computing NativeTypesOnTheStep.Computing.Definitions
open TelescopeAbstraction (applyClosed)
open AlgebraicSchema (SchemaTable)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (pkg)

abbrev setting := ComputationProfile.CheckedDefinitions.setting
abbrev qualified := ComputationProfile.CheckedDefinitions.qualified
abbrev program := ComputationProgram.Controls.program

local instance headPolicy : DecidableRel setting.R.headEq := Classical.decRel _

abbrev input {definition : Vectors.Checker.Definition} {compiled : Tower.Tm 0}
    (checked : Checked definition 0 compiled) {arguments : Sub Tower.Head definition.arity 0}
    (typedArguments : SubstMor pkg definition.telescope .nil arguments) :=
  ComputationProfile.CheckedDefinitions.input checked .nil typedArguments

/-- A final normal reading of an actual run, retaining the complete native
state and firing word rather than projecting the run to a store-change list. -/
def NativeAnswer {definition : Vectors.Checker.Definition} {compiled : Tower.Tm 0}
    (checked : Checked definition 0 compiled) {arguments : Sub Tower.Head definition.arity 0}
    (typedArguments : SubstMor pkg definition.telescope .nil arguments) (value : Tower.Tm 0) : Prop :=
  ∃ run : (Directed.restricted program qualified).Run (input checked typedArguments).state,
    Directed.Represents (S := setting) value run.last ∧ ContextualDependentExecutableJoin.Normal pkg value

theorem compiled_answer_iff_native {definition : Vectors.Checker.Definition} {compiled : Tower.Tm 0}
    (checked : Checked definition 0 compiled) {arguments : Sub Tower.Head definition.arity 0}
    (typedArguments : SubstMor pkg definition.telescope .nil arguments) (value : Tower.Tm 0) :
    DirectedAnswers.DirectedAnswer pkg (applyClosed definition.telescope arguments compiled) value ↔
      NativeAnswer checked typedArguments value :=
  Directed.answers_by_run_iff program qualified
    (Computation.represents_configuration (input checked typedArguments) rfl)

theorem native_answer_keeps_type {definition : Vectors.Checker.Definition} {compiled : Tower.Tm 0}
    (checked : Checked definition 0 compiled) {arguments : Sub Tower.Head definition.arity 0}
    (typedArguments : SubstMor pkg definition.telescope .nil arguments) {value : Tower.Tm 0}
    (answered : NativeAnswer checked typedArguments value) :
    Typed pkg .nil value (subst arguments definition.result) := by
  obtain ⟨run, represented, _⟩ := answered
  exact (Directed.run_keeps_type program qualified (configuration := input checked typedArguments)
    rfl run represented).1

/-- The existing row-completeness certificate is used only for its stated
recursive class. The target is the actual fixed descriptor program. -/
theorem row_answer_iff_native {dev : Development} (ok : devCheck dev = true)
    {rows : SchemaTable Tower.Head} (found : devRules dev = some rows)
    {definition : Vectors.Checker.Definition} {compiled : Tower.Tm 0} {name : DeclName} {q j : Nat}
    (checked : Checked definition 0 compiled)
    (reach : DirectedAnswers.RowsReach definition compiled name rows q j)
    {sourceArguments arguments : Sub Tower.Head definition.arity 0}
    (typedArguments : SubstMor pkg definition.telescope .nil arguments)
    (same : ∀ x, Conv (devPackage dev rows).headEq (sourceArguments x) (arguments x)
      (devPackage dev rows).computation)
    (data : DirectedAnswers.DataType (subst arguments definition.result)) (value : Tower.Tm 0) :
    DirectedAnswers.DirectedAnswer (devPackage dev rows)
      (applyClosed definition.telescope sourceArguments (.const name)) value ↔
        NativeAnswer checked typedArguments value := by
  obtain ⟨answer, _, _, compiledAnswer, rowAnswer, uniqueCompiled, uniqueRow⟩ :=
    DirectedAnswers.rows_reach ok found checked reach typedArguments same data
  constructor
  · intro rowValue
    have equal := uniqueRow value rowValue
    subst value
    exact (compiled_answer_iff_native checked typedArguments answer).mp compiledAnswer
  · intro nativeValue
    have equal := uniqueCompiled value
      ((compiled_answer_iff_native checked typedArguments value).mpr nativeValue)
    subst value
    exact rowAnswer

/-- Every call in the class has a real target execution; every target normal
readout is its unique value. This does not assert that every row-reduction
schedule terminates. -/
theorem checked_rows_execute {dev : Development} (ok : devCheck dev = true)
    {rows : SchemaTable Tower.Head} (found : devRules dev = some rows)
    {definition : Vectors.Checker.Definition} {compiled : Tower.Tm 0} {name : DeclName} {q j : Nat}
    (checked : Checked definition 0 compiled)
    (reach : DirectedAnswers.RowsReach definition compiled name rows q j)
    {sourceArguments arguments : Sub Tower.Head definition.arity 0}
    (typedArguments : SubstMor pkg definition.telescope .nil arguments)
    (same : ∀ x, Conv (devPackage dev rows).headEq (sourceArguments x) (arguments x)
      (devPackage dev rows).computation)
    (data : DirectedAnswers.DataType (subst arguments definition.result)) :
    ∃ value, DirectedAnswers.Value value ∧ Typed pkg .nil value (subst arguments definition.result) ∧
      DirectedAnswers.DirectedAnswer (devPackage dev rows)
        (applyClosed definition.telescope sourceArguments (.const name)) value ∧
      NativeAnswer checked typedArguments value ∧
      ∀ other, NativeAnswer checked typedArguments other → other = value := by
  obtain ⟨value, isValue, typed, compiledAnswer, rowAnswer, uniqueCompiled, _⟩ :=
    DirectedAnswers.rows_reach ok found checked reach typedArguments same data
  exact ⟨value, isValue, typed, rowAnswer,
    (compiled_answer_iff_native checked typedArguments value).mp compiledAnswer,
    fun other answered => uniqueCompiled other
      ((compiled_answer_iff_native checked typedArguments other).mpr answered)⟩

/-- Forgetting the directed policy preserves the actual native event word,
endpoint and declared result type. The terminal state has no admitted
directed-program firing. -/
theorem normal_run_certificate {definition : Vectors.Checker.Definition} {compiled : Tower.Tm 0}
    (checked : Checked definition 0 compiled) {arguments : Sub Tower.Head definition.arity 0}
    (typedArguments : SubstMor pkg definition.telescope .nil arguments) {value : Tower.Tm 0}
    (answered : NativeAnswer checked typedArguments value) :
    ∃ run : (Directed.restricted program qualified).Run (input checked typedArguments).state,
      Directed.Represents (S := setting) value run.last ∧
      (Directed.toFullProgramRun program qualified run).word = run.word ∧
      (Directed.toFullProgramRun program qualified run).last = run.last ∧
      Typed pkg .nil value (subst arguments definition.result) ∧
      ¬ ∃ firing : Firing setting.levels run.last, (Directed.restricted program qualified).Admits firing := by
  obtain ⟨run, represented, normal⟩ := answered
  exact ⟨run, represented, Directed.toFullProgramRun_word program qualified run,
    Directed.toFullProgramRun_last program qualified run,
    native_answer_keeps_type checked typedArguments ⟨run, represented, normal⟩,
    (Directed.normal_iff_no_firing program qualified represented).mp normal⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.CheckedCalls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.CheckedCalls.row_answer_iff_native
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.CheckedCalls.checked_rows_execute
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.CheckedCalls.normal_run_certificate
