import Mettapedia.GSLT.Dynamics.RelationalAnswerEvaluation
import Mettapedia.Languages.MeTTa.PeTTa.DeclarativeSpec
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# PeTTa's declarative operational core as an OSLF-generating GSLT

The older `pettaSpaceToLangDef` route contains only user-authored rewrite
rules.  It therefore cannot, by itself, expose the state changes, built-ins,
empty successful runs, or ordered duplicate answers of PeTTa evaluation.

This module instead instantiates the generic relational-answer GSLT with
`CoreDecl`, PeTTa's declarative stateful operational core.  The bridge theorem
`coreDecl_iff_pettaCmd` then identifies every first-stage GSLT edge with the
existing command semantics.  OSLF modalities are generated from this actual
operational graph, not from a second hand-written typing relation.

The scope is intentionally named `core`: `CoreDecl` does not yet cover every
library/profile feature of the running PeTTa dialect.  Extending that
declarative relation extends this construction without changing the OSLF
machinery.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.OperationalGSLT

open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics.RelationalAnswerEvaluation
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- PeTTa's declarative stateful core supplies the relational evaluator. -/
def coreSource : RelationalAnswerSource EvalState Pattern Pattern where
  Evaluates := CoreDecl

/-- The state-preserving pure operational fragment, expressed in the same
relational-answer interface as the stateful core. -/
def pureSource : RelationalAnswerSource EvalState Pattern Pattern where
  Evaluates := fun initial request final answers =>
    final = initial ∧ PureDecl initial.space request answers

/-- The pure fragment refines into the stateful declarative core. -/
theorem pureSource_refines_coreSource : pureSource.Refines coreSource := by
  intro initial request final answers evaluation
  obtain ⟨rfl, pureEvaluation⟩ := evaluation
  exact CoreDecl.pure _ _ _ pureEvaluation

/-- Consequently every pure operational GSLT edge has a corresponding core
edge after the lossless source rebasing. -/
theorem pureStep_simulates_coreStep
    {source target : (evaluationGSLT pureSource).Term}
    (step : (evaluationGSLT pureSource).Step source target) :
    (evaluationGSLT coreSource).Step
      (source.rebase coreSource) (target.rebase coreSource) :=
  step_rebase_of_refines pureSource_refines_coreSource step

/-- The evidence-bearing, state- and occurrence-preserving operational GSLT. -/
abbrev CoreOperationalGSLT : GSLT := evaluationGSLT coreSource

/-- Terms of the generated PeTTa operational theory. -/
abbrev CoreOperationalTerm : Type := EvaluationTerm coreSource

/-- The OSLF system mechanically generated from PeTTa's operational GSLT. -/
abbrev coreOSLF := gsltOSLF CoreOperationalGSLT

/-- Rich native predicates generated over PeTTa operational terms. -/
abbrev CoreNativeType := GSLTNativeType CoreOperationalGSLT

/-- A request-to-completion edge is exactly a declarative PeTTa core run. -/
theorem request_step_completed_iff_coreDecl
    (initial : EvalState) (request : Pattern) (final : EvalState)
    (answers : Answers) :
    CoreOperationalGSLT.Step (.request initial request)
        (.completed initial request final answers) ↔
      CoreDecl initial request final answers :=
  request_step_completed_iff coreSource initial request final answers

/-- The same edge is exactly the established stateful command semantics.
This theorem rules out a new operational authority hidden in the OSLF view. -/
theorem request_step_completed_iff_pettaCmd
    (initial : EvalState) (request : Pattern) (final : EvalState)
    (answers : Answers) :
    CoreOperationalGSLT.Step (.request initial request)
        (.completed initial request final answers) ↔
      PeTTaCmd initial request final answers := by
  rw [request_step_completed_iff_coreDecl,
    coreDecl_iff_pettaCmd]

/-- The exact completion reached by a run, represented as an OSLF native
behavioral type. -/
def completionPredicate (initial : EvalState) (request : Pattern)
    (final : EvalState) (answers : Answers) :
    EquationPredicate CoreOperationalGSLT :=
  (exactTargetNativeType (evaluationGSLT coreSource)
    (.completed initial request final answers : CoreOperationalTerm)).pred

/-- Package the exact-completion predicate with the sole operational sort. -/
def completionNativeType (initial : EvalState) (request : Pattern)
    (final : EvalState) (answers : Answers) : CoreNativeType :=
  { sort := ()
    pred := completionPredicate initial request final answers }

/-- Inhabiting a completion type is exactly the PeTTa declarative run. -/
theorem satisfies_completionNativeType_iff_coreDecl
    (initial : EvalState) (request : Pattern) (final : EvalState)
    (answers : Answers) :
    completionPredicate initial request final answers
        (.request initial request) ↔
      CoreDecl initial request final answers := by
  let sourceTerm : (evaluationGSLT coreSource).Term :=
    .request initial request
  let targetTerm : (evaluationGSLT coreSource).Term :=
    .completed initial request final answers
  have generated := satisfies_exactTargetNativeType_iff_step
    (evaluationGSLT coreSource) sourceTerm targetTerm
  have operational :
      (evaluationGSLT coreSource).Step sourceTerm targetTerm ↔
        CoreDecl initial request final answers := by
    simpa [sourceTerm, targetTerm] using
      (request_step_completed_iff_coreDecl initial request final answers)
  change (gsltOSLF (evaluationGSLT coreSource)).satisfies sourceTerm
      (exactTargetNativeType (evaluationGSLT coreSource) targetTerm).pred ↔ _
  exact generated.trans operational

/-- The command-semantics formulation of the same generated native type. -/
theorem satisfies_completionNativeType_iff_pettaCmd
    (initial : EvalState) (request : Pattern) (final : EvalState)
    (answers : Answers) :
    completionPredicate initial request final answers
        (.request initial request) ↔
      PeTTaCmd initial request final answers := by
  rw [satisfies_completionNativeType_iff_coreDecl,
    coreDecl_iff_pettaCmd]

/-! ## Positive and negative operational witnesses -/

private def foo : Pattern := .apply "foo" []

private def addThenGet : Pattern :=
  .apply "progn"
    [ .apply "add-atom" [.apply "&self" [], foo]
    , .apply "get-atoms" [.apply "&self" []] ]

private def fooState : EvalState :=
  { space := { facts := [foo], rules := [] } }

/-- The stateful extension is genuine: adding an atom is a core run that the
state-preserving pure source cannot license. -/
theorem addAtom_core_not_pure :
    CoreDecl EvalState.empty
        (.apply "add-atom" [.apply "&self" [], foo])
        (EvalState.empty.addAtom foo) [unitAtom] ∧
      ¬ pureSource.Evaluates EvalState.empty
        (.apply "add-atom" [.apply "&self" [], foo])
        (EvalState.empty.addAtom foo) [unitAtom] := by
  constructor
  · exact CoreDecl.addAtom _ _
  · rintro ⟨stateEqual, _⟩
    have factsEqual := congrArg (fun state : EvalState => state.space.facts) stateEqual
    simp [EvalState.empty, EvalState.addAtom, PeTTaSpace.addAtom, foo] at factsEqual

/-- A real state-changing PeTTa run inhabits its generated OSLF native type. -/
theorem addThenGet_inhabits_completionNativeType :
    completionPredicate EvalState.empty addThenGet fooState [foo]
      (.request EvalState.empty addThenGet) := by
  apply (satisfies_completionNativeType_iff_coreDecl _ _ _ _).2
  exact coreDecl_positive_example_progn

private def emptySuperpose : Pattern :=
  .apply "superpose" [.collection .vec [] none]

/-- An empty answer list is still a completed run. -/
theorem emptySuperpose_inhabits_completionNativeType :
    completionPredicate EvalState.empty emptySuperpose EvalState.empty []
      (.request EvalState.empty emptySuperpose) := by
  apply (satisfies_completionNativeType_iff_coreDecl _ _ _ _).2
  exact CoreDecl.pure _ _ _ (PureDecl.superpose [])

/-- The successful empty completion emits no answer occurrence. -/
theorem emptySuperpose_completion_isNormalForm :
    CoreOperationalGSLT.IsNormalForm
      (.completed EvalState.empty emptySuperpose EvalState.empty []) :=
  empty_completion_isNormalForm coreSource _ _ _

/-- A free variable evaluates to itself, not to an empty answer list. -/
theorem freeVariable_not_empty_completion (name : String) :
    ¬ CoreDecl EvalState.empty (.fvar name) EvalState.empty [] := by
  intro evaluation
  cases evaluation with
  | pure _ _ _ pureEvaluation =>
      exact pureDecl_negative_example_var_not_empty _ _ pureEvaluation

/-- Consequently the impossible completion native type is uninhabited. -/
theorem freeVariable_not_inhabits_empty_completion (name : String) :
    ¬ completionPredicate EvalState.empty (.fvar name) EvalState.empty []
      (.request EvalState.empty (.fvar name)) := by
  rw [satisfies_completionNativeType_iff_coreDecl]
  exact freeVariable_not_empty_completion name

/-! ## Ordered duplicate occurrences -/

private def duplicateSuperpose : Pattern :=
  .apply "superpose" [.collection .vec [foo, foo] none]

private def duplicateAnswers : Answers := [foo, foo]

private def duplicateCompletion : CoreOperationalTerm :=
  .completed EvalState.empty duplicateSuperpose EvalState.empty duplicateAnswers

private def duplicateOccurrence0 : Fin duplicateAnswers.length := ⟨0, by decide⟩
private def duplicateOccurrence1 : Fin duplicateAnswers.length := ⟨1, by decide⟩

/-- The duplicate-producing run is admitted by the declarative semantics. -/
theorem duplicateSuperpose_coreDecl :
    CoreDecl EvalState.empty duplicateSuperpose EvalState.empty duplicateAnswers :=
  CoreDecl.pure _ _ _ (PureDecl.superpose [foo, foo])

/-- Both duplicate occurrences are distinct GSLT edges. -/
theorem duplicateSuperpose_emits_both :
    CoreOperationalGSLT.Step duplicateCompletion
        (.answer EvalState.empty duplicateSuperpose EvalState.empty
          duplicateAnswers duplicateOccurrence0) ∧
      CoreOperationalGSLT.Step duplicateCompletion
        (.answer EvalState.empty duplicateSuperpose EvalState.empty
          duplicateAnswers duplicateOccurrence1) :=
  ⟨completed_step_answer coreSource _ _ _ _ _,
    completed_step_answer coreSource _ _ _ _ _⟩

/-- Equal answer values at different positions are not collapsed. -/
theorem duplicateSuperpose_occurrences_distinct :
    (EvaluationTerm.answer EvalState.empty duplicateSuperpose EvalState.empty
        duplicateAnswers duplicateOccurrence0 : CoreOperationalTerm) ≠
      .answer EvalState.empty duplicateSuperpose EvalState.empty
        duplicateAnswers duplicateOccurrence1 := by
  intro equal
  have positionsEqual :=
    answer_occurrence_injective coreSource EvalState.empty duplicateSuperpose
      EvalState.empty duplicateAnswers equal
  have positionsDifferent : duplicateOccurrence0 ≠ duplicateOccurrence1 := by
    decide
  exact positionsDifferent positionsEqual

/-- The distinct occurrences nevertheless select the same answer value. -/
theorem duplicateSuperpose_selected_values_equal :
    duplicateAnswers.get duplicateOccurrence0 =
      duplicateAnswers.get duplicateOccurrence1 :=
  rfl

end Mettapedia.Languages.MeTTa.PeTTa.OperationalGSLT
