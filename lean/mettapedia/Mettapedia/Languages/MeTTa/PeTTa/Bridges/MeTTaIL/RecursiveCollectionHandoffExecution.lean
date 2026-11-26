import Mettapedia.Languages.MeTTa.PeTTa.EquationEquality
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationSource
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionHandoff

/-! # Native preparation of recursive matches for the shared continuation -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionHandoffExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RecursiveCollectionPresentation RecursiveCollectionHandoff
open CanonicalCompare RuleBinding ScopedRuleMatching
open InferenceCettaWire (encodePattern encodeCollectionType encodeRest)
open RuleInstantiationExecution.GeneralExecution (bagChoiceTerm traceTerm matcherRequestTerm matcherAnswerTerm)
open RecursiveCollectionExecution (eventTerm answerTerm)
open CollectionPresentationExecution (presentationTerm)
open Eval BridgeKit WireKit
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_collection_handoff.metta"
    sha256 "14b11b539d59f89ae41722a5175b97b61502f582fcb7b8cde847441e3dbccc6d"

def library : BridgeKit.Library :=
  RetainedMatchingWire.interpretedLibrary

set_option maxRecDepth 100000 in
theorem checked : library.check = true := RetainedMatchingWire.interpreted_checked

section ProofMetadata

private local instance handoffEquationEq : DecidableEq SpaceSemantics.Equation :=
  SpaceSemantics.Equation.decideEq

/-- Direct outward calls derived from the actual family bodies. -/
def handoffProofInheritedHeads : List String := ["gslt:automata:append", "gslt:collection-presentation:at"]

theorem handoffProofInheritedHeads_derived :
    ((source.program.equations.flatMap (fun row => CompleteExecution.sourceLiteralHeads row.body)).filter
      (fun head => head.startsWith "gslt:" && !(source.program.equations.map (·.head)).contains head)).eraseDups =
        handoffProofInheritedHeads := by decide +kernel

private def handoffMetadataBase : SpaceSemantics.Program where
  equations := [RuleExecutionProgram.scopedProgram.equations[0]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[11]'(by decide +kernel)).program.equations[3]'(by decide +kernel)]
  declarations := [RuleExecutionProgram.scopedProgram.declarations[0]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[11]'(by decide +kernel)).program.declarations[3]'(by decide +kernel)]

/-- Bounded source metadata; all operational conclusions retain the shared runtime. -/
def handoffProofLibrary : Library := ⟨handoffMetadataBase, source.program, ["gslt:collection-handoff:"]⟩

def handoffProofHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || handoffProofLibrary.owns head || handoffProofInheritedHeads.contains head

theorem handoffProof_checked : handoffProofLibrary.check = true := by decide +kernel

theorem handoffProof_agreement :
    ProgramAgreementOn handoffProofHeads handoffProofLibrary.runtime library.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

#print axioms handoffProofInheritedHeads_derived
#print axioms handoffProof_checked
#print axioms handoffProof_agreement

end ProofMetadata

def preparedTerm (prepared : Prepared) : Term :=
  .application "PreparedCollectionMatch" [encodePattern prepared.source, matcherAnswerTerm prepared.ordinary,
    encodeList eventTerm prepared.history]

syntax "handoff_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| handoff_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call_in handoffProof_checked using handoffProof_agreement; metta_eval [$facts,*] with handoffProof_checked in handoffProof_agreement
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        CompleteExecution.pattern_symbol_unmatched, preparedTerm, presentationTerm, eventTerm, answerTerm,
        bagChoiceTerm, traceTerm, encodeList, encodeOption, InferenceCettaWire.encodeList,
        CollectionSelectionExecution.booleanTerm,
        InferenceCettaWire.encodePatterns_eq_encodeList, $extra,*]))

@[metta_head "gslt:automata:append"]
theorem append_returns {α : Type} (element : α → Term) (state : Effects.State) (left right : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:automata:append" [encoded (encodeList element left), encoded (encodeList element right)])
      state (encoded (encodeList element (left ++ right))) := by
  exact CollectionPresentationExecution.append_returns element state left right

mutual
@[metta_head "gslt:collection-handoff:trace"]
theorem trace_returns (state : Effects.State) (path : List Nat) (schema : Pattern) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-handoff:trace" [encoded (encodeList Term.natural path), encoded (encodePattern schema)])
      state (encoded (traceTerm (frontTraceAt path schema))) := by
  rw [frontTraceAt.eq_def]
  cases schema with
  | fvar | bvar => handoff_eval unfolding [encodePattern]
  | apply label schemas =>
    handoff_eval [trace_arguments_returns state false path 0 schemas] unfolding [encodePattern]
  | lambda display body | multiLambda arity display body =>
    handoff_eval [append_returns Term.natural state path [0], trace_returns state (path ++ [0]) body]
      unfolding [encodePattern]
  | subst body replacement =>
    handoff_eval [append_returns Term.natural state path [0], append_returns Term.natural state path [1],
      trace_returns state (path ++ [0]) body, trace_returns state (path ++ [1]) replacement,
      append_returns bagChoiceTerm state (frontTraceAt (path ++ [0]) body) (frontTraceAt (path ++ [1]) replacement)]
      unfolding [encodePattern]
  | collection kind schemas rest =>
    cases kind <;>
      handoff_eval [trace_arguments_returns state false path 0 schemas, trace_arguments_returns state true path 0 schemas]
        unfolding [encodePattern, encodeCollectionType]
termination_by sizeOf schema
decreasing_by all_goals sizeOf_pattern_dec

@[metta_head "gslt:collection-handoff:trace-arguments"]
theorem trace_arguments_returns (state : Effects.State) (select : Bool) (path : List Nat)
    (index : Nat) (schemas : List Pattern) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-handoff:trace-arguments" [encoded (CollectionSelectionExecution.booleanTerm select),
        encoded (encodeList Term.natural path), number index, encoded (encodeList encodePattern schemas)])
      state (encoded (traceTerm (frontTraceArguments select path index schemas))) := by
  rw [frontTraceArguments.eq_def]
  cases schemas with
  | nil => handoff_eval
  | cons schema schemas =>
    have rest := trace_arguments_returns state select path (index + 1) schemas
    have combined := append_returns bagChoiceTerm state (frontTraceAt (path ++ [index]) schema)
      (frontTraceArguments select path (index + 1) schemas)
    cases select <;>
      simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.cons_append] <;>
      handoff_eval [append_returns Term.natural state path [index], trace_returns state (path ++ [index]) schema,
        rest, combined]

termination_by sizeOf schemas
decreasing_by all_goals sizeOf_pattern_dec
end

/-- The native handoff reconstructs exactly one ordinary match per valid
recursive receipt and retains that receipt's full allocation history. -/
@[metta_head "gslt:collection-handoff:prepare"]
theorem prepare_returns (state : Effects.State) (table : List String) (ordered : NameOrdered table)
    (request : RecursiveCollectionMachine.Request) (answer : RecursiveCollectionMachine.Answer)
    (valid : EquationalScopedReceipts.Matches literalBodyComparison request.rule request.spec request.ambient
      request.site request.path request.depth request.initial request.schema request.target
      answer.trace answer.assignment) (covered : Covered table request.target) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-handoff:prepare" [encoded (encodeList Term.string table),
        encoded (matcherRequestTerm request), encoded (answerTerm answer)])
      state (encoded (encodeOption preparedTerm (prepare request answer))) := by
  have present := CollectionPresentationExecution.presentAt_returns state table ordered valid covered []
  simp only [List.append_nil] at present
  obtain ⟨presented, reconstructed, _, _⟩ := presentAt_complete valid []
  simp only [List.append_nil] at reconstructed
  rw [reconstructed] at present
  have lifted : PureReturns library.runtime [] state
      (apply "gslt:collection-presentation:at" [encoded (encodeList Term.string table),
        encoded (encodeList Term.natural request.path), encoded (encodePattern request.schema),
        encoded (encodePattern request.target), encoded (encodeList eventTerm answer.trace)])
      state (encoded (encodeOption (presentationTerm encodePattern) (some (presented, [])))) := by
    exact present
  handoff_eval [lifted, trace_returns state request.path request.schema]
    unfolding [prepare, reconstructed, matcherRequestTerm, matcherAnswerTerm]

/-- Publication by the retained matcher supplies every source-matching
hypothesis of native preparation, including for a partially drained run. -/
theorem published_prepare_returns (state : Effects.State) (table : List String)
    (ordered : NameOrdered table) (request : RecursiveCollectionMachine.Request) (fuel : Nat)
    {answer : RecursiveCollectionMachine.Answer}
    (published : answer ∈ (RecursiveCollectionMachine.run request fuel
      (RecursiveCollectionMachine.start request)).answers)
    (covered : Covered table request.target) :
    ∃ prepared, prepare request answer = some prepared ∧ prepared.Valid request answer ∧
      PureReturns library.runtime [] state
        (apply "gslt:collection-handoff:prepare" [encoded (encodeList Term.string table),
          encoded (matcherRequestTerm request), encoded (answerTerm answer)])
        state (encoded (encodeOption preparedTerm (some prepared))) := by
  have evaluated := prepare_returns state table ordered request answer
    (RecursiveCollectionMachine.published_trace_valid request fuel published) covered
  obtain ⟨prepared, computed, valid⟩ := prepare_published request fuel published
  rw [computed] at evaluated
  exact ⟨prepared, computed, valid, evaluated⟩

#print axioms append_returns
#print axioms trace_returns
#print axioms trace_arguments_returns
#print axioms prepare_returns
#print axioms published_prepare_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionHandoffExecution
