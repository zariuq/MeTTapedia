import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentExpand
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.RootFamily
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionHandoffExecution
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionContinuation
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionStateExecution
import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledCoverage

/-!
# Native retained continuations for recursive collection allocations

The wire frame retains the prepared source, original allocation history and
shared scheduled premise state. Its operations use the established post-match
continuation and descent machine at the actual complete binder context.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RecursiveCollectionContinuation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit
open CompleteExecution.DescentCodec
open RecursiveCollectionHandoffExecution (preparedTerm)
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  CollectionOccurrenceSearchExecution.SelectedNativeSource.continuationSource

def library : BridgeKit.Library :=
  CollectionOccurrenceSearchExecution.SelectedNativeSource.library

theorem checked : library.check = true := CollectionOccurrenceSearchExecution.SelectedNativeSource.checked

def frameTerm (request : Request) (search : State request) : Term :=
  .application "RecursiveCollectionContinuation" [preparedTerm request.prepared, stateTerm search]

def publicationTerm (request : Request) (firing : Complete.DeepRoot.Firing) : Term :=
  .application "RecursiveCollectionContinued" [preparedTerm request.prepared, CompleteExecution.firingTerm firing]


section ContinuationProofMetadata

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program Equation)
open Eval BridgeKit

private local instance continuationEquationEq : DecidableEq SpaceSemantics.Equation := by
  intro first second
  apply decidable_of_iff
    (first.head = second.head ∧ first.arguments = second.arguments ∧ first.body = second.body)
  constructor
  · rintro ⟨head, arguments, body⟩
    cases first
    cases second
    cases head
    cases arguments
    cases body
    rfl
  · intro same
    cases same
    exact ⟨rfl, rfl, rfl⟩

private def continuationProofSource : Program := CollectionOccurrenceSearchExecution.SelectedNativeSource.continuationSource.program

theorem continuationProof_source_quote : continuationProofSource = source.program := by rfl

private def continuationObservedInheritedHeads : List String :=
  ((continuationProofSource.equations.flatMap (fun row => CompleteExecution.sourceLiteralHeads row.body)).filter
    (fun head => head.startsWith "gslt:" && !(continuationProofSource.equations.map (·.head)).contains head)).eraseDups

/-- Direct outward calls derived from the actual family bodies. -/
def continuationProofInheritedHeads : List String := ["gslt:descent:continue-root-answer", "gslt:collection-backend:expansion-state", "gslt:descent:run"]

theorem continuationProofInheritedHeads_derived :
    continuationObservedInheritedHeads = continuationProofInheritedHeads := by decide +kernel

theorem continuationProof_source_count : continuationProofSource.equations.length = 4 := by decide +kernel

theorem continuationProof_inherited_count : continuationObservedInheritedHeads.length = 3 := by
  rw [continuationProofInheritedHeads_derived]
  decide +kernel

private def continuationScopedMetadataEquations : List SpaceSemantics.Equation :=
  []

private def continuationPriorMetadataEquations : List SpaceSemantics.Equation :=
  [(CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[1]'(by decide +kernel)).program.equations[4]'(by decide +kernel),
    (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[1]'(by decide +kernel)).program.equations[11]'(by decide +kernel),
    (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[8]'(by decide +kernel)).program.equations[5]'(by decide +kernel)]

private def continuationScopedMetadataDeclarations : List Atom :=
  []

private def continuationPriorMetadataDeclarations : List Atom :=
  [(CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[1]'(by decide +kernel)).program.declarations[4]'(by decide +kernel),
    (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[1]'(by decide +kernel)).program.declarations[11]'(by decide +kernel),
    (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[8]'(by decide +kernel)).program.declarations[5]'(by decide +kernel)]

private def continuationMetadataBase : Program where
  equations := continuationScopedMetadataEquations ++ continuationPriorMetadataEquations
  declarations := continuationScopedMetadataDeclarations ++ continuationPriorMetadataDeclarations

/-- Bounded call and constructor metadata for the shared selected program. -/
def continuationProofLibrary : Library := ⟨continuationMetadataBase, continuationProofSource, ["gslt:collection-continuation:"]⟩

def continuationProofHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || continuationProofLibrary.owns head || continuationProofInheritedHeads.contains head

theorem continuationProof_checked : continuationProofLibrary.check = true := by decide +kernel

theorem continuationProof_equation_count : continuationProofLibrary.runtime.equations.length = 7 := by decide +kernel

private def continuationPriorSources := CollectionOccurrenceSearchExecution.SelectedNativeSource.sources.take 13
private def continuationLaterSources := CollectionOccurrenceSearchExecution.SelectedNativeSource.sources.drop 14

private theorem continuationScoped_equations_indices :
    (List.finRange RuleExecutionProgram.scopedProgram.equations.length).filter (fun index => (fun row => continuationProofHeads row.head) (RuleExecutionProgram.scopedProgram.equations.get index)) =
      [] := by decide +kernel

private theorem continuationScoped_equations : RuleExecutionProgram.scopedProgram.equations.filter (fun row => continuationProofHeads row.head) = continuationScopedMetadataEquations := by
  rw [CompleteExecution.source_filter_indices, continuationScoped_equations_indices]
  rfl

private theorem continuationPrior_equations_indices :
    (List.finRange (continuationPriorSources.flatMap (fun source => source.program.equations)).length).filter (fun index => (fun row => continuationProofHeads row.head) ((continuationPriorSources.flatMap (fun source => source.program.equations)).get index)) =
      [⟨23, by decide +kernel⟩, ⟨30, by decide +kernel⟩, ⟨208, by decide +kernel⟩] := by decide +kernel

private theorem continuationPrior_equations : (continuationPriorSources.flatMap (fun source => source.program.equations)).filter (fun row => continuationProofHeads row.head) = continuationPriorMetadataEquations := by
  rw [CompleteExecution.source_filter_indices, continuationPrior_equations_indices]
  rfl

private theorem continuationOwned_equations : continuationProofSource.equations.filter (fun row => continuationProofHeads row.head) = continuationProofSource.equations := by
  apply List.filter_eq_self.mpr
  exact List.all_eq_true.mp (by decide +kernel)

private theorem continuationLater_equations : (continuationLaterSources.flatMap (fun source => source.program.equations)).filter (fun row => continuationProofHeads row.head) = [] := by
  have checked : (continuationLaterSources.flatMap (fun source => source.program.equations)).all (fun row => !(fun row => continuationProofHeads row.head) row) = true := by decide +kernel
  apply List.filter_eq_nil_iff.mpr
  intro row member kept
  have rejected := List.all_eq_true.mp checked row member
  simp [kept] at rejected

private theorem continuationSupport_equations :
    CollectionOccurrenceSearchExecution.SelectedNativeSource.sources.flatMap (fun source => source.program.equations) =
      (continuationPriorSources.flatMap (fun source => source.program.equations)) ++ continuationProofSource.equations ++ (continuationLaterSources.flatMap (fun source => source.program.equations)) := by
  have split : CollectionOccurrenceSearchExecution.SelectedNativeSource.sources =
      continuationPriorSources ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[13]'(by decide +kernel)) :: continuationLaterSources := rfl
  rw [split, List.flatMap_append, List.flatMap_cons]
  rfl

private theorem continuationProof_physical_equations : continuationProofLibrary.runtime.equations =
    (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources.foldl
      (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram).equations.filter (fun row => continuationProofHeads row.head) := by
  rw [CompleteExecution.PhysicalSourceAgreement.fold_equations, continuationSupport_equations]
  simp only [List.filter_append, continuationScoped_equations, continuationPrior_equations,
    continuationOwned_equations, continuationLater_equations, List.append_nil]
  change (continuationScopedMetadataEquations ++ continuationPriorMetadataEquations) ++ continuationProofSource.equations = _
  simp only [List.append_assoc]

private theorem continuationScoped_declarations_indices :
    (List.finRange RuleExecutionProgram.scopedProgram.declarations.length).filter (fun index => (retainedCallDeclaration continuationProofHeads) (RuleExecutionProgram.scopedProgram.declarations.get index)) =
      [] := by decide +kernel

private theorem continuationScoped_declarations : RuleExecutionProgram.scopedProgram.declarations.filter (retainedCallDeclaration continuationProofHeads) = continuationScopedMetadataDeclarations := by
  rw [CompleteExecution.source_filter_indices, continuationScoped_declarations_indices]
  rfl

private theorem continuationPrior_declarations_indices :
    (List.finRange (continuationPriorSources.flatMap (fun source => source.program.declarations)).length).filter (fun index => (retainedCallDeclaration continuationProofHeads) ((continuationPriorSources.flatMap (fun source => source.program.declarations)).get index)) =
      [⟨23, by decide +kernel⟩, ⟨30, by decide +kernel⟩, ⟨208, by decide +kernel⟩] := by decide +kernel

private theorem continuationPrior_declarations : (continuationPriorSources.flatMap (fun source => source.program.declarations)).filter (retainedCallDeclaration continuationProofHeads) = continuationPriorMetadataDeclarations := by
  rw [CompleteExecution.source_filter_indices, continuationPrior_declarations_indices]
  rfl

private theorem continuationOwned_declarations : continuationProofSource.declarations.filter (retainedCallDeclaration continuationProofHeads) = continuationProofSource.declarations := by
  apply List.filter_eq_self.mpr
  exact List.all_eq_true.mp (by decide +kernel)

private theorem continuationLater_declarations : (continuationLaterSources.flatMap (fun source => source.program.declarations)).filter (retainedCallDeclaration continuationProofHeads) = [] := by
  have checked : (continuationLaterSources.flatMap (fun source => source.program.declarations)).all (fun row => !(retainedCallDeclaration continuationProofHeads) row) = true := by decide +kernel
  apply List.filter_eq_nil_iff.mpr
  intro row member kept
  have rejected := List.all_eq_true.mp checked row member
  simp [kept] at rejected

private theorem continuationSupport_declarations :
    CollectionOccurrenceSearchExecution.SelectedNativeSource.sources.flatMap (fun source => source.program.declarations) =
      (continuationPriorSources.flatMap (fun source => source.program.declarations)) ++ continuationProofSource.declarations ++ (continuationLaterSources.flatMap (fun source => source.program.declarations)) := by
  have split : CollectionOccurrenceSearchExecution.SelectedNativeSource.sources =
      continuationPriorSources ++ (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources[13]'(by decide +kernel)) :: continuationLaterSources := rfl
  rw [split, List.flatMap_append, List.flatMap_cons]
  rfl

private theorem continuationProof_physical_declarations : continuationProofLibrary.runtime.declarations =
    (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources.foldl
      (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram).declarations.filter (retainedCallDeclaration continuationProofHeads) := by
  rw [CompleteExecution.PhysicalSourceAgreement.fold_declarations, continuationSupport_declarations]
  simp only [List.filter_append, continuationScoped_declarations, continuationPrior_declarations,
    continuationOwned_declarations, continuationLater_declarations, List.append_nil]
  change (continuationScopedMetadataDeclarations ++ continuationPriorMetadataDeclarations) ++ continuationProofSource.declarations = _
  simp only [List.append_assoc]

theorem continuationProof_agreement :
    ProgramAgreementOn continuationProofHeads continuationProofLibrary.runtime CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime := by
  have physical : ProgramAgreementOn continuationProofHeads continuationProofLibrary.runtime
      (CollectionOccurrenceSearchExecution.SelectedNativeSource.sources.foldl
        (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram) :=
    fragment_agreement _ _ continuationProof_physical_equations continuationProof_physical_declarations
      (fun _ supported => supported)
  exact agreement_trans physical
    (agreement_mono (fun _ _ => rfl) CollectionOccurrenceSearchExecution.SelectedNativeSource.PhysicalAgreement.physical_selected_agreement)

/-- The three primitive rows retain their earlier bodies and argument demands. -/
def continuationPrimitiveHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || continuationProofInheritedHeads.contains head

theorem continuationPrimitive_agreement :
    ProgramAgreementOn continuationPrimitiveHeads continuationProofLibrary.runtime
      RuleExecutionProgram.interpretedPremiseProgram := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

/-- The metadata does not assert closure of inherited primitive bodies. -/
theorem continuationProof_not_closed : ¬ ProgramClosed continuationProofHeads continuationProofLibrary.runtime := by
  intro closed
  let row := continuationMetadataBase.equations[0]'(by decide +kernel)
  have member : row ∈ continuationProofLibrary.runtime.equations := by
    apply List.mem_append_left
    exact List.getElem_mem _
  have supported : continuationProofHeads row.head = true := by decide +kernel
  have outside : codeWithin continuationProofHeads row.body = false := by decide +kernel
  have inside := closed.bodies row member supported
  rw [outside] at inside
  cases inside

#print axioms continuationProof_source_quote
#print axioms continuationProofInheritedHeads_derived
#print axioms continuationProof_source_count
#print axioms continuationProof_inherited_count
#print axioms continuationProof_checked
#print axioms continuationProof_equation_count
#print axioms continuationProof_agreement
#print axioms continuationPrimitive_agreement
#print axioms continuationProof_not_closed

end ContinuationProofMetadata

syntax "recursive_continuation_from_lower% " "[" str,* "] " term:max : term
macro_rules
  | `(recursive_continuation_from_lower% [$names,*] $fact) =>
    `(BridgeKit.transport_call
      CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_closed
      CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_agreement
      (by decide +kernel) (by decide)
      (by rw [← continuationPrimitive_agreement.dispatch _ (by decide +kernel)]; decide +kernel)
      (by decide) [$names,*] (by decide) (by rfl)
      (by
        intro index bounded
        simp only [List.length_cons, List.length_nil] at bounded
        rw [← continuationPrimitive_agreement.demand _ index (by decide +kernel)]
        interval_cases index <;> decide +kernel)
      $fact)

syntax "recursive_continuation_eval" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| recursive_continuation_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call_in continuationProof_checked using continuationProof_agreement; metta_eval [$facts,*] with continuationProof_checked in continuationProof_agreement
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        frameTerm, publicationTerm, preparedTerm,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, $extra,*]))

theorem expansion_state_wire_returns (host : Effects.State) (tasks answers unresolved : Term) :
    PureReturns RuleExecutionProgram.interpretedPremiseProgram [] host
      (apply "gslt:collection-backend:expansion-state"
        [encoded (.application "Some" [.application "PremiseExpansion" [tasks, answers, unresolved]])])
      host (encoded (.application "PremiseState" [tasks, answers, unresolved, .natural 0])) := by
  metta_call RetainedMatchingWire.interpreted_checked
  metta_eval with RetainedMatchingWire.interpreted_checked unfolding
    [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
      CettaWireAtom.encode, CettaWireAtom.encodeMany]

@[metta_head "gslt:collection-continuation:begin"]
theorem begin_returns (host : Effects.State) (request : Request) (footprint : List String)
    (inside : ∀ name ∈ request.source.freeFvarNames, name ∈ footprint) :
    PureReturns library.runtime [] host
      (apply "gslt:collection-continuation:begin"
        [CompleteExecution.environmentValue request.environment (request.environment.free.entriesOn footprint),
          number request.depth, encoded (typesTerm request.bound), encoded (typeTerm request.type),
          number request.index, encoded (InferenceCettaWire.AuthoredRule.rewriteTerm request.rule),
          encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm request.spec),
          encoded (preparedTerm request.prepared)])
      host (encoded (frameTerm request (RecursiveCollectionContinuation.start request))) := by
  have original := CompleteExecution.descent_continue_root_answer_returns host
    request.environment footprint request.depth request.bound request.type request.prepared.source
    request.index request.rule request.spec request.declared request.specified request.admitted
    request.sourceTyped request.prepared.ordinary request.matching.matching
    (captures_free_within request footprint inside) (.done request.goal) []
  have continued := recursive_continuation_from_lower%
    ["environment", "depth", "bound", "type", "source", "index", "rule", "spec", "answer", "tail", "next"]
    original
  have expanded : PureReturns library.runtime [] host
      (apply "gslt:collection-backend:expansion-state"
        [encoded (encodeOption expansionTerm (some request.expansion))])
      host (encoded (stateTerm (RecursiveCollectionContinuation.start request))) := by
    have native := recursive_continuation_from_lower% ["expanded"]
      (expansion_state_wire_returns host
        (encodeList taskTerm request.expansion.tasks)
        (encodeList resultTerm request.expansion.answers)
        (encodeList obligationTerm request.expansion.unresolved))
    simpa only [library, CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime_same,
      expansionTerm, stateTerm, PremiseSchedulerExecution.schedulerExpansionTerm,
      PremiseSchedulerExecution.schedulerStateTerm, RecursiveCollectionContinuation.start, encodeOption] using
      native
  recursive_continuation_eval [continued, expanded] unfolding
    [RecursiveCollectionContinuation.start, Request.expansion, Request.goal,
      CompleteExecution.matcher_answer_term,
      CompleteExecution.environmentValue, PremiseOperationsExecution.GeneralExecution.environmentTerm,
      goalTerm, continuationTerm, typesTerm, typeTerm, patternTerm,
      PremiseOperationsExecution.GeneralExecution.Base.typesTerm,
      encodeList, InferenceCettaWire.encodeList]

private theorem descent_returns (host : Effects.State) (request : Request)
    (footprint : List String) (finiteProvider : request.environment.provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames request.environment.provider, name ∈ footprint)
    (search : State request) (work : Nat)
    (covered : StructuralDescent.Scheduled.stateFreeWithin footprint request.environment request.goal search) :
    PureReturns library.runtime [] host
      (apply "gslt:descent:run"
        [CompleteExecution.environmentValue request.environment (request.environment.free.entriesOn footprint),
          number work, encoded (stateTerm search)])
      host (encoded (stateTerm (run request work search))) := by
  exact recursive_continuation_from_lower% ["environment", "work", "state"]
    (CompleteExecution.descent_run_returns host request.environment finiteProvider
      footprint provider request.goal work search covered)

@[metta_head "gslt:collection-continuation:run"]
theorem run_returns (host : Effects.State) (request : Request) (footprint : List String)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames request.environment.provider, name ∈ footprint)
    (search : State request) (work : Nat)
    (covered : StructuralDescent.Scheduled.stateFreeWithin footprint request.environment request.goal search) :
    PureReturns library.runtime [] host
      (apply "gslt:collection-continuation:run"
        [CompleteExecution.environmentValue request.environment (request.environment.free.entriesOn footprint),
          number work, encoded (frameTerm request search)])
      host (encoded (frameTerm request (run request work search))) := by
  have native := descent_returns host request footprint finiteProvider provider search work covered
  recursive_continuation_eval [native]

@[metta_head "gslt:collection-continuation:results"]
theorem results_returns (host : Effects.State) (request : Request) :
    ∀ results : List (StructuralDescent.Scheduled.Result request.environment request.goal),
    PureReturns library.runtime [] host
      (apply "gslt:collection-continuation:results"
        [encoded (preparedTerm request.prepared),
          encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm request.prepared.ordinary.assignment),
          encoded (encodeList resultTerm results)])
      host (encoded (encodeList (publicationTerm request) (results.filterMap (read? request))))
  | [] => by recursive_continuation_eval
  | result :: rest => by
    have later := results_returns host request rest
    cases result with
    | root trace captured completed history target held =>
      by_cases same : captured = request.prepared.ordinary.assignment
      · simp only [List.filterMap_cons, RecursiveCollectionContinuation.read?, Complete.DeepRoot.read,
          same, beq_self_eq_true, ↓reduceIte]
        recursive_continuation_eval [later] unfolding
          [read?, Complete.DeepRoot.read, CompleteExecution.firingTerm, resultTerm, answerTerm,
            same, RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm_injective.eq_iff, encodeList]
      · have wireNe : RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm captured ≠
            RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm request.prepared.ordinary.assignment :=
          fun equal => same (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm_injective equal)
        simp only [List.filterMap_cons, RecursiveCollectionContinuation.read?, Complete.DeepRoot.read,
          show (captured == request.prepared.ordinary.assignment) = false from beq_eq_false_iff_ne.mpr same,
          Bool.false_eq_true, ↓reduceIte]
        recursive_continuation_eval [later] unfolding
          [read?, Complete.DeepRoot.read, CompleteExecution.firingTerm, resultTerm, answerTerm,
            same, wireNe, RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm_injective.eq_iff, encodeList]

@[metta_head "gslt:collection-continuation:publication"]
theorem publication_returns (host : Effects.State) (request : Request) (search : State request) :
    PureReturns library.runtime [] host
      (apply "gslt:collection-continuation:publication" [encoded (frameTerm request search)])
      host (encoded (encodeList (publicationTerm request) (publication request search))) := by
  have published := results_returns host request search.answers
  recursive_continuation_eval [published] unfolding
    [publication, stateTerm, PremiseSchedulerExecution.schedulerStateTerm,
      CompleteExecution.matcher_answer_term]

/- Canonical collection matching realizes the shared retained premise machine. -/
namespace Canonical

open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL GeneralPremise RuleBinding ScopedRuleMatching
open CanonicalCompare CanonicalCompare.AllNameSupport
open CompleteExecution.Interpreted

theorem canonical_answer_free_within (request : GeneralScopedMatchMachine.Request)
    (machine : RecursiveCollectionHandoff.canonicalMatchingExecution.State)
    (reached : RecursiveCollectionHandoff.canonicalMatchingExecution.Reachable request machine)
    (answer : RecursiveCollectionHandoff.canonicalMatchingExecution.Answer)
    (member : answer ∈ RecursiveCollectionHandoff.canonicalMatchingExecution.answers machine)
    (footprint : List String) (initial : ScopedRuleMatching.assignmentFreeWithin footprint request.initial)
    (target : ∀ name ∈ request.target.freeFvarNames, name ∈ footprint) :
    ScopedRuleMatching.assignmentFreeWithin footprint
      (RecursiveCollectionHandoff.canonicalMatchingExecution.assignment answer) := by
  exact MatchingExecution.answer_free_within
    RecursiveCollectionHandoff.canonical_preservesFreeNames request machine reached answer member
    footprint initial target

#print axioms canonical_answer_free_within

theorem canonical_root_match_returns (host : Effects.State) (names : List String)
    (ordered : CanonicalCompare.NameOrdered names) (environment : Environment) (footprint : List String)
    {outer : StructuralDescent.Scheduled.Goal}
    (frame : StructuralDescent.Scheduled.RootMatchFrame environment outer RecursiveCollectionHandoff.canonicalMatchingExecution)
    (source : ∀ name ∈ frame.source.freeFvarNames, name ∈ footprint)
    (covered : CanonicalCompare.Covered names frame.source) :
    PureReturns CompleteExecution.descentLibrary.runtime [] host (apply "gslt:descent:root-match"
      [encoded (RetainedMatchingWire.interpretedEnvironmentTerm names
        (PremiseOperationsExecution.GeneralExecution.environmentTerm environment (environment.free.entriesOn footprint))),
        encoded (RetainedMatchingWire.Scheduled.taskTerm RetainedMatchingWire.canonicalCodec (.rootMatch frame))]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm RetainedMatchingWire.canonicalCodec)
        (some (StructuralDescent.Scheduled.expandRootMatch environment outer frame)))) := by
  let request : GeneralScopedMatchMachine.Request :=
    ⟨frame.rule, frame.spec, frame.bound.length, .left, [], 0, [], frame.rule.left, frame.source⟩
  let core := PremiseOperationsExecution.GeneralExecution.environmentTerm environment (environment.free.entriesOn footprint)
  apply root_match_returns host environment RecursiveCollectionHandoff.canonicalMatchingExecution RetainedMatchingWire.canonicalCodec
    footprint (RetainedMatchingWire.interpretedEnvironmentTerm names core) frame
    (fun query => CanonicalCompare.Covered names query.target)
    (fun state => RecursiveCollectionMachine.StateCovered names state.2) (CanonicalCompare.Covered names)
    (RetainedMatchingWire.canonical_operations names ordered core)
  · exact RecursiveCollectionExecution.canonical_reachable_covered names ordered request frame.state frame.reachable covered
  · intro answer member
    have captures := canonical_answer_free_within request frame.state frame.reachable answer member footprint
      (by intro entry occurs; cases occurs) source
    exact ConditionalEquationExecution.assignment_free_names_covered footprint _ captures
  · simpa only [RecursiveCollectionExecution.library, CompleteExecution.descentLibrary,
      RetainedMatchingWire.interpreted_runtime, core] using
      RecursiveCollectionExecution.matching_environment_returns host names core

#print axioms canonical_root_match_returns

theorem canonical_target_match_returns (host : Effects.State) (names : List String)
    (ordered : CanonicalCompare.NameOrdered names) (environment : Environment) (footprint : List String)
    {outer : StructuralDescent.Scheduled.Goal}
    (frame : StructuralDescent.Scheduled.TargetMatchFrame environment outer RecursiveCollectionHandoff.canonicalMatchingExecution)
    (initial : ScopedRuleMatching.assignmentFreeWithin footprint frame.call.initial)
    (target : ∀ name ∈ frame.target.freeFvarNames, name ∈ footprint)
    (covered : CanonicalCompare.Covered names frame.target) :
    PureReturns CompleteExecution.descentLibrary.runtime [] host (apply "gslt:descent:target-match"
      [encoded (RetainedMatchingWire.interpretedEnvironmentTerm names
        (PremiseOperationsExecution.GeneralExecution.environmentTerm environment (environment.free.entriesOn footprint))),
        encoded (RetainedMatchingWire.Scheduled.taskTerm RetainedMatchingWire.canonicalCodec (.targetMatch frame))]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm RetainedMatchingWire.canonicalCodec)
        (some (StructuralDescent.Scheduled.expandTargetMatch environment outer frame)))) := by
  let request : GeneralScopedMatchMachine.Request :=
    ⟨frame.call.context.rule, frame.call.context.spec, frame.call.context.bound.length,
      frame.call.context.site 1, [], frame.call.binders.length, frame.call.initial, frame.call.targetSchema, frame.target⟩
  let core := PremiseOperationsExecution.GeneralExecution.environmentTerm environment (environment.free.entriesOn footprint)
  apply target_match_returns host environment RecursiveCollectionHandoff.canonicalMatchingExecution RetainedMatchingWire.canonicalCodec
    footprint (RetainedMatchingWire.interpretedEnvironmentTerm names core) frame
    (fun query => CanonicalCompare.Covered names query.target)
    (fun state => RecursiveCollectionMachine.StateCovered names state.2) (CanonicalCompare.Covered names)
    (RetainedMatchingWire.canonical_operations names ordered core)
  · exact RecursiveCollectionExecution.canonical_reachable_covered names ordered request frame.state frame.reachable covered
  · intro answer member
    have captures := canonical_answer_free_within request frame.state frame.reachable answer member footprint initial target
    exact ConditionalEquationExecution.assignment_free_names_covered footprint _ captures
  · simpa only [RecursiveCollectionExecution.library, CompleteExecution.descentLibrary,
      RetainedMatchingWire.interpreted_runtime, core] using
      RecursiveCollectionExecution.matching_environment_returns host names core

#print axioms canonical_target_match_returns

theorem evaluate_canonical_returns (host : Effects.State) (environment : Environment)
    (names : List String) (ordered : CanonicalCompare.NameOrdered names)
    (footprint : List String) {outer : StructuralDescent.Scheduled.Goal}
    (goal : StructuralDescent.Scheduled.Goal)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation
      RecursiveCollectionHandoff.canonicalMatchingExecution environment goal outer)
    (declarations : ∀ rule ∈ environment.language.terms, rule.label ∈ names)
    (freeNames : ∀ name ∈ footprint, name ∈ names)
    (covered : StructuralDescent.Scheduled.goalFreeWithin footprint goal) :
    PureReturns CompleteExecution.descentLibrary.runtime [] host (apply "gslt:descent:evaluate"
      [encoded (RetainedMatchingWire.interpretedEnvironmentTerm names
        (PremiseOperationsExecution.GeneralExecution.environmentTerm environment
          (environment.free.entriesOn footprint))),
        encoded (CompleteExecution.DescentCodec.goalTerm goal),
        encoded (RetainedMatchingWire.Scheduled.continuationTerm
          RetainedMatchingWire.canonicalCodec tail)]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm
        RetainedMatchingWire.canonicalCodec)
        (some (StructuralDescent.Scheduled.evaluate environment outer goal tail)))) := by
  let core := PremiseOperationsExecution.GeneralExecution.environmentTerm environment
    (environment.free.entriesOn footprint)
  let profile := RetainedMatchingWire.interpretedEnvironmentTerm names core
  refine evaluate_returns host environment RecursiveCollectionHandoff.canonicalMatchingExecution
    RetainedMatchingWire.canonicalCodec footprint profile goal tail
    (fun request => CanonicalCompare.Covered names request.target)
    (fun state => RecursiveCollectionMachine.StateCovered names state.2)
    (CanonicalCompare.Covered names) (RetainedMatchingWire.canonical_operations names ordered core)
    ?_ covered ?_
  · intro depth bound type source index shape rule spec declared specified admitted checked
    cases shape
    apply CanonicalCompare.TypedObjectAlphabet.wellSorted_covered
      (Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_sound checked) declarations
    intro name occurs
    exact freeNames name (covered name occurs)
  · simpa only [RecursiveCollectionExecution.library, CompleteExecution.descentLibrary,
      RetainedMatchingWire.interpreted_runtime, core, profile] using
      RecursiveCollectionExecution.matching_environment_returns host names core

#print axioms evaluate_canonical_returns

theorem canonical_expand_returns (host : Effects.State) (names : List String) (ordered : NameOrdered names)
    (environment : Environment) (request : Query.Request)
    (task : Query.Task environment request RecursiveCollectionHandoff.canonicalMatchingExecution)
    (unregistered : request.relation ∉ environment.provider.dynamicRelations) (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (captures : ∀ frame : Query.ArgumentsFrame environment request RecursiveCollectionHandoff.canonicalMatchingExecution,
      task = .arguments frame → ∀ name ∈ ConditionalEquationExecution.assignmentFreeNames frame.assignment, name ∈ footprint)
    (arguments : ∀ frame : Query.ArgumentsFrame environment request RecursiveCollectionHandoff.canonicalMatchingExecution,
      task = .arguments frame → ∀ schema schemas value values mode modes,
      frame.schemas = schema :: schemas → frame.values = value :: values → frame.modes = mode :: modes →
      Covered names value ∧ (mode = .input → ∀ actual,
        ScopedRuleMatching.instantiateAt? request.context.rule request.context.spec request.context.bound.length
          (request.context.site frame.index) [] 0 frame.assignment schema = some actual → Covered names actual))
    (matching : ∀ frame : Query.MatcherFrame environment request RecursiveCollectionHandoff.canonicalMatchingExecution,
      task = .matcher frame → Covered names frame.query.target) :
    PureReturns CompleteExecution.descentLibrary.runtime [] host (apply "gslt:premise:query-expand-in"
      [encoded (RetainedMatchingWire.interpretedEnvironmentTerm names
        (PremiseOperationsExecution.GeneralExecution.environmentTerm environment (environment.free.entriesOn footprint))),
        encoded (PremiseOperationsExecution.GeneralExecution.queryRequestTerm request),
        PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.taskValue RetainedMatchingWire.canonicalCodec task])
      host (PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.expansionValue RetainedMatchingWire.canonicalCodec (Query.expand environment request task)) := by
  let core := PremiseOperationsExecution.GeneralExecution.environmentTerm environment (environment.free.entriesOn footprint)
  apply PremiseOperationsExecution.GeneralExecution.QueryExecution.Interpreted.expand_returns
    RuleExecutionProgram.interpretedPremiseProgram
    PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.interpreted_agreement
    host environment request RecursiveCollectionHandoff.canonicalMatchingExecution
    RetainedMatchingWire.canonicalCodec task unregistered footprint (RetainedMatchingWire.interpretedEnvironmentTerm names core)
    PremiseOperationsExecution.GeneralExecution.QueryLower.interpreted_operations (fun query => Covered names query.target)
    (fun machine => RecursiveCollectionMachine.StateCovered names machine.2) (Covered names) (RetainedMatchingWire.canonical_operations names ordered core)
    provider captures
  · intro frame same schema schemas value values mode modes schemasFound valuesFound modesFound
    exact arguments frame same schema schemas value values mode modes schemasFound valuesFound modesFound
  · intro frame same
    exact RecursiveCollectionExecution.canonical_reachable_covered names ordered frame.query frame.state
      frame.reachable (matching frame same)
  · simpa only [RecursiveCollectionExecution.library, CompleteExecution.descentLibrary,
      RetainedMatchingWire.interpreted_runtime, core] using
      RecursiveCollectionExecution.matching_environment_returns host names core
  · intro index assignment schema value
    exact PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.query_matching_request_returns
      RuleExecutionProgram.interpretedPremiseProgram
      PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.interpreted_agreement
      PremiseOperationsExecution.GeneralExecution.QueryLower.interpreted_operations
      host request index assignment schema value

#print axioms canonical_expand_returns

theorem canonical_query_returns (host : Effects.State) (names : List String)
    (ordered : CanonicalCompare.NameOrdered names) (environment : Environment) (request : Query.Request)
    (unregistered : request.relation ∉ environment.provider.dynamicRelations) (footprint : List String)
    {outer : StructuralDescent.Scheduled.Goal} (depth : Nat)
    (machine : Query.State environment request RecursiveCollectionHandoff.canonicalMatchingExecution) (cursor : Nat)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation RecursiveCollectionHandoff.canonicalMatchingExecution environment
      (.premise depth request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (captures : ∀ current ∈ machine.agenda,
      ∀ frame : Query.ArgumentsFrame environment request RecursiveCollectionHandoff.canonicalMatchingExecution,
      current = .arguments frame → ∀ name ∈ ConditionalEquationExecution.assignmentFreeNames frame.assignment, name ∈ footprint)
    (arguments : ∀ current ∈ machine.agenda,
      ∀ frame : Query.ArgumentsFrame environment request RecursiveCollectionHandoff.canonicalMatchingExecution,
      current = .arguments frame → ∀ schema schemas value values mode modes,
      frame.schemas = schema :: schemas → frame.values = value :: values → frame.modes = mode :: modes →
      CanonicalCompare.Covered names value ∧ (mode = .input → ∀ actual,
        ScopedRuleMatching.instantiateAt? request.context.rule request.context.spec request.context.bound.length
          (request.context.site frame.index) [] 0 frame.assignment schema = some actual → CanonicalCompare.Covered names actual))
    (matching : ∀ current ∈ machine.agenda,
      ∀ frame : Query.MatcherFrame environment request RecursiveCollectionHandoff.canonicalMatchingExecution,
      current = .matcher frame → CanonicalCompare.Covered names frame.query.target) :
    PureReturns CompleteExecution.descentLibrary.runtime [] host (apply "gslt:descent:query"
      [encoded (RetainedMatchingWire.interpretedEnvironmentTerm names
        (PremiseOperationsExecution.GeneralExecution.environmentTerm environment (environment.free.entriesOn footprint))),
        encoded (RetainedMatchingWire.Scheduled.taskTerm RetainedMatchingWire.canonicalCodec
          (.query depth request machine cursor tail))]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm RetainedMatchingWire.canonicalCodec)
        (some (StructuralDescent.Scheduled.expandQuery environment outer depth request machine cursor tail)))) := by
  apply query_returns host environment RecursiveCollectionHandoff.canonicalMatchingExecution RetainedMatchingWire.canonicalCodec
    (RetainedMatchingWire.interpretedEnvironmentTerm names
      (PremiseOperationsExecution.GeneralExecution.environmentTerm environment (environment.free.entriesOn footprint)))
    depth request machine cursor tail
  intro current member
  exact canonical_expand_returns host names ordered environment request current unregistered footprint
    provider (captures current member) (arguments current member) (matching current member)

#print axioms canonical_query_returns

theorem delivery_targets_covered (environment : Environment) (names footprint : List String)
    (declarations : ∀ rule ∈ environment.language.terms, rule.label ∈ names)
    (included : ∀ name ∈ footprint, name ∈ names)
    {goal outer : StructuralDescent.Scheduled.Goal}
    (result : StructuralDescent.Scheduled.Interpreted.Result
      RecursiveCollectionHandoff.canonicalMatchingExecution environment goal)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation
      RecursiveCollectionHandoff.canonicalMatchingExecution environment goal outer)
    (free : StructuralDescent.Scheduled.resultFreeWithin footprint result) :
    ∀ request ∈ deliveryMatchRequests result tail, Covered names request.target := by
  cases tail <;> try simp [deliveryMatchRequests]
  case stepped depth call tail =>
    cases result with
    | steps index trace captured completed events target earlier valid =>
      intro request member
      rcases List.mem_singleton.mp member with rfl
      exact StructuralDescent.Scheduled.NameSupport.firing_target_covered
        environment declarations included valid free.2.2.2

#print axioms delivery_targets_covered

theorem canonical_query_supported_returns (host : Effects.State) (environment : Environment)
    (names : List String) (ordered : NameOrdered names) (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (unregistered : environment.provider.dynamicRelations = [])
    {outer : StructuralDescent.Scheduled.Goal} (depth : Nat) (request : Query.Request)
    (machine : Query.State environment request RecursiveCollectionHandoff.canonicalMatchingExecution)
    (cursor : Nat)
    (tail : StructuralDescent.Scheduled.Interpreted.Continuation
      RecursiveCollectionHandoff.canonicalMatchingExecution environment
      (.premise depth request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (free : Query.stateFreeWithin footprint environment request machine)
    (spines : SpecificationCovered names request.context.spec)
    (covered : Query.NameSupport.StateCovered (table := names) environment request machine) :
    PureReturns CompleteExecution.descentLibrary.runtime [] host (apply "gslt:descent:query"
      [encoded (RetainedMatchingWire.interpretedEnvironmentTerm names
        (PremiseOperationsExecution.GeneralExecution.environmentTerm environment
          (environment.free.entriesOn footprint))),
        encoded (RetainedMatchingWire.Scheduled.taskTerm RetainedMatchingWire.canonicalCodec
          (.query depth request machine cursor tail))]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm RetainedMatchingWire.canonicalCodec)
        (some (StructuralDescent.Scheduled.expandQuery environment outer depth request machine cursor tail)))) := by
  apply canonical_query_returns host names ordered environment request
    (by simp [unregistered]) footprint depth machine cursor tail provider
  · intro current member frame same
    subst current
    exact ConditionalEquationExecution.assignment_free_names_covered footprint _
      (free.1 (.arguments frame) member).1
  · intro current member frame same schema schemas value values mode modes schemasFound valuesFound modesFound
    subst current
    have frameCovered := covered.1 (.arguments frame) member
    constructor
    · exact frameCovered.2.2 value (by rw [valuesFound]; exact List.mem_cons_self)
    · intro _input actual instantiated
      exact Query.NameSupport.input_actual_covered spines frameCovered schemasFound instantiated
  · intro current member frame same
    subst current
    exact (covered.1 (.matcher frame) member).2.1

#print axioms canonical_query_supported_returns

theorem expand_canonical_supported_returns (host : Effects.State) (environment : Environment)
    (names : List String) (ordered : NameOrdered names) (footprint : List String)
    (declarations : ∀ rule ∈ environment.language.terms, rule.label ∈ names)
    (included : ∀ name ∈ footprint, name ∈ names)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (unregistered : environment.provider.dynamicRelations = [])
    (outer : StructuralDescent.Scheduled.Goal)
    (task : StructuralDescent.Scheduled.Interpreted.Task
      RecursiveCollectionHandoff.canonicalMatchingExecution environment outer)
    (free : StructuralDescent.Scheduled.taskFreeWithin footprint task)
    (covered : StructuralDescent.Scheduled.NameSupport.TaskCovered (table := names) task) :
    PureReturns CompleteExecution.descentLibrary.runtime [] host (apply "gslt:descent:expand"
      [encoded (RetainedMatchingWire.interpretedEnvironmentTerm names
        (PremiseOperationsExecution.GeneralExecution.environmentTerm environment
          (environment.free.entriesOn footprint))),
        encoded (RetainedMatchingWire.Scheduled.taskTerm RetainedMatchingWire.canonicalCodec task)]) host
      (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm RetainedMatchingWire.canonicalCodec)
        (some (StructuralDescent.Scheduled.expand environment outer task)))) := by
  let core := PremiseOperationsExecution.GeneralExecution.environmentTerm environment
    (environment.free.entriesOn footprint)
  let profile := RetainedMatchingWire.interpretedEnvironmentTerm names core
  have view : PureReturns CompleteExecution.descentLibrary.runtime [] host (apply "gslt:premise:matching-environment" [encoded profile]) host
      (encoded core) := by
    simpa only [RecursiveCollectionExecution.library, CompleteExecution.descentLibrary,
      RetainedMatchingWire.interpreted_runtime, core, profile] using
      RecursiveCollectionExecution.matching_environment_returns host names core
  apply expand_of_branch_returns host environment RecursiveCollectionHandoff.canonicalMatchingExecution
    RetainedMatchingWire.canonicalCodec profile outer task
  intro call member
  cases task with
  | evaluate goal tail =>
    simp only [branchCall?, Option.mem_def, Option.some.injEq] at member
    subst call
    exact evaluate_canonical_returns host environment names ordered footprint goal tail declarations included free.1
  | deliver result tail =>
    simp only [branchCall?, Option.mem_def, Option.some.injEq] at member
    subst call
    exact delivered_returns host environment RecursiveCollectionHandoff.canonicalMatchingExecution
      RetainedMatchingWire.canonicalCodec footprint profile result tail
      (fun request => Covered names request.target)
      (fun state => RecursiveCollectionMachine.StateCovered names state.2) (Covered names)
      (RetainedMatchingWire.canonical_operations names ordered core)
      (delivery_targets_covered environment names footprint declarations included result tail free.1)
      (delivery_assignments_free environment footprint result tail free.1) view
  | query depth request machine cursor tail =>
    simp only [branchCall?, Option.mem_def, Option.some.injEq] at member
    subst call
    exact canonical_query_supported_returns host environment names ordered footprint provider unregistered
      depth request machine cursor tail free.2.1 covered.1 covered.2.2.1
  | rootMatch frame =>
    simp only [branchCall?, Option.mem_def, Option.some.injEq] at member
    subst call
    exact canonical_root_match_returns host names ordered environment footprint frame free.1
      (TypedObjectAlphabet.wellSorted_covered frame.sorted declarations
        (fun name member => included name (free.1 name member)))
  | targetMatch frame =>
    simp only [branchCall?, Option.mem_def, Option.some.injEq] at member
    subst call
    exact canonical_target_match_returns host names ordered environment footprint frame free.1.2.1 free.2.2.2.1
      (StructuralDescent.Scheduled.NameSupport.firing_target_covered environment declarations included
        frame.valid free.2.2.2.1)
  | scanChildren depth bound type source limit cursor tail =>
    simp only [branchCall?, Option.not_mem_none] at member

#print axioms expand_canonical_supported_returns

theorem run_canonical_supported_returns (host : Effects.State) (environment : Environment)
    (names : List String) (ordered : NameOrdered names) (footprint : List String)
    (declarations : ∀ rule ∈ environment.language.terms, rule.label ∈ names)
    (included : ∀ name ∈ footprint, name ∈ names)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (unregistered : environment.provider.dynamicRelations = [])
    (templates : ∀ rule ∈ environment.language.rewrites, ∀ premise ∈ rule.premises,
      StructuralDescent.Scheduled.NameSupport.PremiseCovered names premise)
    (specifications : ∀ entry ∈ environment.specifications, SpecificationCovered names entry.2)
    (goal : StructuralDescent.Scheduled.Goal) (fuel : Nat)
    (search : StructuralDescent.Scheduled.State environment goal RecursiveCollectionHandoff.canonicalMatchingExecution)
    (free : StructuralDescent.Scheduled.stateFreeWithin footprint environment goal search)
    (covered : StructuralDescent.Scheduled.NameSupport.StateCovered (table := names) environment goal search) :
    PureReturns CompleteExecution.descentLibrary.runtime [] host (apply "gslt:descent:run"
      [encoded (RetainedMatchingWire.interpretedEnvironmentTerm names
        (PremiseOperationsExecution.GeneralExecution.environmentTerm environment
          (environment.free.entriesOn footprint))), number fuel,
        encoded (RetainedMatchingWire.Scheduled.stateTerm RetainedMatchingWire.canonicalCodec search)]) host
      (encoded (RetainedMatchingWire.Scheduled.stateTerm RetainedMatchingWire.canonicalCodec
        (StructuralDescent.Scheduled.run environment goal fuel search))) := by
  let invariant := fun state : StructuralDescent.Scheduled.State environment goal
      RecursiveCollectionHandoff.canonicalMatchingExecution =>
    StructuralDescent.Scheduled.stateFreeWithin footprint environment goal state ∧
      StructuralDescent.Scheduled.NameSupport.StateCovered (table := names) environment goal state
  have rows : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values :=
    provider_coverage_mono _ _ environment.provider provider (provider_covered_by_own_names environment.provider)
  have dynamic := Query.DynamicOutputsFreeWithin.of_unregistered footprint environment unregistered
  apply run_of_invariant_returns host environment RecursiveCollectionHandoff.canonicalMatchingExecution
    RetainedMatchingWire.canonicalCodec _ goal invariant ?_ ?_ fuel search ⟨free, covered⟩
  · intro state before
    refine ⟨StructuralDescent.Scheduled.tick_free_within
      RecursiveCollectionHandoff.canonical_preservesFreeNames footprint environment goal rows dynamic state before.1, ?_⟩
    have next := StructuralDescent.Scheduled.NameSupport.run_covered
      MatchingExecution.canonical_preservesNames RecursiveCollectionHandoff.canonical_preservesFreeNames
      environment goal declarations included rows dynamic templates specifications 1 state before.1 before.2
    exact next
  · intro state before first member
    have present : first ∈ state.agenda := List.mem_of_mem_head? member
    exact expand_canonical_supported_returns host environment names ordered footprint declarations included provider
      unregistered goal first (before.1.1 first present) (before.2.1 first present)

#print axioms run_canonical_supported_returns

theorem run_canonical_source_returns (host : Effects.State) (environment : Environment)
    (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (fuel : Nat)
    (unregistered : environment.provider.dynamicRelations = []) :
    let footprint := source.freeFvarNames ++ providerFreeNames environment.provider
    let names := StructuralDescent.Scheduled.NameSupport.environmentNameTable environment footprint
    let goal := StructuralDescent.Scheduled.Goal.steps depth bound type source environment.language.rewrites.length
    PureReturns CompleteExecution.descentLibrary.runtime [] host (apply "gslt:descent:run"
      [encoded (RetainedMatchingWire.interpretedEnvironmentTerm names
        (PremiseOperationsExecution.GeneralExecution.environmentTerm environment
          (environment.free.entriesOn footprint))), number fuel,
        encoded (RetainedMatchingWire.Scheduled.stateTerm RetainedMatchingWire.canonicalCodec
          (StructuralDescent.Scheduled.start environment goal RecursiveCollectionHandoff.canonicalMatchingExecution))]) host
      (encoded (RetainedMatchingWire.Scheduled.stateTerm RetainedMatchingWire.canonicalCodec
        (StructuralDescent.Scheduled.run environment goal fuel
          (StructuralDescent.Scheduled.start environment goal
            RecursiveCollectionHandoff.canonicalMatchingExecution)))) := by
  dsimp only
  let footprint := source.freeFvarNames ++ providerFreeNames environment.provider
  apply run_canonical_supported_returns host environment
    (StructuralDescent.Scheduled.NameSupport.environmentNameTable environment footprint)
    (StructuralDescent.Scheduled.NameSupport.environment_table_ordered environment footprint)
    footprint
    (StructuralDescent.Scheduled.NameSupport.environment_table_declarations environment footprint)
    (StructuralDescent.Scheduled.NameSupport.environment_table_footprint environment footprint)
    (fun _ member => List.mem_append_right _ member) unregistered
    (StructuralDescent.Scheduled.NameSupport.environment_table_templates environment footprint)
    (StructuralDescent.Scheduled.NameSupport.environment_table_specifications environment footprint)
    (.steps depth bound type source environment.language.rewrites.length) fuel
    (StructuralDescent.Scheduled.start environment _ RecursiveCollectionHandoff.canonicalMatchingExecution)
  · exact StructuralDescent.Scheduled.start_free_within footprint environment _
      (fun _ member => List.mem_append_left _ member)
  · exact StructuralDescent.Scheduled.NameSupport.start_covered environment _ trivial

#print axioms run_canonical_source_returns

theorem finish_canonical_source_complete (host : Effects.State) (environment : Environment)
    (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (unregistered : environment.provider.dynamicRelations = [])
    (wanted : StructuralDescent.Scheduled.Interpreted.Result
      RecursiveCollectionHandoff.canonicalMatchingExecution environment
      (.steps depth bound type source environment.language.rewrites.length))
    (ordered : wanted.ordered = true) :
    let footprint := source.freeFvarNames ++ providerFreeNames environment.provider
    let names := StructuralDescent.Scheduled.NameSupport.environmentNameTable environment footprint
    let goal := StructuralDescent.Scheduled.Goal.steps depth bound type source environment.language.rewrites.length
    let work := (StructuralDescent.Scheduled.treeStart RecursiveCollectionHandoff.canonicalCursorCost
      environment goal).cost
    let finished := StructuralDescent.Scheduled.finishWith RecursiveCollectionHandoff.canonicalCursorCost
      environment goal
    PureReturns CompleteExecution.descentLibrary.runtime [] host (apply "gslt:descent:run"
      [encoded (RetainedMatchingWire.interpretedEnvironmentTerm names
        (PremiseOperationsExecution.GeneralExecution.environmentTerm environment
          (environment.free.entriesOn footprint))), number work,
        encoded (RetainedMatchingWire.Scheduled.stateTerm RetainedMatchingWire.canonicalCodec
          (StructuralDescent.Scheduled.start environment goal
            RecursiveCollectionHandoff.canonicalMatchingExecution))]) host
      (encoded (RetainedMatchingWire.Scheduled.stateTerm RetainedMatchingWire.canonicalCodec finished)) ∧
      finished.agenda = [] ∧ wanted ∈ finished.answers := by
  dsimp only
  refine ⟨run_canonical_source_returns host environment depth bound type source _ unregistered, ?_, ?_⟩
  · exact StructuralDescent.Scheduled.finishWith_settled
      RecursiveCollectionHandoff.canonicalCursorCost environment _
  · exact StructuralDescent.Scheduled.finishWith_contains
      RecursiveCollectionHandoff.canonicalCursorCost RecursiveCollectionHandoff.canonicalCursorLaws
      RecursiveCollectionHandoff.canonical_answer_representation environment _ wanted ordered

#print axioms finish_canonical_source_complete

theorem resumed_canonical_source_returns (host : Effects.State) (environment : Environment)
    (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (first second : Nat) (unregistered : environment.provider.dynamicRelations = []) :
    let footprint := source.freeFvarNames ++ providerFreeNames environment.provider
    let names := StructuralDescent.Scheduled.NameSupport.environmentNameTable environment footprint
    let goal := StructuralDescent.Scheduled.Goal.steps depth bound type source environment.language.rewrites.length
    let initial := StructuralDescent.Scheduled.start environment goal
      RecursiveCollectionHandoff.canonicalMatchingExecution
    PureReturns CompleteExecution.descentLibrary.runtime [] host (apply "gslt:descent:run"
      [encoded (RetainedMatchingWire.interpretedEnvironmentTerm names
        (PremiseOperationsExecution.GeneralExecution.environmentTerm environment
          (environment.free.entriesOn footprint))), number second,
        encoded (RetainedMatchingWire.Scheduled.stateTerm RetainedMatchingWire.canonicalCodec
          (StructuralDescent.Scheduled.run environment goal first initial))]) host
      (encoded (RetainedMatchingWire.Scheduled.stateTerm RetainedMatchingWire.canonicalCodec
        (StructuralDescent.Scheduled.run environment goal (first + second) initial))) := by
  dsimp only
  let footprint := source.freeFvarNames ++ providerFreeNames environment.provider
  let names := StructuralDescent.Scheduled.NameSupport.environmentNameTable environment footprint
  let goal := StructuralDescent.Scheduled.Goal.steps depth bound type source environment.language.rewrites.length
  let initial := StructuralDescent.Scheduled.start environment goal
    RecursiveCollectionHandoff.canonicalMatchingExecution
  have declarations := StructuralDescent.Scheduled.NameSupport.environment_table_declarations environment footprint
  have included := StructuralDescent.Scheduled.NameSupport.environment_table_footprint environment footprint
  have provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint :=
    fun _ member => List.mem_append_right _ member
  have rows := provider_coverage_mono _ _ environment.provider provider
    (provider_covered_by_own_names environment.provider)
  have dynamic := Query.DynamicOutputsFreeWithin.of_unregistered footprint environment unregistered
  have free : StructuralDescent.Scheduled.stateFreeWithin footprint environment goal initial :=
    StructuralDescent.Scheduled.start_free_within footprint environment goal
      (fun _ member => List.mem_append_left _ member)
  have covered : StructuralDescent.Scheduled.NameSupport.StateCovered
      (table := names) environment goal initial :=
    StructuralDescent.Scheduled.NameSupport.start_covered environment goal trivial
  have nextFree := StructuralDescent.Scheduled.run_free_within
    RecursiveCollectionHandoff.canonical_preservesFreeNames footprint environment goal rows dynamic first initial free
  have nextCovered := StructuralDescent.Scheduled.NameSupport.run_covered
    MatchingExecution.canonical_preservesNames RecursiveCollectionHandoff.canonical_preservesFreeNames
    environment goal declarations included rows dynamic
    (StructuralDescent.Scheduled.NameSupport.environment_table_templates environment footprint)
    (StructuralDescent.Scheduled.NameSupport.environment_table_specifications environment footprint)
    first initial free covered
  have resumed := run_canonical_supported_returns host environment names
    (StructuralDescent.Scheduled.NameSupport.environment_table_ordered environment footprint)
    footprint declarations included provider unregistered
    (StructuralDescent.Scheduled.NameSupport.environment_table_templates environment footprint)
    (StructuralDescent.Scheduled.NameSupport.environment_table_specifications environment footprint)
    goal second (StructuralDescent.Scheduled.run environment goal first initial) nextFree nextCovered
  simpa only [StructuralDescent.Scheduled.run_add] using resumed

#print axioms resumed_canonical_source_returns

end Canonical

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.checked

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.begin_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.run_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.results_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.publication_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.Canonical.canonical_answer_free_within

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.Canonical.canonical_root_match_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.Canonical.canonical_target_match_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.Canonical.evaluate_canonical_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.Canonical.canonical_expand_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.Canonical.canonical_query_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.Canonical.delivery_targets_covered

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.Canonical.canonical_query_supported_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.Canonical.expand_canonical_supported_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.Canonical.run_canonical_supported_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.Canonical.run_canonical_source_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.Canonical.finish_canonical_source_complete

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.Canonical.resumed_canonical_source_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.expansion_state_wire_returns


namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.Canonical.SelectedPostmatch

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics Eval BridgeKit WireKit

private local instance equationEq : DecidableEq SpaceSemantics.Equation := by
  intro left right
  apply decidable_of_iff (left.head = right.head ∧ left.arguments = right.arguments ∧ left.body = right.body)
  constructor
  · rintro ⟨head, arguments, body⟩
    cases left
    cases right
    cases head
    cases arguments
    cases body
    rfl
  · intro same
    cases same
    exact ⟨rfl, rfl, rfl⟩

/-- Actual source rows in their retained order; this view is proof metadata. -/
def viewProgram : Program where
  equations :=
    [(RuleExecutionProgram.interpretedPremiseSupportSources[1]'(by decide +kernel)).program.equations[4]'(by decide +kernel),
      (RuleExecutionProgram.interpretedPremiseSupportSources[8]'(by decide +kernel)).program.equations[5]'(by decide +kernel)] ++
    CollectionOccurrenceSearchExecution.SelectedNativeSource.continuationSource.program.equations ++
    [RuleExecutionProgram.scopedProgram.equations[229]'(by decide +kernel)]
  declarations :=
    [(RuleExecutionProgram.interpretedPremiseSupportSources[1]'(by decide +kernel)).program.declarations[4]'(by decide +kernel),
      (RuleExecutionProgram.interpretedPremiseSupportSources[8]'(by decide +kernel)).program.declarations[5]'(by decide +kernel)] ++
    CollectionOccurrenceSearchExecution.SelectedNativeSource.continuationSource.program.declarations ++
    [RuleExecutionProgram.scopedProgram.declarations[229]'(by decide +kernel)]

def viewLibrary : Library := ⟨{equations := [], declarations := []}, viewProgram, ["gslt:"]⟩
def lowerNames : List String := ["gslt:descent:continue-root-answer",
  "gslt:collection-backend:expansion-state", "gslt:premise:matching-environment"]
def lowerViewHeads (head : String) : Bool := !head.startsWith "gslt:" || lowerNames.contains head
def viewHeads (head : String) : Bool :=
  lowerViewHeads head || head.startsWith "gslt:collection-continuation:"

theorem view_checked : viewLibrary.check = true := by decide +kernel

theorem view_agreement : ProgramAgreementOn viewHeads viewLibrary.runtime
    CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

theorem lower_view_agreement : ProgramAgreementOn lowerViewHeads viewLibrary.runtime
    RuleExecutionProgram.interpretedPremiseProgram := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

theorem view_equation_count : viewLibrary.runtime.equations.length = 7 := by decide +kernel

theorem interpreted_environment_wire_returns (host : Effects.State) (names : List String) (core : Term) :
    PureReturns RuleExecutionProgram.interpretedPremiseProgram [] host
      (apply "gslt:premise:matching-environment"
        [encoded (RetainedMatchingWire.interpretedEnvironmentTerm names core)])
      host (encoded core) := by
  metta_call_in view_checked using lower_view_agreement
  metta_eval with view_checked in lower_view_agreement unfolding
    [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
      RetainedMatchingWire.interpretedEnvironmentTerm, encodeList,
      CettaWireAtom.encode, CettaWireAtom.encodeMany]

theorem native_expansion_state_wire_returns (host : Effects.State) (tasks answers unresolved : Term) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:collection-backend:expansion-state"
        [encoded (.application "Some" [.application "PremiseExpansion" [tasks, answers, unresolved]])])
      host (encoded (.application "PremiseState" [tasks, answers, unresolved, .natural 0])) := by
  apply transport_call CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_closed CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_agreement
    (by decide +kernel) (by decide +kernel)
    (by rw [← lower_view_agreement.dispatch _ (by decide +kernel)]; decide +kernel) (by decide +kernel)
    ["expanded"] (by decide +kernel)
    (by rfl) (by
      intro index bound
      have one : index = 0 := by simpa using bound
      subst index
      rw [← lower_view_agreement.demand _ 0 (by decide +kernel)]
      decide +kernel)
  exact RecursiveCollectionContinuationExecution.expansion_state_wire_returns host tasks answers unresolved

open RecursiveCollectionContinuation

def environmentTerm (request : Request) (names footprint : List String) : Term :=
  RetainedMatchingWire.interpretedEnvironmentTerm names
    (PremiseOperationsExecution.GeneralExecution.environmentTerm request.environment
      (request.environment.free.entriesOn footprint))

def frameTermWith (codec : RetainedMatchingWire.MatchingCodec RecursiveCollectionHandoff.canonicalMatchingExecution)
    (request : Request) (search : RecursiveCollectionContinuation.Canonical.State request) : Term :=
  .application "RecursiveCollectionContinuation"
    [RecursiveCollectionHandoffExecution.preparedTerm request.prepared,
      RetainedMatchingWire.Scheduled.stateTerm codec search]

theorem continue_original_answer_returns (host : Effects.State) (request : Request)
    (codec : RetainedMatchingWire.MatchingCodec RecursiveCollectionHandoff.canonicalMatchingExecution)
    (names footprint : List String) (inside : ∀ name ∈ request.source.freeFvarNames, name ∈ footprint)
    (seed : RecursiveCollectionContinuation.Canonical.Seed request) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:descent:continue-root-answer"
        [encoded (environmentTerm request names footprint), number request.depth,
          encoded (CompleteExecution.DescentCodec.typesTerm request.bound),
          encoded (InferenceCettaWire.AuthoredRule.typeTerm request.type),
          encoded (InferenceCettaWire.encodePattern request.prepared.source), number request.index,
          encoded (InferenceCettaWire.AuthoredRule.rewriteTerm request.rule),
          encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm request.spec),
          encoded (RetainedMatchingWire.matcherAnswerTerm codec request.answer),
          encoded (RetainedMatchingWire.Scheduled.continuationTerm codec
            (environment := request.environment) (.done request.goal)),
          encoded (encodeList (RetainedMatchingWire.Scheduled.taskTerm codec
            (environment := request.environment) (outer := request.goal)) [])])
      host (encoded (encodeOption (RetainedMatchingWire.Scheduled.expansionTerm codec)
        (some (RecursiveCollectionContinuation.Canonical.expansion request seed)))) := by
  have captures := RecursiveCollectionContinuation.captures_free_within request footprint inside
  rw [request.matching.assignment] at captures
  have original := CompleteExecution.Interpreted.continue_root_answer_returns host request.environment
    RecursiveCollectionHandoff.canonicalMatchingExecution codec footprint
    (environmentTerm request names footprint) request.depth request.bound request.type request.prepared.source
    request.index request.rule request.spec request.declared request.specified request.admitted request.sourceTyped
    request.answer seed (ConditionalEquationExecution.assignment_free_names_covered footprint _ captures)
    (.done request.goal) [] (interpreted_environment_wire_returns host names _)
  apply transport_call CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_closed CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_agreement
    (by decide +kernel) (by decide +kernel)
    (by rw [← lower_view_agreement.dispatch _ (by decide +kernel)]; decide +kernel) (by decide +kernel)
    ["environment", "depth", "bound", "type", "source", "index", "rule", "spec", "answer", "tail", "next"]
    (by decide +kernel) (by rfl)
    (by
      intro index bound
      simp only [List.length_cons, List.length_nil] at bound
      rw [← lower_view_agreement.demand _ index (by decide +kernel)]
      interval_cases index <;> decide +kernel)
  exact original

theorem begin_returns (host : Effects.State) (request : Request)
    (codec : RetainedMatchingWire.MatchingCodec RecursiveCollectionHandoff.canonicalMatchingExecution)
    (choice : codec.choiceTerm = RecursiveCollectionExecution.eventTerm)
    (names footprint : List String) (inside : ∀ name ∈ request.source.freeFvarNames, name ∈ footprint)
    (seed : RecursiveCollectionContinuation.Canonical.Seed request) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:collection-continuation:begin"
        [encoded (environmentTerm request names footprint), number request.depth,
          encoded (CompleteExecution.DescentCodec.typesTerm request.bound),
          encoded (InferenceCettaWire.AuthoredRule.typeTerm request.type), number request.index,
          encoded (InferenceCettaWire.AuthoredRule.rewriteTerm request.rule),
          encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm request.spec),
          encoded (RecursiveCollectionHandoffExecution.preparedTerm request.prepared)])
      host (encoded (frameTermWith codec request
        (RecursiveCollectionContinuation.Canonical.start request seed))) := by
  have continued := continue_original_answer_returns host request codec names footprint inside seed
  have expanded := native_expansion_state_wire_returns host
    (encodeList (RetainedMatchingWire.Scheduled.taskTerm codec)
      (RecursiveCollectionContinuation.Canonical.expansion request seed).tasks)
    (encodeList (RetainedMatchingWire.Scheduled.resultTerm codec)
      (RecursiveCollectionContinuation.Canonical.expansion request seed).answers)
    (encodeList CompleteExecution.DescentCodec.obligationTerm
      (RecursiveCollectionContinuation.Canonical.expansion request seed).unresolved)
  metta_call_in view_checked using view_agreement
  metta_eval [continued, expanded] with view_checked in view_agreement unfolding
    [Library.bind, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
      environmentTerm, frameTermWith, RecursiveCollectionHandoffExecution.preparedTerm,
      RetainedMatchingWire.interpretedEnvironmentTerm, RetainedMatchingWire.matcherAnswerTerm,
      RecursiveCollectionHandoff.canonicalMatchingExecution,
      RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm,
      RetainedMatchingWire.Scheduled.continuationTerm, RetainedMatchingWire.Scheduled.expansionTerm,
      RetainedMatchingWire.Scheduled.stateTerm, CompleteExecution.DescentCodec.typesTerm,
      CompleteExecution.DescentCodec.goalTerm, PremiseSchedulerExecution.schedulerExpansionTerm,
      PremiseSchedulerExecution.schedulerStateTerm, RecursiveCollectionContinuation.Canonical.start,
      RecursiveCollectionContinuation.Request.goal, choice, request.matching.assignment, request.matching.history,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, encodeList, encodeOption,
      InferenceCettaWire.encodeList]

#print axioms view_checked
#print axioms view_agreement
#print axioms lower_view_agreement
#print axioms view_equation_count
#print axioms interpreted_environment_wire_returns
#print axioms native_expansion_state_wire_returns
#print axioms continue_original_answer_returns
#print axioms begin_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.Canonical.SelectedPostmatch


namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.Canonical.SelectedPostmatch
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise RecursiveCollectionContinuation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics Eval BridgeKit WireKit
def publicationTermWith
    (codec : RetainedMatchingWire.MatchingCodec RecursiveCollectionHandoff.canonicalMatchingExecution)
    (request : Request) (firing : RecursiveCollectionContinuation.Canonical.Firing) : Term :=
  .application "RecursiveCollectionContinued"
    [RecursiveCollectionHandoffExecution.preparedTerm request.prepared,
      CompleteExecution.firingTermWith codec.choiceTerm firing]

theorem results_returns (host : Effects.State) (request : Request)
    (codec : RetainedMatchingWire.MatchingCodec RecursiveCollectionHandoff.canonicalMatchingExecution) :
    ∀ results : List (StructuralDescent.Scheduled.Interpreted.Result
      RecursiveCollectionHandoff.canonicalMatchingExecution request.environment request.goal),
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:collection-continuation:results"
        [encoded (RecursiveCollectionHandoffExecution.preparedTerm request.prepared),
          encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm request.answer.assignment),
          encoded (encodeList (RetainedMatchingWire.Scheduled.resultTerm codec) results)])
      host (encoded (encodeList (publicationTermWith codec request)
        (results.filterMap (RecursiveCollectionContinuation.Canonical.read? request))))
  | [] => by
    metta_call_in view_checked using view_agreement
    metta_eval with view_checked in view_agreement unfolding
      [Library.bind, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?, encodeList,
        CettaWireAtom.encode, CettaWireAtom.encodeMany]
  | result :: rest => by
    have later := results_returns host request codec rest
    cases result with
    | root trace captured completed history target held =>
      by_cases same : captured = request.answer.assignment
      · simp only [List.filterMap_cons, RecursiveCollectionContinuation.Canonical.read?, Complete.DeepRoot.readIn,
          same, beq_self_eq_true, ↓reduceIte]
        metta_call_in view_checked using view_agreement
        metta_eval [later] with view_checked in view_agreement unfolding
          [Library.bind, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
            Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
            Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
            publicationTermWith, CompleteExecution.firingTermWith,
            RetainedMatchingWire.Scheduled.resultTerm, RetainedMatchingWire.Scheduled.answerTerm,
            CompleteExecution.DescentCodec.assignmentTerm, CompleteExecution.DescentCodec.patternTerm,
            same, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany]
      · have wireNe : RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm captured ≠
            RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm request.answer.assignment :=
          fun equal => same (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm_injective equal)
        simp only [List.filterMap_cons, RecursiveCollectionContinuation.Canonical.read?, Complete.DeepRoot.readIn,
          show (captured == request.answer.assignment) = false from beq_eq_false_iff_ne.mpr same,
          Bool.false_eq_true, ↓reduceIte]
        metta_call_in view_checked using view_agreement
        metta_eval [later] with view_checked in view_agreement unfolding
          [Library.bind, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
            Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
            Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
            publicationTermWith, CompleteExecution.firingTermWith,
            RetainedMatchingWire.Scheduled.resultTerm, RetainedMatchingWire.Scheduled.answerTerm,
            CompleteExecution.DescentCodec.assignmentTerm, CompleteExecution.DescentCodec.patternTerm,
            same, wireNe, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany]

theorem publication_returns (host : Effects.State) (request : Request)
    (codec : RetainedMatchingWire.MatchingCodec RecursiveCollectionHandoff.canonicalMatchingExecution)
    (search : RecursiveCollectionContinuation.Canonical.State request) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:collection-continuation:publication" [encoded (frameTermWith codec request search)])
      host (encoded (encodeList (publicationTermWith codec request)
        (RecursiveCollectionContinuation.Canonical.publication request search))) := by
  have published := results_returns host request codec search.answers
  metta_call_in view_checked using view_agreement
  metta_eval [published] with view_checked in view_agreement unfolding
    [Library.bind, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
      frameTermWith, publicationTermWith, RecursiveCollectionHandoffExecution.preparedTerm,
      RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm,
      RetainedMatchingWire.Scheduled.stateTerm, PremiseSchedulerExecution.schedulerStateTerm,
      RecursiveCollectionContinuation.Canonical.publication, request.matching.assignment,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, encodeList]

#print axioms results_returns
#print axioms publication_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.Canonical.SelectedPostmatch


namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.Canonical.SelectedPostmatch
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise RecursiveCollectionContinuation CanonicalCompare
open SpaceSemantics Eval BridgeKit WireKit
open CanonicalCompare.AllNameSupport

private local instance runEquationEq : DecidableEq SpaceSemantics.Equation := by
  intro left right
  apply decidable_of_iff (left.head = right.head ∧ left.arguments = right.arguments ∧ left.body = right.body)
  constructor
  · rintro ⟨head, arguments, body⟩
    cases left
    cases right
    cases head
    cases arguments
    cases body
    rfl
  · intro same
    cases same
    exact ⟨rfl, rfl, rfl⟩

/-- Only the unchanged run bodies are used from the inherited continuation metadata. -/
def runHeads (head : String) : Bool := !head.startsWith "gslt:" ||
  ["gslt:descent:run", "gslt:collection-continuation:run"].contains head

theorem run_agreement : ProgramAgreementOn runHeads
    RecursiveCollectionContinuationExecution.continuationProofLibrary.runtime
    CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

theorem descent_run_returns (host : Effects.State) (request : Request)
    (names : List String) (ordered : NameOrdered names) (footprint : List String)
    (declarations : ∀ rule ∈ request.environment.language.terms, rule.label ∈ names)
    (included : ∀ name ∈ footprint, name ∈ names)
    (provider : ∀ name ∈ providerFreeNames request.environment.provider, name ∈ footprint)
    (unregistered : request.environment.provider.dynamicRelations = [])
    (templates : ∀ rule ∈ request.environment.language.rewrites, ∀ premise ∈ rule.premises,
      StructuralDescent.Scheduled.NameSupport.PremiseCovered names premise)
    (specifications : ∀ entry ∈ request.environment.specifications, SpecificationCovered names entry.2)
    (search : RecursiveCollectionContinuation.Canonical.State request) (work : Nat)
    (free : StructuralDescent.Scheduled.stateFreeWithin footprint request.environment request.goal search)
    (covered : StructuralDescent.Scheduled.NameSupport.StateCovered (table := names)
      request.environment request.goal search) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:descent:run" [encoded (environmentTerm request names footprint), number work,
        encoded (RetainedMatchingWire.Scheduled.stateTerm RetainedMatchingWire.canonicalCodec search)]) host
      (encoded (RetainedMatchingWire.Scheduled.stateTerm RetainedMatchingWire.canonicalCodec
        (RecursiveCollectionContinuation.Canonical.run request work search))) := by
  have native := RecursiveCollectionContinuationExecution.Canonical.run_canonical_supported_returns host
    request.environment names ordered footprint declarations included provider unregistered templates
    specifications request.goal work search free covered
  have metadata := RecursiveCollectionContinuationExecution.continuationPrimitive_agreement
  apply transport_call CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_closed
    CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_agreement
    (by decide +kernel) (by decide)
    (by rw [← metadata.dispatch _ (by decide +kernel)]; decide +kernel) (by decide)
    ["environment", "work", "state"] (by decide) (by rfl)
    (by
      intro index bounded
      have small : index < 3 := by simpa using bounded
      rw [← metadata.demand _ index (by decide +kernel)]
      interval_cases index <;> decide +kernel)
  simpa only [CompleteExecution.descentLibrary, RetainedMatchingWire.interpreted_runtime,
    environmentTerm, RecursiveCollectionContinuation.Canonical.run] using native

theorem run_returns (host : Effects.State) (request : Request)
    (names : List String) (ordered : NameOrdered names) (footprint : List String)
    (declarations : ∀ rule ∈ request.environment.language.terms, rule.label ∈ names)
    (included : ∀ name ∈ footprint, name ∈ names)
    (provider : ∀ name ∈ providerFreeNames request.environment.provider, name ∈ footprint)
    (unregistered : request.environment.provider.dynamicRelations = [])
    (templates : ∀ rule ∈ request.environment.language.rewrites, ∀ premise ∈ rule.premises,
      StructuralDescent.Scheduled.NameSupport.PremiseCovered names premise)
    (specifications : ∀ entry ∈ request.environment.specifications, SpecificationCovered names entry.2)
    (search : RecursiveCollectionContinuation.Canonical.State request) (work : Nat)
    (free : StructuralDescent.Scheduled.stateFreeWithin footprint request.environment request.goal search)
    (covered : StructuralDescent.Scheduled.NameSupport.StateCovered (table := names)
      request.environment request.goal search) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:collection-continuation:run" [encoded (environmentTerm request names footprint), number work,
        encoded (frameTermWith RetainedMatchingWire.canonicalCodec request search)]) host
      (encoded (frameTermWith RetainedMatchingWire.canonicalCodec request
        (RecursiveCollectionContinuation.Canonical.run request work search))) := by
  have native := descent_run_returns host request names ordered footprint declarations included provider
    unregistered templates specifications search work free covered
  metta_call_in RecursiveCollectionContinuationExecution.continuationProof_checked using run_agreement
  metta_eval [native] with RecursiveCollectionContinuationExecution.continuationProof_checked in run_agreement
    unfolding [frameTermWith, environmentTerm, RetainedMatchingWire.Scheduled.stateTerm,
      PremiseSchedulerExecution.schedulerStateTerm,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
      CettaWireAtom.encode, CettaWireAtom.encodeMany]

/-- The original source determines every finite table obligation for a retained run. -/
theorem seeded_run_returns (host : Effects.State) (request : Request)
    (seed : RecursiveCollectionContinuation.Canonical.Seed request) (work : Nat)
    (unregistered : request.environment.provider.dynamicRelations = []) :
    let footprint := request.source.freeFvarNames ++ providerFreeNames request.environment.provider
    let names := StructuralDescent.Scheduled.NameSupport.environmentNameTable request.environment footprint
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:collection-continuation:run" [encoded (environmentTerm request names footprint), number work,
        encoded (frameTermWith RetainedMatchingWire.canonicalCodec request
          (RecursiveCollectionContinuation.Canonical.start request seed))]) host
      (encoded (frameTermWith RetainedMatchingWire.canonicalCodec request
        (RecursiveCollectionContinuation.Canonical.run request work
          (RecursiveCollectionContinuation.Canonical.start request seed)))) := by
  dsimp only
  let footprint := request.source.freeFvarNames ++ providerFreeNames request.environment.provider
  have ready := RecursiveCollectionContinuation.Canonical.start_ready request seed
  exact run_returns host request _
    (StructuralDescent.Scheduled.NameSupport.environment_table_ordered request.environment footprint) footprint
    (StructuralDescent.Scheduled.NameSupport.environment_table_declarations request.environment footprint)
    (StructuralDescent.Scheduled.NameSupport.environment_table_footprint request.environment footprint)
    (fun _ member => List.mem_append_right _ member) unregistered
    (StructuralDescent.Scheduled.NameSupport.environment_table_templates request.environment footprint)
    (StructuralDescent.Scheduled.NameSupport.environment_table_specifications request.environment footprint)
    (RecursiveCollectionContinuation.Canonical.start request seed) work ready.1 ready.2

/-- Continuing a retained state gives exactly the uninterrupted state, including histories and work. -/
theorem resumed_seed_returns (host : Effects.State) (request : Request)
    (seed : RecursiveCollectionContinuation.Canonical.Seed request) (first extra : Nat)
    (unregistered : request.environment.provider.dynamicRelations = []) :
    let footprint := request.source.freeFvarNames ++ providerFreeNames request.environment.provider
    let names := StructuralDescent.Scheduled.NameSupport.environmentNameTable request.environment footprint
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:collection-continuation:run" [encoded (environmentTerm request names footprint), number extra,
        encoded (frameTermWith RetainedMatchingWire.canonicalCodec request
          (RecursiveCollectionContinuation.Canonical.run request first
            (RecursiveCollectionContinuation.Canonical.start request seed)))]) host
      (encoded (frameTermWith RetainedMatchingWire.canonicalCodec request
        (RecursiveCollectionContinuation.Canonical.run request (first + extra)
          (RecursiveCollectionContinuation.Canonical.start request seed)))) := by
  dsimp only
  let footprint := request.source.freeFvarNames ++ providerFreeNames request.environment.provider
  have ready := RecursiveCollectionContinuation.Canonical.run_ready request seed first unregistered
  have continued := run_returns host request _
    (StructuralDescent.Scheduled.NameSupport.environment_table_ordered request.environment footprint) footprint
    (StructuralDescent.Scheduled.NameSupport.environment_table_declarations request.environment footprint)
    (StructuralDescent.Scheduled.NameSupport.environment_table_footprint request.environment footprint)
    (fun _ member => List.mem_append_right _ member) unregistered
    (StructuralDescent.Scheduled.NameSupport.environment_table_templates request.environment footprint)
    (StructuralDescent.Scheduled.NameSupport.environment_table_specifications request.environment footprint)
    (RecursiveCollectionContinuation.Canonical.run request first
      (RecursiveCollectionContinuation.Canonical.start request seed)) extra ready.1 ready.2
  have add : RecursiveCollectionContinuation.Canonical.run request (first + extra)
      (RecursiveCollectionContinuation.Canonical.start request seed) =
      RecursiveCollectionContinuation.Canonical.run request extra
        (RecursiveCollectionContinuation.Canonical.run request first
          (RecursiveCollectionContinuation.Canonical.start request seed)) :=
    StructuralDescent.Scheduled.run_add ..
  rw [← add] at continued
  exact continued

theorem initial_publication_returns (host : Effects.State) (request : Request)
    (seed : RecursiveCollectionContinuation.Canonical.Seed request) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:collection-continuation:publication" [encoded (frameTermWith RetainedMatchingWire.canonicalCodec
        request (RecursiveCollectionContinuation.Canonical.start request seed))]) host (encoded (.symbol "LNil")) := by
  have empty : RecursiveCollectionContinuation.Canonical.publication request
      (RecursiveCollectionContinuation.Canonical.start request seed) = [] := by
    simp only [RecursiveCollectionContinuation.Canonical.publication,
      RecursiveCollectionContinuation.Canonical.start,
      RecursiveCollectionContinuation.Canonical.expansion_no_early_answers, List.filterMap_nil]
  have native := publication_returns host request RetainedMatchingWire.canonicalCodec
    (RecursiveCollectionContinuation.Canonical.start request seed)
  rw [empty] at native
  exact native

#print axioms run_agreement
#print axioms descent_run_returns
#print axioms run_returns
#print axioms seeded_run_returns
#print axioms resumed_seed_returns
#print axioms initial_publication_returns
end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution.Canonical.SelectedPostmatch
