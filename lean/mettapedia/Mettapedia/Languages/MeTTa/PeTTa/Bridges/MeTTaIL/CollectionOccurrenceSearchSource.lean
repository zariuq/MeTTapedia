import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceBatchExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceMatcherExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompletePlanWire
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceSearch

/-!
# Native retained occurrence search operations

The search stores the plan needed by the original rule-job receipt readout.
Matching and premise continuations remain in the existing retained machine.
The wire keeps that complete machine beside its derived finished receipt view;
reading publication does not replay validation or change the raw packet log.
Completion checks matcher work, continuation agendas and unresolved obligations
separately. These operations do not select an emission profile.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionOccurrenceBatch CollectionOccurrenceMatcher CanonicalCompare
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.ResumableSearchRunner (Status)
open SpaceSemantics Eval BridgeKit WireKit
open scoped ProgramQuotation

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {sourcePattern : Pattern}

def source : ProgramQuotation.QuotedProgram := SelectedNativeSource.occurrenceSource

def library : Library := SelectedNativeSource.library

theorem checked : library.check = true := SelectedNativeSource.checked

private def proofBase : Program where
  equations :=
    [RuleExecutionProgram.scopedProgram.equations[118]'(by decide +kernel),
     RuleExecutionProgram.scopedProgram.equations[228]'(by decide +kernel),
     (RuleExecutionProgram.interpretedPremiseSupportSources[4]'(by decide +kernel)).program.equations[17]'(by decide +kernel),
     (RuleExecutionProgram.interpretedPremiseSupportSources[10]'(by decide +kernel)).program.equations[11]'(by decide +kernel),
     (RuleExecutionProgram.interpretedPremiseSupportSources[18]'(by decide +kernel)).program.equations[2]'(by decide +kernel),
     (RuleExecutionProgram.interpretedPremiseSupportSources[19]'(by decide +kernel)).program.equations[3]'(by decide +kernel)]
  declarations :=
    [RuleExecutionProgram.scopedProgram.declarations[118]'(by decide +kernel),
     RuleExecutionProgram.scopedProgram.declarations[228]'(by decide +kernel),
     (RuleExecutionProgram.interpretedPremiseSupportSources[4]'(by decide +kernel)).program.declarations[17]'(by decide +kernel),
     (RuleExecutionProgram.interpretedPremiseSupportSources[10]'(by decide +kernel)).program.declarations[11]'(by decide +kernel),
     (RuleExecutionProgram.interpretedPremiseSupportSources[18]'(by decide +kernel)).program.declarations[2]'(by decide +kernel),
     (RuleExecutionProgram.interpretedPremiseSupportSources[19]'(by decide +kernel)).program.declarations[3]'(by decide +kernel)]

private def proofSource : Program where
  equations := source.program.equations.take 12 ++ [RuleExecutionProgram.scopedProgram.equations[229]'(by decide +kernel)]
  declarations := source.program.declarations.take 12 ++ [RuleExecutionProgram.scopedProgram.declarations[229]'(by decide +kernel)]

/-- This finite body/metadata view executes only at the selected target runtime. -/
def proofLibrary : Library := ⟨proofBase, proofSource,
  ["gslt:occurrence-search:", "gslt:premise:matching-environment"]⟩

def proofHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || (proofLibrary.runtime.equations.map (·.head)).contains head

theorem proof_checked : proofLibrary.check = true := by decide +kernel

theorem proof_row_count : proofLibrary.runtime.equations.length = 19 := by decide +kernel

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

theorem proof_agreement : ProgramAgreementOn proofHeads proofLibrary.runtime library.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

def runTerm (table : List (String × TypeExpr))
    (run : CollectionOccurrenceSearch.Run plan bound expected) : Term :=
  .application "RecursiveOccurrenceRun"
    [CompletePlanWire.planTerm plan table bound expected,
      InferenceCettaWire.encodePattern run.source,
      .application "RecursiveOccurrenceState"
        [encodeList CollectionOccurrenceMatcherExecution.laneTerm run.state.matchers,
          CollectionOccurrenceBatchExecution.stateTerm run.state.batch],
      encodeList ScopedRuleJobReadoutExecution.receiptTerm
        (run.state.batch.log.filterMap fun packet => packet.finish? plan bound expected)]

/-- The full retained run wire with an explicit matching codec and receipt projection. -/
def runTermWith {matcher : GeneralPremise.MatchingExecution}
    (codec : RetainedMatchingWire.MatchingCodec matcher) (planWire : Term)
    (finish : Publication matcher.Choice → Option (GeneralRuleJobs.Receipt matcher.Choice))
    (run : CollectionOccurrenceSearch.Run plan bound expected matcher) : Term :=
  .application "RecursiveOccurrenceRun"
    [planWire, InferenceCettaWire.encodePattern run.source,
      .application "RecursiveOccurrenceState"
        [encodeList CollectionOccurrenceMatcherExecution.laneTerm run.state.matchers,
          CollectionOccurrenceBatchExecution.stateTermWith codec run.state.batch],
      encodeList (ScopedRuleJobReadoutExecution.receiptTermWith codec.choiceTerm)
        (run.state.batch.log.filterMap finish)]

theorem runTermWith_ordinary (table : List (String × TypeExpr))
    (run : CollectionOccurrenceSearch.Run plan bound expected) :
    runTermWith RetainedMatchingWire.ordinaryCodec
      (CompletePlanWire.planTerm plan table bound expected)
      (fun packet => packet.finish? plan bound expected) run = runTerm table run := by
  unfold runTermWith runTerm
  rw [CollectionOccurrenceBatchExecution.stateTermWith_ordinary]
  have receipts : ScopedRuleJobReadoutExecution.receiptTermWith RetainedMatchingWire.ordinaryCodec.choiceTerm =
      ScopedRuleJobReadoutExecution.receiptTerm :=
    funext ScopedRuleJobReadoutExecution.receiptTermWith_ordinary
  rw [receipts]

def statusAtom : Status → Atom
  | .complete => .symbol "SearchComplete"
  | .blocked => .symbol "SearchBlocked"
  | .pending => .symbol "SearchPending"

@[local simp] private theorem opaque_match_variable
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (name : String) (value : Atom) :
    SpaceSemantics.matchValue bindings (.var name) value =
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom bindings (.var name) value := by
  cases value <;> simp [SpaceSemantics.matchValue]

syntax "occurrence_search_eval" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
syntax "occurrence_search_eval" " using " "(" term ")" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| occurrence_search_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) =>
      `(tactic| occurrence_search_eval using (proof_agreement) $[[$facts,*]]? $[unfolding [$extra,*]]?)
  | `(tactic| occurrence_search_eval using ($agreement) $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic|
      (metta_call_in proof_checked using $agreement
       metta_eval [$facts,*] with proof_checked in $agreement
        unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
          Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, opaque_match_variable, $extra,*]))

theorem publication_wire_returns (program : Program)
    (agreement : ProgramAgreementOn proofHeads proofLibrary.runtime program)
    (host : Effects.State) (planWire sourceWire stateWire published : Term) :
    PureReturns program [] host
      (apply "gslt:occurrence-search:publication"
        [encoded (.application "RecursiveOccurrenceRun" [planWire, sourceWire, stateWire, published])])
      host (encoded published) := by
  occurrence_search_eval using (agreement)


/-- The independently proved canonical primitive is preserved by the closed lower fragment. -/
theorem canon_lower_returns (host : Effects.State) (names : List String) (ordered : NameOrdered names)
    (pattern : Pattern) (covered : Covered names pattern) :
    PureReturns library.runtime [] host
      (apply "gslt:canon:canon" [CompleteExecution.tableValue names,
        encoded (InferenceCettaWire.encodePattern pattern)])
      host (encoded (InferenceCettaWire.encodePattern (CanonicalBags.canon pattern))) := by
  refine transport_call SelectedNativeSource.lower_closed SelectedNativeSource.lower_agreement
    (head := "gslt:canon:canon") (by decide +kernel) (by decide) ?_ (by decide)
    ["names", "pattern"] (by decide) (by rfl) ?_
    (CompleteExecution.canon_returns host ordered pattern covered)
  · change RuleExecutionProgram.interpretedPremiseProgram.equations.any (·.head == "gslt:canon:canon") = true
    rw [← CompleteExecution.canonicalProof_agreement.dispatch "gslt:canon:canon" (by decide +kernel)]
    decide +kernel
  · intro index bounded
    have small : index < 2 := by simpa using bounded
    interval_cases index <;>
      rw [← CompleteExecution.canonicalProof_agreement.demand "gslt:canon:canon" _ (by decide +kernel)] <;>
      decide +kernel

private theorem complete_lower_returns (host : Effects.State) (machine : RecursiveCollectionMachine.State) :
    PureReturns library.runtime [] host
      (apply "gslt:recursive-collection:complete" [encoded (RecursiveCollectionExecution.stateTerm machine)])
      host (Effects.boolean (RecursiveCollectionMachine.complete machine)) := by
  refine transport_call SelectedNativeSource.lower_closed SelectedNativeSource.lower_agreement
    (head := "gslt:recursive-collection:complete") (by decide +kernel) (by decide) ?_ (by decide)
    ["state"] (by decide) (by rfl) ?_
    (RecursiveCollectionExecution.complete_returns host machine)
  · change RuleExecutionProgram.interpretedPremiseProgram.equations.any (·.head == "gslt:recursive-collection:complete") = true
    rw [← RecursiveCollectionExecution.recursiveProof_agreement.dispatch "gslt:recursive-collection:complete" (by decide +kernel)]
    decide +kernel
  · intro index bounded
    have small : index < 1 := by simpa using bounded
    interval_cases index
    rw [← RecursiveCollectionExecution.recursiveProof_agreement.demand "gslt:recursive-collection:complete" 0 (by decide +kernel)]
    decide +kernel

@[metta_head "gslt:occurrence-search:lanes-complete"]
theorem lanes_complete_returns (host : Effects.State) :
    ∀ lanes : List (Lane plan bound expected sourcePattern),
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-search:lanes-complete"
        [encoded (encodeList CollectionOccurrenceMatcherExecution.laneTerm lanes)])
      host (Effects.boolean (lanes.all fun lane => RecursiveCollectionMachine.complete lane.state))
  | [] => by occurrence_search_eval unfolding [encodeList]
  | lane :: lanes => by
    have complete := complete_lower_returns host lane.state
    have later := lanes_complete_returns host lanes
    cases done : RecursiveCollectionMachine.complete lane.state <;>
      occurrence_search_eval [complete, later] unfolding
        [CollectionOccurrenceMatcherExecution.laneTerm, encodeList, List.all_cons, done]

@[metta_head "gslt:occurrence-search:frames-idle"]
theorem frames_idle_returns (host : Effects.State) :
    ∀ frames : List (Frame plan bound expected sourcePattern),
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-search:frames-idle"
        [encoded (encodeList CollectionOccurrenceBatchExecution.frameTerm frames)])
      host (Effects.boolean (frames.all fun frame => frame.state.agenda.isEmpty))
  | [] => by occurrence_search_eval unfolding [encodeList]
  | frame :: frames => by
    have later := frames_idle_returns host frames
    cases agenda : frame.state.agenda <;>
      simp only [List.all_cons, agenda, List.isEmpty_nil, List.isEmpty_cons, Bool.true_and, Bool.false_and] <;>
      occurrence_search_eval [later] unfolding
        [CollectionOccurrenceBatchExecution.frameTerm, RecursiveCollectionContinuationExecution.frameTerm,
          CompleteExecution.DescentCodec.stateTerm, PremiseSchedulerExecution.schedulerStateTerm,
          encodeList, List.all_cons, agenda]

@[metta_head "gslt:occurrence-search:frames-resolved"]
theorem frames_resolved_returns (host : Effects.State) :
    ∀ frames : List (Frame plan bound expected sourcePattern),
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-search:frames-resolved"
        [encoded (encodeList CollectionOccurrenceBatchExecution.frameTerm frames)])
      host (Effects.boolean (frames.all fun frame => frame.state.unresolved.isEmpty))
  | [] => by occurrence_search_eval unfolding [encodeList]
  | frame :: frames => by
    have later := frames_resolved_returns host frames
    cases unresolved : frame.state.unresolved <;>
      simp only [List.all_cons, unresolved, List.isEmpty_nil, List.isEmpty_cons, Bool.true_and, Bool.false_and] <;>
      occurrence_search_eval [later] unfolding
        [CollectionOccurrenceBatchExecution.frameTerm, RecursiveCollectionContinuationExecution.frameTerm,
          CompleteExecution.DescentCodec.stateTerm, PremiseSchedulerExecution.schedulerStateTerm,
          encodeList, List.all_cons, unresolved]

@[metta_head "gslt:occurrence-search:status"]
theorem status_returns (host : Effects.State) (table : List (String × TypeExpr))
    (run : CollectionOccurrenceSearch.Run plan bound expected) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-search:status" [encoded (runTerm table run)])
      host (statusAtom (CollectionOccurrenceSearch.status run)) := by
  have matchers := lanes_complete_returns host run.state.matchers
  have idle := frames_idle_returns host run.state.batch.frames
  have resolved := frames_resolved_returns host run.state.batch.frames
  cases matching : run.state.matchers.all (fun lane => RecursiveCollectionMachine.complete lane.state) <;>
    cases agendas : run.state.batch.frames.all (fun frame => frame.state.agenda.isEmpty) <;>
    cases obligations : run.state.batch.frames.all (fun frame => frame.state.unresolved.isEmpty) <;>
    occurrence_search_eval [matchers, idle, resolved] unfolding
      [runTerm, CollectionOccurrenceBatchExecution.stateTerm,
        CollectionOccurrenceSearch.status, CollectionOccurrenceSearch.statusWith, matching, agendas, obligations, statusAtom]

@[metta_head "gslt:occurrence-search:target"]
theorem target_returns (host : Effects.State) (names : List String) (ordered : NameOrdered names)
    (receipt : GeneralRuleJobs.Receipt) (covered : Covered names receipt.target) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-search:target"
        [encoded (encodeList Term.string names), encoded (ScopedRuleJobReadoutExecution.receiptTerm receipt)])
      host (encoded (InferenceCettaWire.encodePattern (CanonicalBags.canon receipt.target))) := by
  have canonical := canon_lower_returns host names ordered receipt.target covered
  occurrence_search_eval [canonical] unfolding [ScopedRuleJobReadoutExecution.receiptTerm]


namespace Declared
/-- Prefix ownership would also promise a missing canon-list operation. Exact support is essential. -/
theorem prefix_metadata_agreement_rejected :
    ¬ ProgramAgreementOn (fun head => !head.startsWith "gslt:" || keyLibrary.owns head)
      keyLibrary.runtime SelectedNativeSource.runtime := by
  intro agreed
  have equal := agreed.dispatch "gslt:canon:canon-list" (by decide +kernel)
  have absent : keyLibrary.runtime.equations.any (·.head == "gslt:canon:canon-list") = false := by
    decide +kernel
  have present : SelectedNativeSource.runtime.equations.any (·.head == "gslt:canon:canon-list") = true := by
    decide +kernel
  rw [absent, present] at equal
  cases equal

#print axioms prefix_metadata_agreement_rejected
end Declared

#print axioms checked
#print axioms proof_checked
#print axioms proof_row_count
#print axioms runTermWith_ordinary
#print axioms proof_agreement
#print axioms publication_wire_returns
#print axioms canon_lower_returns
#print axioms lanes_complete_returns
#print axioms frames_idle_returns
#print axioms frames_resolved_returns
#print axioms status_returns
#print axioms target_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution
