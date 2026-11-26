import Mettapedia.Languages.MeTTa.PeTTa.BridgeTransport
import Mettapedia.Languages.MeTTa.PeTTa.EquationEquality
import Mettapedia.GSLT.LanguageDef.BagEquationDecision
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Source
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionExecution
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionPresentationProofs

/-!
# Native reconstruction of ordinary collection presentations

The source replays retained decisions using the established allocator and
canonical comparison. The original allocation history stays with its answer.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RecursiveCollectionPresentation
open CanonicalBags CanonicalCompare CollectionSelection
open InferenceCettaWire (encodePattern encodeCollectionType encodeRest encodeBinder)
open RecursiveCollectionExecution (eventTerm)
open CollectionSelectionExecution (decisionTerm pairTerm booleanTerm)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_collection_presentation.metta"
    sha256 "01c97faf6f6a8aa54f5af704c39cbce46166a1f076de29fef855861b47929a0b"

def library : BridgeKit.Library :=
  RetainedMatchingWire.interpretedLibrary

set_option maxRecDepth 100000 in
theorem checked : library.check = true := RetainedMatchingWire.interpreted_checked

section ProofMetadata

private local instance presentationEquationEq : DecidableEq SpaceSemantics.Equation :=
  SpaceSemantics.Equation.decideEq

/-- Direct outward calls derived from the actual family bodies. -/
def presentationProofInheritedHeads : List String := ["gslt:automata:append", "gslt:automata:length", "gslt:recursive-collection:arrange", "gslt:collection:replay",  "gslt:complete:take", "gslt:complete:drop", "gslt:rule:row-at", "gslt:rule:scope-match-erase-at"]

theorem presentationProofInheritedHeads_derived :
    ((source.program.equations.flatMap (fun row => CompleteExecution.sourceLiteralHeads row.body)).filter
      (fun head => head.startsWith "gslt:" && !(source.program.equations.map (·.head)).contains head)).eraseDups =
        presentationProofInheritedHeads := by decide +kernel

private def presentationMetadataBase : SpaceSemantics.Program where
  equations := [RuleExecutionProgram.scopedProgram.equations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[1]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[65]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[120]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[2]'(by decide +kernel)).program.equations[12]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[2]'(by decide +kernel)).program.equations[26]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[5]'(by decide +kernel)).program.equations[5]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[10]'(by decide +kernel)).program.equations[0]'(by decide +kernel)]
  declarations := [RuleExecutionProgram.scopedProgram.declarations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[1]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[65]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[120]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[2]'(by decide +kernel)).program.declarations[12]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[2]'(by decide +kernel)).program.declarations[26]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[5]'(by decide +kernel)).program.declarations[5]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[10]'(by decide +kernel)).program.declarations[0]'(by decide +kernel)]

/-- Bounded source metadata; all operational conclusions retain the shared runtime. -/
def presentationProofLibrary : Library := ⟨presentationMetadataBase, source.program, ["gslt:collection-presentation:"]⟩

def presentationProofHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || presentationProofLibrary.owns head || presentationProofInheritedHeads.contains head

theorem presentationProof_checked : presentationProofLibrary.check = true := by decide +kernel

theorem presentationProof_agreement :
    ProgramAgreementOn presentationProofHeads presentationProofLibrary.runtime library.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

#print axioms presentationProofInheritedHeads_derived
#print axioms presentationProof_checked
#print axioms presentationProof_agreement

end ProofMetadata

def presentationTerm {α : Type} (element : α → Term)
    (result : α × List EquationalScopedReceipts.Event) : Term :=
  .application "RecursivePresentation" [element result.1, encodeList eventTerm result.2]

syntax "presentation_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| presentation_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call_in presentationProof_checked using presentationProof_agreement; metta_eval [$facts,*] with presentationProof_checked in presentationProof_agreement
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        CompleteExecution.pattern_symbol_unmatched, presentationTerm, eventTerm,
        encodeList, encodeOption, InferenceCettaWire.encodeList, InferenceCettaWire.encodePatterns_eq_encodeList, $extra,*]))

@[metta_head "gslt:automata:append"]
theorem append_returns {α : Type} (element : α → Term) (state : Effects.State) (left right : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:automata:append" [encoded (encodeList element left), encoded (encodeList element right)])
      state (encoded (encodeList element (left ++ right))) := by
  exact RecursiveCollectionExecution.append_returns element state left right

@[metta_head "gslt:automata:length"]
theorem length_returns {α : Type} (element : α → Term) (state : Effects.State) (items : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:automata:length" [encoded (encodeList element items)]) state (number items.length) := by
  exact RecursiveCollectionExecution.length_returns element state items

@[metta_head "gslt:recursive-collection:arrange"]
theorem arrange_returns (state : Effects.State) (table : List String) (ordered : NameOrdered table)
    (kind : CollType) (items : List Pattern) (covered : ∀ item ∈ items, Covered table item) :
    PureReturns library.runtime [] state
      (apply "gslt:recursive-collection:arrange" [encoded (encodeList Term.string table),
        encoded (encodeCollectionType kind), encoded (encodeList encodePattern items)])
      state (encoded (encodeList encodePattern (arrange kind items))) := by
  exact RecursiveCollectionExecution.arrange_returns state table ordered kind items covered

@[metta_head "gslt:collection:replay"]
theorem replay_returns (state : Effects.State) (idempotent : Bool) (items : List Pattern)
    (decisions : List Decision) :
    PureReturns library.runtime [] state
      (apply "gslt:collection:replay" [encoded (booleanTerm idempotent),
        encoded (encodeList encodePattern items), encoded (encodeList decisionTerm decisions)])
      state (encoded (encodeOption (pairTerm encodePattern) (replay idempotent items decisions))) := by
  exact CollectionSelectionExecution.replay_returns encodePattern state idempotent decisions items

@[metta_head "gslt:complete:take"]
theorem take_returns (state : Effects.State) (count : Nat) (items : List Pattern) :
    PureReturns library.runtime [] state
      (apply "gslt:complete:take" [number count, encoded (encodeList encodePattern items)])
      state (encoded (encodeList encodePattern (items.take count))) := by
  induction count generalizing items with
  | zero =>
    metta_call_in CompleteExecution.completeProof_checked using CompleteExecution.completeProof_agreement
    metta_eval with CompleteExecution.completeProof_checked in CompleteExecution.completeProof_agreement
      unfolding [encodeList, List.take, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        CettaWireAtom.encode, CettaWireAtom.encodeMany]
  | succ count ih =>
    metta_call_in CompleteExecution.completeProof_checked using CompleteExecution.completeProof_agreement
    cases items with
    | nil =>
      metta_eval with CompleteExecution.completeProof_checked in CompleteExecution.completeProof_agreement
        unfolding [encodeList, List.take, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
          Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
          CettaWireAtom.encode, CettaWireAtom.encodeMany]
    | cons head rest =>
      have later := ih rest
      metta_eval [later] with CompleteExecution.completeProof_checked
        in CompleteExecution.completeProof_agreement unfolding
        [encodeList, List.take, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
          Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
          CettaWireAtom.encode, CettaWireAtom.encodeMany]

@[metta_head "gslt:complete:drop"]
theorem drop_returns (state : Effects.State) (count : Nat) (items : List Pattern) :
    PureReturns library.runtime [] state
      (apply "gslt:complete:drop" [number count, encoded (encodeList encodePattern items)])
      state (encoded (encodeList encodePattern (items.drop count))) := by
  have mapped (values : List Pattern) : encoded (encodeList encodePattern values) =
      CompleteExecution.terms (values.map encodePattern) := by
    simp only [CompleteExecution.terms, CettaWire.encodeList_map, Function.id_comp]
  rw [mapped, mapped, List.map_drop]
  exact CompleteExecution.drop_returns state count (items.map encodePattern)

@[metta_head "gslt:collection-presentation:wrap"]
theorem wrap_app_returns (state : Effects.State) (label : String) (items : List Pattern)
    (remaining : List EquationalScopedReceipts.Event) :
    PureReturns library.runtime [] state (apply "gslt:collection-presentation:wrap"
      [encoded (.application "PresentationApp" [.string label]),
        encoded (encodeOption (presentationTerm (encodeList encodePattern)) (some (items, remaining)))])
      state (encoded (encodeOption (presentationTerm encodePattern) (some (.apply label items, remaining)))) := by
  presentation_eval unfolding [encodePattern]

@[metta_head "gslt:collection-presentation:wrap"]
theorem wrap_lambda_returns (state : Effects.State) (display : Option String) (body : Pattern)
    (remaining : List EquationalScopedReceipts.Event) :
    PureReturns library.runtime [] state (apply "gslt:collection-presentation:wrap"
      [encoded (.application "PresentationLam" [encodeBinder display]),
        encoded (encodeOption (presentationTerm encodePattern) (some (body, remaining)))])
      state (encoded (encodeOption (presentationTerm encodePattern) (some (.lambda display body, remaining)))) := by
  presentation_eval unfolding [encodePattern]

@[metta_head "gslt:collection-presentation:wrap"]
theorem wrap_multiLambda_returns (state : Effects.State) (arity : Nat) (display : List String) (body : Pattern)
    (remaining : List EquationalScopedReceipts.Event) :
    PureReturns library.runtime [] state (apply "gslt:collection-presentation:wrap"
      [encoded (.application "PresentationMultiLam" [.natural arity, encodeList Term.string display]),
        encoded (encodeOption (presentationTerm encodePattern) (some (body, remaining)))])
      state (encoded (encodeOption (presentationTerm encodePattern)
        (some (.multiLambda arity display body, remaining)))) := by
  presentation_eval unfolding [encodePattern]

@[metta_head "gslt:collection-presentation:wrap"]
theorem wrap_subst_returns (state : Effects.State) (body replacement : Pattern)
    (remaining : List EquationalScopedReceipts.Event) :
    PureReturns library.runtime [] state (apply "gslt:collection-presentation:wrap"
      [encoded (.application "PresentationSubst" [encodePattern body]),
        encoded (encodeOption (presentationTerm encodePattern) (some (replacement, remaining)))])
      state (encoded (encodeOption (presentationTerm encodePattern)
        (some (.subst body replacement, remaining)))) := by
  presentation_eval unfolding [encodePattern]

@[metta_head "gslt:collection-presentation:wrap"]
theorem wrap_cons_returns (state : Effects.State) (head : Pattern) (tail : List Pattern)
    (remaining : List EquationalScopedReceipts.Event) :
    PureReturns library.runtime [] state (apply "gslt:collection-presentation:wrap"
      [encoded (.application "PresentationCons" [encodePattern head]),
        encoded (encodeOption (presentationTerm (encodeList encodePattern)) (some (tail, remaining)))])
      state (encoded (encodeOption (presentationTerm (encodeList encodePattern))
        (some (head :: tail, remaining)))) := by presentation_eval

@[metta_head "gslt:collection-presentation:wrap"]
theorem wrap_collection_returns (state : Effects.State) (kind : CollType) (items residual : List Pattern)
    (remaining : List EquationalScopedReceipts.Event) :
    PureReturns library.runtime [] state (apply "gslt:collection-presentation:wrap"
      [encoded (.application "PresentationCollection" [encodeCollectionType kind, encodeList encodePattern residual]),
        encoded (encodeOption (presentationTerm (encodeList encodePattern)) (some (items, remaining)))])
      state (encoded (encodeOption (presentationTerm encodePattern)
        (some (.collection kind (items ++ residual) none, remaining)))) := by
  presentation_eval [append_returns encodePattern state items residual] unfolding [encodePattern, encodeRest]

#print axioms append_returns
#print axioms length_returns
#print axioms arrange_returns
#print axioms replay_returns
#print axioms take_returns
#print axioms drop_returns
#print axioms wrap_app_returns
#print axioms wrap_lambda_returns
#print axioms wrap_multiLambda_returns
#print axioms wrap_subst_returns
#print axioms wrap_cons_returns
#print axioms wrap_collection_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution


set_option Elab.async false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.Grouping

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus
open Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView.GroupedCursor
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit
open CollectionOccurrenceSearchExecution
open scoped ProgramQuotation

def source : SpaceSemantics.Program :=
  RuleExecutionProgram.callFragment
    ["gslt:collection-presentation:group-reverse-onto",
     "gslt:collection-presentation:group-expand",
     "gslt:collection-presentation:group-begin",
     "gslt:collection-presentation:group-tick",
     "gslt:collection-presentation:group-run",
     "gslt:collection-presentation:group-complete",
     "gslt:collection-presentation:group-answers"]
    (RuleExecutionProgram.interpretedPremiseSupportSources[11]'(by decide +kernel)).program

def physicalBase : SpaceSemantics.Program where
  equations := [RuleExecutionProgram.scopedProgram.equations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[65]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[120]'(by decide +kernel)]
  declarations := [RuleExecutionProgram.scopedProgram.declarations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[65]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[120]'(by decide +kernel)]

def proofLibrary : BridgeKit.Library :=
  ⟨{equations := [],declarations := []},physicalBase.append source,["gslt:"]⟩

theorem proof_checked : proofLibrary.check = true := by decide +kernel


def proofHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || (proofLibrary.runtime.equations.map (·.head)).contains head

private local instance groupingEquationEq : DecidableEq SpaceSemantics.Equation :=
  SpaceSemantics.Equation.decideEq

/-- Ordered primitive source rows agree with the shared interpreted program. -/
theorem shared_program_agreement :
    ProgramAgreementOn proofHeads proofLibrary.runtime RuleExecutionProgram.interpretedPremiseProgram := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

#print axioms shared_program_agreement


/-- The same ordered primitive rows occur in the selected physical runtime. -/
theorem selected_program_agreement :
    ProgramAgreementOn proofHeads proofLibrary.runtime SelectedNativeSource.runtime := by
  apply agreement_trans shared_program_agreement
  apply SelectedNativeSource.agreement_of_replacement_rows <;> decide +kernel

#print axioms selected_program_agreement

variable (program : SpaceSemantics.Program)
    (agreement : ProgramAgreementOn proofHeads proofLibrary.runtime program)

def workTerm (element : SourceOccurrence → Term) : Work → Term
  | .groups slots closed selected remaining => .application "GroupingGroups"
      [.natural slots,encodeList (encodeList element) closed,encodeList element selected,encodeList element remaining]
  | .selectGroup slots closed selected remaining cursor => .application "GroupingSelectGroup"
      [.natural slots,encodeList (encodeList element) closed,encodeList element selected,encodeList element remaining,.natural cursor]
  | .residual closed selected remaining => .application "GroupingResidual"
      [encodeList (encodeList element) closed,encodeList element selected,encodeList element remaining]
  | .selectResidual closed selected remaining cursor => .application "GroupingSelectResidual"
      [encodeList (encodeList element) closed,encodeList element selected,encodeList element remaining,.natural cursor]

def allocationTerm (element : SourceOccurrence → Term)
    (allocation : List (List SourceOccurrence) × List SourceOccurrence) : Term :=
  .application "GroupingAllocation" [encodeList (encodeList element) allocation.1,encodeList element allocation.2]

def stateTerm (element : SourceOccurrence → Term)
    (state : Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView.GroupedCursor.State) : Term :=
  .application "GroupingState" [encodeList (workTerm element) state.agenda,encodeList (allocationTerm element) state.answers]

def expansionTerm (element : SourceOccurrence → Term) (work : Work) : Term :=
  match work.finished? with
  | some allocation => .application "GroupingExpansion" [.symbol "LNil",encodeList (allocationTerm element) [allocation]]
  | none => .application "GroupingExpansion" [encodeList (workTerm element) (expand work),.symbol "LNil"]

include agreement in
@[metta_head "gslt:automata:append"]
theorem append_returns {α : Type} (element : α → Term) (host : Effects.State) :
    ∀ left right : List α,
    PureReturns program [] host
      (apply "gslt:automata:append" [encoded (encodeList element left),encoded (encodeList element right)])
      host (encoded (encodeList element (left ++ right)))
  | [],right => by
      metta_call_in proof_checked using agreement
      metta_eval with proof_checked in agreement unfolding [encodeList]
  | first :: rest,right => by
      metta_call_in proof_checked using agreement
      metta_eval [append_returns element host rest right] with proof_checked in agreement unfolding [encodeList]

include agreement in
@[metta_head "gslt:rule:scope-match-erase-at"]
theorem erase_returns {α : Type} (element : α → Term) (host : Effects.State) :
    ∀ (items : List α) (index : Nat),
    PureReturns program [] host
      (apply "gslt:rule:scope-match-erase-at" [number index,encoded (encodeList element items)])
      host (encoded (encodeList element (items.eraseIdx index)))
  | [],index => by
      metta_call_in proof_checked using agreement
      metta_eval with proof_checked in agreement unfolding [encodeList,List.eraseIdx_nil,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,List.find?]
  | first :: rest,0 => by
      metta_call_in proof_checked using agreement
      metta_eval with proof_checked in agreement unfolding [encodeList,List.eraseIdx_zero,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,List.find?]
  | first :: rest,index + 1 => by
      metta_call_in proof_checked using agreement
      metta_eval [erase_returns element host rest index] with proof_checked in agreement
        unfolding [encodeList,List.eraseIdx_cons_succ,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
          Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,List.find?]

include agreement in
@[metta_head "gslt:rule:row-at"]
theorem row_returns {α : Type} (element : α → Term) (host : Effects.State) :
    ∀ (items : List α) (index : Nat),
    PureReturns program [] host
      (apply "gslt:rule:row-at" [number index,encoded (encodeList element items)])
      host (encoded (encodeOption element items[index]?))
  | [],index => by
      metta_call_in proof_checked using agreement
      metta_eval with proof_checked in agreement unfolding [encodeList,encodeOption]
  | first :: rest,0 => by
      metta_call_in proof_checked using agreement
      metta_eval with proof_checked in agreement unfolding [encodeList,encodeOption,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,List.find?]
  | first :: rest,index + 1 => by
      metta_call_in proof_checked using agreement
      metta_eval [row_returns element host rest index] with proof_checked in agreement
        unfolding [encodeList,encodeOption]

include agreement in
@[metta_head "gslt:collection-presentation:group-reverse-onto"]
theorem reverse_onto_returns {α : Type} (element : α → Term) (host : Effects.State) :
    ∀ (items reversed : List α),
    PureReturns program [] host
      (apply "gslt:collection-presentation:group-reverse-onto"
        [encoded (encodeList element items),encoded (encodeList element reversed)])
      host (encoded (encodeList element (items.reverse ++ reversed)))
  | [],reversed => by
      metta_call_in proof_checked using agreement
      metta_eval with proof_checked in agreement unfolding [encodeList,List.reverse_nil,List.nil_append]
  | first :: rest,reversed => by
      rw [List.reverse_cons,List.append_assoc,List.singleton_append]
      metta_call_in proof_checked using agreement
      metta_eval [reverse_onto_returns element host rest (first :: reversed)] with proof_checked in agreement
        unfolding [encodeList]

#print axioms proof_checked
#print axioms append_returns
#print axioms erase_returns
#print axioms row_returns
#print axioms reverse_onto_returns

theorem nil_matches_encoded_list {α : Type} (element : α → Term)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (items : List α) :
    SpaceSemantics.matchValue bindings (.symbol "LNil") (encoded (encodeList element items)) =
      match items with
      | [] => some bindings
      | _ :: _ => none := by
  cases items <;> simp [SpaceSemantics.matchValue,encodeList,CettaWireAtom.encode,
    Mettapedia.Languages.ProcessCalculi.MORK.matchAtom]

syntax "grouping_eval" " using " "(" term ")" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| grouping_eval using ($agreement) $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call_in proof_checked using $agreement; metta_eval [$facts,*] with proof_checked in $agreement
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,List.find?,
        nil_matches_encoded_list,encodeList,encodeOption,workTerm,allocationTerm,stateTerm,expansionTerm,$extra,*]))

include agreement in
@[metta_head "gslt:collection-presentation:group-expand"]
theorem expand_returns (element : SourceOccurrence → Term) (host : Effects.State) (work : Work) :
    PureReturns program [] host
      (apply "gslt:collection-presentation:group-expand" [encoded (workTerm element work)])
      host (encoded (expansionTerm element work)) := by
  cases work with
  | groups slots closed selected remaining =>
    cases slots with
    | zero => grouping_eval using (agreement) unfolding [Work.finished?,expand]
    | succ slots =>
      have reversed := reverse_onto_returns program agreement element host selected []
      simp only [List.append_nil] at reversed
      have joined := append_returns program agreement (encodeList element) host closed [selected.reverse]
      cases slots with
      | zero => grouping_eval using (agreement) [reversed,joined] unfolding [Work.finished?,expand]
      | succ slots => grouping_eval using (agreement) [reversed,joined] unfolding [Work.finished?,expand]
  | selectGroup slots closed selected remaining cursor =>
    have looked := row_returns program agreement element host remaining cursor
    cases found : remaining[cursor]? with
    | none =>
      rw [found] at looked
      grouping_eval using (agreement) [looked] unfolding [Work.finished?,expand,found]
    | some occurrence =>
      rw [found] at looked
      have erased := erase_returns program agreement element host remaining cursor
      grouping_eval using (agreement) [looked,erased] unfolding [Work.finished?,expand,found]
  | residual closed selected remaining =>
    cases remaining with
    | nil =>
      have reversed := reverse_onto_returns program agreement element host selected []
      simp only [List.append_nil] at reversed
      grouping_eval using (agreement) [reversed] unfolding [Work.finished?]
    | cons first rest => grouping_eval using (agreement) unfolding [Work.finished?,expand]
  | selectResidual closed selected remaining cursor =>
    have looked := row_returns program agreement element host remaining cursor
    cases found : remaining[cursor]? with
    | none =>
      rw [found] at looked
      grouping_eval using (agreement) [looked] unfolding [Work.finished?,expand,found]
    | some occurrence =>
      rw [found] at looked
      have erased := erase_returns program agreement element host remaining cursor
      grouping_eval using (agreement) [looked,erased] unfolding [Work.finished?,expand,found]

#print axioms expand_returns

include agreement in
@[metta_head "gslt:collection-presentation:group-begin"]
theorem begin_returns (element : SourceOccurrence → Term) (host : Effects.State)
    (count : Nat) (occurrences : List SourceOccurrence) :
    PureReturns program [] host
      (apply "gslt:collection-presentation:group-begin"
        [number count,encoded (encodeList element occurrences)])
      host (encoded (stateTerm element (start count occurrences))) := by
  cases count with
  | zero => grouping_eval using (agreement) unfolding [start]
  | succ count =>
    metta_call_in proof_checked using agreement
    refine pure_let_returns _ _ _ _ _
      (encoded (workTerm element (.groups (count + 1) [] [] occurrences))) _ _ (by rfl) ?_ ?_
    · metta_eval with proof_checked in agreement unfolding [workTerm,encodeList]
    · metta_eval with proof_checked in agreement unfolding [start,stateTerm,workTerm,encodeList]

abbrev ModelState :=
  Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView.GroupedCursor.State

include agreement in
@[metta_head "gslt:collection-presentation:group-tick"]
theorem tick_returns (element : SourceOccurrence → Term) (host : Effects.State) (state : ModelState) :
    PureReturns program [] host
      (apply "gslt:collection-presentation:group-tick" [encoded (stateTerm element state)])
      host (encoded (stateTerm element (tick state))) := by
  cases state with
  | mk agenda answers =>
    cases agenda with
    | nil => grouping_eval using (agreement) unfolding [tick]
    | cons work pending =>
      have expanded := expand_returns program agreement element host work
      cases finished : work.finished? with
      | none =>
        simp only [expansionTerm,finished] at expanded
        have joined := append_returns program agreement (workTerm element) host (expand work) pending
        have retained := append_returns program agreement (allocationTerm element) host answers []
        grouping_eval using (agreement) [expanded,joined,retained] unfolding [tick,finished]
      | some allocation =>
        simp only [expansionTerm,finished] at expanded
        have joined := append_returns program agreement (workTerm element) host [] pending
        have published := append_returns program agreement (allocationTerm element) host answers [allocation]
        grouping_eval using (agreement) [expanded,joined,published] unfolding [tick,finished]

include agreement in
@[metta_head "gslt:collection-presentation:group-run"]
theorem run_returns (element : SourceOccurrence → Term) (host : Effects.State) :
    ∀ (steps : Nat) (state : ModelState),
    PureReturns program [] host
      (apply "gslt:collection-presentation:group-run" [number steps,encoded (stateTerm element state)])
      host (encoded (stateTerm element (run steps state)))
  | 0,state => by grouping_eval using (agreement) unfolding [RecursiveView.GroupedCursor.run]
  | steps + 1,state => by
      rw [RecursiveView.GroupedCursor.run]
      have first := tick_returns program agreement element host state
      have later := run_returns element host steps (tick state)
      grouping_eval using (agreement) [first,later] unfolding [RecursiveView.GroupedCursor.run]

include agreement in
@[metta_head "gslt:collection-presentation:group-complete"]
theorem complete_returns (element : SourceOccurrence → Term) (host : Effects.State) (state : ModelState) :
    PureReturns program [] host
      (apply "gslt:collection-presentation:group-complete" [encoded (stateTerm element state)])
      host (Effects.boolean (complete state)) := by
  cases state with
  | mk agenda answers =>
    cases agenda with
    | nil => grouping_eval using (agreement) unfolding [complete]
    | cons first rest => grouping_eval using (agreement) unfolding [complete]

include agreement in
@[metta_head "gslt:collection-presentation:group-answers"]
theorem answers_returns (element : SourceOccurrence → Term) (host : Effects.State) (state : ModelState) :
    PureReturns program [] host
      (apply "gslt:collection-presentation:group-answers" [encoded (stateTerm element state)])
      host (encoded (encodeList (allocationTerm element) state.answers)) := by
  cases state
  grouping_eval using (agreement)

#print axioms begin_returns
#print axioms tick_returns
#print axioms run_returns
#print axioms complete_returns
#print axioms answers_returns

/-- The actual source record retains all syntax, address, zipper and value data. -/
def occurrenceTerm (occurrence : SourceOccurrence) : Term :=
  .application "AlgebraSourceOccurrence"
    [InferenceCettaWire.encodePattern occurrence.original,
     encodeList Term.natural occurrence.address,
     InferenceCettaWire.ContextObservation.contextTerm occurrence.context,
     InferenceCettaWire.encodePattern occurrence.value]

def decodeOccurrence? : Term → Option SourceOccurrence
  | .application "AlgebraSourceOccurrence" [original,address,context,value] => do
      pure ⟨← InferenceCettaWire.decodePattern original,
        ← decodeList (fun term => match term with | .natural index => some index | _ => none) address,
        ← InferenceCettaWire.ContextObservation.decodeContext? context,
        ← InferenceCettaWire.decodePattern value⟩
  | _ => none

@[simp] theorem decodeOccurrence?_occurrenceTerm (occurrence : SourceOccurrence) :
    decodeOccurrence? (occurrenceTerm occurrence) = some occurrence := by
  cases occurrence
  simp [occurrenceTerm,decodeOccurrence?,decodeList_encodeList]

theorem occurrenceTerm_injective : Function.Injective occurrenceTerm := by
  intro left right same
  simpa using congrArg decodeOccurrence? same

def decodeAllocation? : Term → Option (List (List SourceOccurrence) × List SourceOccurrence)
  | .application "GroupingAllocation" [groups,residual] => do
      pure (← decodeList (decodeList decodeOccurrence?) groups, ← decodeList decodeOccurrence? residual)
  | _ => none

@[simp] theorem decodeAllocation?_allocationTerm
    (allocation : List (List SourceOccurrence) × List SourceOccurrence) :
    decodeAllocation? (allocationTerm occurrenceTerm allocation) = some allocation := by
  cases allocation
  simp [decodeAllocation?,allocationTerm,decodeList_encodeList]

theorem allocationTerm_injective : Function.Injective (allocationTerm occurrenceTerm) := by
  intro left right same
  simpa using congrArg decodeAllocation? same

/-- A native encoded allocation cannot identify different source occurrences. -/
theorem encoded_allocation_injective :
    Function.Injective (fun allocation => encoded (allocationTerm occurrenceTerm allocation)) := by
  intro left right same
  exact allocationTerm_injective (CettaWireAtom.encode_injective _ _ same)

/-- Existence of enough work is earned from the real retained cursor's
finite expansion measure. The returned complete state covers every physical
grouping; no completed-run assumption is supplied by the caller. -/
theorem shared_completes_with_exact_allocations (host : Effects.State)
    (count : Nat) (occurrences : List SourceOccurrence) :
    ∃ steps,
      PureReturns RuleExecutionProgram.interpretedPremiseProgram [] host
        (apply "gslt:collection-presentation:group-begin"
          [number count,encoded (encodeList occurrenceTerm occurrences)])
        host (encoded (stateTerm occurrenceTerm (start count occurrences))) ∧
      PureReturns RuleExecutionProgram.interpretedPremiseProgram [] host
        (apply "gslt:collection-presentation:group-run"
          [number steps,encoded (stateTerm occurrenceTerm (start count occurrences))])
        host (encoded (stateTerm occurrenceTerm (RecursiveView.GroupedCursor.run steps (start count occurrences)))) ∧
      PureReturns RuleExecutionProgram.interpretedPremiseProgram [] host
        (apply "gslt:collection-presentation:group-complete"
          [encoded (stateTerm occurrenceTerm (RecursiveView.GroupedCursor.run steps (start count occurrences)))])
        host (Effects.boolean true) ∧
      ∀ groups residual,
        (groups,residual) ∈ (RecursiveView.GroupedCursor.run steps (start count occurrences)).answers ↔
          (groups,residual) ∈ groupedOccurrences count occurrences := by
  obtain ⟨steps,done,covered⟩ := completes_with_exact_allocations count occurrences
  refine ⟨steps,begin_returns _ shared_program_agreement occurrenceTerm host count occurrences,
    run_returns _ shared_program_agreement occurrenceTerm host steps (start count occurrences),?_,covered⟩
  simpa only [done] using complete_returns _ shared_program_agreement occurrenceTerm host
    (RecursiveView.GroupedCursor.run steps (start count occurrences))

/-- Native resume has exactly the full state obtained with the combined budget. -/
theorem shared_resume_returns (host : Effects.State) (first second : Nat) (state : ModelState) :
    PureReturns RuleExecutionProgram.interpretedPremiseProgram [] host
      (apply "gslt:collection-presentation:group-run"
        [number second,encoded (stateTerm occurrenceTerm (RecursiveView.GroupedCursor.run first state))])
      host (encoded (stateTerm occurrenceTerm (RecursiveView.GroupedCursor.run (first + second) state))) := by
  rw [RecursiveView.GroupedCursor.run_add]
  exact run_returns _ shared_program_agreement occurrenceTerm host second _

/-- Existence of enough work is earned from the real retained cursor's
finite expansion measure. The returned complete state covers every physical
grouping; no completed-run assumption is supplied by the caller. -/
theorem selected_completes_with_exact_allocations (host : Effects.State)
    (count : Nat) (occurrences : List SourceOccurrence) :
    ∃ steps,
      PureReturns SelectedNativeSource.runtime [] host
        (apply "gslt:collection-presentation:group-begin"
          [number count,encoded (encodeList occurrenceTerm occurrences)])
        host (encoded (stateTerm occurrenceTerm (start count occurrences))) ∧
      PureReturns SelectedNativeSource.runtime [] host
        (apply "gslt:collection-presentation:group-run"
          [number steps,encoded (stateTerm occurrenceTerm (start count occurrences))])
        host (encoded (stateTerm occurrenceTerm (RecursiveView.GroupedCursor.run steps (start count occurrences)))) ∧
      PureReturns SelectedNativeSource.runtime [] host
        (apply "gslt:collection-presentation:group-complete"
          [encoded (stateTerm occurrenceTerm (RecursiveView.GroupedCursor.run steps (start count occurrences)))])
        host (Effects.boolean true) ∧
      ∀ groups residual,
        (groups,residual) ∈ (RecursiveView.GroupedCursor.run steps (start count occurrences)).answers ↔
          (groups,residual) ∈ groupedOccurrences count occurrences := by
  obtain ⟨steps,done,covered⟩ := completes_with_exact_allocations count occurrences
  refine ⟨steps,begin_returns _ selected_program_agreement occurrenceTerm host count occurrences,
    run_returns _ selected_program_agreement occurrenceTerm host steps (start count occurrences),?_,covered⟩
  simpa only [done] using complete_returns _ selected_program_agreement occurrenceTerm host
    (RecursiveView.GroupedCursor.run steps (start count occurrences))

/-- Native resume has exactly the full state obtained with the combined budget. -/
theorem selected_resume_returns (host : Effects.State) (first second : Nat) (state : ModelState) :
    PureReturns SelectedNativeSource.runtime [] host
      (apply "gslt:collection-presentation:group-run"
        [number second,encoded (stateTerm occurrenceTerm (RecursiveView.GroupedCursor.run first state))])
      host (encoded (stateTerm occurrenceTerm (RecursiveView.GroupedCursor.run (first + second) state))) := by
  rw [RecursiveView.GroupedCursor.run_add]
  exact run_returns _ selected_program_agreement occurrenceTerm host second _

/-- Reading encoded publications preserves the complete physical source account,
including actual unit leaves kept outside the selected algebra groups. -/
theorem native_publication_source_account (count steps : Nat) (unitLabel : String)
    (source : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (published : encoded (allocationTerm occurrenceTerm (groups,residual)) ∈
      ((RecursiveView.GroupedCursor.run steps
        (start count (normalizedOccurrences unitLabel source))).answers.map
          (fun allocation => encoded (allocationTerm occurrenceTerm allocation)))) :
    ((groups.flatten ++ residual) ++ unitOccurrences unitLabel source).Perm
      (sourceOccurrences unitLabel source) := by
  obtain ⟨allocation,member,same⟩ := List.mem_map.mp published
  have identified := encoded_allocation_injective same
  subst allocation
  exact publication_source_account count steps unitLabel source member

theorem equal_values_distinct_addresses :
    let source := SourceOccurrence.leaf "unit" (.apply "Token" [])
    occurrenceTerm {source with address := [0]} ≠ occurrenceTerm {source with address := [1]} := by
  dsimp only
  intro same
  have identified := occurrenceTerm_injective same
  have address := congrArg SourceOccurrence.address identified
  simp at address

theorem incomplete_occurrence_refused :
    decodeOccurrence? (.application "AlgebraSourceOccurrence" [.symbol "Token"]) = none := rfl

#print axioms decodeOccurrence?_occurrenceTerm
#print axioms occurrenceTerm_injective
#print axioms decodeAllocation?_allocationTerm
#print axioms allocationTerm_injective
#print axioms encoded_allocation_injective
#print axioms shared_completes_with_exact_allocations
#print axioms shared_resume_returns
#print axioms selected_completes_with_exact_allocations
#print axioms selected_resume_returns
#print axioms native_publication_source_account
#print axioms equal_values_distinct_addresses
#print axioms incomplete_occurrence_refused

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.Grouping
