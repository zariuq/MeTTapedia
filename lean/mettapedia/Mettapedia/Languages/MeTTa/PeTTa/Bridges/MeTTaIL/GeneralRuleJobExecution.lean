import Mettapedia.Languages.MeTTa.PeTTa.BridgeTransport
import Mettapedia.Languages.MeTTa.PeTTa.AppendAgreement
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralPremiseExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RulePlanWire
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics
import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobCoverage
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseFinishReadout

/-!
# Original scoped rule-job receipts through PeTTa execution

The codecs retain physical sites, typing frames, captured dependencies and
ordered premise evidence. The authored readout realizes the original finishRoot
operation. Receipt validity and GSLT steps are derived from the original
source-authorized machine and its actual completed observations.
The quoted execution claims require no registered dynamic relations; native
primitive service execution requires its own correspondence proof.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedRuleJobReadoutExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralTypedSites
open GeneralExecutionAdmission GeneralRuleJobs


private def natural? : Term → Option Nat
  | .natural value => some value
  | _ => none

def typingFrameTerm : TypingFrame → Term
  | .application declaration index => .application "TypingApplication" [.natural declaration, .natural index]
  | .lambda domain => .application "TypingLambda" [InferenceCettaWire.AuthoredRule.typeTerm domain]
  | .multiLambda arity domain => .application "TypingMultiLambda" [.natural arity, InferenceCettaWire.AuthoredRule.typeTerm domain]
  | .directCollection kind => .application "TypingDirectCollection" [InferenceCettaWire.encodeCollectionType kind]
  | .authoredCollection declaration => .application "TypingAuthoredCollection" [.natural declaration]

def decodeTypingFrame? : Term → Option TypingFrame
  | .application "TypingApplication" [.natural declaration, .natural index] => some (.application declaration index)
  | .application "TypingLambda" [domain] => TypingFrame.lambda <$> InferenceCettaWire.AuthoredRule.decodeType? domain
  | .application "TypingMultiLambda" [.natural arity, domain] => TypingFrame.multiLambda arity <$> InferenceCettaWire.AuthoredRule.decodeType? domain
  | .application "TypingDirectCollection" [kind] => TypingFrame.directCollection <$> InferenceCettaWire.decodeCollectionType kind
  | .application "TypingAuthoredCollection" [.natural declaration] => some (.authoredCollection declaration)
  | _ => none

@[simp] theorem decodeTypingFrame?_typingFrameTerm (frame : TypingFrame) :
    decodeTypingFrame? (typingFrameTerm frame) = some frame := by
  cases frame <;> simp [typingFrameTerm, decodeTypingFrame?]

def siteTerm (site : SiteData) : Term :=
  .application "RuleJobSite" [encodeList Term.natural site.address, InferenceCettaWire.ContextObservation.contextTerm site.context,
    InferenceCettaWire.encodePattern site.focus, encodeList InferenceCettaWire.AuthoredRule.typeTerm site.focusBound,
    InferenceCettaWire.AuthoredRule.typeTerm site.focusType, encodeList typingFrameTerm site.typingFrames]

def decodeSite? : Term → Option SiteData
  | .application "RuleJobSite" [address, context, focus, bound, type, frames] => do
      pure ⟨← decodeList natural? address, ← InferenceCettaWire.ContextObservation.decodeContext? context,
        ← InferenceCettaWire.decodePattern focus, ← decodeList InferenceCettaWire.AuthoredRule.decodeType? bound,
        ← InferenceCettaWire.AuthoredRule.decodeType? type, ← decodeList decodeTypingFrame? frames⟩
  | _ => none

@[simp] theorem decodeSite?_siteTerm (site : SiteData) : decodeSite? (siteTerm site) = some site := by
  have naturals : decodeList natural? (encodeList Term.natural site.address) = some site.address :=
    decodeList_encodeList natural? Term.natural (fun _ => rfl) site.address
  cases site
  simp [siteTerm, decodeSite?, decodeList_encodeList, naturals]

def jobTerm (job : Job) : Term :=
  .application "RuleJob" [.natural job.ordinal, rulePlanTerm job.declaration, siteTerm job.site]

def decodeJob? : Term → Option Job
  | .application "RuleJob" [.natural ordinal, declaration, site] => do
      pure ⟨ordinal, ← decodeRulePlan? declaration, ← decodeSite? site⟩
  | _ => none

@[simp] theorem decodeJob?_jobTerm (job : Job) : decodeJob? (jobTerm job) = some job := by
  cases job
  simp [jobTerm, decodeJob?]

theorem jobTerm_injective : Function.Injective jobTerm := by
  intro first second same
  have decoded := congrArg decodeJob? same
  simpa only [decodeJob?_jobTerm, Option.some.injEq] using decoded

private abbrev assignmentTerm := RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm

private def assignmentEntry? : Term → Option (String × ContextualValue)
  | .application "Binding" [.string name, value] => do
      pure (name, ← InferenceCettaWire.AuthoredRule.decodeContextualValue? value)
  | _ => none

def decodeAssignment? (wire : Term) : Option Assignment := decodeList assignmentEntry? wire

@[simp] theorem decodeAssignment?_assignmentTerm (assignment : Assignment) :
    decodeAssignment? (assignmentTerm assignment) = some assignment := by
  have encoded : assignmentTerm assignment = encodeList
      (fun entry => .application "Binding" [.string entry.1, InferenceCettaWire.AuthoredRule.contextualValueTerm entry.2]) assignment := by
    simp only [assignmentTerm, RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
      MatchAutomataBindingExecution.payloadBindingsTerm, encodeList_map,
      Function.comp_def, MatchAutomataBindingExecution.payloadBindingTerm]
  rw [decodeAssignment?, encoded]
  apply decodeList_encodeList
  intro entry
  simp [assignmentEntry?]

private def decodeBagChoice? : Term → Option GeneralScopedMatchMachine.BagChoice
  | .application "BagChoice" [path, .natural selected] => do
      pure ⟨← decodeList natural? path, selected⟩
  | _ => none

private theorem decodeBagChoice?_bagChoiceTerm (choice : GeneralScopedMatchMachine.BagChoice) :
    decodeBagChoice? (PremiseOperationsExecution.GeneralExecution.bagChoiceTerm choice) = some choice := by
  change decodeBagChoice? (.application "BagChoice" [encodeList Term.natural choice.path,
    .natural choice.selected]) = some choice
  have naturals : decodeList natural? (encodeList Term.natural choice.path) = some choice.path :=
    decodeList_encodeList natural? Term.natural (fun _ => rfl) choice.path
  cases choice
  simp [decodeBagChoice?, naturals]

def decodeTrace? (wire : Term) : Option (List GeneralScopedMatchMachine.BagChoice) :=
  decodeList decodeBagChoice? wire

@[simp] theorem decodeTrace?_traceTerm (trace : List GeneralScopedMatchMachine.BagChoice) :
    decodeTrace? (PremiseOperationsExecution.GeneralExecution.traceTerm trace) = some trace :=
  decodeList_encodeList _ _ decodeBagChoice?_bagChoiceTerm trace

private def decodeOriginRow? : Term → Option (Nat × List GeneralScopedMatchMachine.BagChoice)
  | .application "ArgumentOrigin" [.natural index, trace] => do
      pure (index, ← decodeTrace? trace)
  | _ => none

private theorem decodeOrigins_originsTerm (origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)) :
    decodeList decodeOriginRow? (PremiseOperationsExecution.GeneralExecution.originsTerm origins) = some origins := by
  apply decodeList_encodeList
  intro origin
  simp [decodeOriginRow?]

mutual
def decodeEvent? : Term → Option GeneralPremise.Event
  | .application "PremiseQueryEvent" [.natural index, .natural quantifiers, .natural row, origins] => do
      pure (.query index quantifiers row (← decodeList decodeOriginRow? origins))
  | .application "PremiseFreshnessEvent" [.natural index, .natural quantifiers, .string atom, subject] => do
      pure (.freshness index quantifiers atom (← InferenceCettaWire.decodePattern subject))
  | .application "PremiseQuantifiedEvent" [.natural index, .natural quantifiers, kind, elements] => do
      pure (.quantified index quantifiers (← InferenceCettaWire.decodeCollectionType kind)
        (← decodeQuantifiedEvents? elements))
  | .application "PremiseChildEvent" [.natural index, .natural quantifiers, .natural declaration,
      bound, source, target, trace, targetTrace, captured, completed, history] => do
      pure (.child index quantifiers declaration (← decodeList InferenceCettaWire.AuthoredRule.decodeType? bound)
        (← InferenceCettaWire.decodePattern source) (← InferenceCettaWire.decodePattern target)
        (← decodeTrace? trace) (← decodeTrace? targetTrace) (← decodeAssignment? captured)
        (← decodeAssignment? completed) (← decodeEvents? history))
  | _ => none
termination_by wire => sizeOf wire

def decodeEvents? : Term → Option (List GeneralPremise.Event)
  | .symbol "LNil" => some []
  | .application "LCons" [event, events] => do
      pure ((← decodeEvent? event) :: (← decodeEvents? events))
  | _ => none
termination_by wire => sizeOf wire

def decodeQuantifiedEvents? : Term → Option (List (Nat × Pattern × List GeneralPremise.Event))
  | .symbol "LNil" => some []
  | .application "LCons" [.application "QuantifiedElement" [.natural index, element, history], rest] => do
      pure ((index, ← InferenceCettaWire.decodePattern element, ← decodeEvents? history) ::
        (← decodeQuantifiedEvents? rest))
  | _ => none
termination_by wire => sizeOf wire
end

mutual
@[simp] theorem decodeEvent?_eventTerm (event : GeneralPremise.Event) :
    decodeEvent? (PremiseOperationsExecution.GeneralExecution.eventTerm event) = some event := by
  cases event with
  | query index quantifiers row origins => simp [PremiseOperationsExecution.GeneralExecution.eventTerm, decodeEvent?, decodeOrigins_originsTerm]
  | freshness index quantifiers atom subject => simp [PremiseOperationsExecution.GeneralExecution.eventTerm, decodeEvent?]
  | quantified index quantifiers kind elements =>
      simp [PremiseOperationsExecution.GeneralExecution.eventTerm, decodeEvent?, decodeQuantifiedEvents?_quantifiedEventsTerm elements]
  | child index quantifiers declaration bound source target trace targetTrace captured completed history =>
      simp [PremiseOperationsExecution.GeneralExecution.eventTerm, decodeEvent?, decodeEvents?_eventsTerm history, decodeList_encodeList]
termination_by sizeOf event

@[simp] theorem decodeEvents?_eventsTerm (events : List GeneralPremise.Event) :
    decodeEvents? (PremiseOperationsExecution.GeneralExecution.eventsTerm events) = some events := by
  cases events with
  | nil => simp [PremiseOperationsExecution.GeneralExecution.eventsTerm, decodeEvents?]
  | cons event events =>
      simp [PremiseOperationsExecution.GeneralExecution.eventsTerm, decodeEvents?, decodeEvent?_eventTerm event, decodeEvents?_eventsTerm events]
termination_by sizeOf events

@[simp] theorem decodeQuantifiedEvents?_quantifiedEventsTerm
    (elements : List (Nat × Pattern × List GeneralPremise.Event)) :
    decodeQuantifiedEvents? (PremiseOperationsExecution.GeneralExecution.quantifiedEventsTerm elements) = some elements := by
  cases elements with
  | nil => simp [PremiseOperationsExecution.GeneralExecution.quantifiedEventsTerm, decodeQuantifiedEvents?]
  | cons entry rest =>
      rcases entry with ⟨index, element, history⟩
      simp [PremiseOperationsExecution.GeneralExecution.quantifiedEventsTerm, decodeQuantifiedEvents?, decodeEvents?_eventsTerm history,
        decodeQuantifiedEvents?_quantifiedEventsTerm rest]
termination_by sizeOf elements
end

def receiptTerm (receipt : Receipt) : Term :=
  .application "RuleJobReceipt" [jobTerm receipt.job, PremiseOperationsExecution.GeneralExecution.traceTerm receipt.matcherTrace,
    assignmentTerm receipt.captured, assignmentTerm receipt.completed, PremiseOperationsExecution.GeneralExecution.eventsTerm receipt.premiseHistory,
    InferenceCettaWire.encodePattern receipt.localTarget, InferenceCettaWire.encodePattern receipt.target]

def decodeReceipt? : Term → Option Receipt
  | .application "RuleJobReceipt" [job, trace, captured, completed, history, localTarget, target] => do
      pure ⟨← decodeJob? job, ← decodeTrace? trace, ← decodeAssignment? captured,
        ← decodeAssignment? completed, ← decodeEvents? history,
        ← InferenceCettaWire.decodePattern localTarget, ← InferenceCettaWire.decodePattern target⟩
  | _ => none

@[simp] theorem decodeReceipt?_receiptTerm (receipt : Receipt) :
    decodeReceipt? (receiptTerm receipt) = some receipt := by
  cases receipt
  simp [receiptTerm, decodeReceipt?]

theorem receiptTerm_injective : Function.Injective receiptTerm := by
  intro first second same
  have decoded := congrArg decodeReceipt? same
  simpa only [decodeReceipt?_receiptTerm, Option.some.injEq] using decoded

private def decodeOriginRowWith? {Choice : Type} (decodeChoice : Term → Option Choice) :
    Term → Option (Nat × List Choice)
  | .application "ArgumentOrigin" [.natural index, trace] => do
      pure (index, ← decodeList decodeChoice trace)
  | _ => none

private theorem decodeOriginsWith_originsTerm {Choice : Type} (choiceTerm : Choice → Term)
    (decodeChoice : Term → Option Choice) (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice)
    (origins : List (Nat × List Choice)) :
    decodeList (decodeOriginRowWith? decodeChoice) (RetainedMatchingWire.originsTerm choiceTerm origins) =
      some origins := by
  unfold RetainedMatchingWire.originsTerm
  apply decodeList_encodeList
  intro origin
  simp [decodeOriginRowWith?, decodeList_encodeList decodeChoice choiceTerm inverse]

mutual
def decodeEventWith? {Choice : Type} (decodeChoice : Term → Option Choice) : Term → Option (GeneralPremise.Event Choice)
  | .application "PremiseQueryEvent" [.natural index, .natural quantifiers, .natural row, origins] => do
      pure (.query index quantifiers row (← decodeList (decodeOriginRowWith? decodeChoice) origins))
  | .application "PremiseFreshnessEvent" [.natural index, .natural quantifiers, .string atom, subject] => do
      pure (.freshness index quantifiers atom (← InferenceCettaWire.decodePattern subject))
  | .application "PremiseQuantifiedEvent" [.natural index, .natural quantifiers, kind, elements] => do
      pure (.quantified index quantifiers (← InferenceCettaWire.decodeCollectionType kind)
        (← decodeQuantifiedEventsWith? decodeChoice elements))
  | .application "PremiseChildEvent" [.natural index, .natural quantifiers, .natural declaration,
      bound, source, target, trace, targetTrace, captured, completed, history] => do
      pure (.child index quantifiers declaration (← decodeList InferenceCettaWire.AuthoredRule.decodeType? bound)
        (← InferenceCettaWire.decodePattern source) (← InferenceCettaWire.decodePattern target)
        (← decodeList decodeChoice trace) (← decodeList decodeChoice targetTrace) (← decodeAssignment? captured)
        (← decodeAssignment? completed) (← decodeEventsWith? decodeChoice history))
  | _ => none
termination_by wire => sizeOf wire

def decodeEventsWith? {Choice : Type} (decodeChoice : Term → Option Choice) :
    Term → Option (List (GeneralPremise.Event Choice))
  | .symbol "LNil" => some []
  | .application "LCons" [event, events] => do
      pure ((← decodeEventWith? decodeChoice event) :: (← decodeEventsWith? decodeChoice events))
  | _ => none
termination_by wire => sizeOf wire

def decodeQuantifiedEventsWith? {Choice : Type} (decodeChoice : Term → Option Choice) :
    Term → Option (List (Nat × Pattern × List (GeneralPremise.Event Choice)))
  | .symbol "LNil" => some []
  | .application "LCons" [.application "QuantifiedElement" [.natural index, element, history], rest] => do
      pure ((index, ← InferenceCettaWire.decodePattern element, ← decodeEventsWith? decodeChoice history) ::
        (← decodeQuantifiedEventsWith? decodeChoice rest))
  | _ => none
termination_by wire => sizeOf wire
end

mutual
theorem decodeEventWith?_eventTerm {Choice : Type} (choiceTerm : Choice → Term)
    (decodeChoice : Term → Option Choice) (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice)
    (event : GeneralPremise.Event Choice) :
    decodeEventWith? decodeChoice (RetainedMatchingWire.eventTerm choiceTerm event) = some event := by
  cases event with
  | query index quantifiers row origins =>
      simp [RetainedMatchingWire.eventTerm, decodeEventWith?, decodeOriginsWith_originsTerm choiceTerm decodeChoice inverse]
  | freshness index quantifiers atom subject => simp [RetainedMatchingWire.eventTerm, decodeEventWith?]
  | quantified index quantifiers kind elements =>
      simp [RetainedMatchingWire.eventTerm, decodeEventWith?,
        decodeQuantifiedEventsWith?_quantifiedEventsTerm choiceTerm decodeChoice inverse elements]
  | child index quantifiers declaration bound source target trace targetTrace captured completed history =>
      simp [RetainedMatchingWire.eventTerm, decodeEventWith?,
        PremiseOperationsExecution.GeneralExecution.Base.typesTerm,
        decodeEventsWith?_eventsTerm choiceTerm decodeChoice inverse history,
        decodeList_encodeList decodeChoice choiceTerm inverse, decodeList_encodeList]
termination_by sizeOf event

theorem decodeEventsWith?_eventsTerm {Choice : Type} (choiceTerm : Choice → Term)
    (decodeChoice : Term → Option Choice) (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice)
    (events : List (GeneralPremise.Event Choice)) :
    decodeEventsWith? decodeChoice (RetainedMatchingWire.eventsTerm choiceTerm events) = some events := by
  cases events with
  | nil => simp [RetainedMatchingWire.eventsTerm, decodeEventsWith?]
  | cons event events =>
      simp [RetainedMatchingWire.eventsTerm, decodeEventsWith?,
        decodeEventWith?_eventTerm choiceTerm decodeChoice inverse event,
        decodeEventsWith?_eventsTerm choiceTerm decodeChoice inverse events]
termination_by sizeOf events

theorem decodeQuantifiedEventsWith?_quantifiedEventsTerm {Choice : Type} (choiceTerm : Choice → Term)
    (decodeChoice : Term → Option Choice) (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice)
    (elements : List (Nat × Pattern × List (GeneralPremise.Event Choice))) :
    decodeQuantifiedEventsWith? decodeChoice (RetainedMatchingWire.quantifiedEventsTerm choiceTerm elements) =
      some elements := by
  cases elements with
  | nil => simp [RetainedMatchingWire.quantifiedEventsTerm, decodeQuantifiedEventsWith?]
  | cons entry rest =>
      rcases entry with ⟨index, element, history⟩
      simp [RetainedMatchingWire.quantifiedEventsTerm, decodeQuantifiedEventsWith?,
        decodeEventsWith?_eventsTerm choiceTerm decodeChoice inverse history,
        decodeQuantifiedEventsWith?_quantifiedEventsTerm choiceTerm decodeChoice inverse rest]
termination_by sizeOf elements
end

/-- The choice encoder is declared separately from the retained receipt fields. -/
def receiptTermWith {Choice : Type} (choiceTerm : Choice → Term) (receipt : Receipt Choice) : Term :=
  .application "RuleJobReceipt" [jobTerm receipt.job, encodeList choiceTerm receipt.matcherTrace,
    assignmentTerm receipt.captured, assignmentTerm receipt.completed,
    RetainedMatchingWire.eventsTerm choiceTerm receipt.premiseHistory,
    InferenceCettaWire.encodePattern receipt.localTarget, InferenceCettaWire.encodePattern receipt.target]

def decodeReceiptWith? {Choice : Type} (decodeChoice : Term → Option Choice) : Term → Option (Receipt Choice)
  | .application "RuleJobReceipt" [job, trace, captured, completed, history, localTarget, target] => do
      pure ⟨← decodeJob? job, ← decodeList decodeChoice trace, ← decodeAssignment? captured,
        ← decodeAssignment? completed, ← decodeEventsWith? decodeChoice history,
        ← InferenceCettaWire.decodePattern localTarget, ← InferenceCettaWire.decodePattern target⟩
  | _ => none

theorem decodeReceiptWith?_receiptTermWith {Choice : Type} (choiceTerm : Choice → Term)
    (decodeChoice : Term → Option Choice) (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice)
    (receipt : Receipt Choice) : decodeReceiptWith? decodeChoice (receiptTermWith choiceTerm receipt) = some receipt := by
  cases receipt
  simp [receiptTermWith, decodeReceiptWith?, decodeList_encodeList decodeChoice choiceTerm inverse,
    decodeEventsWith?_eventsTerm choiceTerm decodeChoice inverse]

theorem receiptTermWith_injective {Choice : Type} (choiceTerm : Choice → Term)
    (decodeChoice : Term → Option Choice) (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice) :
    Function.Injective (receiptTermWith choiceTerm) := by
  intro first second same
  have decoded := congrArg (decodeReceiptWith? decodeChoice) same
  simpa only [decodeReceiptWith?_receiptTermWith choiceTerm decodeChoice inverse, Option.some.injEq] using decoded

theorem receiptTermWith_ordinary (receipt : Receipt) :
    receiptTermWith RetainedMatchingWire.ordinaryCodec.choiceTerm receipt = receiptTerm receipt := by
  unfold receiptTermWith receiptTerm
  rw [RetainedMatchingWire.ordinary_events]
  rfl

theorem decodeReceiptWith?_wrong_constructor {Choice : Type} (decodeChoice : Term → Option Choice) :
    decodeReceiptWith? decodeChoice (.application "RootAnswer" []) = none := rfl

#print axioms decodeEventWith?_eventTerm
#print axioms decodeEventsWith?_eventsTerm
#print axioms decodeQuantifiedEventsWith?_quantifiedEventsTerm
#print axioms decodeReceiptWith?_receiptTermWith
#print axioms receiptTermWith_injective
#print axioms receiptTermWith_ordinary
#print axioms decodeReceiptWith?_wrong_constructor


def requestProjectionTerm (request : GeneralRuleJobExecution.Request) (footprint : List String) : Term :=
  .application "RuleJobRequestProjection"
    [PremiseOperationsExecution.GeneralExecution.environmentTerm request.environment (request.environment.free.entriesOn footprint),
     InferenceCettaWire.ContextObservation.permissionsTerm request.plan.permissions.sites, encodeList InferenceCettaWire.AuthoredRule.typeTerm request.bound,
     InferenceCettaWire.AuthoredRule.typeTerm request.expected, InferenceCettaWire.encodePattern request.source, jobTerm request.job]


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedRuleJobReadoutExecution

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedRuleJobReadoutExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program Equation)
open Eval
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralTypedSites DerivedContexts
open scoped ProgramQuotation

def sourceProgram : Program := RuleExecutionProgram.ruleJobReadoutProgram

def runtime : Program := RuleExecutionProgram.program.append sourceProgram

theorem runtime_eq_append : runtime = RuleExecutionProgram.program.append sourceProgram := rfl

theorem source_declarations : sourceProgram.declarations = [
    .expression [.symbol ":", .symbol "gslt:rule:site-replacement-represented",
      .expression [.symbol "->", .symbol "Atom", .symbol "Atom", .symbol "Atom", .symbol "Atom", .symbol "%Undefined%"]],
    .expression [.symbol ":", .symbol "gslt:rule:job-finish-root",
      .expression [.symbol "->", .symbol "Atom", .symbol "Atom", .symbol "%Undefined%"]]] := rfl

theorem source_equation_heads : sourceProgram.equations.map SpaceSemantics.Equation.head =
    ["gslt:rule:site-replacement-represented", "gslt:rule:job-finish-root"] := rfl

theorem source_load_order : sourceProgram.layout =
    [.equation, .equation, .declaration, .declaration] := rfl

theorem source_raw_arguments :
    (List.range 4).all (Eval.argumentIsRaw sourceProgram "gslt:rule:site-replacement-represented") = true ∧
      (List.range 2).all (Eval.argumentIsRaw sourceProgram "gslt:rule:job-finish-root") = true := by
  decide +kernel

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev number (value : Nat) : Atom := encoded (.natural value)
private abbrev patternValue (pattern : Pattern) : Atom := encoded (InferenceCettaWire.encodePattern pattern)
private abbrev contextValue (context : OneHoleContext) : Atom :=
  encoded (InferenceCettaWire.ContextObservation.contextTerm context)
private abbrev framesValue (frames : List TypingFrame) : Atom := encoded (encodeList typingFrameTerm frames)
private abbrev declarationsValue (language : LanguageDef) : Atom :=
  encoded (PremiseOperationsExecution.DeclarationTyping.declarationsTerm language.terms)

attribute [local simp] Effects.boolean encoded number patternValue contextValue framesValue declarationsValue

private inductive Helper where | represented | finish
private def Helper.head : Helper → String
  | .represented => "gslt:rule:site-replacement-represented"
  | .finish => "gslt:rule:job-finish-root"
private def Helper.names : Helper → List String
  | .represented => ["declarations", "context", "frames", "target"]
  | .finish => ["request", "result"]
private def ownedHeads : List String := [.represented, .finish].map Helper.head

private def retainedHead (head : String) : Bool := head != "eval" && !ownedHeads.contains head
private theorem retained_closed : ProgramClosed retainedHead RuleExecutionProgram.program := by
  exact BridgeKit.closed_of_all _ _ (by decide +kernel) (by decide +kernel)
private theorem retained_agreement : ProgramAgreementOn retainedHead RuleExecutionProgram.program runtime := by
  exact appended_program_agreement_of_all _ _ _ (by decide +kernel) (by decide +kernel)
private theorem retained_returns {caller : Subst} {state : State} {code answer : Atom}
    (supported : codeWithin retainedHead code = true)
    (returned : PureReturns RuleExecutionProgram.program caller state code state answer) :
    PureReturns runtime caller state code state answer :=
  path_of_closed_agreement retained_closed retained_agreement ⟨supported, rfl⟩ returned

private def equations (head : String) : List SpaceSemantics.Equation := runtime.equations.filter (fun equation => equation.head == head)
private def equation (helper : Helper) : SpaceSemantics.Equation := (equations helper.head)[0]'(by cases helper <;> decide +kernel)
private def environment (helper : Helper) (values : List Atom) : Subst := (helper.names.zip values).reverse

private theorem helper_clause (helper : Helper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses runtime helper.head values = [.evaluate (environment helper values) (equation helper).body] :=
  PureData.named_equation_clause runtime helper.head (equation helper) helper.names values
    (by cases helper <;> rfl) (by cases helper <;> decide +kernel)
    (by cases helper <;> decide) length

private theorem helper_raw (helper : Helper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw runtime helper.head index = true := by
  have checked : (List.range helper.names.length).all
      (fun index => argumentIsRaw runtime helper.head index) = true := by
    cases helper <;> decide +kernel
  exact List.all_eq_true.mp checked index (List.mem_range.mpr bounded)

private theorem helper_call (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns runtime (environment helper values) state (equation helper).body state answer) :
    PureReturns runtime caller state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return runtime caller (environment helper values) state state
    helper.head arguments (equation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide +kernel)
  · intro index bounded
    apply helper_raw helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · rw [captured]
    exact helper_clause helper values length
  · exact returned

private theorem captured_closed (values : List Atom) : values.map (applySubst []) = values := by
  have unchanged : applySubst [] = id := by
    funext value; exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
  simp only [unchanged, List.map_id]

private theorem helper_capture (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns runtime [] state (a helper.head values) state answer) :
    PureReturns runtime caller state (a helper.head arguments) state answer := by
  apply PureData.raw_capture_returns runtime [] caller state state helper.head values arguments answer
    (by cases helper <;> decide +kernel) _ (by cases helper <;> decide) _ returned
  · intro index bounded
    exact helper_raw helper index (by omega)
  · simpa only [captured_closed] using captured.symm

private theorem branch_returns (caller selected : Subst) (state : State)
    (expression value : Atom) (rows : SpaceSemantics.Cases) (body answer : Atom)
    (computed : PureReturns runtime caller state expression state value)
    (matched : SpaceSemantics.selectCase caller value rows = some (selected, body))
    (continued : PureReturns runtime selected state body state answer) :
    PureReturns runtime caller state
      (a "case" [expression, .expression (rows.map fun row => .expression [row.1, row.2])]) state answer :=
  case_returns runtime caller selected state state state expression value body answer _ rows
    (read_cases_encoded _) computed matched continued

private theorem bool_if_returns (caller : Subst) (state : State) (condition : Atom)
    (value : Bool) (yes no answer : Atom)
    (tested : PureReturns runtime caller state condition state (Effects.boolean value))
    (returned : PureReturns runtime caller state (if value then yes else no) state answer) :
    PureReturns runtime caller state (a "if" [condition, yes, no]) state answer := by
  apply if_returns runtime caller state state state condition (Effects.boolean value) yes no answer tested
  have boolean_same : (Effects.boolean value == Effects.boolean true) = value := by
    cases value <;> decide +kernel
  simpa only [boolean_same] using returned

private theorem named_let_returns (caller : Subst) (state : State) (name : String)
    (expression value body answer : Atom)
    (fresh : Subst.lookup caller name = none)
    (returned : PureReturns runtime caller state expression state value)
    (continuation : PureReturns runtime ((name, value) :: caller) state body state answer) :
    PureReturns runtime caller state (a "let" [v name, expression, body]) state answer := by
  apply let_returns runtime caller ((name, value) :: caller) state state state
    (v name) expression body value answer returned _ continuation
  simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]


private def representationValues (language : LanguageDef) (context : OneHoleContext)
    (frames : List TypingFrame) (target : Pattern) : List Atom :=
  [declarationsValue language, contextValue context, framesValue frames, patternValue target]

private def recurseBody : Atom := a Helper.represented.head
  [v "declarations", v "inner", v "tail", v "target"]

private def parameterBody : Atom :=
  a "let" [v "filled", a "gslt:rule:scope-fill" [v "inner", v "target"],
    a "if" [a "gslt:premise:parameter-representation" [v "parameter", v "filled"],
      recurseBody, Effects.boolean false]]

private def parameterFallback : CollectionRepresentation → String
  | .bare => "_____________"
  | .wrapped => "______________"

private def parameterCases (mode : CollectionRepresentation) : SpaceSemantics.Cases :=
  [(a "Some" [v "parameter"], parameterBody), (v (parameterFallback mode), Effects.boolean false)]

private def declarationBody (mode : CollectionRepresentation) : Atom := a "case" [a "gslt:rule:row-at" [v "index", v "parameters"],
  .expression ((parameterCases mode).map fun row => .expression [row.1, row.2])]

private def declarationCases : SpaceSemantics.Cases :=
  [(a "Some" [a "GrammarTypingV1" [v "label", v "category", v "parameters"]], declarationBody .bare),
   (a "Some" [a "GrammarTypingWrappedV1" [v "label", v "category", v "parameters"]], declarationBody .wrapped),
   (v "_______________", Effects.boolean false)]

private def applicationBody : Atom := a "case" [a "gslt:rule:row-at" [v "declaration", v "declarations"],
  .expression (declarationCases.map fun row => .expression [row.1, row.2])]

private def representationCases : SpaceSemantics.Cases :=
  [(a "ReplacementShape" [.symbol "ContextHole", .symbol "LNil"], Effects.boolean true),
   (a "ReplacementShape" [a "ContextApp" [v "head", v "before", v "inner", v "after"],
      a "LCons" [a "TypingApplication" [v "declaration", v "index"], v "tail"]], applicationBody),
   (a "ReplacementShape" [a "ContextLam" [v "binder", v "inner"],
      a "LCons" [a "TypingLambda" [v "domain"], v "tail"]], recurseBody),
   (a "ReplacementShape" [a "ContextMultiLam" [v "arity", v "binders", v "inner"],
      a "LCons" [a "TypingMultiLambda" [v "frameArity", v "domain"], v "tail"]], recurseBody),
   (a "ReplacementShape" [a "ContextCollection" [v "kind", v "before", v "inner", v "after", v "rest"],
      a "LCons" [a "TypingDirectCollection" [v "frameKind"], v "tail"]], recurseBody),
   (a "ReplacementShape" [a "ContextCollection" [v "kind", v "before", v "inner", v "after", v "rest"],
      a "LCons" [a "TypingAuthoredCollection" [v "declaration"], v "tail"]], recurseBody),
   (v "________________", Effects.boolean false)]

private theorem representation_shape : (equation .represented).body =
    a "case" [a "ReplacementShape" [v "context", v "frames"],
      .expression (representationCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private def representationBindings (context : OneHoleContext) (frames : List TypingFrame) : Subst :=
  match context, frames with
  | .hole, [] => []
  | .apply head before inner after, .application declaration index :: frames =>
      [("tail", framesValue frames), ("index", number index), ("declaration", number declaration),
       ("after", encoded (InferenceCettaWire.encodePatterns after)), ("inner", contextValue inner),
       ("before", encoded (InferenceCettaWire.encodePatterns before)), ("head", encoded (.string head))]
  | .lambda binder inner, .lambda domain :: frames =>
      [("tail", framesValue frames), ("domain", encoded (InferenceCettaWire.AuthoredRule.typeTerm domain)),
       ("inner", contextValue inner), ("binder", encoded (InferenceCettaWire.encodeBinder binder))]
  | .multiLambda arity binders inner, .multiLambda frameArity domain :: frames =>
      [("tail", framesValue frames), ("domain", encoded (InferenceCettaWire.AuthoredRule.typeTerm domain)),
       ("frameArity", number frameArity), ("inner", contextValue inner),
       ("binders", encoded (encodeList Term.string binders)), ("arity", number arity)]
  | .collection kind before inner after rest, .directCollection frameKind :: frames =>
      [("tail", framesValue frames), ("frameKind", encoded (InferenceCettaWire.encodeCollectionType frameKind)),
       ("rest", encoded (InferenceCettaWire.encodeRest rest)), ("after", encoded (InferenceCettaWire.encodePatterns after)),
       ("inner", contextValue inner), ("before", encoded (InferenceCettaWire.encodePatterns before)),
       ("kind", encoded (InferenceCettaWire.encodeCollectionType kind))]
  | .collection kind before inner after rest, .authoredCollection declaration :: frames =>
      [("tail", framesValue frames), ("declaration", number declaration),
       ("rest", encoded (InferenceCettaWire.encodeRest rest)), ("after", encoded (InferenceCettaWire.encodePatterns after)),
       ("inner", contextValue inner), ("before", encoded (InferenceCettaWire.encodePatterns before)),
       ("kind", encoded (InferenceCettaWire.encodeCollectionType kind))]
  | context, frames => [("________________", a "ReplacementShape" [contextValue context, framesValue frames])]

private def representationBody : OneHoleContext → List TypingFrame → Atom
  | .hole, [] => Effects.boolean true
  | .apply .., .application .. :: _ => applicationBody
  | .lambda .., .lambda .. :: _ => recurseBody
  | .multiLambda .., .multiLambda .. :: _ => recurseBody
  | .collection .., .directCollection .. :: _ => recurseBody
  | .collection .., .authoredCollection .. :: _ => recurseBody
  | _, _ => Effects.boolean false

private theorem shape_template : PureData.Template runtime (a "ReplacementShape" [v "context", v "frames"]) := by
  apply PureData.Template.constructor "ReplacementShape" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .captured _

private theorem representation_frame_returns (state : State) (language : LanguageDef)
    (context : OneHoleContext) (frames : List TypingFrame) (target : Pattern)
    (continued : PureReturns runtime
      (representationBindings context frames ++ environment .represented (representationValues language context frames target))
      state (representationBody context frames) state
      (Effects.boolean (GeneralTypedOccurrence.replacementRepresentations? language context frames target))) :
    PureReturns runtime [] state (a Helper.represented.head (representationValues language context frames target)) state
      (Effects.boolean (GeneralTypedOccurrence.replacementRepresentations? language context frames target)) := by
  let caller := environment .represented (representationValues language context frames target)
  apply helper_call .represented [] state _ _ _ rfl (captured_closed _)
  rw [representation_shape]
  apply branch_returns caller (representationBindings context frames ++ caller) state
    (a "ReplacementShape" [v "context", v "frames"])
    (a "ReplacementShape" [contextValue context, framesValue frames]) representationCases
    (representationBody context frames)
  · simpa [caller, environment, representationValues, Helper.names, applySubst,
      applySubst.applySubstList, Subst.lookup] using PureData.template_return runtime caller state _ shape_template
  · cases context <;> cases frames with
    | nil => simp [representationCases, representationBindings, representationBody,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        caller, environment, representationValues, Helper.names, matchAtom, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        InferenceCettaWire.ContextObservation.contextTerm, encodeList]
    | cons frame frames => cases frame <;> simp [representationCases, representationBindings, representationBody,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        caller, environment, representationValues, Helper.names, matchAtom, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        InferenceCettaWire.ContextObservation.contextTerm, typingFrameTerm, encodeList, InferenceCettaWire.encodeList]
  · exact continued

private theorem row_captured_returns {α : Type} (caller : Subst) (state : State)
    (index : Nat) (rows : List α) (encoder : α → Term) (first second : String)
    (captured : [v first, v second].map (applySubst caller) =
      [number index, encoded (encodeList encoder rows)]) :
    PureReturns runtime caller state (a "gslt:rule:row-at" [v first, v second]) state
      (encoded (encodeOption encoder rows[index]?)) := by
  have returned := retained_returns (by rfl)
    (RuleInstantiationExecution.RowLookup.row_at_captured_returns caller state index
      (rows.map encoder) (v first) (v second)
      (by simpa only [encodeList_map, Function.id_comp] using captured))
  rw [List.getElem?_map] at returned
  cases found : rows[index]? <;>
    simpa [found, MatchAutomataBindingExecution.payloadOptionTerm, encodeOption] using returned

private def applicationCaller (language : LanguageDef) (head : String) (before after : List Pattern)
    (inner : OneHoleContext) (declaration index : Nat) (frames : List TypingFrame) (target : Pattern) : Subst :=
  representationBindings (.apply head before inner after) (.application declaration index :: frames) ++
    environment .represented (representationValues language (.apply head before inner after)
      (.application declaration index :: frames) target)

private def declarationCaller (caller : Subst) (grammar : GrammarRule) : Subst :=
  [("parameters", encoded (encodeList InferenceCettaWire.AuthoredRule.parameterTerm grammar.params)),
   ("category", encoded (.string grammar.category)), ("label", encoded (.string grammar.label))] ++ caller

private theorem representation_application_returns (state : State) (language : LanguageDef)
    (head : String) (before after : List Pattern) (inner : OneHoleContext)
    (declaration index : Nat) (frames : List TypingFrame) (target : Pattern)
    (recursive : PureReturns runtime [] state
      (a Helper.represented.head (representationValues language inner frames target)) state
      (Effects.boolean (GeneralTypedOccurrence.replacementRepresentations? language inner frames target))) :
    PureReturns runtime (applicationCaller language head before after inner declaration index frames target)
      state applicationBody state
      (Effects.boolean (GeneralTypedOccurrence.replacementRepresentations? language
        (.apply head before inner after) (.application declaration index :: frames) target)) := by
  let caller := applicationCaller language head before after inner declaration index frames target
  have lookup := row_captured_returns caller state declaration language.terms
    InferenceCettaWire.AuthoredRule.typingDeclarationTerm "declaration" "declarations" (by
      simp [caller, applicationCaller, representationBindings, environment, representationValues,
        Helper.names, applySubst, Subst.lookup, PremiseOperationsExecution.DeclarationTyping.declarationsTerm])
  unfold applicationBody
  cases declared : language.terms[declaration]? with
  | none =>
      apply branch_returns caller (("_______________", .symbol "None") :: caller) state
        (a "gslt:rule:row-at" [v "declaration", v "declarations"]) (.symbol "None")
        declarationCases (Effects.boolean false)
      · simpa [declared, encodeOption, CettaWireAtom.encode] using lookup
      · simp [declarationCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          matchAtom, Subst.lookup, caller, applicationCaller,
          representationBindings, environment, representationValues, Helper.names]
      · simpa [GeneralTypedOccurrence.replacementRepresentations?, declared, Effects.boolean] using
          (grounded_returns runtime _ state (.bool false))
  | some grammar =>
      let parsed := declarationCaller caller grammar
      apply branch_returns caller parsed state
        (a "gslt:rule:row-at" [v "declaration", v "declarations"])
        (encoded (.application "Some" [InferenceCettaWire.AuthoredRule.typingDeclarationTerm grammar]))
        declarationCases (declarationBody grammar.collectionRepresentation)
      · simpa [declared, encodeOption, CettaWireAtom.encode] using lookup
      · cases mode : grammar.collectionRepresentation <;> simp [mode, declarationCases, parsed, declarationCaller, InferenceCettaWire.AuthoredRule.typingDeclarationTerm,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, caller, applicationCaller, representationBindings, environment,
          representationValues, Helper.names, CettaWireAtom.encode, CettaWireAtom.encodeMany]
        all_goals rfl
      · have lookupParameter := row_captured_returns parsed state index grammar.params
          InferenceCettaWire.AuthoredRule.parameterTerm "index" "parameters" (by
            simp [parsed, declarationCaller, caller, applicationCaller, representationBindings,
              environment, representationValues, Helper.names, applySubst, Subst.lookup])
        unfold declarationBody
        cases parameterFound : grammar.params[index]? with
        | none =>
            apply branch_returns parsed ((parameterFallback grammar.collectionRepresentation, .symbol "None") :: parsed) state
              (a "gslt:rule:row-at" [v "index", v "parameters"]) (.symbol "None")
              (parameterCases grammar.collectionRepresentation) (Effects.boolean false)
            · simpa [parameterFound, encodeOption, CettaWireAtom.encode] using lookupParameter
            · cases grammar.collectionRepresentation <;> simp [parameterCases, parameterFallback, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                matchAtom, Subst.lookup, parsed, declarationCaller,
                caller, applicationCaller, representationBindings, environment, representationValues, Helper.names]
            · simpa [GeneralTypedOccurrence.replacementRepresentations?, declared, parameterFound,
                Effects.boolean] using (grounded_returns runtime _ state (.bool false))
        | some parameter =>
            let selected := ("parameter", encoded (InferenceCettaWire.AuthoredRule.parameterTerm parameter)) :: parsed
            apply branch_returns parsed selected state (a "gslt:rule:row-at" [v "index", v "parameters"])
              (encoded (.application "Some" [InferenceCettaWire.AuthoredRule.parameterTerm parameter]))
              (parameterCases grammar.collectionRepresentation) parameterBody
            · simpa [parameterFound, encodeOption, CettaWireAtom.encode] using lookupParameter
            · cases grammar.collectionRepresentation <;> simp [parameterCases, parameterFallback, selected, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, parsed, declarationCaller,
                caller, applicationCaller, representationBindings, environment, representationValues,
                Helper.names, CettaWireAtom.encode, CettaWireAtom.encodeMany]
            · unfold parameterBody
              let filled := ("filled", patternValue (inner.fill target)) :: selected
              apply named_let_returns selected state "filled" _ (patternValue (inner.fill target)) _ _
              · simp [selected, parsed, declarationCaller, caller, applicationCaller, representationBindings,
                  environment, representationValues, Helper.names, Subst.lookup]
              · apply retained_returns (by decide +kernel)
                exact RuleInstantiationExecution.ContextObservation.fill_captured_returns selected state inner target
                  (v "inner") (v "target") (by
                    simp [selected, parsed, declarationCaller, caller, applicationCaller, representationBindings,
                      environment, representationValues, Helper.names, Subst.lookup, applySubst])
              · apply bool_if_returns filled state _ (WellSorted.matchesParameterRepresentation? parameter (inner.fill target)) _ _ _
                · apply retained_returns (by decide +kernel)
                  exact PremiseOperationsExecution.TypedParameters.parameter_representation_captured_returns filled
                    state parameter (inner.fill target) (v "parameter") (v "filled") (by
                      simp [filled, selected, parsed, declarationCaller, caller, applicationCaller, representationBindings,
                        environment, representationValues, Helper.names, Subst.lookup, applySubst])
                · cases represented : WellSorted.matchesParameterRepresentation? parameter (inner.fill target) with
                  | false =>
                      simpa [GeneralTypedOccurrence.replacementRepresentations?, declared, parameterFound,
                        represented, Effects.boolean] using grounded_returns runtime filled state (.bool false)
                  | true =>
                      simpa [GeneralTypedOccurrence.replacementRepresentations?, declared, parameterFound,
                        represented, recurseBody] using helper_capture .represented filled state _
                          (representationValues language inner frames target) _ rfl (by
                            simp [filled, selected, parsed, declarationCaller, caller, applicationCaller,
                              representationBindings, environment, representationValues, Helper.names,
                              Subst.lookup, applySubst]) recursive

theorem replacement_representations_returns (state : State) (language : LanguageDef)
    (context : OneHoleContext) (frames : List TypingFrame) (target : Pattern) :
    PureReturns runtime [] state (a "gslt:rule:site-replacement-represented"
      (representationValues language context frames target)) state
      (Effects.boolean (GeneralTypedOccurrence.replacementRepresentations? language context frames target)) := by
  induction context generalizing frames with
  | hole =>
      apply representation_frame_returns
      cases frames with
      | nil => simpa [representationBody, GeneralTypedOccurrence.replacementRepresentations?, Effects.boolean] using
          (grounded_returns runtime _ state (.bool true))
      | cons frame frames => cases frame <;>
          simpa [representationBody, GeneralTypedOccurrence.replacementRepresentations?, Effects.boolean] using
            (grounded_returns runtime _ state (.bool false))
  | apply head before inner after ih =>
      apply representation_frame_returns
      cases frames with
      | nil => simpa [representationBody, GeneralTypedOccurrence.replacementRepresentations?, Effects.boolean] using
          (grounded_returns runtime _ state (.bool false))
      | cons frame frames =>
          cases frame with
          | application declaration index => exact
              representation_application_returns state language head before after inner declaration index frames target (ih frames)
          | _ => simpa [representationBody, GeneralTypedOccurrence.replacementRepresentations?, Effects.boolean] using
              (grounded_returns runtime _ state (.bool false))
  | lambda binder inner ih =>
      apply representation_frame_returns
      cases frames with
      | nil => simpa [representationBody, GeneralTypedOccurrence.replacementRepresentations?, Effects.boolean] using
          (grounded_returns runtime _ state (.bool false))
      | cons frame frames =>
          cases frame with
          | lambda domain =>
              simpa [representationBody, GeneralTypedOccurrence.replacementRepresentations?, recurseBody] using
                helper_capture .represented _ state _ (representationValues language inner frames target) _ rfl (by
                  simp [representationBindings, environment, representationValues, Helper.names, applySubst, Subst.lookup]) (ih frames)
          | _ => simpa [representationBody, GeneralTypedOccurrence.replacementRepresentations?, Effects.boolean] using
              (grounded_returns runtime _ state (.bool false))
  | multiLambda arity names inner ih =>
      apply representation_frame_returns
      cases frames with
      | nil => simpa [representationBody, GeneralTypedOccurrence.replacementRepresentations?, Effects.boolean] using
          (grounded_returns runtime _ state (.bool false))
      | cons frame frames =>
          cases frame with
          | multiLambda frameArity domain =>
              simpa [representationBody, GeneralTypedOccurrence.replacementRepresentations?, recurseBody] using
                helper_capture .represented _ state _ (representationValues language inner frames target) _ rfl (by
                  simp [representationBindings, environment, representationValues, Helper.names, applySubst, Subst.lookup]) (ih frames)
          | _ => simpa [representationBody, GeneralTypedOccurrence.replacementRepresentations?, Effects.boolean] using
              (grounded_returns runtime _ state (.bool false))
  | substBody inner replacement ih =>
      apply representation_frame_returns
      simpa [representationBody, GeneralTypedOccurrence.replacementRepresentations?, Effects.boolean] using
        (grounded_returns runtime _ state (.bool false))
  | substReplacement body inner ih =>
      apply representation_frame_returns
      simpa [representationBody, GeneralTypedOccurrence.replacementRepresentations?, Effects.boolean] using
        (grounded_returns runtime _ state (.bool false))
  | collection kind before inner after rest ih =>
      apply representation_frame_returns
      cases frames with
      | nil => simpa [representationBody, GeneralTypedOccurrence.replacementRepresentations?, Effects.boolean] using
          (grounded_returns runtime _ state (.bool false))
      | cons frame frames =>
          cases frame with
          | directCollection frameKind =>
              simpa [representationBody, GeneralTypedOccurrence.replacementRepresentations?, recurseBody] using
                helper_capture .represented _ state _ (representationValues language inner frames target) _ rfl (by
                  simp [representationBindings, environment, representationValues, Helper.names, applySubst, Subst.lookup]) (ih frames)
          | authoredCollection declaration =>
              simpa [representationBody, GeneralTypedOccurrence.replacementRepresentations?, recurseBody] using
                helper_capture .represented _ state _ (representationValues language inner frames target) _ rfl (by
                  simp [representationBindings, environment, representationValues, Helper.names, applySubst, Subst.lookup]) (ih frames)
          | _ => simpa [representationBody, GeneralTypedOccurrence.replacementRepresentations?, Effects.boolean] using
              (grounded_returns runtime _ state (.bool false))

theorem replacement_representations_captured_returns (caller : Subst) (state : State)
    (language : LanguageDef) (context : OneHoleContext) (frames : List TypingFrame) (target : Pattern)
    (one two three four : Atom)
    (captured : [one, two, three, four].map (applySubst caller) = representationValues language context frames target) :
    PureReturns runtime caller state (a "gslt:rule:site-replacement-represented" [one, two, three, four]) state
      (Effects.boolean (GeneralTypedOccurrence.replacementRepresentations? language context frames target)) :=
  helper_capture .represented caller state _ _ _ rfl captured
    (replacement_representations_returns state language context frames target)

private inductive DataConstructor where | input | goal | site | job | receipt | some
private def DataConstructor.head : DataConstructor → String
  | .input => "RuleJobFinishInput"
  | .goal => "RootGoal"
  | .site => "RuleJobSite"
  | .job => "RuleJob"
  | .receipt => "RuleJobReceipt"
  | .some => "Some"

private theorem data_template (constructor : DataConstructor) (children : List Atom)
    (templates : ∀ child ∈ children, PureData.Template runtime child) :
    PureData.Template runtime (a constructor.head children) :=
  .constructor _ _ (by cases constructor <;> decide +kernel) (by cases constructor <;> decide) templates

private theorem data_variables_template (constructor : DataConstructor) (names : List String) :
    PureData.Template runtime (a constructor.head (names.map v)) := by
  apply data_template
  intro child member
  obtain ⟨name, _, rfl⟩ := List.mem_map.mp member
  exact .captured name

private def nativeGoalBody : Atom := a "RootGoal" [v "focusBound", v "focusType", v "focus", v "ordinal"]

private def nativeReceiptBody : Atom := a "Some" [a "RuleJobReceipt"
  [a "RuleJob" [v "ordinal", v "declaration", a "RuleJobSite"
    [v "address", v "context", v "focus", v "focusBound", v "focusType", v "frames"]],
   v "trace", v "captured", v "completed", v "history", v "localTarget", v "target"]]

private theorem native_receipt_template : PureData.Template runtime nativeReceiptBody := by
  have site := data_variables_template .site ["address", "context", "focus", "focusBound", "focusType", "frames"]
  have job : PureData.Template runtime (a "RuleJob" [v "ordinal", v "declaration", a "RuleJobSite"
      [v "address", v "context", v "focus", v "focusBound", v "focusType", v "frames"]]) := by
    apply data_template .job
    intro child member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact .captured _
    · exact .captured _
    · exact site
  apply data_template .some
  intro child member
  rcases List.mem_singleton.mp member with rfl
  apply data_template .receipt
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact job
  all_goals exact .captured _

private def finishTypedBody : Atom := a "if"
  [a "gslt:premise:open-well-sorted" [v "declarations", v "free", v "bound", v "expected", v "target"],
   nativeReceiptBody, .symbol "None"]
private def finishFillBody : Atom := a "let"
  [v "target", a "gslt:rule:scope-fill" [v "context", v "localTarget"], finishTypedBody]
private def finishRepresentedBody : Atom := a "if"
  [a Helper.represented.head [v "declarations", v "context", v "frames", v "localTarget"],
   finishFillBody, .symbol "None"]
private def finishPermittedBody : Atom := a "if"
  [a "gslt:rule:scope-permitted" [v "permissions", v "context"], finishRepresentedBody, .symbol "None"]
private def finishGoalBody : Atom := a "if"
  [a "==" [v "goal", nativeGoalBody], finishPermittedBody, .symbol "None"]

private def finishCases : SpaceSemantics.Cases :=
  [(a "RuleJobFinishInput"
    [a "RuleJobRequestProjection"
      [a "PremiseEnvironment" [v "declarations", v "rewrites", v "specifications", v "provider", v "reflection", v "free"],
       v "permissions", v "bound", v "expected", v "source", a "RuleJob" [v "ordinal", v "declaration", a "RuleJobSite"
        [v "address", v "context", v "focus", v "focusBound", v "focusType", v "frames"]]],
     a "PremiseResult" [v "goal", a "RootAnswer" [v "trace", v "captured", v "completed", v "history", v "localTarget"]]],
    finishGoalBody), (v "_______________", .symbol "None")]

private theorem finish_shape : (equation .finish).body = a "case"
    [a "RuleJobFinishInput" [v "request", v "result"], .expression (finishCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

/-- The primitive finisher receives the actual root data and a declared choice
encoder. Premise histories, child traces and query origins remain intact. -/
def rootResultTermWith {Choice : Type} (choiceTerm : Choice → Term)
    (request : GeneralRuleJobExecution.Request) (trace : List Choice)
    (captured completed : Assignment) (history : List (GeneralPremise.Event Choice))
    (localTarget : Pattern) : Term :=
  .application "PremiseResult" [PremiseOperationsExecution.GeneralExecution.goalTerm request.goal,
    .application "RootAnswer" [encodeList choiceTerm trace, assignmentTerm captured,
      assignmentTerm completed, RetainedMatchingWire.eventsTerm choiceTerm history,
      InferenceCettaWire.encodePattern localTarget]]

private def finishValuesWith {Choice : Type} (choiceTerm : Choice → Term)
    (request : GeneralRuleJobExecution.Request) (footprint : List String) (trace : List Choice)
    (captured completed : Assignment) (history : List (GeneralPremise.Event Choice))
    (localTarget : Pattern) : List Atom :=
  [encoded (requestProjectionTerm request footprint),
    encoded (rootResultTermWith choiceTerm request trace captured completed history localTarget)]

private def finishValues (request : GeneralRuleJobExecution.Request) (footprint : List String)
    (result : GeneralPremise.Execution.Result request.environment request.goal) : List Atom :=
  [encoded (requestProjectionTerm request footprint), encoded (PremiseOperationsExecution.GeneralExecution.resultTerm result)]

def finishRootQuery (request : GeneralRuleJobExecution.Request) (footprint : List String)
    (result : GeneralPremise.Execution.Result request.environment request.goal) : Atom :=
  a "gslt:rule:job-finish-root" (finishValues request footprint result)

def finishRootQueryWith {Choice : Type} (choiceTerm : Choice → Term)
    (request : GeneralRuleJobExecution.Request) (footprint : List String) (trace : List Choice)
    (captured completed : Assignment) (history : List (GeneralPremise.Event Choice))
    (localTarget : Pattern) : Atom :=
  a "gslt:rule:job-finish-root"
    (finishValuesWith choiceTerm request footprint trace captured completed history localTarget)

theorem rootResultTermWith_ordinary (request : GeneralRuleJobExecution.Request)
    (trace : List GeneralScopedMatchMachine.BagChoice) (captured completed : Assignment)
    (history : List GeneralPremise.Event) (localTarget : Pattern)
    (valid : GeneralPremise.RootFiring request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history localTarget) :
    rootResultTermWith RetainedMatchingWire.ordinaryCodec.choiceTerm request trace captured completed history localTarget =
      PremiseOperationsExecution.GeneralExecution.resultTerm (.root trace captured completed history localTarget valid) := by
  unfold rootResultTermWith PremiseOperationsExecution.GeneralExecution.resultTerm
  rw [RetainedMatchingWire.ordinary_events]
  rfl

private theorem finishValuesWith_ordinary (request : GeneralRuleJobExecution.Request)
    (footprint : List String) (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : Assignment) (history : List GeneralPremise.Event) (localTarget : Pattern)
    (valid : GeneralPremise.RootFiring request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history localTarget) :
    finishValuesWith RetainedMatchingWire.ordinaryCodec.choiceTerm request footprint trace captured completed history localTarget =
      finishValues request footprint (.root trace captured completed history localTarget valid) := by
  unfold finishValuesWith finishValues
  rw [rootResultTermWith_ordinary request trace captured completed history localTarget valid]
  rfl

private def finishBindingsWith {Choice : Type} (choiceTerm : Choice → Term)
    (request : GeneralRuleJobExecution.Request) (footprint : List String)
    (trace : List Choice) (captured completed : Assignment)
    (history : List (GeneralPremise.Event Choice)) (localTarget : Pattern) : Subst :=
  [("declarations", declarationsValue request.environment.language),
   ("rewrites", encoded (encodeList InferenceCettaWire.AuthoredRule.rewriteTerm request.environment.language.rewrites)),
   ("specifications", encoded (encodeList PremiseOperationsExecution.GeneralExecution.specificationTerm request.environment.specifications)),
   ("provider", encoded (PremiseOperationsExecution.GeneralExecution.providerTerm request.environment.provider)),
   ("reflection", encoded (PremiseOperationsExecution.GeneralExecution.reflectionTerm request.environment.reflection)),
   ("free", encoded (PremiseOperationsExecution.DeclarationTyping.freeContextTerm (request.environment.free.entriesOn footprint))),
   ("permissions", encoded (InferenceCettaWire.ContextObservation.permissionsTerm request.plan.permissions.sites)),
   ("bound", encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm request.bound)),
   ("expected", encoded (InferenceCettaWire.AuthoredRule.typeTerm request.expected)),
   ("source", patternValue request.source), ("ordinal", number request.job.ordinal),
   ("declaration", encoded (rulePlanTerm request.job.declaration)),
   ("address", encoded (encodeList Term.natural request.job.site.address)),
   ("context", contextValue request.job.site.context), ("focus", patternValue request.job.site.focus),
   ("focusBound", encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm request.job.site.focusBound)),
   ("focusType", encoded (InferenceCettaWire.AuthoredRule.typeTerm request.job.site.focusType)),
   ("frames", framesValue request.job.site.typingFrames),
   ("goal", encoded (PremiseOperationsExecution.GeneralExecution.goalTerm request.goal)),
   ("trace", encoded (encodeList choiceTerm trace)),
   ("captured", encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm captured)),
   ("completed", encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm completed)),
   ("history", encoded (RetainedMatchingWire.eventsTerm choiceTerm history)),
   ("localTarget", patternValue localTarget)].reverse

private theorem finish_frame_returnsWith {Choice : Type} (choiceTerm : Choice → Term) (state : State) (request : GeneralRuleJobExecution.Request)
    (footprint : List String) (trace : List Choice)
    (captured completed : Assignment) (history : List (GeneralPremise.Event Choice)) (localTarget : Pattern)
    (answer : Atom)
    (continued : PureReturns runtime
      (finishBindingsWith choiceTerm request footprint trace captured completed history localTarget ++
        environment .finish (finishValuesWith choiceTerm request footprint trace captured completed history localTarget))
      state finishGoalBody state answer) :
    PureReturns runtime [] state (a Helper.finish.head
      (finishValuesWith choiceTerm request footprint trace captured completed history localTarget)) state answer := by
  let values := finishValuesWith choiceTerm request footprint trace captured completed history localTarget
  let caller := environment .finish values
  apply helper_call .finish [] state _ values _ rfl (captured_closed _)
  rw [finish_shape]
  apply branch_returns caller
    (finishBindingsWith choiceTerm request footprint trace captured completed history localTarget ++ caller) state
    (a "RuleJobFinishInput" [v "request", v "result"])
    (a "RuleJobFinishInput" values) finishCases finishGoalBody
  · simpa [caller, values, finishValuesWith, rootResultTermWith, environment, Helper.names, DataConstructor.head, applySubst, applySubst.applySubstList, Subst.lookup] using
      (PureData.template_return runtime caller state _ (data_variables_template .input ["request", "result"]))
  · simp [finishCases, finishBindingsWith, caller, values, finishValuesWith, rootResultTermWith, environment, Helper.names,
      requestProjectionTerm, PremiseOperationsExecution.GeneralExecution.environmentTerm,
      PremiseOperationsExecution.DeclarationTyping.declarationsTerm,
      jobTerm, siteTerm,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  · exact continued

theorem finish_root_interpreted_finite_returns {Choice : Type}
    (choiceTerm : Choice → Term) (meaning : GeneralPremise.MatchingInterpretation Choice) (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (footprint : List String) (trace : List Choice)
    (captured completed : Assignment) (history : List (GeneralPremise.Event Choice)) (localTarget : Pattern)
    (valid : GeneralPremise.Interpreted.RootFiring meaning request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history localTarget)
    (covered : ∀ name ∈ (request.job.site.context.fill localTarget).freeFvarNames, name ∈ footprint) :
    PureReturns runtime [] state
      (finishRootQueryWith choiceTerm request footprint trace captured completed history localTarget) state
      (encoded (encodeOption (fun answer : GeneralRuleJobExecution.AnswerIn meaning request => receiptTermWith choiceTerm answer.val)
        (GeneralRuleJobExecution.finishRootIn meaning request licensed trace captured completed history localTarget valid))) := by
  let caller := finishBindingsWith choiceTerm request footprint trace captured completed history localTarget ++
    environment .finish (finishValuesWith choiceTerm request footprint trace captured completed history localTarget)
  change PureReturns runtime [] state (a Helper.finish.head (finishValuesWith choiceTerm request footprint trace captured completed history localTarget)) state _
  apply finish_frame_returnsWith
  change PureReturns runtime caller state finishGoalBody state _
  unfold finishGoalBody
  apply bool_if_returns caller state _ true _ _ _
  · simpa only [decide_true] using CettaWireAtom.equality_evaluated_returns runtime caller state
      (PremiseOperationsExecution.GeneralExecution.goalTerm request.goal)
      (PremiseOperationsExecution.GeneralExecution.goalTerm request.goal)
      (v "goal") nativeGoalBody (by decide +kernel) (by decide +kernel)
      (by simpa [caller, finishBindingsWith, environment, finishValuesWith, rootResultTermWith, Helper.names, applySubst, Subst.lookup] using
        variable_returns runtime caller state "goal")
      (by
        change PureReturns runtime caller state nativeGoalBody state (encoded (.application "RootGoal"
          [encodeList InferenceCettaWire.AuthoredRule.typeTerm request.job.site.focusBound,
           InferenceCettaWire.AuthoredRule.typeTerm request.job.site.focusType,
           InferenceCettaWire.encodePattern request.job.site.focus, .natural request.job.ordinal]))
        simpa [nativeGoalBody, caller, finishBindingsWith, environment, finishValuesWith, rootResultTermWith, Helper.names, DataConstructor.head,
          applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
          (PureData.template_return runtime caller state _
            (data_variables_template .goal ["focusBound", "focusType", "focus", "ordinal"])))
  · simp only [ite_true]
    unfold finishPermittedBody
    have permitted : request.plan.permissions.sites.permitsContext request.job.site.context = true := licensed.2.permitted
    apply bool_if_returns caller state _ true _ _ _
    · have computed := retained_returns (by decide +kernel)
        (RuleInstantiationExecution.ContextObservation.permitted_captured_returns caller state
          request.plan.permissions.sites request.job.site.context (v "permissions") (v "context") (by
            simp [caller, finishBindingsWith, environment, finishValuesWith, rootResultTermWith, Helper.names, applySubst, Subst.lookup]))
      simpa only [permitted] using computed
    · simp only [ite_true]
      unfold finishRepresentedBody
      apply bool_if_returns caller state _
        (request.job.site.acceptsReplacementRepresentation request.environment.language localTarget) _ _ _
      · exact replacement_representations_captured_returns caller state request.environment.language
          request.job.site.context request.job.site.typingFrames localTarget
          (v "declarations") (v "context") (v "frames") (v "localTarget") (by
            simp [caller, finishBindingsWith, environment, finishValuesWith, rootResultTermWith, Helper.names, representationValues,
              applySubst, Subst.lookup])
      · cases represented : request.job.site.acceptsReplacementRepresentation request.environment.language localTarget with
        | false =>
            simpa [GeneralRuleJobExecution.finishRootIn, represented, encodeOption, CettaWireAtom.encode] using
              symbol_returns runtime caller state "None"
        | true =>
            unfold finishFillBody
            let filled := ("target", patternValue (request.job.site.context.fill localTarget)) :: caller
            apply named_let_returns caller state "target" _
              (patternValue (request.job.site.context.fill localTarget)) _ _
            · simp [caller, finishBindingsWith, environment, finishValuesWith, rootResultTermWith, Helper.names, Subst.lookup]
            · exact retained_returns (by decide +kernel)
                (RuleInstantiationExecution.ContextObservation.fill_captured_returns caller state
                  request.job.site.context localTarget (v "context") (v "localTarget") (by
                    simp [caller, finishBindingsWith, environment, finishValuesWith, rootResultTermWith, Helper.names, applySubst, Subst.lookup]))
            · unfold finishTypedBody
              have finite := Mettapedia.GSLT.LanguageDef.WellSorted.check_open_pattern_snapshot
                request.environment.language request.environment.free request.bound request.expected
                (request.job.site.context.fill localTarget) footprint covered
              apply bool_if_returns filled state _
                (WellSorted.checkOpenPatternWellSorted request.environment.language request.environment.free
                  request.bound request.expected (request.job.site.context.fill localTarget)) _ _ _
              · have computed := retained_returns (by decide +kernel)
                  (PremiseOperationsExecution.DeclarationTyping.check_open_pattern_captured_returns filled state
                    request.environment.language (request.environment.free.entriesOn footprint)
                    request.bound request.expected (request.job.site.context.fill localTarget)
                    (v "declarations") (v "free") (v "bound") (v "expected") (v "target") (by
                      simp [filled, caller, finishBindingsWith, environment, finishValuesWith, rootResultTermWith, Helper.names,
                        applySubst, Subst.lookup, PremiseOperationsExecution.DeclarationTyping.boundContextTerm]))
                simpa only [finite] using computed
              · cases typed : WellSorted.checkOpenPatternWellSorted request.environment.language request.environment.free
                  request.bound request.expected (request.job.site.context.fill localTarget) with
                | false =>
                    simpa [GeneralRuleJobExecution.finishRootIn, represented, typed, encodeOption,
                      CettaWireAtom.encode] using symbol_returns runtime filled state "None"
                | true =>
                    simpa [GeneralRuleJobExecution.finishRootIn, represented, typed, encodeOption,
                      nativeReceiptBody, receiptTermWith, jobTerm, siteTerm, filled, caller, finishBindingsWith,
                      environment, finishValuesWith, rootResultTermWith, Helper.names, applySubst, applySubst.applySubstList,
                      Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                      (PureData.template_return runtime filled state _ native_receipt_template)

theorem finish_root_interpreted_readout_returns {Choice : Type}
    (choiceTerm : Choice → Term) (meaning : GeneralPremise.MatchingInterpretation Choice)
    (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (footprint : List String) (trace : List Choice)
    (captured completed : Assignment) (history : List (GeneralPremise.Event Choice)) (localTarget : Pattern)
    (valid : GeneralPremise.Interpreted.RootFiring meaning request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history localTarget)
    (covered : ∀ name ∈ (request.job.site.context.fill localTarget).freeFvarNames, name ∈ footprint) :
    PureReturns runtime [] state
      (finishRootQueryWith choiceTerm request footprint trace captured completed history localTarget) state
      (encoded (encodeOption (receiptTermWith choiceTerm)
        (GeneralRuleJobs.finish? request.plan request.bound request.expected request.job trace captured completed history))) := by
  have returned := finish_root_interpreted_finite_returns choiceTerm meaning state request licensed footprint
    trace captured completed history localTarget valid covered
  rw [← GeneralRuleJobExecution.finishRootIn_eq_finish meaning request licensed trace captured completed history localTarget valid]
  cases selected : GeneralRuleJobExecution.finishRootIn meaning request licensed trace captured completed history localTarget valid <;>
    simpa only [selected, Option.map_none, Option.map_some, encodeOption] using returned

#print axioms rootResultTermWith_ordinary
#print axioms finish_root_interpreted_finite_returns
#print axioms finish_root_interpreted_readout_returns

theorem finish_root_finite_returns (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (footprint : List String) (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : Assignment) (history : List GeneralPremise.Event) (localTarget : Pattern)
    (valid : GeneralPremise.RootFiring request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history localTarget)
    (covered : ∀ name ∈ (request.job.site.context.fill localTarget).freeFvarNames, name ∈ footprint) :
    PureReturns runtime [] state
      (finishRootQuery request footprint (.root trace captured completed history localTarget valid)) state
      (encoded (encodeOption (fun answer : GeneralRuleJobExecution.Answer request => receiptTerm answer.val)
        (GeneralRuleJobExecution.finishRoot request licensed trace captured completed history localTarget valid))) := by
  have returned := finish_root_interpreted_finite_returns RetainedMatchingWire.ordinaryCodec.choiceTerm
    GeneralPremise.ordinaryInterpretation state request licensed footprint trace captured completed history localTarget valid covered
  change PureReturns runtime [] state
    (a "gslt:rule:job-finish-root"
      (finishValuesWith RetainedMatchingWire.ordinaryCodec.choiceTerm request footprint trace captured completed history localTarget))
    state (encoded (encodeOption
      (fun answer : GeneralRuleJobExecution.Answer request =>
        receiptTermWith RetainedMatchingWire.ordinaryCodec.choiceTerm answer.val)
      (GeneralRuleJobExecution.finishRoot request licensed trace captured completed history localTarget valid))) at returned
  have encodedReceipt : (fun answer : GeneralRuleJobExecution.Answer request =>
      receiptTermWith RetainedMatchingWire.ordinaryCodec.choiceTerm answer.val) =
      (fun answer : GeneralRuleJobExecution.Answer request => receiptTerm answer.val) := by
    funext answer
    exact receiptTermWith_ordinary answer.val
  rw [finishValuesWith_ordinary request footprint trace captured completed history localTarget valid, encodedReceipt] at returned
  exact returned

theorem finish_root_interpreted_finite_captured_returns {Choice : Type}
    (choiceTerm : Choice → Term) (meaning : GeneralPremise.MatchingInterpretation Choice) (caller : Subst) (state : State)
    (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (footprint : List String) (trace : List Choice)
    (captured completed : Assignment) (history : List (GeneralPremise.Event Choice)) (localTarget : Pattern)
    (valid : GeneralPremise.Interpreted.RootFiring meaning request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history localTarget)
    (covered : ∀ name ∈ (request.job.site.context.fill localTarget).freeFvarNames, name ∈ footprint)
    (one two : Atom)
    (inputs : [one, two].map (applySubst caller) =
      finishValuesWith choiceTerm request footprint trace captured completed history localTarget) :
    PureReturns runtime caller state (a "gslt:rule:job-finish-root" [one, two]) state
      (encoded (encodeOption (fun answer : GeneralRuleJobExecution.AnswerIn meaning request => receiptTermWith choiceTerm answer.val)
        (GeneralRuleJobExecution.finishRootIn meaning request licensed trace captured completed history localTarget valid))) :=
  helper_capture .finish caller state _ _ _ rfl inputs
    (finish_root_interpreted_finite_returns choiceTerm meaning state request licensed footprint trace captured completed history localTarget valid covered)

theorem finish_root_finite_captured_returns (caller : Subst) (state : State)
    (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (footprint : List String) (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : Assignment) (history : List GeneralPremise.Event) (localTarget : Pattern)
    (valid : GeneralPremise.RootFiring request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history localTarget)
    (covered : ∀ name ∈ (request.job.site.context.fill localTarget).freeFvarNames, name ∈ footprint)
    (one two : Atom)
    (inputs : [one, two].map (applySubst caller) =
      finishValues request footprint (.root trace captured completed history localTarget valid)) :
    PureReturns runtime caller state (a "gslt:rule:job-finish-root" [one, two]) state
      (encoded (encodeOption (fun answer : GeneralRuleJobExecution.Answer request => receiptTerm answer.val)
        (GeneralRuleJobExecution.finishRoot request licensed trace captured completed history localTarget valid))) := by
  have actualInputs : [one, two].map (applySubst caller) =
      finishValuesWith RetainedMatchingWire.ordinaryCodec.choiceTerm request footprint trace captured completed history localTarget := by
    rw [finishValuesWith_ordinary request footprint trace captured completed history localTarget valid]
    exact inputs
  have returned := finish_root_interpreted_finite_captured_returns RetainedMatchingWire.ordinaryCodec.choiceTerm
    GeneralPremise.ordinaryInterpretation caller state request licensed footprint trace captured completed history localTarget
    valid covered one two actualInputs
  change PureReturns runtime caller state (a "gslt:rule:job-finish-root" [one, two]) state
    (encoded (encodeOption
      (fun answer : GeneralRuleJobExecution.Answer request =>
        receiptTermWith RetainedMatchingWire.ordinaryCodec.choiceTerm answer.val)
      (GeneralRuleJobExecution.finishRoot request licensed trace captured completed history localTarget valid))) at returned
  have encodedReceipt : (fun answer : GeneralRuleJobExecution.Answer request =>
      receiptTermWith RetainedMatchingWire.ordinaryCodec.choiceTerm answer.val) =
      (fun answer : GeneralRuleJobExecution.Answer request => receiptTerm answer.val) := by
    funext answer
    exact receiptTermWith_ordinary answer.val
  rw [encodedReceipt] at returned
  exact returned

theorem finish_root_run_returns (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (trace : List GeneralScopedMatchMachine.BagChoice) (captured completed : Assignment)
    (history : List GeneralPremise.Event) (localTarget : Pattern)
    (valid : GeneralPremise.RootFiring request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history localTarget)
    (member : GeneralPremise.Execution.Result.root trace captured completed history localTarget valid ∈
      (GeneralPremise.Execution.run request.environment request.goal fuel
        (GeneralPremise.Execution.start request.environment request.goal)).answers) :
    PureReturns runtime [] state
      (finishRootQuery request (request.source.freeFvarNames ++
        Mettapedia.OSLF.MeTTaIL.GeneralPremise.providerFreeNames request.environment.provider)
        (.root trace captured completed history localTarget valid)) state
      (encoded (encodeOption (fun answer : GeneralRuleJobExecution.Answer request => receiptTerm answer.val)
        (GeneralRuleJobExecution.finishRoot request licensed trace captured completed history localTarget valid))) :=
  finish_root_finite_returns state request licensed _ trace captured completed history localTarget valid
    (Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.request_run_global_target_free_within request licensed fuel
      trace captured completed history localTarget valid member)

def executionHeadNames : List String :=
  ["+",
   "-",
   "<",
   "==",
   "Binding",
   "ContextApp",
   "ContextCollection",
   "ContextHole",
   "ContextLam",
   "ContextMultiLam",
   "ContextSubstBody",
   "ContextSubstReplacement",
   "FVar",
   "GrammarTypingV1",
   "GrammarTypingWrappedV1",
   "LCons",
   "LNil",
   "None",
   "OperationalPermissions",
   "PApp",
   "PCollection",
   "PLam",
   "PMultiLam",
   "PSubst",
   "PremiseEnvironment",
   "PremiseResult",
   "RNone",
   "ReplacementShape",
   "RootAnswer",
   "RootGoal",
   "RuleJob",
   "RuleJobFinishInput",
   "RuleJobReceipt",
   "RuleJobRequestProjection",
   "RuleJobSite",
   "Some",
   "TArrow",
   "TBase",
   "TCollection",
   "TMultiBinder",
   "TermAbstraction",
   "TermMultiAbstraction",
   "TermSimple",
   "TermSlot",
   "TypingApplication",
   "TypingAuthoredCollection",
   "TypingDirectCollection",
   "TypingLambda",
   "TypingMultiLambda",
   "Var",
   "case",
   "gslt:automata:append",
   "gslt:automata:binding",
   "gslt:automata:length",
   "gslt:automata:member",
   "gslt:premise:canonical-binders",
   "gslt:premise:canonical-binders-list",
   "gslt:premise:object-pattern",
   "gslt:premise:object-patterns",
   "gslt:premise:open-well-sorted",
   "gslt:premise:parameter-representation",
   "gslt:premise:parameter-type",
   "gslt:premise:type-arguments",
   "gslt:premise:type-collection-declarations",
   "gslt:premise:type-constructors",
   "gslt:premise:type-elements",
   "gslt:premise:type-extend-count",
   "gslt:premise:type-has",
   "gslt:rule:job-finish-root",
   "gslt:rule:row-at",
   "gslt:rule:scope-fill",
   "gslt:rule:scope-permitted",
   "gslt:rule:scope-well-scoped",
   "gslt:rule:scope-well-scoped-list",
   "gslt:rule:site-replacement-represented",
   "if",
   "let",
   "let*"]

def executionHeads (head : String) : Bool := executionHeadNames.contains head

theorem runtime_closed : ProgramClosed executionHeads runtime := by
  exact BridgeKit.closed_of_all _ _ (by decide +kernel) (by decide +kernel)

/-- The same inert readout operation transports to any program agreeing on its
actual closed primitive dependency set. The local firing supplies its semantics. -/
theorem finish_root_interpreted_captured_returns_in_extension {Choice : Type}
    (choiceTerm : Choice → Term) (meaning : GeneralPremise.MatchingInterpretation Choice)
    (targetProgram : Program) (agreement : ProgramAgreementOn executionHeads runtime targetProgram)
    (caller : Subst) (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (footprint : List String) (trace : List Choice)
    (captured completed : Assignment) (history : List (GeneralPremise.Event Choice)) (localTarget : Pattern)
    (valid : GeneralPremise.Interpreted.RootFiring meaning request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history localTarget)
    (covered : ∀ name ∈ (request.job.site.context.fill localTarget).freeFvarNames, name ∈ footprint)
    (requestName resultName : String)
    (inputs : [v requestName, v resultName].map (applySubst caller) =
      [encoded (requestProjectionTerm request footprint),
        encoded (rootResultTermWith choiceTerm request trace captured completed history localTarget)]) :
    PureReturns targetProgram caller state (a "gslt:rule:job-finish-root" [v requestName, v resultName]) state
      (encoded (encodeOption (receiptTermWith choiceTerm)
        (GeneralRuleJobs.finish? request.plan request.bound request.expected request.job trace captured completed history))) :=
  path_of_closed_agreement runtime_closed agreement ⟨by rfl, rfl⟩
    (helper_capture .finish caller state _ _ _ rfl inputs
      (finish_root_interpreted_readout_returns choiceTerm meaning state request licensed footprint
        trace captured completed history localTarget valid covered))

theorem finish_root_interpreted_captured_receipt_iff_in_extension {Choice : Type}
    (choiceTerm : Choice → Term) (decodeChoice : Term → Option Choice)
    (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice)
    (meaning : GeneralPremise.MatchingInterpretation Choice)
    (targetProgram : Program) (agreement : ProgramAgreementOn executionHeads runtime targetProgram)
    (caller : Subst) (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (footprint : List String) (trace : List Choice)
    (captured completed : Assignment) (history : List (GeneralPremise.Event Choice)) (localTarget : Pattern)
    (valid : GeneralPremise.Interpreted.RootFiring meaning request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history localTarget)
    (covered : ∀ name ∈ (request.job.site.context.fill localTarget).freeFvarNames, name ∈ footprint)
    (requestName resultName : String)
    (inputs : [v requestName, v resultName].map (applySubst caller) =
      [encoded (requestProjectionTerm request footprint),
        encoded (rootResultTermWith choiceTerm request trace captured completed history localTarget)])
    (receipt : GeneralRuleJobs.Receipt Choice) :
    (∃ nativeFuel, run targetProgram nativeFuel {state, control := (.evaluate caller
      (a "gslt:rule:job-finish-root" [v requestName, v resultName]))} =
        .complete state [encoded (.application "Some" [receiptTermWith choiceTerm receipt])] [] []) ↔
      GeneralRuleJobs.finish? request.plan request.bound request.expected request.job
        trace captured completed history = some receipt := by
  rw [pure_returns_completed_iff targetProgram caller state state _ _
    (finish_root_interpreted_captured_returns_in_extension choiceTerm meaning targetProgram agreement caller state
      request licensed footprint trace captured completed history localTarget valid covered requestName resultName inputs)
    state [encoded (.application "Some" [receiptTermWith choiceTerm receipt])] [] []]
  cases GeneralRuleJobs.finish? request.plan request.bound request.expected request.job trace captured completed history with
  | none => simp [encodeOption, CettaWireAtom.encode]
  | some found =>
      simp only [true_and, encodeOption, List.cons.injEq, and_true, CettaWireAtom.encode_eq_encode,
        Term.application.injEq, receiptTermWith_injective choiceTerm decodeChoice inverse |>.eq_iff, Option.some.injEq]
      exact eq_comm

theorem finish_root_interpreted_captured_valid_in_extension {Choice : Type}
    (choiceTerm : Choice → Term) (decodeChoice : Term → Option Choice)
    (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice)
    (meaning : GeneralPremise.MatchingInterpretation Choice)
    (targetProgram : Program) (agreement : ProgramAgreementOn executionHeads runtime targetProgram)
    (caller : Subst) (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (footprint : List String) (trace : List Choice)
    (captured completed : Assignment) (history : List (GeneralPremise.Event Choice)) (localTarget : Pattern)
    (valid : GeneralPremise.Interpreted.RootFiring meaning request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history localTarget)
    (covered : ∀ name ∈ (request.job.site.context.fill localTarget).freeFvarNames, name ∈ footprint)
    (requestName resultName : String)
    (inputs : [v requestName, v resultName].map (applySubst caller) =
      [encoded (requestProjectionTerm request footprint),
        encoded (rootResultTermWith choiceTerm request trace captured completed history localTarget)])
    (receipt : GeneralRuleJobs.Receipt Choice)
    (observed : ∃ nativeFuel, run targetProgram nativeFuel {state, control := (.evaluate caller
      (a "gslt:rule:job-finish-root" [v requestName, v resultName]))} =
        .complete state [encoded (.application "Some" [receiptTermWith choiceTerm receipt])] [] []) :
    receipt.ValidInWith meaning GeneralPremise.DynamicProvider.empty
      request.plan request.bound request.expected request.source := by
  have emitted := (finish_root_interpreted_captured_receipt_iff_in_extension choiceTerm decodeChoice inverse meaning
    targetProgram agreement caller state request licensed footprint trace captured completed history localTarget
    valid covered requestName resultName inputs receipt).mp observed
  exact GeneralRuleJobs.finishWith_interpreted_root_sound licensed valid emitted

#print axioms finish_root_interpreted_captured_returns_in_extension
#print axioms finish_root_interpreted_captured_receipt_iff_in_extension
#print axioms finish_root_interpreted_captured_valid_in_extension

theorem finish_root_run_captured_variables_returns_in_extension (targetProgram : Program)
    (agreement : ProgramAgreementOn executionHeads runtime targetProgram)
    (caller : Subst) (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (trace : List GeneralScopedMatchMachine.BagChoice) (captured completed : Assignment)
    (history : List GeneralPremise.Event) (localTarget : Pattern)
    (valid : GeneralPremise.RootFiring request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history localTarget)
    (member : GeneralPremise.Execution.Result.root trace captured completed history localTarget valid ∈
      (GeneralPremise.Execution.run request.environment request.goal fuel
        (GeneralPremise.Execution.start request.environment request.goal)).answers)
    (requestName resultName : String)
    (inputs : [v requestName, v resultName].map (applySubst caller) = finishValues request
      (request.source.freeFvarNames ++ Mettapedia.OSLF.MeTTaIL.GeneralPremise.providerFreeNames request.environment.provider)
      (.root trace captured completed history localTarget valid)) :
    PureReturns targetProgram caller state (a "gslt:rule:job-finish-root" [v requestName, v resultName]) state
      (encoded (encodeOption (fun answer : GeneralRuleJobExecution.Answer request => receiptTerm answer.val)
        (GeneralRuleJobExecution.finishRoot request licensed trace captured completed history localTarget valid))) :=
  path_of_closed_agreement runtime_closed agreement ⟨by rfl, rfl⟩
    (finish_root_finite_captured_returns caller state request licensed _ trace captured completed history localTarget valid
      (Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.request_run_global_target_free_within request licensed fuel
        trace captured completed history localTarget valid member) _ _ inputs)

theorem finish_root_run_completed_iff (state after : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (trace : List GeneralScopedMatchMachine.BagChoice) (captured completed : Assignment)
    (history : List GeneralPremise.Event) (localTarget : Pattern)
    (valid : GeneralPremise.RootFiring request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history localTarget)
    (member : GeneralPremise.Execution.Result.root trace captured completed history localTarget valid ∈
      (GeneralPremise.Execution.run request.environment request.goal fuel
        (GeneralPremise.Execution.start request.environment request.goal)).answers)
    (answers input output : List Atom) :
    (∃ nativeFuel, run runtime nativeFuel {state, control := (.evaluate []
      (finishRootQuery request (request.source.freeFvarNames ++
        Mettapedia.OSLF.MeTTaIL.GeneralPremise.providerFreeNames request.environment.provider)
        (.root trace captured completed history localTarget valid)))} = .complete after answers input output) ↔
      after = state ∧ answers = [encoded (encodeOption
        (fun answer : GeneralRuleJobExecution.Answer request => receiptTerm answer.val)
        (GeneralRuleJobExecution.finishRoot request licensed trace captured completed history localTarget valid))] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff runtime [] state state _ _
    (finish_root_run_returns state request licensed fuel trace captured completed history localTarget valid member)
    after answers input output

theorem finish_root_run_receipt_iff (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (trace : List GeneralScopedMatchMachine.BagChoice) (captured completed : Assignment)
    (history : List GeneralPremise.Event) (localTarget : Pattern)
    (valid : GeneralPremise.RootFiring request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history localTarget)
    (member : GeneralPremise.Execution.Result.root trace captured completed history localTarget valid ∈
      (GeneralPremise.Execution.run request.environment request.goal fuel
        (GeneralPremise.Execution.start request.environment request.goal)).answers)
    (receipt : GeneralRuleJobs.Receipt) :
    (∃ nativeFuel, run runtime nativeFuel {state, control := (.evaluate []
      (finishRootQuery request (request.source.freeFvarNames ++
        Mettapedia.OSLF.MeTTaIL.GeneralPremise.providerFreeNames request.environment.provider)
        (.root trace captured completed history localTarget valid)))} =
        .complete state [encoded (.application "Some" [receiptTerm receipt])] [] []) ↔
    ∃ answer : GeneralRuleJobExecution.Answer request,
      GeneralRuleJobExecution.finishRoot request licensed trace captured completed history localTarget valid = some answer ∧
      answer.val = receipt := by
  rw [finish_root_run_completed_iff state state request licensed fuel trace captured completed history localTarget valid member]
  cases emitted : GeneralRuleJobExecution.finishRoot request licensed trace captured completed history localTarget valid with
  | none => simp [encodeOption, CettaWireAtom.encode]
  | some answer =>
      simp only [true_and, List.cons.injEq, and_true, encodeOption,
        CettaWireAtom.encode_eq_encode, Term.application.injEq, List.cons.injEq,
        receiptTerm_injective.eq_iff]
      constructor
      · intro same
        exact ⟨answer, rfl, same.symm⟩
      · rintro ⟨other, same, receiptSame⟩
        cases Option.some.inj same
        exact receiptSame.symm

theorem finish_root_run_native_receipt_gslt (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (trace : List GeneralScopedMatchMachine.BagChoice) (captured completed : Assignment)
    (history : List GeneralPremise.Event) (localTarget : Pattern)
    (valid : GeneralPremise.RootFiring request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history localTarget)
    (member : GeneralPremise.Execution.Result.root trace captured completed history localTarget valid ∈
      (GeneralPremise.Execution.run request.environment request.goal fuel
        (GeneralPremise.Execution.start request.environment request.goal)).answers)
    (receipt : GeneralRuleJobs.Receipt)
    (observed : ∃ nativeFuel, run runtime nativeFuel {state, control := (.evaluate []
      (finishRootQuery request (request.source.freeFvarNames ++
        Mettapedia.OSLF.MeTTaIL.GeneralPremise.providerFreeNames request.environment.provider)
        (.root trace captured completed history localTarget valid)))} =
        .complete state [encoded (.application "Some" [receiptTerm receipt])] [] []) :
    GeneralOccurrenceSemantics.Primitive request.plan request.bound request.expected request.source receipt ∧
      (GeneralOccurrenceSemantics.gslt request.plan request.bound request.expected).Step request.source receipt.target ∧
      receipt.Valid request.plan request.bound request.expected request.source := by
  obtain ⟨answer, _, same⟩ := (finish_root_run_receipt_iff state request licensed fuel trace captured completed history
    localTarget valid member receipt).mp observed
  have certified : receipt.Valid request.plan request.bound request.expected request.source := same ▸ answer.property
  refine ⟨certified, ?_, certified⟩
  exact ⟨request.source, receipt, .refl _, certified, .refl _⟩

theorem finish_root_run_captured_completed_iff_in_extension (targetProgram : Program)
    (agreement : ProgramAgreementOn executionHeads runtime targetProgram)
    (caller : Subst) (state after : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (trace : List GeneralScopedMatchMachine.BagChoice) (captured completed : Assignment)
    (history : List GeneralPremise.Event) (localTarget : Pattern)
    (valid : GeneralPremise.RootFiring request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history localTarget)
    (member : GeneralPremise.Execution.Result.root trace captured completed history localTarget valid ∈
      (GeneralPremise.Execution.run request.environment request.goal fuel
        (GeneralPremise.Execution.start request.environment request.goal)).answers)
    (requestName resultName : String)
    (inputs : [v requestName, v resultName].map (applySubst caller) = finishValues request
      (request.source.freeFvarNames ++ Mettapedia.OSLF.MeTTaIL.GeneralPremise.providerFreeNames request.environment.provider)
      (.root trace captured completed history localTarget valid))
    (answers input output : List Atom) :
    (∃ nativeFuel, run targetProgram nativeFuel {state, control := (.evaluate caller
      (a "gslt:rule:job-finish-root" [v requestName, v resultName]))} = .complete after answers input output) ↔
      after = state ∧ answers = [encoded (encodeOption
        (fun answer : GeneralRuleJobExecution.Answer request => receiptTerm answer.val)
        (GeneralRuleJobExecution.finishRoot request licensed trace captured completed history localTarget valid))] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff targetProgram caller state state _ _
    (finish_root_run_captured_variables_returns_in_extension targetProgram agreement caller state request licensed
      fuel trace captured completed history localTarget valid member requestName resultName inputs)
    after answers input output

theorem finish_root_run_captured_receipt_iff_in_extension (targetProgram : Program)
    (agreement : ProgramAgreementOn executionHeads runtime targetProgram)
    (caller : Subst) (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (trace : List GeneralScopedMatchMachine.BagChoice) (captured completed : Assignment)
    (history : List GeneralPremise.Event) (localTarget : Pattern)
    (valid : GeneralPremise.RootFiring request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history localTarget)
    (member : GeneralPremise.Execution.Result.root trace captured completed history localTarget valid ∈
      (GeneralPremise.Execution.run request.environment request.goal fuel
        (GeneralPremise.Execution.start request.environment request.goal)).answers)
    (requestName resultName : String)
    (inputs : [v requestName, v resultName].map (applySubst caller) = finishValues request
      (request.source.freeFvarNames ++ Mettapedia.OSLF.MeTTaIL.GeneralPremise.providerFreeNames request.environment.provider)
      (.root trace captured completed history localTarget valid))
    (receipt : GeneralRuleJobs.Receipt) :
    (∃ nativeFuel, run targetProgram nativeFuel {state, control := (.evaluate caller
      (a "gslt:rule:job-finish-root" [v requestName, v resultName]))} =
        .complete state [encoded (.application "Some" [receiptTerm receipt])] [] []) ↔
    ∃ answer : GeneralRuleJobExecution.Answer request,
      GeneralRuleJobExecution.finishRoot request licensed trace captured completed history localTarget valid = some answer ∧
      answer.val = receipt := by
  rw [finish_root_run_captured_completed_iff_in_extension targetProgram agreement caller state state request
    licensed fuel trace captured completed history localTarget valid member requestName resultName inputs]
  cases GeneralRuleJobExecution.finishRoot request licensed trace captured completed history localTarget valid with
  | none => simp [encodeOption, CettaWireAtom.encode]
  | some answer =>
      simp only [true_and, List.cons.injEq, and_true, encodeOption,
        CettaWireAtom.encode_eq_encode, Term.application.injEq, List.cons.injEq,
        receiptTerm_injective.eq_iff]
      constructor
      · intro same
        exact ⟨answer, rfl, same.symm⟩
      · rintro ⟨other, same, receiptSame⟩
        cases Option.some.inj same
        exact receiptSame.symm

theorem finish_root_run_captured_native_receipt_gslt_in_extension (targetProgram : Program)
    (agreement : ProgramAgreementOn executionHeads runtime targetProgram)
    (caller : Subst) (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (trace : List GeneralScopedMatchMachine.BagChoice) (captured completed : Assignment)
    (history : List GeneralPremise.Event) (localTarget : Pattern)
    (valid : GeneralPremise.RootFiring request.environment request.job.site.focusBound request.job.site.focusType
      request.job.site.focus request.job.ordinal trace captured completed history localTarget)
    (member : GeneralPremise.Execution.Result.root trace captured completed history localTarget valid ∈
      (GeneralPremise.Execution.run request.environment request.goal fuel
        (GeneralPremise.Execution.start request.environment request.goal)).answers)
    (requestName resultName : String)
    (inputs : [v requestName, v resultName].map (applySubst caller) = finishValues request
      (request.source.freeFvarNames ++ Mettapedia.OSLF.MeTTaIL.GeneralPremise.providerFreeNames request.environment.provider)
      (.root trace captured completed history localTarget valid))
    (receipt : GeneralRuleJobs.Receipt)
    (observed : ∃ nativeFuel, run targetProgram nativeFuel {state, control := (.evaluate caller
      (a "gslt:rule:job-finish-root" [v requestName, v resultName]))} =
        .complete state [encoded (.application "Some" [receiptTerm receipt])] [] []) :
    GeneralOccurrenceSemantics.Primitive request.plan request.bound request.expected request.source receipt ∧
      (GeneralOccurrenceSemantics.gslt request.plan request.bound request.expected).Step request.source receipt.target ∧
      receipt.Valid request.plan request.bound request.expected request.source := by
  obtain ⟨answer, _, same⟩ := (finish_root_run_captured_receipt_iff_in_extension targetProgram agreement caller
    state request licensed fuel trace captured completed history localTarget valid member requestName resultName
    inputs receipt).mp observed
  have certified : receipt.Valid request.plan request.bound request.expected request.source := same ▸ answer.property
  refine ⟨certified, ?_, certified⟩
  exact ⟨request.source, receipt, .refl _, certified, .refl _⟩

theorem finish_root_observed_answer_gslt_in_extension (targetProgram : Program)
    (agreement : ProgramAgreementOn executionHeads runtime targetProgram)
    (caller : Subst) (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (resultWire : Term)
    (member : resultWire ∈ (GeneralPremise.Execution.run request.environment request.goal fuel
      (GeneralPremise.Execution.start request.environment request.goal)).answers.map
        PremiseOperationsExecution.GeneralExecution.resultTerm)
    (requestName resultName : String)
    (inputs : [v requestName, v resultName].map (applySubst caller) =
      [encoded (requestProjectionTerm request (request.source.freeFvarNames ++
        Mettapedia.OSLF.MeTTaIL.GeneralPremise.providerFreeNames request.environment.provider)), encoded resultWire])
    (receipt : GeneralRuleJobs.Receipt)
    (observed : ∃ nativeFuel, run targetProgram nativeFuel {state, control := (.evaluate caller
      (a "gslt:rule:job-finish-root" [v requestName, v resultName]))} =
        .complete state [encoded (.application "Some" [receiptTerm receipt])] [] []) :
    GeneralOccurrenceSemantics.Primitive request.plan request.bound request.expected request.source receipt ∧
      (GeneralOccurrenceSemantics.gslt request.plan request.bound request.expected).Step request.source receipt.target ∧
      receipt.Valid request.plan request.bound request.expected request.source := by
  obtain ⟨result, actual, same⟩ := List.mem_map.mp member
  cases same
  cases result with
  | root trace captured completed history localTarget valid =>
      exact finish_root_run_captured_native_receipt_gslt_in_extension targetProgram agreement caller state
        request licensed fuel trace captured completed history localTarget valid actual requestName resultName
        inputs receipt observed








end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedRuleJobReadoutExecution

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.CompletedAssembly

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program)
open Eval

private def readoutNames : List String :=
  ["gslt:rule:site-replacement-represented", "gslt:rule:job-finish-root"]

/-- Pending source code stays in the retained machine. Captured data need not
have a supported application head. Dynamic evaluation is checked separately. -/
def retainedHead (head : String) : Bool :=
  head != "eval" && !readoutNames.contains head

theorem retained_machine_closed : ProgramClosed retainedHead RuleExecutionProgram.scopedMachineProgram := by
  exact BridgeKit.closed_of_all _ _ (by decide +kernel) (by decide +kernel)

theorem completed_retained_machine_closed : ProgramClosed retainedHead RuleExecutionProgram.scopedProgram := by
  exact BridgeKit.closed_of_all _ _ (by decide +kernel) (by decide +kernel)

theorem retained_machine_equations :
    RuleExecutionProgram.scopedMachineProgram.equations.filter (fun equation => retainedHead equation.head) =
    RuleExecutionProgram.scopedProgram.equations.filter (fun equation => retainedHead equation.head) := by rfl

theorem retained_machine_declarations :
    RuleExecutionProgram.scopedMachineProgram.declarations.filter (retainedCallDeclaration retainedHead) =
    RuleExecutionProgram.scopedProgram.declarations.filter (retainedCallDeclaration retainedHead) := by rfl

theorem retained_machine_agreement : ProgramAgreementOn retainedHead RuleExecutionProgram.scopedMachineProgram RuleExecutionProgram.scopedProgram :=
  programAgreementOn_of_retained_rows _ _ _
    retained_machine_equations retained_machine_declarations

theorem readout_retained_equations :
    ScopedRuleJobReadoutExecution.runtime.equations.filter
      (fun equation => ScopedRuleJobReadoutExecution.executionHeads equation.head) =
    RuleExecutionProgram.scopedProgram.equations.filter
      (fun equation => ScopedRuleJobReadoutExecution.executionHeads equation.head) := by rfl

theorem readout_retained_declarations :
    ScopedRuleJobReadoutExecution.runtime.declarations.filter
      (retainedCallDeclaration ScopedRuleJobReadoutExecution.executionHeads) =
    RuleExecutionProgram.scopedProgram.declarations.filter
      (retainedCallDeclaration ScopedRuleJobReadoutExecution.executionHeads) := by rfl

theorem readout_agreement : ProgramAgreementOn ScopedRuleJobReadoutExecution.executionHeads
    ScopedRuleJobReadoutExecution.runtime RuleExecutionProgram.scopedProgram :=
  programAgreementOn_of_retained_rows _ _ _
    readout_retained_equations readout_retained_declarations

/-- The original machine run is preserved and reflected after adding the
readout. Its arguments are captured variables, so arbitrary user data remain
data throughout this transport. Store, answer, and I/O observations are exact. -/
theorem captured_machine_run_iff (caller : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (before after : Effects.State) (environmentName fuelName stateName : String) (answer : Atom) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller before
      (.expression [.symbol "gslt:premise:machine-run", .var environmentName,
        .var fuelName, .var stateName]) after answer ↔
    PureReturns RuleExecutionProgram.scopedProgram caller before
      (.expression [.symbol "gslt:premise:machine-run", .var environmentName,
        .var fuelName, .var stateName]) after answer := by
  have within : configurationWithin retainedHead
      { state := before, control := .evaluate caller (.expression [.symbol "gslt:premise:machine-run", .var environmentName,
          .var fuelName, .var stateName]) } := by
    constructor
    · rfl
    · rfl
  constructor
  · exact path_of_closed_agreement retained_machine_closed retained_machine_agreement within
  · apply path_of_closed_agreement completed_retained_machine_closed
    · constructor
      · intro head supported
        exact (retained_machine_agreement.dispatch head supported).symm
      · intro head index supported
        exact (retained_machine_agreement.demand head index supported).symm
      · intro head values supported
        exact (retained_machine_agreement.bodies head values supported).symm
    · exact within


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.CompletedAssembly

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralRuleJobObservation

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open Eval


private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term

def requestFootprint (request : GeneralRuleJobExecution.Request) : List String :=
  request.source.freeFvarNames ++ Mettapedia.OSLF.MeTTaIL.GeneralPremise.providerFreeNames request.environment.provider

theorem licensed_goal_free_within (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source) :
    Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.goalFreeWithin (requestFootprint request) request.goal := by
  intro name member
  apply List.mem_append_left
  have contains := (GeneralEquationContexts.fill_contains_source
    request.job.site.context request.job.site.focus).2.1 name member
  rw [Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.Licensed.source_eq licensed.2] at contains
  exact contains

/-- One actual readout call, including refusals, with exact store and I/O.
The supplied result is data captured from the premise machine. -/
def ReadoutObserved (state : State) (request : GeneralRuleJobExecution.Request)
    (resultWire observation : Term) : Prop :=
  ∃ caller : Subst,
    [v "jobRequest", v "jobResult"].map (applySubst caller) =
      [encoded (ScopedRuleJobReadoutExecution.requestProjectionTerm request (requestFootprint request)),
       encoded resultWire] ∧
    ∃ evaluatorFuel, run RuleExecutionProgram.scopedProgram evaluatorFuel
      {state, control := .evaluate caller
        (a "gslt:rule:job-finish-root" [v "jobRequest", v "jobResult"])} =
        .complete state [encoded observation] [] []

/-- Encoding of the original projection, with an explicit observation for a
replacement that is refused. -/
def rootReadoutTerm (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (result : Execution.Result request.environment request.goal) : Term :=
  encodeOption (fun answer : GeneralRuleJobExecution.Answer request =>
    ScopedRuleJobReadoutExecution.receiptTerm answer.val)
    (GeneralRuleJobExecution.rootProjection request licensed result)

/-- Interpret a successful protocol observation with the existing receipt
decoder. Refusal and malformed observations contribute no receipt. -/
def successfulReadout? : Term → Option GeneralRuleJobs.Receipt
  | .application "Some" [receipt] => ScopedRuleJobReadoutExecution.decodeReceipt? receipt
  | _ => none

@[simp] theorem successful_root_readout (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (result : Execution.Result request.environment request.goal) :
    successfulReadout? (rootReadoutTerm request licensed result) =
      (GeneralRuleJobExecution.rootProjection request licensed result).map (fun answer => answer.val) := by
  cases projected : GeneralRuleJobExecution.rootProjection request licensed result <;>
    simp only [rootReadoutTerm, projected, encodeOption, successfulReadout?,
      ScopedRuleJobReadoutExecution.decodeReceipt?_receiptTerm, Option.map_none, Option.map_some]

/-- The receipt decoder retains the complete ordered projection of a drained
source machine, including repeated occurrences. -/
theorem finished_root_readouts_exact (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source) :
    ((Execution.finish request.environment request.goal).answers.map
      (rootReadoutTerm request licensed)).filterMap successfulReadout? =
      (GeneralRuleJobExecution.finishState request licensed).answers.map (fun answer => answer.val) := by
  rw [List.filterMap_map]
  change (Execution.finish request.environment request.goal).answers.filterMap
    (fun result => successfulReadout? (rootReadoutTerm request licensed result)) = _
  simp only [successful_root_readout]
  rw [Execution.finish_answers, GeneralRuleJobExecution.finishState_root_readouts, List.map_filterMap]

theorem readout_observed_iff (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (result : Execution.Result request.environment request.goal)
    (member : result ∈ (Execution.run request.environment request.goal fuel
      (Execution.start request.environment request.goal)).answers) (observation : Term) :
    ReadoutObserved state request (PremiseOperationsExecution.GeneralExecution.resultTerm result) observation ↔
      observation = rootReadoutTerm request licensed result := by
  cases result with
  | root trace captured completed history target valid =>
    constructor
    · rintro ⟨caller, inputs, evaluatorFuel, observed⟩
      have checked :=
        (ScopedRuleJobReadoutExecution.finish_root_run_captured_completed_iff_in_extension
          RuleExecutionProgram.scopedProgram
          PremiseOperationsExecution.GeneralExecution.CompletedAssembly.readout_agreement
          caller state state request licensed fuel trace captured completed history target valid member
          "jobRequest" "jobResult" inputs [encoded observation] [] []).mp ⟨evaluatorFuel, observed⟩
      simpa only [rootReadoutTerm, GeneralRuleJobExecution.rootProjection,
        List.cons.injEq, and_true, CettaWireAtom.encode_eq_encode] using checked.2.1
    · intro same
      subst observation
      let caller : Subst :=
        [("jobRequest", encoded (ScopedRuleJobReadoutExecution.requestProjectionTerm request
            (requestFootprint request))),
         ("jobResult", encoded (PremiseOperationsExecution.GeneralExecution.resultTerm
            (.root trace captured completed history target valid)))]
      have inputs : [v "jobRequest", v "jobResult"].map (applySubst caller) =
          [encoded (ScopedRuleJobReadoutExecution.requestProjectionTerm request (requestFootprint request)),
           encoded (PremiseOperationsExecution.GeneralExecution.resultTerm
             (.root trace captured completed history target valid))] := by
        simp [caller, applySubst, Subst.lookup]
      refine ⟨caller, inputs, ?_⟩
      exact (ScopedRuleJobReadoutExecution.finish_root_run_captured_completed_iff_in_extension
        RuleExecutionProgram.scopedProgram
        PremiseOperationsExecution.GeneralExecution.CompletedAssembly.readout_agreement
        caller state state request licensed fuel trace captured completed history target valid member
        "jobRequest" "jobResult" inputs _ [] []).mpr ⟨rfl, rfl, rfl, rfl⟩

/-- An ordered selection of actual source results has an exact sequence of
target readouts. The relation records one call per physical occurrence. -/
theorem readouts_of_results_iff (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (results : List (Execution.Result request.environment request.goal))
    (members : ∀ result ∈ results, result ∈ (Execution.run request.environment request.goal fuel
      (Execution.start request.environment request.goal)).answers) (observations : List Term) :
    List.Forall₂ (ReadoutObserved state request)
        (results.map PremiseOperationsExecution.GeneralExecution.resultTerm) observations ↔
      observations = results.map (rootReadoutTerm request licensed) := by
  induction results generalizing observations with
  | nil => simp only [List.map_nil, List.forall₂_nil_left_iff]
  | cons result rest ih =>
    cases observations with
    | nil =>
      constructor <;> intro impossible <;> cases impossible
    | cons observation remaining =>
      simp only [List.map_cons, List.forall₂_cons, List.cons.injEq]
      rw [readout_observed_iff state request licensed fuel result
        (members result List.mem_cons_self) observation]
      exact and_congr Iff.rfl (ih
        (fun other member => members other (List.mem_cons_of_mem result member)) remaining)

theorem job_run_captured_returns (caller : Subst) (state : State)
    (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (environmentName fuelName stateName : String)
    (inputs : [v environmentName, v fuelName, v stateName].map (applySubst caller) =
      [encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm request.environment
        (request.environment.free.entriesOn (requestFootprint request))),
       encoded (.natural fuel), encoded (PremiseOperationsExecution.GeneralExecution.stateTerm (Execution.start request.environment request.goal))]) :
    PureReturns RuleExecutionProgram.scopedProgram caller state
      (a "gslt:premise:machine-run" [v environmentName, v fuelName, v stateName]) state
      (encoded (encodeOption PremiseOperationsExecution.GeneralExecution.stateTerm (some (Execution.run request.environment request.goal fuel
        (Execution.start request.environment request.goal))))) := by
  apply PremiseOperationsExecution.GeneralExecution.CompletedAssembly.captured_machine_run_iff caller state state environmentName fuelName stateName _ |>.mp
  exact PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.Machine.run_from_start_captured_returns caller state
    request.environment finiteProvider request.goal fuel (requestFootprint request)
    (fun _ member => List.mem_append_right _ member)
    (licensed_goal_free_within request licensed) _ inputs

theorem job_run_captured_completed_iff (caller : Subst) (state : State)
    (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (environmentName fuelName stateName : String)
    (inputs : [v environmentName, v fuelName, v stateName].map (applySubst caller) =
      [encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm request.environment
        (request.environment.free.entriesOn (requestFootprint request))),
       encoded (.natural fuel), encoded (PremiseOperationsExecution.GeneralExecution.stateTerm (Execution.start request.environment request.goal))])
    (after : State) (answers input output : List Atom) :
    (∃ evaluatorFuel, run RuleExecutionProgram.scopedProgram evaluatorFuel
      {state, control := .evaluate caller
        (a "gslt:premise:machine-run" [v environmentName, v fuelName, v stateName])} =
        .complete after answers input output) ↔
      after = state ∧ answers = [encoded (encodeOption PremiseOperationsExecution.GeneralExecution.stateTerm
        (some (Execution.run request.environment request.goal fuel
          (Execution.start request.environment request.goal))))] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff RuleExecutionProgram.scopedProgram caller state state _ _
    (job_run_captured_returns caller state request finiteProvider licensed fuel environmentName fuelName stateName inputs)
    after answers input output

/-- A completed machine observation retains the entire ordered scheduler
state, including pending tasks, unresolved obligations and the work count. -/
theorem observed_job_state_fields_exact (caller : Subst) (state : State)
    (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (environmentName fuelName stateName : String)
    (inputs : [v environmentName, v fuelName, v stateName].map (applySubst caller) =
      [encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm request.environment
        (request.environment.free.entriesOn (requestFootprint request))),
       encoded (.natural fuel), encoded (PremiseOperationsExecution.GeneralExecution.stateTerm (Execution.start request.environment request.goal))])
    (agendaWire unresolvedWire : Term) (answerWires : List Term) (work : Nat)
    (observed : ∃ evaluatorFuel, run RuleExecutionProgram.scopedProgram evaluatorFuel
      {state, control := .evaluate caller
        (a "gslt:premise:machine-run" [v environmentName, v fuelName, v stateName])} =
        .complete state [encoded (.application "Some" [.application "PremiseState"
          [agendaWire, encodeList id answerWires, unresolvedWire, .natural work]])] [] []) :
    agendaWire = encodeList PremiseOperationsExecution.GeneralExecution.taskTerm
        (Execution.run request.environment request.goal fuel
          (Execution.start request.environment request.goal)).agenda ∧
      answerWires = (Execution.run request.environment request.goal fuel
        (Execution.start request.environment request.goal)).answers.map
          PremiseOperationsExecution.GeneralExecution.resultTerm ∧
      unresolvedWire = encodeList PremiseOperationsExecution.GeneralExecution.obligationTerm
        (Execution.run request.environment request.goal fuel
          (Execution.start request.environment request.goal)).unresolved ∧
      work = (Execution.run request.environment request.goal fuel
        (Execution.start request.environment request.goal)).work := by
  have same := ((job_run_captured_completed_iff caller state request finiteProvider licensed fuel
    environmentName fuelName stateName inputs state _ [] []).mp observed).2.1
  have wireSame := CettaWireAtom.encode_injective _ _ (List.cons.inj same).1
  dsimp only [encodeOption, PremiseOperationsExecution.GeneralExecution.stateTerm,
    PremiseSchedulerExecution.schedulerStateTerm] at wireSame
  have fields := (Term.application.inj (List.cons.inj (Term.application.inj wireSame).2).1).2
  have first := List.cons.inj fields
  have second := List.cons.inj first.2
  have third := List.cons.inj second.2
  have fourth := List.cons.inj third.2
  refine ⟨first.1, ?_, third.1, Term.natural.inj fourth.1⟩
  apply CettaWire.encodeList_injective id Function.injective_id
  simpa only [CettaWire.encodeList_map, Function.id_comp] using second.1

theorem observed_job_answers_exact (caller : Subst) (state : State)
    (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (environmentName fuelName stateName : String)
    (inputs : [v environmentName, v fuelName, v stateName].map (applySubst caller) =
      [encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm request.environment
        (request.environment.free.entriesOn (requestFootprint request))),
       encoded (.natural fuel), encoded (PremiseOperationsExecution.GeneralExecution.stateTerm (Execution.start request.environment request.goal))])
    (agendaWire unresolvedWire : Term) (answerWires : List Term) (work : Nat)
    (observed : ∃ evaluatorFuel, run RuleExecutionProgram.scopedProgram evaluatorFuel
      {state, control := .evaluate caller
        (a "gslt:premise:machine-run" [v environmentName, v fuelName, v stateName])} =
        .complete state [encoded (.application "Some" [.application "PremiseState"
          [agendaWire, encodeList id answerWires, unresolvedWire, .natural work]])] [] []) :
    answerWires = (Execution.run request.environment request.goal fuel
      (Execution.start request.environment request.goal)).answers.map PremiseOperationsExecution.GeneralExecution.resultTerm :=
  (observed_job_state_fields_exact caller state request finiteProvider licensed fuel environmentName fuelName stateName
    inputs agendaWire unresolvedWire answerWires work observed).2.1

/-- Reading every physical result in its emitted order gives exactly the
source projection list. Refused replacements occupy their original positions;
equal receipts and equal result values are not deduplicated. -/
theorem observed_job_readouts_iff (caller : Subst) (state : State)
    (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (environmentName fuelName stateName : String)
    (inputs : [v environmentName, v fuelName, v stateName].map (applySubst caller) =
      [encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm request.environment
        (request.environment.free.entriesOn (requestFootprint request))),
       encoded (.natural fuel), encoded (PremiseOperationsExecution.GeneralExecution.stateTerm
         (Execution.start request.environment request.goal))])
    (agendaWire unresolvedWire : Term) (answerWires : List Term) (work : Nat)
    (observed : ∃ evaluatorFuel, run RuleExecutionProgram.scopedProgram evaluatorFuel
      {state, control := .evaluate caller
        (a "gslt:premise:machine-run" [v environmentName, v fuelName, v stateName])} =
        .complete state [encoded (.application "Some" [.application "PremiseState"
          [agendaWire, encodeList id answerWires, unresolvedWire, .natural work]])] [] [])
    (readouts : List Term) :
    List.Forall₂ (ReadoutObserved state request) answerWires readouts ↔
      readouts = (Execution.run request.environment request.goal fuel
        (Execution.start request.environment request.goal)).answers.map
          (rootReadoutTerm request licensed) := by
  rw [observed_job_answers_exact caller state request finiteProvider licensed fuel environmentName fuelName stateName
    inputs agendaWire unresolvedWire answerWires work observed]
  exact readouts_of_results_iff state request licensed fuel _ (fun _ member => member) readouts

/-- Once the inner source machine has drained, actual readout calls produce
the complete outer cursor's receipt list, in its original order and with every
duplicate occurrence. Only the original projection's refusals are removed. -/
theorem observed_job_completed_receipts_exact (caller : Subst) (state : State)
    (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (environmentName fuelName stateName : String)
    (inputs : [v environmentName, v fuelName, v stateName].map (applySubst caller) =
      [encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm request.environment
        (request.environment.free.entriesOn (requestFootprint request))),
       encoded (.natural (Execution.treeStart request.environment request.goal).cost),
       encoded (PremiseOperationsExecution.GeneralExecution.stateTerm
         (Execution.start request.environment request.goal))])
    (agendaWire unresolvedWire : Term) (answerWires : List Term) (work : Nat)
    (observed : ∃ evaluatorFuel, run RuleExecutionProgram.scopedProgram evaluatorFuel
      {state, control := .evaluate caller
        (a "gslt:premise:machine-run" [v environmentName, v fuelName, v stateName])} =
        .complete state [encoded (.application "Some" [.application "PremiseState"
          [agendaWire, encodeList id answerWires, unresolvedWire, .natural work]])] [] [])
    (readouts : List Term) (readoutCalls : List.Forall₂ (ReadoutObserved state request) answerWires readouts) :
    readouts.filterMap successfulReadout? =
      (GeneralRuleJobExecution.finishState request licensed).answers.map (fun answer => answer.val) := by
  have exactReadouts := (observed_job_readouts_iff caller state request finiteProvider licensed
    (Execution.treeStart request.environment request.goal).cost environmentName fuelName stateName
    inputs agendaWire unresolvedWire answerWires work observed readouts).mp readoutCalls
  rw [exactReadouts]
  exact finished_root_readouts_exact request licensed

theorem observed_job_receipt_gslt (caller : Subst) (state : State)
    (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (environmentName fuelName stateName : String)
    (runInputs : [v environmentName, v fuelName, v stateName].map (applySubst caller) =
      [encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm request.environment
        (request.environment.free.entriesOn (requestFootprint request))),
       encoded (.natural fuel), encoded (PremiseOperationsExecution.GeneralExecution.stateTerm (Execution.start request.environment request.goal))])
    (agendaWire unresolvedWire : Term) (answerWires : List Term) (work : Nat)
    (machineObserved : ∃ evaluatorFuel, run RuleExecutionProgram.scopedProgram evaluatorFuel
      {state, control := .evaluate caller
        (a "gslt:premise:machine-run" [v environmentName, v fuelName, v stateName])} =
        .complete state [encoded (.application "Some" [.application "PremiseState"
          [agendaWire, encodeList id answerWires, unresolvedWire, .natural work]])] [] [])
    (resultWire : Term) (selected : resultWire ∈ answerWires)
    (requestName resultName : String)
    (readoutInputs : [v requestName, v resultName].map (applySubst caller) =
      [encoded (ScopedRuleJobReadoutExecution.requestProjectionTerm request (requestFootprint request)), encoded resultWire])
    (receipt : GeneralRuleJobs.Receipt)
    (readoutObserved : ∃ evaluatorFuel, run RuleExecutionProgram.scopedProgram evaluatorFuel
      {state, control := .evaluate caller (a "gslt:rule:job-finish-root" [v requestName, v resultName])} =
        .complete state [encoded (.application "Some" [ScopedRuleJobReadoutExecution.receiptTerm receipt])] [] []) :
    GeneralOccurrenceSemantics.Primitive request.plan request.bound request.expected request.source receipt ∧
      (GeneralOccurrenceSemantics.gslt request.plan request.bound request.expected).Step request.source receipt.target ∧
      receipt.Valid request.plan request.bound request.expected request.source := by
  have exactAnswers := observed_job_answers_exact caller state request finiteProvider licensed fuel
    environmentName fuelName stateName runInputs agendaWire unresolvedWire answerWires work machineObserved
  apply ScopedRuleJobReadoutExecution.finish_root_observed_answer_gslt_in_extension RuleExecutionProgram.scopedProgram
    PremiseOperationsExecution.GeneralExecution.CompletedAssembly.readout_agreement caller state request licensed fuel resultWire _
    requestName resultName readoutInputs receipt readoutObserved
  rwa [← exactAnswers]

/-- Readout at a physical answer index preserves and reflects the original
cursor expansion. The machine observation supplies the source answer;
replacement, target typing and every field of its receipt remain checked. -/
theorem observed_job_cursor_receipt_iff (caller : Subst) (state : State)
    (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (environmentName fuelName stateName : String)
    (runInputs : [v environmentName, v fuelName, v stateName].map (applySubst caller) =
      [encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm request.environment
        (request.environment.free.entriesOn (requestFootprint request))),
       encoded (.natural fuel), encoded (PremiseOperationsExecution.GeneralExecution.stateTerm
        (Execution.start request.environment request.goal))])
    (agendaWire unresolvedWire : Term) (answerWires : List Term) (work : Nat)
    (machineObserved : ∃ evaluatorFuel, run RuleExecutionProgram.scopedProgram evaluatorFuel
      {state, control := .evaluate caller
        (a "gslt:premise:machine-run" [v environmentName, v fuelName, v stateName])} =
        .complete state [encoded (.application "Some" [.application "PremiseState"
          [agendaWire, encodeList id answerWires, unresolvedWire, .natural work]])] [] [])
    (cursor : Nat) (resultWire : Term) (selected : answerWires[cursor]? = some resultWire)
    (requestName resultName : String)
    (readoutInputs : [v requestName, v resultName].map (applySubst caller) =
      [encoded (ScopedRuleJobReadoutExecution.requestProjectionTerm request (requestFootprint request)),
       encoded resultWire]) (receipt : GeneralRuleJobs.Receipt) :
    (∃ evaluatorFuel, run RuleExecutionProgram.scopedProgram evaluatorFuel
      {state, control := .evaluate caller (a "gslt:rule:job-finish-root" [v requestName, v resultName])} =
        .complete state [encoded (.application "Some" [ScopedRuleJobReadoutExecution.receiptTerm receipt])] [] []) ↔
      ∃ answer ∈ (GeneralRuleJobExecution.expand request
        (.root ⟨licensed, Execution.run request.environment request.goal fuel
          (Execution.start request.environment request.goal), cursor⟩)).answers,
        answer.val = receipt := by
  have exactAnswers := observed_job_answers_exact caller state request finiteProvider licensed fuel
    environmentName fuelName stateName runInputs agendaWire unresolvedWire answerWires work machineObserved
  rw [exactAnswers, List.getElem?_map] at selected
  obtain ⟨result, atCursor, sameWire⟩ := Option.map_eq_some_iff.mp selected
  cases sameWire
  cases result with
  | root trace captured completed history target valid =>
      rw [ScopedRuleJobReadoutExecution.finish_root_run_captured_receipt_iff_in_extension
        RuleExecutionProgram.scopedProgram
        PremiseOperationsExecution.GeneralExecution.CompletedAssembly.readout_agreement
        caller state request licensed fuel trace captured completed history target valid
        (List.mem_of_getElem? atCursor) requestName resultName readoutInputs receipt]
      exact (GeneralRuleJobExecution.expand_root_receipt_iff request
        ⟨licensed, Execution.run request.environment request.goal fuel
          (Execution.start request.environment request.goal), cursor⟩
        trace captured completed history target valid atCursor receipt).symm

/-- Actual machine and readout observations for one physical result occurrence.
No source-result membership or semantic validity is assumed by this predicate. -/
def ObservesReceipt (state : State) (request : GeneralRuleJobExecution.Request)
    (receipt : GeneralRuleJobs.Receipt) : Prop :=
  ∃ (caller : Subst) (fuel : Nat) (agendaWire unresolvedWire : Term)
    (answerWires : List Term) (work cursor : Nat) (resultWire : Term),
    [v "jobEnvironment", v "jobFuel", v "jobState"].map (applySubst caller) =
      [encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm request.environment
        (request.environment.free.entriesOn (requestFootprint request))),
       encoded (.natural fuel), encoded (PremiseOperationsExecution.GeneralExecution.stateTerm
        (Execution.start request.environment request.goal))] ∧
    (∃ evaluatorFuel, run RuleExecutionProgram.scopedProgram evaluatorFuel
      {state, control := .evaluate caller
        (a "gslt:premise:machine-run" [v "jobEnvironment", v "jobFuel", v "jobState"])} =
        .complete state [encoded (.application "Some" [.application "PremiseState"
          [agendaWire, encodeList id answerWires, unresolvedWire, .natural work]])] [] []) ∧
    answerWires[cursor]? = some resultWire ∧
    [v "jobRequest", v "jobResult"].map (applySubst caller) =
      [encoded (ScopedRuleJobReadoutExecution.requestProjectionTerm request (requestFootprint request)),
       encoded resultWire] ∧
    ∃ evaluatorFuel, run RuleExecutionProgram.scopedProgram evaluatorFuel
      {state, control := .evaluate caller
        (a "gslt:rule:job-finish-root" [v "jobRequest", v "jobResult"])} =
        .complete state [encoded (.application "Some" [ScopedRuleJobReadoutExecution.receiptTerm receipt])] [] []

theorem observes_receipt_valid (state : State) (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (receipt : GeneralRuleJobs.Receipt) (observed : ObservesReceipt state request receipt) :
    receipt.Valid request.plan request.bound request.expected request.source ∧ receipt.job = request.job := by
  obtain ⟨caller, fuel, agendaWire, unresolvedWire, answerWires, work, cursor, resultWire,
    runInputs, machineObserved, selected, readoutInputs, readoutObserved⟩ := observed
  have exactAnswers := observed_job_answers_exact caller state request finiteProvider licensed fuel
    "jobEnvironment" "jobFuel" "jobState" runInputs agendaWire unresolvedWire answerWires work machineObserved
  rw [exactAnswers, List.getElem?_map] at selected
  obtain ⟨result, atCursor, sameWire⟩ := Option.map_eq_some_iff.mp selected
  cases sameWire
  cases result with
  | root trace captured completed history target valid =>
      obtain ⟨answer, finished, same⟩ :=
        (ScopedRuleJobReadoutExecution.finish_root_run_captured_receipt_iff_in_extension
          RuleExecutionProgram.scopedProgram
          PremiseOperationsExecution.GeneralExecution.CompletedAssembly.readout_agreement
          caller state request licensed fuel trace captured completed history target valid
          (List.mem_of_getElem? atCursor) "jobRequest" "jobResult" readoutInputs receipt).mp readoutObserved
      subst receipt
      exact ⟨answer.property, GeneralRuleJobExecution.projection_job
        (show GeneralRuleJobExecution.rootProjection request licensed
          (.root trace captured completed history target valid) = some answer from finished)⟩

/-- Every authorized receipt occurs in the target, with the original result
index and all evidence fields. The stratification check is the original source
admission condition used by its finite-work completeness theorem. -/
theorem valid_receipt_observed (state : State) (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (stratified : GeneralPremise.checkStepStratification request.environment.language = true)
    (receipt : GeneralRuleJobs.Receipt)
    (valid : receipt.Valid request.plan request.bound request.expected request.source)
    (job : receipt.job = request.job) : ObservesReceipt state request receipt := by
  let wanted : Execution.Result request.environment request.goal :=
    .root receipt.matcherTrace receipt.captured receipt.completed receipt.premiseHistory receipt.localTarget
      (job ▸ valid.2.1)
  let fuel := (Execution.treeStart request.environment request.goal).cost
  let finishedState := Execution.run request.environment request.goal fuel
    (Execution.start request.environment request.goal)
  have ordered : wanted.ordered = true := (job ▸ valid.2.1).ordered stratified
  have member : wanted ∈ finishedState.answers :=
    Execution.finish_contains request.environment request.goal wanted ordered
  obtain ⟨cursor, selected⟩ := List.mem_iff_getElem?.mp member
  let caller : Subst :=
    [("jobEnvironment", encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm request.environment
        (request.environment.free.entriesOn (requestFootprint request)))),
     ("jobFuel", encoded (.natural fuel)),
     ("jobState", encoded (PremiseOperationsExecution.GeneralExecution.stateTerm
        (Execution.start request.environment request.goal))),
     ("jobRequest", encoded (ScopedRuleJobReadoutExecution.requestProjectionTerm request (requestFootprint request))),
     ("jobResult", encoded (PremiseOperationsExecution.GeneralExecution.resultTerm wanted))]
  have runInputs : [v "jobEnvironment", v "jobFuel", v "jobState"].map (applySubst caller) =
      [encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm request.environment
        (request.environment.free.entriesOn (requestFootprint request))),
       encoded (.natural fuel), encoded (PremiseOperationsExecution.GeneralExecution.stateTerm
        (Execution.start request.environment request.goal))] := by
    simp [caller, applySubst, Subst.lookup]
  have readoutInputs : [v "jobRequest", v "jobResult"].map (applySubst caller) =
      [encoded (ScopedRuleJobReadoutExecution.requestProjectionTerm request (requestFootprint request)),
       encoded (PremiseOperationsExecution.GeneralExecution.resultTerm wanted)] := by
    simp [caller, applySubst, Subst.lookup]
  have machineObserved : ∃ evaluatorFuel, run RuleExecutionProgram.scopedProgram evaluatorFuel
      {state, control := .evaluate caller
        (a "gslt:premise:machine-run" [v "jobEnvironment", v "jobFuel", v "jobState"])} =
      .complete state [encoded (encodeOption PremiseOperationsExecution.GeneralExecution.stateTerm
        (some finishedState))] [] [] :=
    (job_run_captured_completed_iff caller state request finiteProvider licensed fuel
      "jobEnvironment" "jobFuel" "jobState" runInputs state _ [] []).mpr ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨answer, finished, same⟩ := GeneralRuleJobExecution.finishRoot_complete valid job
  have readoutObserved :=
    (ScopedRuleJobReadoutExecution.finish_root_run_captured_receipt_iff_in_extension
      RuleExecutionProgram.scopedProgram
      PremiseOperationsExecution.GeneralExecution.CompletedAssembly.readout_agreement
      caller state request licensed fuel receipt.matcherTrace receipt.captured receipt.completed
      receipt.premiseHistory receipt.localTarget (job ▸ valid.2.1) member
      "jobRequest" "jobResult" readoutInputs receipt).mpr ⟨answer, finished, same⟩
  refine ⟨caller, fuel, encodeList PremiseOperationsExecution.GeneralExecution.taskTerm finishedState.agenda,
    encodeList PremiseOperationsExecution.GeneralExecution.obligationTerm finishedState.unresolved,
    finishedState.answers.map PremiseOperationsExecution.GeneralExecution.resultTerm,
    finishedState.work, cursor, PremiseOperationsExecution.GeneralExecution.resultTerm wanted,
    runInputs, ?_, ?_, readoutInputs, readoutObserved⟩
  · simpa only [PremiseOperationsExecution.GeneralExecution.stateTerm,
      PremiseSchedulerExecution.schedulerStateTerm, encodeOption, CettaWire.encodeList_map,
      Function.id_comp] using machineObserved
  · simp only [List.getElem?_map, selected, Option.map_some]

/-- Completed target observations preserve and reflect the original
source-authorized receipts for every admitted scoped conditional rule job. -/
theorem observes_receipt_iff_valid (state : State) (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (stratified : GeneralPremise.checkStepStratification request.environment.language = true)
    (receipt : GeneralRuleJobs.Receipt) :
    ObservesReceipt state request receipt ↔
      receipt.Valid request.plan request.bound request.expected request.source ∧ receipt.job = request.job :=
  ⟨observes_receipt_valid state request finiteProvider licensed receipt,
    fun ⟨valid, job⟩ => valid_receipt_observed state request finiteProvider licensed stratified receipt valid job⟩

theorem observes_receipt_gslt (state : State) (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (receipt : GeneralRuleJobs.Receipt) (observed : ObservesReceipt state request receipt) :
    (GeneralOccurrenceSemantics.gslt request.plan request.bound request.expected).Step
      request.source receipt.target :=
  ⟨request.source, receipt, .refl _, (observes_receipt_valid state request finiteProvider licensed receipt observed).1, .refl _⟩

/-- An unauthorized receipt or one naming a different physical job cannot be
returned by these machine and readout observations. -/
theorem observes_receipt_refused (state : State) (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (receipt : GeneralRuleJobs.Receipt)
    (invalid : ¬ receipt.Valid request.plan request.bound request.expected request.source ∨
      receipt.job ≠ request.job) : ¬ ObservesReceipt state request receipt := by
  intro observed
  have checked := observes_receipt_valid state request finiteProvider licensed receipt observed
  rcases invalid with invalid | wrongJob
  · exact invalid checked.1
  · exact wrongJob checked.2


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralRuleJobObservation
