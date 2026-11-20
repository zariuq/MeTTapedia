import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceResolve
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.SourceDAGReceive

/-!
# Numbered proof requests through the existing registered checker

This reader handles the ten inference requests and explicit axioms. Source
declarations retain their own state-changing registry protocol. Numbered
syntax is resolved by the total reference queries; primitive checking,
parent-address checking and claimed-output checking use the existing kernel.
Preparation alone is not admission. Source IDs and event serials are retained
separately, including repeated ordered parent occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceProofs

open Lean Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution DefinitionAdapters SignatureFormation ExportReplay

structure Header where
  rule : String
  serial : Nat
  payload : List Json
  parents : List Nat
  outputs : List Json

def header? (raw : Json) : Option Header := do
  pure ⟨← ExportCodec.string? (← ExportCodec.field? raw "rule"),
    ← ExportCodec.natural? (← ExportCodec.field? raw "event"),
    ← ExportCodec.array? (← ExportCodec.field? raw "payload"),
    ← (← ExportCodec.array? (← ExportCodec.field? raw "parents")).mapM ExportCodec.natural?,
    ← ExportCodec.array? (← ExportCodec.field? raw "outputs")⟩

def sourceTerm? (reading : SourceDAGReceive.Reading) (index : Nat) : Option SourceTerm :=
  NumberedSourceResolve.term? reading.symbols (fun child => reading.input.types[child]?)
    (fun child => reading.input.terms[child]?) index

def sourceType? (reading : SourceDAGReceive.Reading) (index : Nat) : Option Ty :=
  NumberedSourceResolve.type? reading.symbols (fun child => reading.input.types[child]?) index

def canonical? (reading : SourceDAGReceive.Reading) (index : Nat) : Option CanonicalTerm := do
  (← sourceTerm? reading index).check

def checked? (reading : SourceDAGReceive.Reading) (index : Nat) : Option CheckedSourceTerm := do
  ExportReplay.checkedSource? (← sourceTerm? reading index)

structure Claim where
  id : Nat
  sequent : Sequent
  source : SourceTerm

def claim? (reading : SourceDAGReceive.Reading) (raw : Json) : Option Claim := do
  let id ← ExportCodec.natural? (← ExportCodec.field? raw "id")
  let hypotheses ← ExportCodec.array? (← ExportCodec.field? raw "hypotheses")
  let hypotheses ← hypotheses.mapM fun item => do canonical? reading (← ExportCodec.natural? item)
  let index ← ExportCodec.natural? (← ExportCodec.field? raw "conclusion")
  let source ← sourceTerm? reading index
  let conclusion ← canonical? reading index
  let sequent ← Sequent.ofObjectTerms? hypotheses conclusion
  pure ⟨id,sequent,source⟩

def parent? (reading : SourceDAGReceive.Reading) (source : Nat) : Option (Nat × Theorem) := do
  let address ← reading.registered.addresses[source]?
  pure (address, ← reading.registered.registered.cache[address]?)

def termMaplet? (reading : SourceDAGReceive.Reading) (raw : Json) : Option SourceSubstitution.TermMaplet := do
  match ← ExportCodec.array? raw with
  | [replacement,key] =>
      pure (← checked? reading (← ExportCodec.natural? replacement),
        ← sourceTerm? reading (← ExportCodec.natural? key))
  | _ => none

def typeMaplet? (reading : SourceDAGReceive.Reading) (raw : Json) : Option (Ty × Ty) := do
  match ← ExportCodec.array? raw with
  | [replacement,key] =>
      pure (← sourceType? reading (← ExportCodec.natural? replacement),
        ← sourceType? reading (← ExportCodec.natural? key))
  | _ => none

def request? (reading : SourceDAGReceive.Reading) (header : Header) (inputs : List (Nat × Theorem)) :
    Option RuleRequest := do
  match header.rule, header.payload, inputs with
  | "REFL", [term], [] => pure (.inference (.refl (← canonical? reading (← ExportCodec.natural? term))))
  | "BETA", [term], [] => pure (.inference (.beta (← checked? reading (← ExportCodec.natural? term))))
  | "ASSUME", [term], [] => pure (.inference (.assume (← canonical? reading (← ExportCodec.natural? term))))
  | "AXIOM", [term], [] => pure (.axiom ⟨∅,← canonical? reading (← ExportCodec.natural? term)⟩)
  | "TRANS", [], [(_,left),(_,right)] => pure (.inference (.trans left right))
  | "MK_COMB", [], [(_,left),(_,right)] => pure (.inference (.mkComb left right))
  | "EQ_MP", [], [(_,left),(_,right)] => pure (.inference (.eqMp left right))
  | "DEDUCT_ANTISYM_RULE", [], [(_,left),(_,right)] => pure (.inference (.deductAntisym left right))
  | "ABS", [binder], [(_,input)] =>
      match ← sourceTerm? reading (← ExportCodec.natural? binder) with
      | .var name type => pure (.inference (.abs ⟨name,type⟩ input))
      | _ => none
  | "INST", entries, [(_,input)] => pure (.inference (.inst (← entries.mapM (termMaplet? reading)) input))
  | "INST_TYPE", entries, [(_,input)] => pure (.inference (.instType (← entries.mapM (typeMaplet? reading)) input))
  | _, _, _ => none

def requestKind : RuleRequest → String
  | .axiom _ => "AXIOM"
  | .inference (.refl _) => "REFL"
  | .inference (.beta _) => "BETA"
  | .inference (.assume _) => "ASSUME"
  | .inference (.trans _ _) => "TRANS"
  | .inference (.mkComb _ _) => "MK_COMB"
  | .inference (.eqMp _ _) => "EQ_MP"
  | .inference (.deductAntisym _ _) => "DEDUCT_ANTISYM_RULE"
  | .inference (.abs _ _) => "ABS"
  | .inference (.inst _ _) => "INST"
  | .inference (.instType _ _) => "INST_TYPE"

theorem request_kind (reading : SourceDAGReceive.Reading) (header : Header)
    (inputs : List (Nat × Theorem)) (request : RuleRequest)
    (parsed : request? reading header inputs = some request) : requestKind request = header.rule := by
  unfold request? at parsed
  split at parsed
  all_goals
    try simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
  all_goals
    repeat' rcases parsed with ⟨_, parsed⟩
    try split at parsed
    all_goals simp_all [requestKind]
  all_goals cases parsed; rfl

def proofReceipt? : Registered.Command → Option Receipt
  | .proof receipt _ => some receipt
  | _ => none

structure Prepared (raw : Json) where
  header : Header
  parsed : header? raw = some header
  event : Event
  source : SourceTerm
  sourceIds : event.sourceIds.length = 1
  sourceParents : event.sourceParents = header.parents
  receipt : Receipt
  receiptAt : proofReceipt? event.command = some receipt
  receiptChecked : receipt.witness.check SourceProfileModels.policy = some receipt.conclusion
  receiptKind : requestKind receipt.witness = header.rule
  receiptOrigin : receipt.origin = ("indexed-hol-source-export",header.serial)

/- A Prepared value alone is a header/primitive-receipt candidate. The
successful prepare? equation binds its payload and claims to the particular
receiving state; consumers retain that equation. -/

def prepare? (reading : SourceDAGReceive.Reading) (raw : Json) : Option (Prepared raw) := do
  match parsed : header? raw with
  | none => none
  | some header =>
      match header.outputs with
      | [output] => do
          let inputs ← header.parents.mapM (parent? reading)
          match requested : request? reading header inputs with
          | none => none
          | some request =>
              match checked : request.check SourceProfileModels.policy with
              | none => none
              | some actual => do
                  let claim ← claim? reading output
                  let node : Receipt := ⟨actual,request,inputs.map (·.1),("indexed-hol-source-export",header.serial)⟩
                  let event : Event := ⟨[claim.id],header.parents,
                    .proof node (ExportReplay.instanceCertificates reading.registered.registered.context.signature),
                    [claim.sequent]⟩
                  pure ⟨header,parsed,event,claim.source,rfl,rfl,node,rfl,checked,
                    request_kind reading header inputs request requested,rfl⟩
      | _ => none

def receive? (before : SourceDAGReceive.Reading) (raw : Json) : Option SourceDAGReceive.Reading := do
  let prepared ← prepare? before raw
  match accepted : ExportReplay.apply SourceProfileModels.policy before.registered prepared.event with
  | none => none
  | some after =>
      pure { before with
        registered := after
        history := ExportReceiptHistory.apply_history SourceProfile.primitiveContext
          SourceProfileModels.policy before.history accepted
        sourceConclusions := ExportCodec.addConclusions before.sourceConclusions prepared.event.sourceIds [prepared.source] }

theorem receive_checked (before after : SourceDAGReceive.Reading) (raw : Json)
    (received : receive? before raw = some after) :
    ∃ prepared : Prepared raw,
      prepare? before raw = some prepared ∧
      ExportReplay.apply SourceProfileModels.policy before.registered prepared.event = some after.registered ∧
      Registered.apply SourceProfileModels.policy before.registered.registered prepared.event.command =
        some after.registered.registered ∧
      ExportReplay.resolveParents before.registered prepared.event.sourceParents = some prepared.event.command.parents ∧
      after.input = before.input ∧ after.symbols = before.symbols := by
  unfold receive? at received
  cases prepared : prepare? before raw with
  | none => simp only [prepared, bind, Option.bind] at received; cases received
  | some candidate =>
      simp only [prepared, bind, Option.bind] at received
      split at received
      · cases received
      · rename_i state accepted
        have equal := Option.some.inj received
        subst after
        have actual := ExportReplay.apply_checked SourceProfileModels.policy accepted
        exact ⟨candidate,rfl,accepted,actual.1,actual.2.1,rfl,rfl⟩

theorem receive_event_graph (before after : SourceDAGReceive.Reading) (raw : Json)
    (received : receive? before raw = some after) :
    ∃ prepared : Prepared raw,
      prepare? before raw = some prepared ∧
      header? raw = some prepared.header ∧
      after.registered.receipts = before.registered.receipts.push prepared.event ∧
      ExportReplay.resolveParents before.registered prepared.header.parents = some prepared.event.command.parents ∧
      prepared.event.sourceIds.length = 1 := by
  obtain ⟨prepared,preparedAt,accepted,_,parents,_,_⟩ := receive_checked before after raw received
  have actual := ExportReplay.apply_checked SourceProfileModels.policy accepted
  refine ⟨prepared,preparedAt,prepared.parsed,actual.2.2.2.1,?_,prepared.sourceIds⟩
  rw [← prepared.sourceParents]
  exact parents

def replay? : SourceDAGReceive.Reading → List Json → Option SourceDAGReceive.Reading
  | before, [] => some before
  | before, raw :: rest => do
      let after ← receive? before raw
      replay? after rest

/-- The same intermediate receiving state is used by both command calls.
The witness is the actual source event list, with one event per raw record. -/
theorem replay_event_graph (before after : SourceDAGReceive.Reading) (raws : List Json)
    (accepted : replay? before raws = some after) :
    ∃ events : List Event, events.length = raws.length ∧
      ExportReplay.replayFrom SourceProfileModels.policy before.registered events = some after.registered ∧
      after.input = before.input ∧ after.symbols = before.symbols := by
  induction raws generalizing before with
  | nil =>
      simp only [replay?, Option.some.injEq] at accepted
      subst after
      exact ⟨[],rfl,rfl,rfl,rfl⟩
  | cons raw rest ih =>
      cases first : receive? before raw with
      | none => simp [replay?,first] at accepted
      | some middle =>
          have remaining : replay? middle rest = some after := by simpa [replay?,first] using accepted
          obtain ⟨events,length,continued,inputSame,symbolsSame⟩ := ih middle remaining
          obtain ⟨prepared,_,stepped,_,_,inputFirst,symbolsFirst⟩ := receive_checked before middle raw first
          refine ⟨prepared.event :: events,by simpa only [List.length_cons] using congrArg Nat.succ length,
            ?_,inputSame.trans inputFirst,symbolsSame.trans symbolsFirst⟩
          simp [ExportReplay.replayFrom,stepped,continued]

theorem replay_registered_reachable (before after : SourceDAGReceive.Reading) (raws : List Json)
    (accepted : replay? before raws = some after) :
    (Registered.gslt SourceProfileModels.policy).MultiStep before.registered.registered after.registered.registered := by
  obtain ⟨events,_,replayed,_,_⟩ := replay_event_graph before after raws accepted
  exact ExportReplay.replayFrom_reachable SourceProfileModels.policy before.registered events after.registered replayed

def receiveAt? (before : SourceDAGReceive.Reading) (index : Nat) : Option SourceDAGReceive.Reading := do
  let raw ← before.input.events[index]?
  receive? before raw

theorem receiveAt_checked (before after : SourceDAGReceive.Reading) (index : Nat)
    (accepted : receiveAt? before index = some after) :
    ∃ raw, before.input.events[index]? = some raw ∧ receive? before raw = some after := by
  cases found : before.input.events[index]? with
  | none => simp [receiveAt?,found] at accepted
  | some raw => exact ⟨raw,rfl,by simpa [receiveAt?,found] using accepted⟩

/-- Count is the requested number of input records, not a search budget.
Missing input or an unsupported declaration does not prove semantic refusal. -/
def replayInput? : SourceDAGReceive.Reading → Nat → Nat → Option SourceDAGReceive.Reading
  | before, _, 0 => some before
  | before, index, count+1 => do
      let after ← receiveAt? before index
      replayInput? after (index+1) count

theorem replayInput_registered_reachable (before after : SourceDAGReceive.Reading) (index count : Nat)
    (accepted : replayInput? before index count = some after) :
    (Registered.gslt SourceProfileModels.policy).MultiStep before.registered.registered after.registered.registered ∧
      after.input = before.input ∧ after.symbols = before.symbols := by
  induction count generalizing before index with
  | zero =>
      simp only [replayInput?, Option.some.injEq] at accepted
      subst after
      exact ⟨.refl _,rfl,rfl⟩
  | succ count ih =>
      cases first : receiveAt? before index with
      | none => simp [replayInput?,first] at accepted
      | some middle =>
          have remaining : replayInput? middle (index+1) count = some after := by
            simpa [replayInput?,first] using accepted
          obtain ⟨raw,_,received⟩ := receiveAt_checked before middle index first
          obtain ⟨prepared,_,_,step,_,inputFirst,symbolsFirst⟩ := receive_checked before middle raw received
          obtain ⟨continued,inputLast,symbolsLast⟩ := ih middle (index+1) remaining
          exact ⟨.step ⟨prepared.event.command,step⟩ continued,
            inputLast.trans inputFirst,symbolsLast.trans symbolsFirst⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceProofs
