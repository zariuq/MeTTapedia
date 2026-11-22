import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceDeclarations

/-!
# Mixed total numbered source reception

This named sequential driver dispatches the actual raw header to the existing
numbered declaration or proof reader. Each accepted record contributes one
registered command, including a type definition with two ordered outputs.
Intermediate registries, source conclusions and registered states are carried
between calls. The driver selects a requested finite input window; an absent
or unsupported record does not establish semantic refusal or termination.

The source driver retains the fixed standard policy. Transform rule storage,
worlds and firing-grain choices belong to its later realization bridges.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceReception

open Lean Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution ExportReplay

abbrev Reading := SourceDAGReceive.Reading

def isDeclaration (header : NumberedSourceProofs.Header) : Bool :=
  header.rule == "DEFINITION" || header.rule == "TYPE_DEFINITION"

def receive? (before : Reading) (raw : Json) : Option Reading := do
  let header ← NumberedSourceProofs.header? raw
  if isDeclaration header then NumberedSourceDeclarations.receive? before raw
  else NumberedSourceProofs.receive? before raw

theorem receive_dispatch (before after : Reading) (raw : Json)
    (accepted : receive? before raw = some after) :
    ∃ header, NumberedSourceProofs.header? raw = some header ∧
      ((isDeclaration header = true ∧ NumberedSourceDeclarations.receive? before raw = some after) ∨
       (isDeclaration header = false ∧ NumberedSourceProofs.receive? before raw = some after)) := by
  cases headerAt : NumberedSourceProofs.header? raw with
  | none => simp [receive?,headerAt] at accepted
  | some header =>
      cases selected : isDeclaration header with
      | false => exact ⟨header,rfl,.inr ⟨selected,by simpa [receive?,headerAt,selected] using accepted⟩⟩
      | true => exact ⟨header,rfl,.inl ⟨selected,by simpa [receive?,headerAt,selected] using accepted⟩⟩

theorem receive_checked (before after : Reading) (raw : Json)
    (accepted : receive? before raw = some after) :
    ∃ (header : NumberedSourceProofs.Header) (event : Event) (sources : List SourceTerm),
      NumberedSourceProofs.header? raw = some header ∧
      ExportReplay.apply SourceProfileModels.policy before.registered event = some after.registered ∧
      Registered.apply SourceProfileModels.policy before.registered.registered event.command =
        some after.registered.registered ∧
      after.input = before.input ∧
      after.sourceConclusions = ExportCodec.addConclusions before.sourceConclusions event.sourceIds sources ∧
      List.Forall₂ (fun source claim => source.check = some claim.concl) sources event.claims ∧
      after.registered.receipts = before.registered.receipts.push event := by
  obtain ⟨header,headerAt,declared | proof⟩ := receive_dispatch before after raw accepted
  · obtain ⟨prepared,_,applied,registered,inputSame,_,sourcesEq,_⟩ :=
      NumberedSourceDeclarations.receive_checked before after raw declared.2
    exact ⟨header,prepared.event,prepared.sources,headerAt,applied,registered,inputSame,
      sourcesEq,prepared.claimChecks,(ExportReplay.apply_checked SourceProfileModels.policy applied).2.2.2.1⟩
  · obtain ⟨prepared,preparedAt,applied,sourcesEq⟩ :=
      NumberedSourceProofMetadata.receive_data before after raw proof.2
    obtain ⟨_,_,_,_,_,inputSame,_⟩ := NumberedSourceProofs.receive_checked before after raw proof.2
    have checked := ExportReplay.apply_checked SourceProfileModels.policy applied
    exact ⟨header,prepared.event,[prepared.source],headerAt,applied,checked.1,inputSame,
      sourcesEq,NumberedSourceProofMetadata.prepare_source_checks before raw prepared preparedAt,
      checked.2.2.2.1⟩

theorem receive_preserves_conclusions (before after : Reading) (raw : Json)
    (coherent : NumberedSourceMetadata.ConclusionsChecked before.registered before.sourceConclusions)
    (accepted : receive? before raw = some after) :
    NumberedSourceMetadata.ConclusionsChecked after.registered after.sourceConclusions := by
  obtain ⟨_,event,sources,_,applied,_,_,sourcesEq,checks,_⟩ := receive_checked before after raw accepted
  rw [sourcesEq]
  exact NumberedSourceMetadata.apply_preserves_conclusions SourceProfileModels.policy
    before.registered after.registered event before.sourceConclusions sources coherent checks applied

def replay? : Reading → List Json → Option Reading
  | before, [] => some before
  | before, raw :: rest => do
      let after ← receive? before raw
      replay? after rest

theorem replay_event_graph (before after : Reading) (raws : List Json)
    (accepted : replay? before raws = some after) :
    ∃ events : List Event, events.length = raws.length ∧
      ExportReplay.replayFrom SourceProfileModels.policy before.registered events = some after.registered ∧
      after.input = before.input := by
  induction raws generalizing before with
  | nil =>
      simp only [replay?,Option.some.injEq] at accepted
      subst after
      exact ⟨[],rfl,rfl,rfl⟩
  | cons raw rest ih =>
      cases first : receive? before raw with
      | none => simp [replay?,first] at accepted
      | some middle =>
          have remaining : replay? middle rest = some after := by simpa [replay?,first] using accepted
          obtain ⟨events,length,continued,inputLast⟩ := ih middle remaining
          obtain ⟨_,event,_,_,stepped,_,inputFirst,_,_,_⟩ := receive_checked before middle raw first
          refine ⟨event :: events,by simpa only [List.length_cons] using congrArg Nat.succ length,
            ?_,inputLast.trans inputFirst⟩
          simp [ExportReplay.replayFrom,stepped,continued]

theorem replay_registered_reachable (before after : Reading) (raws : List Json)
    (accepted : replay? before raws = some after) :
    (Registered.gslt SourceProfileModels.policy).MultiStep before.registered.registered after.registered.registered := by
  obtain ⟨events,_,replayed,_⟩ := replay_event_graph before after raws accepted
  exact ExportReplay.replayFrom_reachable SourceProfileModels.policy before.registered events after.registered replayed

theorem replay_preserves_conclusions (before after : Reading) (raws : List Json)
    (coherent : NumberedSourceMetadata.ConclusionsChecked before.registered before.sourceConclusions)
    (accepted : replay? before raws = some after) :
    NumberedSourceMetadata.ConclusionsChecked after.registered after.sourceConclusions := by
  induction raws generalizing before with
  | nil =>
      simp only [replay?,Option.some.injEq] at accepted
      subst after
      exact coherent
  | cons raw rest ih =>
      cases first : receive? before raw with
      | none => simp [replay?,first] at accepted
      | some middle =>
          exact ih middle (receive_preserves_conclusions before middle raw coherent first)
            (by simpa [replay?,first] using accepted)

def receiveAt? (before : Reading) (index : Nat) : Option Reading := do
  let raw ← before.input.events[index]?
  receive? before raw

theorem receiveAt_checked (before after : Reading) (index : Nat)
    (accepted : receiveAt? before index = some after) :
    ∃ raw, before.input.events[index]? = some raw ∧ receive? before raw = some after := by
  cases found : before.input.events[index]? with
  | none => simp [receiveAt?,found] at accepted
  | some raw => exact ⟨raw,rfl,by simpa [receiveAt?,found] using accepted⟩

def replayInput? : Reading → Nat → Nat → Option Reading
  | before, _, 0 => some before
  | before, index, count+1 => do
      let after ← receiveAt? before index
      replayInput? after (index+1) count

theorem replayInput_event_graph (before after : Reading) (index count : Nat)
    (accepted : replayInput? before index count = some after) :
    ∃ events : List Event, events.length = count ∧
      ExportReplay.replayFrom SourceProfileModels.policy before.registered events = some after.registered ∧
      after.input = before.input := by
  induction count generalizing before index with
  | zero =>
      simp only [replayInput?,Option.some.injEq] at accepted
      subst after
      exact ⟨[],rfl,rfl,rfl⟩
  | succ count ih =>
      cases first : receiveAt? before index with
      | none => simp [replayInput?,first] at accepted
      | some middle =>
          have remaining : replayInput? middle (index+1) count = some after := by simpa [replayInput?,first] using accepted
          obtain ⟨events,length,continued,inputLast⟩ := ih middle (index+1) remaining
          obtain ⟨raw,_,received⟩ := receiveAt_checked before middle index first
          obtain ⟨_,event,_,_,stepped,_,inputFirst,_,_,_⟩ := receive_checked before middle raw received
          refine ⟨event :: events,by simpa only [List.length_cons] using congrArg Nat.succ length,
            ?_,inputLast.trans inputFirst⟩
          simp [ExportReplay.replayFrom,stepped,continued]

theorem replayInput_registered_reachable (before after : Reading) (index count : Nat)
    (accepted : replayInput? before index count = some after) :
    (Registered.gslt SourceProfileModels.policy).MultiStep before.registered.registered after.registered.registered := by
  obtain ⟨events,_,replayed,_⟩ := replayInput_event_graph before after index count accepted
  exact ExportReplay.replayFrom_reachable SourceProfileModels.policy before.registered events after.registered replayed

theorem replayInput_preserves_conclusions (before after : Reading) (index count : Nat)
    (coherent : NumberedSourceMetadata.ConclusionsChecked before.registered before.sourceConclusions)
    (accepted : replayInput? before index count = some after) :
    NumberedSourceMetadata.ConclusionsChecked after.registered after.sourceConclusions := by
  induction count generalizing before index with
  | zero =>
      simp only [replayInput?,Option.some.injEq] at accepted
      subst after
      exact coherent
  | succ count ih =>
      cases first : receiveAt? before index with
      | none => simp [replayInput?,first] at accepted
      | some middle =>
          obtain ⟨raw,_,received⟩ := receiveAt_checked before middle index first
          exact ih middle (index+1) (receive_preserves_conclusions before middle raw coherent received)
            (by simpa [replayInput?,first] using accepted)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceReception
