import Mettapedia.Machines.ContextualCBPV

/-!
# Scoped first acceptance preserves the returned packet

The source boundary installs a body continuation and a fresh choice floor.
The target is a scope followed by sequencing into packet-preserving commit.
Entry and accepted-return transitions are compared explicitly. Raised control
bypasses the commit; conditional obligations are retained without solving them.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScopedFirst

open NativeCallReturn
open ContextualCBPV

variable {Value Call Effect Fault Delay Suspension Context World Worker : Type}

local notation "Code" => ContextualCBPV.Code Value Call Effect Fault Delay Suspension
local notation "State" => ContextualCBPV.State Value Call Effect Fault Delay Suspension Context World Worker
local notation "Frames" => List (ContextualCBPV.Frame Value Call Effect Fault Delay Suspension Context)
local notation "Pending" => List (ContextualCBPV.Work Value Call Effect Fault Delay Suspension Context Worker)
local notation "Semantics" => ContextualCBPV.Semantics Value Call Effect Fault Delay Suspension Context World Worker

def lower (body : Code) : Code := .scope (.sequence body .commitPacket)

def elaborate (arity : Nat) : Option Nat := if arity = 1 then some 0 else none

def read (source : Option Nat) (fields : Array Code) : Option Code := do
  let coordinate ← source
  let body ← fields[coordinate + 1]?
  pure (lower body)

def reference : List Code → Option Code
  | [_, body] => some (lower body)
  | _ => none

theorem elaboration_readback (fields : List Code) :
    read (elaborate (fields.length - 1)) fields.toArray = reference fields := by
  cases fields with
  | nil => rfl
  | cons head rest =>
      cases rest with
      | nil => rfl
      | cons body tail =>
          cases tail with
          | nil => rfl
          | cons extra rest => simp [read, elaborate, reference]

theorem absent_body_refuses (fields : Array Code) : read none fields = none := rfl

def sourceEnter (state : State) (context : Context) (body : Code) : State :=
  {state with focus := ⟨.compute context body,
    .sequence context .commitPacket :: .scope state.alternatives.length :: state.focus.frames⟩}

def sourceAccepted (sem : Semantics) (state : State) (saved context : Context)
    (packet : Packet Value Fault Delay) (rest : Frames) (outside : Pending) : State :=
  {state with
    focus := ⟨.returned (sem.resume saved context) packet, rest⟩
    alternatives := outside}

def normal : Packet Value Fault Delay → Bool
  | .raised _ => false
  | _ => true

theorem entry_refines (sem : Semantics) (state : State) (context : Context) (body : Code) :
    (core sem state.world context).runSlice 2
      {state with focus := ⟨.compute context (lower body), state.focus.frames⟩} =
      (sourceEnter state context body, 2) := by
  simp [MachineCore.runSlice, core, step, ContextualCBPV.advance, lower, sourceEnter, debit, origin]

theorem accepted_return_refines (sem : Semantics) (state : State)
    (saved context : Context) (packet : Packet Value Fault Delay)
    (rest : Frames) (inside outside : Pending) (successful : normal packet = true) :
    (core sem state.world context).runSlice 3
      {state with
        focus := ⟨.returned context packet,
          .sequence saved .commitPacket :: .scope outside.length :: rest⟩
        alternatives := inside ++ outside} =
      (sourceAccepted sem state saved context packet rest outside, 3) := by
  cases packet with
  | value role value =>
      simp [MachineCore.runSlice, core, step, ContextualCBPV.advance, commitReturn, choiceFloor,
        retainOutside_suffix, sourceAccepted, debit, origin]
  | conditional value delayed =>
      simp [MachineCore.runSlice, core, step, ContextualCBPV.advance, commitReturn, choiceFloor,
        retainOutside_suffix, sourceAccepted, debit, origin]
  | raised fault => simp [normal] at successful

theorem raised_bypasses_commit (sem : Semantics) (state : State)
    (saved context : Context) (fault : Fault) (rest : Frames) (inside outside : Pending) :
    (core sem state.world context).runSlice 2
      {state with
        focus := ⟨.returned context (.raised fault),
          .sequence saved .commitPacket :: .scope outside.length :: rest⟩
        alternatives := inside ++ outside} =
      ({state with
        focus := ⟨.returned (sem.resume saved context) (.raised fault), rest⟩
        alternatives := inside ++ outside}, 2) := by
  simp [MachineCore.runSlice, core, step, ContextualCBPV.advance, debit, origin]

theorem charged_entry_refines (sem : Semantics) (state : State)
    (context : Context) (body : Code) (occurrence cost : Nat) :
    (core sem state.world context).runSlice 3
      {state with focus := ⟨.compute context (.source occurrence cost (lower body)), state.focus.frames⟩} =
      (sourceEnter {state with
        spent := state.spent + cost
        sourceTrace := state.sourceTrace ++ [occurrence]} context body, 3) := by
  simp [MachineCore.runSlice, core, step, ContextualCBPV.advance, lower, sourceEnter, debit, origin]

theorem conditional_publication (sem : Semantics) (state : State) (saved context : Context)
    (value : Value) (delayed : Delay) (outside : Pending) :
    publication (sourceAccepted sem state saved context (.conditional value delayed) [] outside).focus =
      some (sem.resume saved context, .conditional value delayed) := rfl

theorem value_provenance (sem : Semantics) (state : State) (saved context : Context)
    (role : ValueRole) (value : Value) (outside : Pending) :
    publication (sourceAccepted sem state saved context (.value role value) [] outside).focus =
      some (sem.resume saved context, .value role value) := rfl

theorem refusal_retains_publication (sem : Semantics) (state : State)
    (saved context : Context) (packet : Packet Value Fault Delay)
    (outside : Pending) (successful : normal packet = true) :
    consumerStep sem (fun _ => false)
      (sourceAccepted sem state saved context packet [] outside) = none := by
  cases packet with
  | value role value => rfl
  | conditional value delayed => rfl
  | raised fault => simp [normal] at successful

theorem conditional_is_not_value_only_commit (sem : Semantics) (state : State)
    (context : Context) (value : Value) (delayed : Delay) (frames : Frames) :
    ContextualCBPV.advance sem {state with focus := ⟨.compute context (.commitPacket (.conditional value delayed)), frames⟩} ≠
      ContextualCBPV.advance sem {state with focus := ⟨.compute context (.commit value), frames⟩} := by
  intro same
  have control := congrArg (fun result => result.map (fun s => s.focus.control)) same
  simp [ContextualCBPV.advance, commitReturn] at control

end Mettapedia.Machines.ScopedFirst

#print axioms Mettapedia.Machines.ScopedFirst.entry_refines
#print axioms Mettapedia.Machines.ScopedFirst.elaboration_readback
#print axioms Mettapedia.Machines.ScopedFirst.absent_body_refuses
#print axioms Mettapedia.Machines.ScopedFirst.accepted_return_refines
#print axioms Mettapedia.Machines.ScopedFirst.raised_bypasses_commit
#print axioms Mettapedia.Machines.ScopedFirst.charged_entry_refines
#print axioms Mettapedia.Machines.ScopedFirst.conditional_publication
#print axioms Mettapedia.Machines.ScopedFirst.value_provenance
#print axioms Mettapedia.Machines.ScopedFirst.refusal_retains_publication
#print axioms Mettapedia.Machines.ScopedFirst.conditional_is_not_value_only_commit
