import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckedReplay

/-!
# A typed-terminal certificate checks the guard service's logical meaning

The dishonest compiled guard below returns no service. Its logical definition
is the ordinary source guard. The replay must reject the resulting proposed
suspension, even though its reached state and readout are genuine.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTerminalReplayControls

open Lean Elab Command
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open PettaOccurrenceOverlay

def number : Atom := .grounded (.int 7)

def initial : State Unit :=
  let branchControl : DControl := ⟨[], [], number, ∅, 0⟩
  let frame : CallFrame := ⟨"guarded", ⟨[.sym "Number"], .sym "Number"⟩,
    [], [], 0, [], [], number, 0, number, 1, .argument (.sym "Number") number⟩
  (Allocator.empty 0 1, ⟨{state := Effects.empty},
    [⟨[(branchControl, ⟨(), [frame]⟩, [])], [], none⟩]⟩)

def falseGuardProposal (_world : EagerDFS.World) (_index : Nat) (_store : Store)
    (_expected : Ty String) (_value : Atom) : Option (List Store) := none

@[implemented_by falseGuardProposal]
def logicalGuard (world : EagerDFS.World) (index : Nat) (store : Store)
    (expected : Ty String) (value : Atom) : Option (List Store) :=
  PettaSourceTypeServices.orderedGuard [] world index store expected value

def challenged : Services Unit := { PettaSourceTypeServices.services [] with
  orderedGuard := logicalGuard
  guard_exact := by
    intro world index store expected value answers served
    exact PettaSourceTypeServices.orderedGuard_exact [] world index store expected value answers served }

def program : SpaceSemantics.Program := {equations := [], declarations := []}

def bodyInitial (bad : Bool) : State Unit :=
  let value := if bad then Atom.grounded (.string "wrong") else number
  let branchControl : DControl := ⟨[], [], value, ∅, 0⟩
  let frame : CallFrame := ⟨"guarded", ⟨[.sym "Number"], .sym "Number"⟩,
    [], [number], 1, [], [], value, 0, value, 1, .body⟩
  (Allocator.empty 0 1, ⟨{state := Effects.empty},
    [⟨[(branchControl, ⟨(), [frame]⟩, [])], [], none⟩]⟩)

/-- error: Replay certificates must be closed and contain no admitted proof -/
#guard_msgs (error, drop warning, drop info, substring := true) in
kernel_petta_run rejectedGuard using (machine challenged .eagerValue program) for 1 from initial

/-- error: Replay certificates must be closed and contain no admitted proof -/
#guard_msgs (error, drop warning, drop info, substring := true) in
kernel_petta_run rejectedBodyGuard using (machine challenged .eagerValue program)
  for 1 from (bodyInitial false)

run_cmd do
  let namespaceName ← getCurrNamespace
  for suffix in [`rejectedGuard.run, `rejectedBodyGuard.run] do
    if (← getEnv).contains (namespaceName ++ suffix) then
      throwError "A false guard proposal installed a run theorem"

kernel_petta_run actualGuard using
  (machine (PettaSourceTypeServices.services []) .eagerValue program) for 1 from initial

kernel_petta_run actualBody using (machine (PettaSourceTypeServices.services []) .eagerValue program)
  for 1 from (bodyInitial false)

kernel_petta_run refusedBody using (machine (PettaSourceTypeServices.services []) .eagerValue program)
  for 1 from (bodyInitial true)

def unavailable : Services Unit := {PettaSourceTypeServices.services [] with
  orderedGuard := fun _ _ _ _ _ => none
  guard_exact := by intro _ _ _ _ _ _ impossible; cases impossible}

kernel_petta_run unavailableBody using (machine unavailable .eagerValue program)
  for 1 from (bodyInitial false)

theorem a_missing_body_guard_is_suspension_not_failure :
    ((machine unavailable .eagerValue program).run 1 (bodyInitial false)).2 =
      .suspended (.guard "guarded" 1 (.sym "Number") number) (bodyInitial false) := by
  rw [unavailableBody.run]
  rfl

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTerminalReplayControls
