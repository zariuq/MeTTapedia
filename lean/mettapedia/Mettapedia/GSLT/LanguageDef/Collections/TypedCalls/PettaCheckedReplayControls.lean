import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckedReplay
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRunFixtures

/-!
# Checked replay rejects false proposals and unsupported store changes

The deliberately incorrect compiled implementation below tests the trust
boundary: native execution may propose data, but cannot establish a step.
The logical function remains the unchanged, silent terminal operation.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckedReplayControls

open Lean Elab Command
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open PettaOccurrenceOverlay

def initial : State Unit :=
  (Allocator.empty 0 1, ⟨{state := Effects.empty}, []⟩)

def falseOutputProposal (source : State Unit) :
    Option (Transition (State Unit) EagerDFS.Destination.CollectedAnswer (State Unit) Request) :=
  some (.finish (source.1,
    {source.2 with world := {source.2.world with output := [.symbol "forged"]}}))

@[implemented_by falseOutputProposal]
def logicalFinish (source : State Unit) :
    Option (Transition (State Unit) EagerDFS.Destination.CollectedAnswer (State Unit) Request) :=
  some (.finish source)

def challenged : Machine (State Unit) EagerDFS.Destination.CollectedAnswer (State Unit) Request :=
  ⟨logicalFinish⟩

theorem the_logical_step_does_not_print :
    logicalFinish initial = some (.finish initial) := rfl

/-- error: Replay certificates must be closed and contain no admitted proof -/
#guard_msgs (error, drop warning, drop info, substring := true) in
kernel_petta_run rejectedOutput using challenged for 1 from initial

def changesStore : Machine (State Unit) EagerDFS.Destination.CollectedAnswer (State Unit) Request :=
  ⟨fun source => some (.finish (source.1,
    {source.2 with world := {source.2.world with state := Effects.loaded {
      equations := [⟨"new", [], .symbol "row"⟩], declarations := [], layout := [.equation] }}}))⟩

/-- error: Replay certificates must be closed and contain no admitted proof -/
#guard_msgs (error, drop warning, drop info, substring := true) in
kernel_petta_run rejectedStoreChange using changesStore for 1 from initial

run_cmd do
  let env ← getEnv
  let namespaceName ← getCurrNamespace
  for suffix in [`rejectedOutput.run, `rejectedStoreChange.run] do
    let name := namespaceName ++ suffix
    if env.contains name then throwError "A rejected replay installed a theorem: {name}"

kernel_petta_run actualPrefix using
  (PettaOccurrenceOverlay.machine PettaCallerReturnRunFixtures.services .eagerValue
    PettaCallerReturnRunFixtures.ordinary)
  for 3 from (PettaCallerReturnRunFixtures.initial PettaCallerReturnRunFixtures.services
    PettaCallerReturnRunFixtures.ordinary)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckedReplayControls
