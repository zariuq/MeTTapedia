import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnReplayPrefix
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSourceClassGuardReduction

/-!
# The actual caller-return prefix reaches and serves its first argument guard

The binding read and guard reply are checked separately before applying the
existing source terminal theorem. The retained world and older alternatives
are never evaluated again or reconstructed from the answer.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnGuardEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaCallerReturnRunFixtures (num ordinary services initial)

def source : State Unit := PettaCallerReturnReplayPrefix.nextFour.residual
def current : Scope Unit := source.2.scopes[0]'(by decide +kernel)
def selected : Work Unit := current.frontier[0]'(by decide +kernel)
def saved : CallFrame := selected.2.1.calls[0]'(by decide +kernel)

theorem argument_read :
    (resolve selected.1.bindings).map (fun environment => read environment selected.1.destination) =
      some (num 7) := by
  change (resolve [
    (.expression [.symbol "keep", num 4], .expression [.symbol "keep", .var "#######"]),
    (.symbol "&self", .var "############"),
    (.var "########", num 7), (.var "########", .var "##############")]).map
      (fun environment => read environment (.var "##############")) = some (num 7)
  cbv

def stores : List Store := [[(.sym "Number", .sym "Number")]]

theorem guard_reply :
    guardResult services source.2.world saved (.sym "Number") (num 7) true = some stores := by
  change PettaSourceTypeServices.orderedGuard [] ⟨Effects.loaded ordinary, [], []⟩
    0 [] (.sym "Number") (num 7) = some stores
  cbv

def after : State Unit := install source current []
  (argumentContinuations services source selected.1 selected.2.1 selected.2.2 saved []
    (.var "##############") stores) (current.frontier.drop 1)

theorem actual_guard_step :
    step services .eagerValue ordinary source = .silent after := by
  obtain ⟨environment, resolved, readback⟩ := Option.map_eq_some_iff.mp argument_read
  apply terminal_argument_step services .eagerValue ordinary source current [] selected.1 selected.2.1
    selected.2.2 (current.frontier.drop 1) saved [] (.sym "Number") (.var "##############")
    environment stores
  all_goals first | rfl | exact resolved | skip
  rw [readback]
  exact guard_reply

theorem ten_source_steps_reach_the_guarded_continuation :
    PettaCallerReturnReplayPrefix.runner.run 10 (initial services ordinary) =
      ([], .exhausted after) := by
  have tail : PettaCallerReturnReplayPrefix.runner.run 1 source = ([], .exhausted after) := by
    apply Machine.run_succ_silent
    exact congrArg some actual_guard_step
  exact Mettapedia.Machines.ReplaySlices.compose PettaCallerReturnReplayPrefix.runner 9 1
    (initial services ordinary) source [] [] (.exhausted after)
    PettaCallerReturnReplayPrefix.nine_steps_reach_the_guard tail

def unavailable : Services Unit := {services with
  orderedGuard := fun _ _ _ _ _ => none
  guard_exact := by intro _ _ _ _ _ _ impossible; cases impossible}

theorem unavailable_guard_retains_the_actual_reached_state :
    step unavailable .eagerValue ordinary source =
      .call (.guard "prefix" 0 (.sym "Number") (num 7)) source := by
  have actual := PettaTerminalReadout.argument unavailable .eagerValue ordinary source current []
    selected.1 selected.2.1 selected.2.2 (current.frontier.drop 1) saved [] (.sym "Number")
    (.var "##############") (num 7) rfl rfl rfl rfl rfl rfl argument_read
  rw [actual]
  rfl

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnGuardEntry
