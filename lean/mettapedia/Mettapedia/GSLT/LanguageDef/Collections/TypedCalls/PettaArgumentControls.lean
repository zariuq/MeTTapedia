import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentMachine
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckpointFixtures
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeEquationScalarReduction

/-!
# Actual raw and evaluated argument stages, with malformed-plan controls

The first operand is held at Atom and is not run. The second is evaluated and
guarded at Number. Their frame is obtained from named source entry. Missing
service at argument index one cannot append its pending slot or enter the body.
The direct row-operation mutation below isolates why its arity guard matters.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaCheckpointFixtures (num text call)
open PettaArgumentProgress

def row : Row := ⟨[.sym "Atom", .sym "Number"], .sym "Number"⟩
def held : Atom := call "println!" [text "must-not-run"]

def program : SpaceSemantics.Program where
  equations := [⟨"two", [.var "raw", .var "value"], .var "value"⟩]
  declarations := [PettaSourceTypeRows.declaration "two" row.asType]
  layout := [.equation, .declaration]

def services : Services Unit := PettaSourceTypeServices.services []

def control : DControl :=
  ⟨[], [.evaluate (call "two" [held, num 4]) (.var "result")], .var "result", ∅, 0⟩

def initial : State Unit :=
  (Allocator.empty 8 64,
    ⟨{state := Effects.loaded program}, [⟨[(control, ⟨(), []⟩, [])], [], none⟩]⟩)

def frameAt (operations : Services Unit) (fuel : Nat) : Option CallFrame := do
  let reached ← PettaCallerReturnMachine.exitState
    ((PettaOccurrenceOverlay.machine operations .eagerValue program).run fuel initial).2
  let current ← reached.2.scopes.head?
  let (_, context, _) ← current.frontier.head?
  context.calls.head?

def view (frame : CallFrame) : Nat × Nat × Nat × Nat × Nat :=
  (frame.ready.length, frame.index, frame.remaining.length, pending frame.phase, frame.row.parameters.length)

theorem source_head_returns_its_second_parameter :
    Bridges.ScopedReturnFunction.checksHead program "two" 1 8 = true := by decide

theorem raw_operand_is_kept_as_written :
    (frameAt services 2).bind (fun frame => frame.ready[0]?) = some held := by cbv

theorem raw_stage_counts_the_held_operand :
    (frameAt services 2).map view = some (1, 1, 1, 0, 2) := by cbv

theorem producing_stage_keeps_one_pending_position :
    (frameAt services 3).map view = some (1, 1, 0, 1, 2) := by cbv

theorem body_entry_has_both_ready_operands :
    (frameAt services 7).map view = some (2, 2, 0, 0, 2) := by cbv

theorem body_entry_uses_the_result_guard_index :
    (frameAt services 7).map (fun frame => frame.phase == .body) = some true := by cbv

theorem the_raw_computation_has_not_run_at_body_entry :
    (PettaCallerReturnMachine.exitState
      ((PettaOccurrenceOverlay.machine services .eagerValue program).run 7 initial).2).map
        (fun reached => reached.2.world.output) = some [] := by cbv

theorem missing_second_guard_does_not_advance :
    (frameAt PettaCheckpointFixtures.missingResult 7).map view = some (1, 1, 0, 1, 2) := by cbv

theorem missing_second_guard_does_not_supply_the_second_slot :
    (frameAt PettaCheckpointFixtures.missingResult 7).bind (fun frame => frame.ready[1]?) = none := by cbv

def malformedRowService : Services Unit := {services with rows := fun _ _ _ _ => .typed [row]}

theorem the_actual_arity_guard_retains_the_input :
    enterRows malformedRowService initial ⟨[(control, ⟨(), []⟩, [])], [], none⟩ []
      control ⟨(), []⟩ [] [] "two" [num 4] (.var "result") [] =
      .call (.arity "two" [num 4] [row]) initial := by cbv

theorem unchecked_zip_truncation_breaks_alignment :
    ∀ frame, (rowWork control (⟨(), []⟩ : Context Unit) [] 1 "two" [num 4] (.var "result") [] row 0).2.1.calls.head? =
      some frame → ¬ Aligned frame := by
  intro frame selected bad
  cases Option.some.inj selected
  have balance := bad.balance
  norm_num [row, pending] at balance

theorem wrong_formal_can_fail_even_with_matching_counts :
    ¬ Aligned (⟨"two", row, [], [held], 1, [], [], .var "result", 0,
      .var "result", 1, .argument (.sym "String") (.var "slot")⟩ : CallFrame) := by
  intro bad
  have wrong := bad.argument_formal (.sym "String") (.var "slot") rfl
  simp [row] at wrong

theorem an_index_increment_without_a_ready_operand_is_invalid :
    ¬ Aligned (⟨"two", row, [], [held], 2, [], [], .var "result", 0,
      .var "result", 1, .nextArgument⟩ : CallFrame) := by
  intro bad
  have wrong := bad.ready_count
  norm_num at wrong

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentControls
