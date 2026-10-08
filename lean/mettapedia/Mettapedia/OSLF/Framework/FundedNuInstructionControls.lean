import Mettapedia.OSLF.Framework.FundedNuInstructionAssays
import Mettapedia.OSLF.Framework.FundedNuAssayControls
import Mettapedia.Logic.HMLStackControls

/-!
# Received-state instruction assay controls

Repeated successor occurrences preserve all modal predicates but change the
independently emitted instructions and actual funded progress. The aggregate
and instruction controllers agree on public packets while their unfinished
spending differs. A decisive received-state refutation and a finite persistent
loop confirmation exercise both certificate directions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.FundedNuInstructionControls

open Mettapedia.Logic.ModalMuCalculus Inspection Unfolding StackInspection
open Mettapedia.GSLT.Causality ProbeCampaign ComplementaryAssay
open FundedNuAssays FundedNuAssayControls FundedNuInstructionAssays

def instructionChain := inspectReceived chain (fun _ _ => 1) request 3 true rfl (by decide)

def instructionRepeated := inspectReceived repeatedChain (fun _ _ => 1) request 3 true rfl (by decide)

theorem compiled_occurrences_differ :
    compile chain (continuation.atStage 1) (continuation.stage_admitted 1) true =
        [.literal true, .gatherAny 1] ∧
      compile repeatedChain (continuation.atStage 1) (continuation.stage_admitted 1) true =
        [.literal true, .literal true, .gatherAny 2] := by
  decide

theorem funded_chain_packet :
    instructionChain.responses = {(12, Verdict.confirm, 7, true)} ∧
      instructionChain.remaining = 0 ∧ instructionChain.spent = 3 := by
  have packet : instructionChain.responses = {(12, Verdict.confirm, 7, true)} := by decide
  have rest : instructionChain.remaining = 0 := by decide
  have ledger := instructionChain.ledger chain (fun _ _ => 1)
  exact ⟨packet, rest, by omega⟩

theorem funded_repetition_has_unreported_paid_work :
    instructionRepeated.responses = 0 ∧ instructionRepeated.remaining = 0 ∧
      instructionRepeated.spent = 3 ∧
      instructionRepeated.inspection.endpoint.pending = [.gatherAny 2] ∧
      instructionRepeated.inspection.endpoint.stack = [true, true] := by
  have packet : instructionRepeated.responses = 0 := by decide
  have rest : instructionRepeated.remaining = 0 := by decide
  have ledger := instructionRepeated.ledger repeatedChain (fun _ _ => 1)
  exact ⟨packet, rest, by omega, by decide, by decide⟩

theorem same_public_observation_different_partial_spending :
    instructionRepeated.responses = repeatedRound.responses ∧
      instructionRepeated.spent ≠ repeatedRound.spent := by
  have quiet := repeated_price_prevents_response
  have instructions := funded_repetition_has_unreported_paid_work
  exact ⟨instructions.1.trans quiet.1.symm, by rw [instructions.2.2.1, quiet.2.2]; decide⟩

theorem equal_semantics_different_actual_funding :
    (∀ {n : Nat} (environment : Env Bool n) (formula : Formula Unit n) (state : Bool),
      satisfies chain.toLTS environment formula state ↔
        satisfies repeatedChain.toLTS environment formula state) ∧
      instructionChain.responses ≠ instructionRepeated.responses := by
  refine ⟨fun environment formula state => repeated_semantics environment formula state, ?_⟩
  rw [funded_chain_packet.1, funded_repetition_has_unreported_paid_work.1]
  simp only [ne_eq, Multiset.singleton_ne_zero, not_false_eq_true]

def decisiveInstructions :=
  inspectReceived chain (fun _ _ => 1) decisiveRequest 3 true rfl (by decide)

theorem decisive_instruction_packet :
    decisiveInstructions.responses = {(12, Verdict.refute, 7, true)} ∧
      decisiveInstructions.inspection.path.sites = [.gatherAny 0, .gatherAny 1] := by
  decide

theorem actual_decisive_receipt_refutes_original :
    ¬ satisfies chain.toLTS Env.empty (.nu continuation.body) true :=
  decisiveInstructions.received_refutation chain (fun _ _ => 1) (by decide)

def loopRequest : Request (Question Unit) Unit Unit Nat where
  question := (continuation, 1)
  session := 31
  provider := ()
  client := 7
  arrival := some ()

def loopInstructions := inspectReceived loop (fun _ _ => 1) loopRequest 3 () rfl (by decide)

theorem loop_instruction_packet :
    loopInstructions.responses = {(31, Verdict.confirm, 7, ())} ∧
      loopInstructions.spent = 3 := by
  have packet : loopInstructions.responses = {(31, Verdict.confirm, 7, ())} := by decide
  have reported : Funded.publicAnswer loopInstructions.inspection.endpoint = some true := by decide
  have account := loopInstructions.reporting_spent loop (fun _ _ => 1) true reported
  exact ⟨packet, account⟩

theorem actual_finite_receipt_confirms_original :
    satisfies loop.toLTS Env.empty (.nu continuation.body) () :=
  loopInstructions.received_finite_confirmation loop (fun _ _ => 1)
    (by simp [loopRequest, Nat.card_eq_fintype_card]) (by decide)

theorem paid_shallow_receipt_is_not_limit_confirmation :
    instructionChain.responses = {(12, Verdict.confirm, 7, true)} ∧
      ¬ satisfies chain.toLTS Env.empty (.nu continuation.body) true :=
  ⟨funded_chain_packet.1, chain_original_refuted true⟩

end Mettapedia.OSLF.Framework.FundedNuInstructionControls
