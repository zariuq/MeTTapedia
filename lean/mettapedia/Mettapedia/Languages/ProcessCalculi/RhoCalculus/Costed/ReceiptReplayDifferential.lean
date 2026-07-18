import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.BudgetedDifferential
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.ReceiptReplay

/-!
# Versioned wire boundary for external receipt replay

The source term and an externally emitted causal-prefix record are decoded
independently.  The status field is retained by the surrounding differential
gate; this checker certifies the stronger shared core: the complete receipt and
residual are realized by an actual Lean `CostPath`.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
namespace CostWire

def receiptReplaySchema : String :=
  "cetta.cost-rho.receipt-replay.v1"

structure ReceiptReplayRequest where
  schema : String
  term : CostWire
  result : CostWire
  deriving Repr, Lean.ToJson, Lean.FromJson

inductive ReceiptReplayOutcome where
  | schemaMismatch
  | malformedSource
  | malformedResult
  | rejected
  | accepted
  deriving Repr, DecidableEq, Lean.ToJson, Lean.FromJson

/-- Decode only the evidence-bearing portion of a causal-prefix record.  The
status symbol is intentionally not used to establish path realizability. -/
def decodeReceiptClaim : CostWire → Option (RawReceipt × RawCostTerm)
  | .node "causal-prefix" [_status, receipt, residual] =>
      Prod.mk <$> decodeReceipt receipt <*> decodeTerm residual
  | _ => none

def evaluateReceiptReplay
    (request : ReceiptReplayRequest) : ReceiptReplayOutcome :=
  if request.schema != receiptReplaySchema then .schemaMismatch
  else
    match decodeTerm request.term with
    | none => .malformedSource
    | some term =>
        match decodeReceiptClaim request.result with
        | none => .malformedResult
        | some (receipt, residual) =>
            if validateReceipt term receipt residual then .accepted
            else .rejected

/-- Acceptance at the versioned wire boundary exposes the decoded evidence and
a genuine declarative path realizing every emitted occurrence and the claimed
residual. -/
theorem evaluateReceiptReplay_accepted_sound
    {request : ReceiptReplayRequest}
    (accepted : evaluateReceiptReplay request = .accepted) :
    ∃ term receipt residual finalComponents,
      decodeTerm request.term = some term ∧
      decodeReceiptClaim request.result = some (receipt, residual) ∧
      ∃ path : CostPath 0 (initialTraceComponents term)
          receipt.length finalComponents,
        path.rawEmission = receipt ∧
        tracedResidual finalComponents = residual := by
  by_cases schemaOk : request.schema = receiptReplaySchema
  · cases decodedTerm : decodeTerm request.term with
    | none =>
        simp [evaluateReceiptReplay, schemaOk, decodedTerm] at accepted
    | some term =>
        cases decodedClaim : decodeReceiptClaim request.result with
        | none =>
            simp [evaluateReceiptReplay, schemaOk, decodedTerm,
              decodedClaim] at accepted
        | some claim =>
            by_cases replayed :
                validateReceipt term claim.1 claim.2 = true
            · obtain ⟨finalComponents, path, emissionEq, residualEq⟩ :=
                validateReceipt_sound replayed
              exact ⟨term, claim.1, claim.2, finalComponents,
                rfl, rfl, path, emissionEq, residualEq⟩
            · simp [evaluateReceiptReplay, schemaOk, decodedTerm,
                decodedClaim, replayed] at accepted
  · simp [evaluateReceiptReplay, schemaOk] at accepted

end CostWire
end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
