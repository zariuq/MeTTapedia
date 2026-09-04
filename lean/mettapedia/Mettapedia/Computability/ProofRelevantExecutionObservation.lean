import Mettapedia.Computability.ReflectiveExecutionValuation
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Observer factorization for proof-relevant execution events

An authentic execution event may carry more information than its endpoints
and operational cost.  This module states the exact observer boundary on the
two-receipt reflective execution model.

The endpoint-and-WorkSpan image is made surjective by restricting its target
to the actual range.  An observation descends to that image exactly when it
is constant on its fibres.  Endpoint and WorkSpan observations pass this
test.  Receipt provenance does not: two distinct receipts have equal
endpoints and equal WorkSpan.  Refining the readout with the receipt restores
injectivity.

Thus equal denotation and equal cost do not license proof erasure.  Erasure
is relative to a declared observer, while provenance remains available to a
finer observer.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.ProofRelevantExecutionObservation

open Mettapedia.Algebra
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.Computability.ReflectiveExecutionValuation
open Mettapedia.Computability.ReflectiveExecutionValuation.Canary

/-! ## A surjective endpoint-and-cost readout -/

abbrev ReceiptEvent := ExecutionEvent ReceiptStep

/-- The actual image of endpoint-and-WorkSpan observation.  Restricting to
the image avoids pretending that every arbitrary cost pair is realized. -/
def EndpointCostImage := Set.range endpointWorkSpanReadout

/-- Every authentic receipt event has a point in the realized image. -/
def endpointCostImageReadout (event : ReceiptEvent) : EndpointCostImage :=
  ⟨endpointWorkSpanReadout event, event, rfl⟩

theorem endpointCostImageReadout_surjective :
    Function.Surjective endpointCostImageReadout := by
  intro image
  rcases image.2 with ⟨event, sameImage⟩
  refine ⟨event, ?_⟩
  apply Subtype.ext
  exact sameImage

/-- An observation of authentic events descends to endpoint-and-cost data
exactly when equal endpoint-and-cost fibres give equal observations. -/
theorem factors_through_endpointCost_iff_constantOnFibers
    {Observation : Type*} (observe : ReceiptEvent → Observation) :
    Factors endpointCostImageReadout observe ↔
      ConstantOnFibers endpointCostImageReadout observe :=
  factors_iff_constantOnFibers endpointCostImageReadout_surjective observe

/-! ## Coarse observations which lawfully descend -/

/-- Endpoint denotation, independent of the proof receipt. -/
def endpointObservation (event : ReceiptEvent) : Bool × Bool :=
  event.endpoints

/-- Operational WorkSpan for one event, independent of receipt provenance in
this model. -/
def workSpanObservation (event : ReceiptEvent) : WorkSpan :=
  (endpointWorkSpanReadout event).2

theorem endpoints_factor_through_endpointCost :
    Factors endpointCostImageReadout endpointObservation := by
  refine ⟨fun image => image.1.1, ?_⟩
  intro event
  rfl

theorem workSpan_factors_through_endpointCost :
    Factors endpointCostImageReadout workSpanObservation := by
  refine ⟨fun image => image.1.2, ?_⟩
  intro event
  rfl

/-! ## Provenance which cannot descend -/

/-- The exact proof-relevant receipt carried by an event. -/
def receiptObservation (event : ReceiptEvent) : Bool :=
  event.witness

/-- The two canonical events lie in one endpoint-and-cost fibre while their
receipts differ. -/
def receiptNontrivialFiber :
    NonTrivialFiber endpointCostImageReadout receiptObservation where
  left := falseReceiptEvent
  right := trueReceiptEvent
  sameShadow := by
    apply Subtype.ext
    rfl
  differentValue := Bool.false_ne_true

theorem receipt_does_not_factor_through_endpointCost :
    ¬ Factors endpointCostImageReadout receiptObservation :=
  receiptNontrivialFiber.not_factors

/-- Adding WorkSpan to the receipt observation does not make the receipt
recoverable from endpoint-and-cost data. -/
def workSpanAndReceiptObservation (event : ReceiptEvent) : WorkSpan × Bool :=
  (workSpanObservation event, receiptObservation event)

def workSpanAndReceiptNontrivialFiber :
    NonTrivialFiber endpointCostImageReadout
      workSpanAndReceiptObservation where
  left := falseReceiptEvent
  right := trueReceiptEvent
  sameShadow := by
    apply Subtype.ext
    rfl
  differentValue := by decide

theorem workSpanAndReceipt_does_not_factor_through_endpointCost :
    ¬ Factors endpointCostImageReadout workSpanAndReceiptObservation :=
  workSpanAndReceiptNontrivialFiber.not_factors

/-! ## Refinement restores faithfulness -/

/-- A finer readout keeps endpoints, WorkSpan, and the exact receipt. -/
def proofRelevantReadout (event : ReceiptEvent) :
    ((Bool × Bool) × WorkSpan) × Bool :=
  (endpointWorkSpanReadout event, event.witness)

/-- The refined readout is faithful for this event family.  Cost remains one
coordinate; it is not identified with the witness or with truth. -/
theorem proofRelevantReadout_injective :
    Function.Injective proofRelevantReadout := by
  rintro ⟨leftSource, leftTarget, leftReceipt⟩
    ⟨rightSource, rightTarget, rightReceipt⟩ sameReadout
  simp only [proofRelevantReadout, endpointWorkSpanReadout,
    ExecutionEvent.endpoints] at sameReadout
  have sameEndpoints :
      (leftSource, leftTarget) = (rightSource, rightTarget) :=
    congrArg (fun value => value.1.1) sameReadout
  have sameReceipt : leftReceipt = rightReceipt :=
    congrArg Prod.snd sameReadout
  cases sameEndpoints
  cases sameReceipt
  rfl

/-- Paired control: endpoint and WorkSpan observations may be erased to the
coarse image, receipt provenance may not, and retaining the receipt gives a
faithful readout. -/
theorem observer_relative_erasure_boundary :
    Factors endpointCostImageReadout endpointObservation ∧
      Factors endpointCostImageReadout workSpanObservation ∧
      ¬ Factors endpointCostImageReadout receiptObservation ∧
      Function.Injective proofRelevantReadout :=
  ⟨endpoints_factor_through_endpointCost,
    workSpan_factors_through_endpointCost,
    receipt_does_not_factor_through_endpointCost,
    proofRelevantReadout_injective⟩

#print axioms factors_through_endpointCost_iff_constantOnFibers
#print axioms receipt_does_not_factor_through_endpointCost
#print axioms workSpanAndReceipt_does_not_factor_through_endpointCost
#print axioms proofRelevantReadout_injective
#print axioms observer_relative_erasure_boundary

end Mettapedia.Computability.ProofRelevantExecutionObservation
