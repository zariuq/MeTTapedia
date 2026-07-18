import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.AuthorityObservation

/-!
# Authority-observation examples

The exact receipt records occurrence identity before any pricing fold.  Two
receipts can therefore have the same aggregate price while remaining distinct
authority evidence.  Consequently no total reconstruction can recover exact
receipts from aggregate prices.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
namespace AuthorityObservationExamples

/-- A nonempty signature used by the closed examples. -/
def exampleSpend : CostSig String := {"alice"}

theorem exampleSpend_valid : exampleSpend.RuntimeValid := by
  simp [exampleSpend, CostSig.RuntimeValid]

/-- One located funding contribution. -/
def exampleLabel : SpendEvent String String :=
  SpendEvent.singleton "pay" exampleSpend exampleSpend_valid

/-- A one-event exact receipt whose occurrence identity is still visible. -/
def oneEventReceipt (id : Nat) : ReceiptEmission Nat String String :=
  [{ id := id, causes := [], label := exampleLabel }]

@[simp]
theorem oneEventReceipt_aggregate (id : Nat) :
    (oneEventReceipt id).aggregate = exampleSpend := by
  simp [oneEventReceipt, ReceiptEmission.aggregate, exampleLabel,
    SpendEvent.singleton, SpendEvent.rawSpend]

/-- Changing an occurrence identity changes authority evidence. -/
theorem zero_receipt_ne_one_receipt :
    oneEventReceipt 0 ≠ oneEventReceipt 1 := by
  intro equality
  have ids := congrArg (List.map EmittedEvent.id) equality
  simp [oneEventReceipt] at ids

/-- Aggregate pricing forgets occurrence identity and is therefore not
injective on exact authority receipts. -/
theorem aggregate_not_injective :
    ¬Function.Injective
      (ReceiptEmission.aggregate :
        ReceiptEmission Nat String String → CostSig String) := by
  intro injective
  apply zero_receipt_ne_one_receipt
  apply injective
  simp

/-- No total function can reconstruct every exact authority receipt from its
aggregate price. -/
theorem no_total_reconstruction_from_aggregate :
    ¬∃ reconstruct : CostSig String → ReceiptEmission Nat String String,
      ∀ receipt, reconstruct receipt.aggregate = receipt := by
  rintro ⟨reconstruct, leftInverse⟩
  apply aggregate_not_injective
  intro first second aggregateEquality
  calc
    first = reconstruct first.aggregate := (leftInverse first).symm
    _ = reconstruct second.aggregate := congrArg reconstruct aggregateEquality
    _ = second := leftInverse second

end AuthorityObservationExamples
end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
