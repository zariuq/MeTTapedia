import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Valuation
import Mathlib.Tactic

/-!
# Executable causal-receipt examples

These small receipts pin both positive behavior and malformed emissions.  All
validity decisions use kernel reduction (`decide`), never a native evaluator.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Examples

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

abbrev TestGround := String
abbrev TestSurface := String

def aliceSig : CostSig TestGround := {"alice"}
def bobSig : CostSig TestGround := {"bob"}

theorem aliceSig_valid : aliceSig.RuntimeValid := by
  simp [aliceSig, CostSig.RuntimeValid]

theorem bobSig_valid : bobSig.RuntimeValid := by
  simp [bobSig, CostSig.RuntimeValid]

def aliceEvent : SpendEvent TestGround TestSurface :=
  SpendEvent.singleton "shop-a" aliceSig aliceSig_valid

def bobEvent : SpendEvent TestGround TestSurface :=
  SpendEvent.singleton "lab-b" bobSig bobSig_valid

/-! ## Valid causal and independent emissions -/

def chainEmission : ReceiptEmission Nat TestGround TestSurface :=
  [⟨0, [], aliceEvent⟩, ⟨1, [0], bobEvent⟩]

theorem chainEmission_valid : chainEmission.Valid := by
  simp [ReceiptEmission.Valid, chainEmission]

def chainReceipt : CausalReceipt (Fin chainEmission.length) TestGround TestSurface :=
  chainEmission.toReceipt chainEmission_valid

theorem chain_direct_cause :
    chainReceipt.DirectCause ⟨0, by decide⟩ ⟨1, by decide⟩ := by
  norm_num [chainReceipt, chainEmission, ReceiptEmission.toReceipt,
    CausalReceipt.DirectCause]

theorem chain_causal_order :
    chainReceipt.CausalLE ⟨0, by decide⟩ ⟨1, by decide⟩ :=
  Relation.ReflTransGen.single chain_direct_cause

theorem chain_not_reversed :
    ¬chainReceipt.CausalLE ⟨1, by decide⟩ ⟨0, by decide⟩ := by
  intro path
  rcases chainReceipt.causalLE_eq_or_rank_lt path with heq | hlt
  · have hvals := congrArg Fin.val heq
    norm_num [chainEmission] at hvals
  · change 1 < 0 at hlt
    omega

def independentEmission : ReceiptEmission Nat TestGround TestSurface :=
  [⟨0, [], aliceEvent⟩, ⟨1, [], bobEvent⟩]

theorem independentEmission_valid : independentEmission.Valid := by
  simp [ReceiptEmission.Valid, independentEmission]

def independentReceipt :
    CausalReceipt (Fin independentEmission.length) TestGround TestSurface :=
  independentEmission.toReceipt independentEmission_valid

theorem independent_events :
    independentReceipt.Independent ⟨0, by decide⟩ ⟨1, by decide⟩ := by
  constructor
  · intro path
    have noEdge : ∀ next, ¬independentReceipt.DirectCause ⟨0, by decide⟩ next := by
      intro next
      fin_cases next <;>
        norm_num [independentReceipt, independentEmission, ReceiptEmission.toReceipt,
          CausalReceipt.DirectCause]
    have heq := (Relation.reflTransGen_iff_eq noEdge).mp path
    have hvals := congrArg Fin.val heq
    norm_num [independentEmission] at hvals
  · intro path
    have noEdge : ∀ next, ¬independentReceipt.DirectCause ⟨1, by decide⟩ next := by
      intro next
      fin_cases next <;>
        norm_num [independentReceipt, independentEmission, ReceiptEmission.toReceipt,
          CausalReceipt.DirectCause]
    have heq := (Relation.reflTransGen_iff_eq noEdge).mp path
    have hvals := congrArg Fin.val heq
    norm_num [independentEmission] at hvals

/-! ## Opaque event identities -/

inductive TestEventId where
  | source
  | sink
  deriving DecidableEq

def opaqueIdEmission : ReceiptEmission TestEventId TestGround TestSurface :=
  [⟨.source, [], aliceEvent⟩, ⟨.sink, [.source], bobEvent⟩]

theorem opaqueIdEmission_valid : opaqueIdEmission.Valid := by
  simp [ReceiptEmission.Valid, opaqueIdEmission]

/-! ## Repeated occurrences and repeated consumption arcs -/

def repeatedEmission : ReceiptEmission Nat TestGround TestSurface :=
  [⟨0, [], aliceEvent⟩, ⟨1, [], aliceEvent⟩]

theorem repeatedEmission_valid : repeatedEmission.Valid := by
  simp [ReceiptEmission.Valid, repeatedEmission]

def repeatedReceipt :
    CausalReceipt (Fin repeatedEmission.length) TestGround TestSurface :=
  repeatedEmission.toReceipt repeatedEmission_valid

theorem identical_labels_are_distinct_occurrences :
    repeatedReceipt.label ⟨0, by decide⟩ = repeatedReceipt.label ⟨1, by decide⟩ ∧
      (⟨0, by decide⟩ : Fin repeatedEmission.length) ≠ ⟨1, by decide⟩ := by
  constructor
  · rfl
  · decide

theorem repeated_spends_are_measured_twice :
    repeatedReceipt.totalRawMeasure.card = 2 := by
  decide

def repeatedArcEmission : ReceiptEmission Nat TestGround TestSurface :=
  [⟨0, [], aliceEvent⟩, ⟨1, [0, 0], bobEvent⟩]

theorem repeatedArcEmission_valid : repeatedArcEmission.Valid := by
  simp [ReceiptEmission.Valid, repeatedArcEmission]

theorem repeated_consumption_arcs_are_not_deduplicated :
    (repeatedArcEmission.toReceipt repeatedArcEmission_valid).arcMultiplicity
      ⟨0, by decide⟩ ⟨1, by decide⟩ = 2 := by
  decide

/-! ## Multiple opaque funding surfaces -/

def aliceAtShop : FundingContribution TestGround TestSurface :=
  ⟨"shop-a", aliceSig, aliceSig_valid⟩

def bobAtLab : FundingContribution TestGround TestSurface :=
  ⟨"lab-b", bobSig, bobSig_valid⟩

def multiSurfaceEvent : SpendEvent TestGround TestSurface where
  funding := aliceAtShop ::ₘ bobAtLab ::ₘ 0
  funding_nonempty := by simp

theorem multi_surface_restrictions_preserve_contributions :
    multiSurfaceEvent.rawSpendAt "shop-a" = aliceSig ∧
      multiSurfaceEvent.rawSpendAt "lab-b" = bobSig := by
  decide

theorem signatures_are_not_locations :
    multiSurfaceEvent.rawSpendAt "alice" = 0 := by
  decide

/-! ## Rejected malformed emissions -/

def danglingCauseEmission : ReceiptEmission Nat TestGround TestSurface :=
  [⟨0, [99], aliceEvent⟩]

theorem danglingCauseEmission_invalid : ¬danglingCauseEmission.Valid := by
  simp [ReceiptEmission.Valid, danglingCauseEmission]

def selfCauseEmission : ReceiptEmission Nat TestGround TestSurface :=
  [⟨0, [0], aliceEvent⟩]

theorem selfCauseEmission_invalid : ¬selfCauseEmission.Valid := by
  simp [ReceiptEmission.Valid, selfCauseEmission]

def forwardCauseEmission : ReceiptEmission Nat TestGround TestSurface :=
  [⟨0, [1], aliceEvent⟩, ⟨1, [], bobEvent⟩]

theorem forwardCauseEmission_invalid : ¬forwardCauseEmission.Valid := by
  simp [ReceiptEmission.Valid, forwardCauseEmission]

def duplicateIdEmission : ReceiptEmission Nat TestGround TestSurface :=
  [⟨0, [], aliceEvent⟩, ⟨0, [], bobEvent⟩]

theorem duplicateIdEmission_invalid : ¬duplicateIdEmission.Valid := by
  simp [ReceiptEmission.Valid, duplicateIdEmission]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Examples
