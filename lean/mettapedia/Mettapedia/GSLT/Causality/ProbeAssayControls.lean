import Mettapedia.GSLT.Causality.ProbeAssayExecution

/-!
# Controls for actual probe delivery, verdicts and separate costs
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.AssayProbeDelivery.Controls

open ResourceInteraction OccurrenceHistory
open ComplementaryAssay (Verdict purse)

def test (value : Nat) : Bool := value == 7
def deliveryCost (_ : Nat) : Nat := 3
def inspectionCost (_ : Nat) : Nat := 4

theorem funded_confirmation :
    observed test deliveryCost inspectionCost 0 (11 : Nat) (22 : Nat) (some 7) 7 =
      { (0, Verdict.confirm, 22, 7) } := by
  rw [observed_some]
  rfl

theorem funded_refutation :
    observed test deliveryCost inspectionCost 0 (11 : Nat) (22 : Nat) (some 8) 7 =
      { (0, Verdict.refute, 22, 8) } := by
  rw [observed_some]
  rfl

theorem absent_offer_quiet :
    observed test deliveryCost inspectionCost 0 (11 : Nat) (22 : Nat) none 100 = 0 :=
  observed_none _ _ _ _ _ _ _

theorem unaffordable_delivery_retains_offer :
    (execute test deliveryCost inspectionCost 0 (11 : Nat) (22 : Nat) (some 7) 2).1 =
      paidOffered 0 11 22 7 2 := rfl

theorem unaffordable_delivery_quiet :
    observed test deliveryCost inspectionCost 0 (11 : Nat) (22 : Nat) (some 7) 2 = 0 := by
  rw [observed_some]
  rfl

theorem delivered_but_unaffordable_inspection :
    (execute test deliveryCost inspectionCost 0 (11 : Nat) (22 : Nat) (some 7) 6).1 =
      paidReceived 0 11 22 7 3 ∧
    observed test deliveryCost inspectionCost 0 (11 : Nat) (22 : Nat) (some 7) 6 = 0 := by
  exact ⟨rfl, by rw [observed_some]; rfl⟩

theorem delivered_receipt_survives_exhaustion :
    rightPart (leftPart
      (execute test deliveryCost inspectionCost 0 (11 : Nat) (22 : Nat) (some 7) 6).1) =
      {ProbeResource.delivered 0 11 22 7} := by
  change rightPart (leftPart (paidReceived 0 11 22 7 3)) = _
  rw [paidReceived, leftPart_marking, received, rightPart_marking]

theorem underfunded_delivered_prefix_is_maximal :
    Maximal test deliveryCost inspectionCost (paidReceived 0 (11 : Nat) (22 : Nat) 7 3) := by
  intro site firing enabled
  have step : (paid test deliveryCost inspectionCost).theory.rewrites
      (paidReceived 0 (11 : Nat) (22 : Nat) 7 3)
      ((paid test deliveryCost inspectionCost).fire (paidReceived 0 11 22 7 3) firing) :=
    ⟨site, firing, enabled, rfl⟩
  have affordable := (paid_received_step_iff test deliveryCost inspectionCost
    0 (11 : Nat) (22 : Nat) 7 3 _).1 step
  exact (by decide : ¬ inspectionCost 7 ≤ 3) affordable.1

theorem affordable_delivery_prefix_not_maximal :
    ¬ Maximal test deliveryCost inspectionCost (paidReceived 0 (11 : Nat) (22 : Nat) 7 4) := by
  intro maximal
  exact maximal (site := .inl ⟨⟨Verdict.confirm⟩⟩)
    ⟨ComplementaryAssay.selected test 0 22 7⟩
      ((inspection_enabled_iff test deliveryCost inspectionCost 0 (11 : Nat) (22 : Nat) 7 4).2 (by decide))

theorem actual_complete_history :
    (paid (Providers := Nat) (Clients := Nat) test deliveryCost inspectionCost).pathEntries
      (completeRun test deliveryCost inspectionCost 0 (11 : Nat) (22 : Nat) 7 9
        (by decide) (by decide)) =
      [⟨.inr ⟨()⟩, deliver 0 11 22 7⟩,
        ⟨.inl ⟨⟨Verdict.confirm⟩⟩, ⟨ComplementaryAssay.selected test 0 22 7⟩⟩] :=
  completeRun_entries _ _ _ _ _ _ _ _ _ _

theorem whole_ledger :
    purse 9 = purse 2 + (purse 3 + purse 4) := by decide

theorem actual_complete_ledger :
    purse 9 = rightPart (paidTested test 0 (11 : Nat) (22 : Nat) 7 2) +
      ((paid test deliveryCost inspectionCost).instanceValuation
        (@price Nat Nat Nat test deliveryCost inspectionCost)).onPath
          (completeRun test deliveryCost inspectionCost 0 (11 : Nat) (22 : Nat) 7 9
            (by decide) (by decide)) :=
  prefix_ledger _ _ _ _ _ _ _ _ _

theorem same_public_verdict_different_providers :
    observed test deliveryCost inspectionCost 0 (11 : Nat) (22 : Nat) (some 7) 7 =
      observed test deliveryCost inspectionCost 0 (12 : Nat) (22 : Nat) (some 7) 7 ∧
    (execute test deliveryCost inspectionCost 0 (11 : Nat) (22 : Nat) (some 7) 7).1 ≠
      (execute test deliveryCost inspectionCost 0 (12 : Nat) (22 : Nat) (some 7) 7).1 := by
  constructor
  · rw [observed_some, observed_some]
  · intro same
    have receipts := congrArg (fun resources => rightPart (leftPart resources)) same
    change rightPart (leftPart (paidTested test 0 (11 : Nat) (22 : Nat) 7 0)) =
      rightPart (leftPart (paidTested test 0 (12 : Nat) (22 : Nat) 7 0)) at receipts
    simp only [paidTested, leftPart_marking, tested, rightPart_marking,
      Multiset.singleton_inj, ProbeResource.delivered.injEq] at receipts
    omega

def mismatched : Multiset (Resources Nat Nat Nat) :=
  marking (ComplementaryAssay.pending 0 22)
    {ProbeResource.request 0 22, ProbeResource.offer 1 11 7}

theorem wrong_session_cannot_deliver {site : (system (Providers := Nat) (Clients := Nat) test).Site}
    (firing : (system (Providers := Nat) (Clients := Nat) test).Instance site) :
    ¬ (system test).Enables mismatched firing := by
  cases site with
  | inl site => exact assay_pending_disabled test 0 22 _ firing
  | inr site =>
    intro enabled
    have request := Multiset.mem_of_le enabled
      (show Sum.inr (ProbeResource.request firing.session firing.client) ∈
        deliverySystem.consume (site := site) firing + deliverySystem.read (site := site) firing
        by simp [deliverySystem])
    have offer := Multiset.mem_of_le enabled
      (show Sum.inr (ProbeResource.offer firing.session firing.provider firing.value) ∈
        deliverySystem.consume (site := site) firing + deliverySystem.read (site := site) firing
        by simp [deliverySystem])
    simp [mismatched, marking, Multiset.disjSum, ComplementaryAssay.pending] at request offer
    omega

end Mettapedia.GSLT.Causality.AssayProbeDelivery.Controls
