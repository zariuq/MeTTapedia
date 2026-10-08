import Mettapedia.GSLT.Causality.AssayProbeDelivery

/-!
# Funding delivery and testing in one assay execution

The request/offer protocol and the complementary receiver system share a token
purse. Their independently supplied prices are charged at their actual rule
sites. Delivery can succeed while testing remains unaffordable; an offered
answer may also remain undelivered. Both distinctions are visible in retained
resources and histories, while the public verdict readout is empty.

Prices account for declared protocol work. They do not assert provider
authority, physical elapsed time or a compiled probe-context implementation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.AssayProbeDelivery

open ResourceInteraction OccurrenceHistory
open ComplementaryAssay (Verdict verdictOf purse)

universe u v w

variable {X : Type u} {Providers : Type v} {Clients : Type w}

def price (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    {site : (system (Providers := Providers) (Clients := Clients) test).Site} :
    (system test).Instance site → Multiset Unit :=
  match site with
  | .inl _ => fun firing => purse (inspectionCost firing.down.value)
  | .inr _ => fun firing => purse (deliveryCost firing.value)

def paid (test : X → Bool) (deliveryCost inspectionCost : X → Nat) :
    System.{max u v w, max u v w} (Resources X Providers Clients ⊕ Unit) :=
  funded (system test) (@price X Providers Clients test deliveryCost inspectionCost)

theorem purse_sub (before charged : Nat) : purse before - purse charged = purse (before - charged) := by
  ext token
  cases token
  simp [purse, Multiset.count_sub]

def paidOffered (session : Nat) (provider : Providers) (client : Clients) (value : X)
    (budget : Nat) : Multiset (Resources X Providers Clients ⊕ Unit) :=
  marking (offered session provider client value) (purse budget)

def paidReceived (session : Nat) (provider : Providers) (client : Clients) (value : X)
    (budget : Nat) : Multiset (Resources X Providers Clients ⊕ Unit) :=
  marking (received session provider client value) (purse budget)

def paidTested (test : X → Bool) (session : Nat) (provider : Providers) (client : Clients)
    (value : X) (budget : Nat) : Multiset (Resources X Providers Clients ⊕ Unit) :=
  marking (tested test session provider client value) (purse budget)

theorem delivery_enabled_iff (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (value : X) (budget : Nat) :
    (paid test deliveryCost inspectionCost).Enables
      (paidOffered session provider client value budget) (site := .inr ⟨()⟩)
      (deliver session provider client value) ↔ deliveryCost value ≤ budget := by
  exact (funded_enables_iff (system test) (@price X Providers Clients test deliveryCost inspectionCost)
    (offered session provider client value) (purse budget)
      (site := .inr ⟨()⟩) (deliver session provider client value)).trans
        ⟨fun enabled => (Multiset.replicate_le_replicate ()).1 enabled.2,
          fun affordable => ⟨deliver_enabled session provider client value,
            (Multiset.replicate_le_replicate ()).2 affordable⟩⟩

theorem inspection_enabled_iff (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (value : X) (budget : Nat) :
    (paid test deliveryCost inspectionCost).Enables
      (paidReceived session provider client value budget)
      (site := .inl ⟨⟨verdictOf (test value)⟩⟩)
      ⟨ComplementaryAssay.selected test session client value⟩ ↔ inspectionCost value ≤ budget := by
  exact (funded_enables_iff (system test) (@price X Providers Clients test deliveryCost inspectionCost)
    (received session provider client value) (purse budget)
      (site := .inl ⟨⟨verdictOf (test value)⟩⟩)
      ⟨ComplementaryAssay.selected test session client value⟩).trans
        ⟨fun enabled => (Multiset.replicate_le_replicate ()).1 enabled.2,
          fun affordable =>
            ⟨((ComplementaryAssay.system test).raise.{max u w, max u w, v}.map_inl_enables_frame _ _ _).2
              (ComplementaryAssay.selected_enabled test session client value),
                (Multiset.replicate_le_replicate ()).2 affordable⟩⟩

section Decidable

variable [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]

theorem delivery_fire_paid (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (value : X) (budget : Nat) :
    (paid test deliveryCost inspectionCost).fire
      (paidOffered session provider client value budget) (site := .inr ⟨()⟩)
      (deliver session provider client value) =
        paidReceived session provider client value (budget - deliveryCost value) := by
  exact (funded_fire (system test) (@price X Providers Clients test deliveryCost inspectionCost)
    (offered session provider client value) (purse budget)
      (site := .inr ⟨()⟩) (deliver session provider client value)).trans
        (congrArg₂ marking (deliver_fire session provider client value) (purse_sub _ _))

theorem inspection_fire_paid (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (value : X) (budget : Nat) :
    (paid test deliveryCost inspectionCost).fire
      (paidReceived session provider client value budget)
      (site := .inl ⟨⟨verdictOf (test value)⟩⟩)
      ⟨ComplementaryAssay.selected test session client value⟩ =
        paidTested test session provider client value (budget - inspectionCost value) := by
  exact (funded_fire (system test) (@price X Providers Clients test deliveryCost inspectionCost)
    (received session provider client value) (purse budget)
      (site := .inl ⟨⟨verdictOf (test value)⟩⟩)
      ⟨ComplementaryAssay.selected test session client value⟩).trans
        (congrArg₂ marking
          (assay_received_fire test session provider client value _
            (((ComplementaryAssay.system test).raise.{max u w, max u w, v}.map_inl_enables_frame _ _ _).2
              (ComplementaryAssay.selected_enabled test session client value))) (purse_sub _ _))

theorem paid_offered_step_iff (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (value : X) (budget : Nat)
    (target : Multiset (Resources X Providers Clients ⊕ Unit)) :
    (paid test deliveryCost inspectionCost).theory.rewrites
      (paidOffered session provider client value budget) target ↔
      deliveryCost value ≤ budget ∧
        target = paidReceived session provider client value (budget - deliveryCost value) := by
  constructor
  · rintro ⟨site, firing, enabled, rfl⟩
    have base := (funded_enables_iff (system test)
      (@price X Providers Clients test deliveryCost inspectionCost)
      (offered session provider client value) (purse budget) firing).1 enabled
    cases site with
    | inl site => exact False.elim (assay_pending_disabled test session client _ firing base.1)
    | inr site =>
      obtain ⟨_, _, _, sameValue⟩ := delivery_fields session provider client value
        (site := site) firing base.1
      refine ⟨?_, ?_⟩
      · simpa only [price, sameValue, purse, Multiset.replicate_le_replicate] using base.2
      · exact (funded_fire (system test) (@price X Providers Clients test deliveryCost inspectionCost)
          (offered session provider client value) (purse budget) (site := .inr site) firing).trans
            (congrArg₂ marking (delivery_fire session provider client value (site := site) firing base.1)
              (by simpa only [price, sameValue] using purse_sub budget (deliveryCost value)))
  · rintro ⟨affordable, endpoint⟩
    exact ⟨.inr ⟨()⟩, deliver session provider client value,
      (delivery_enabled_iff test deliveryCost inspectionCost session provider client value budget).2 affordable,
      endpoint.trans (delivery_fire_paid test deliveryCost inspectionCost session provider client value budget).symm⟩

theorem paid_received_step_iff (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (value : X) (budget : Nat)
    (target : Multiset (Resources X Providers Clients ⊕ Unit)) :
    (paid test deliveryCost inspectionCost).theory.rewrites
      (paidReceived session provider client value budget) target ↔
      inspectionCost value ≤ budget ∧
        target = paidTested test session provider client value (budget - inspectionCost value) := by
  constructor
  · rintro ⟨site, firing, enabled, rfl⟩
    have base := (funded_enables_iff (system test)
      (@price X Providers Clients test deliveryCost inspectionCost)
      (received session provider client value) (purse budget) firing).1 enabled
    cases site with
    | inl site =>
      have guardEnabled :=
        ((ComplementaryAssay.system test).raise.{max u w, max u w, v}.map_inl_enables_frame _ _ firing).1 base.1
      obtain ⟨_, _, sameValue, _⟩ := ComplementaryAssay.enabled_fields test firing.down guardEnabled
      refine ⟨?_, ?_⟩
      · simpa only [price, sameValue, purse, Multiset.replicate_le_replicate] using base.2
      · exact (funded_fire (system test) (@price X Providers Clients test deliveryCost inspectionCost)
          (received session provider client value) (purse budget) (site := .inl site) firing).trans
            (congrArg₂ marking (assay_received_fire test session provider client value firing base.1)
              (by simpa only [price, sameValue] using purse_sub budget (inspectionCost value)))
    | inr site => exact False.elim (no_offer_delivery _ _ (by intros; simp)
        (site := site) firing base.1)
  · rintro ⟨affordable, endpoint⟩
    exact ⟨.inl ⟨⟨verdictOf (test value)⟩⟩, ⟨ComplementaryAssay.selected test session client value⟩,
      (inspection_enabled_iff test deliveryCost inspectionCost session provider client value budget).2 affordable,
      endpoint.trans (inspection_fire_paid test deliveryCost inspectionCost session provider client value budget).symm⟩

omit [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients] in
theorem paid_tested_stuck (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (value : X) (budget : Nat)
    {site : (paid (Providers := Providers) test deliveryCost inspectionCost).Site}
    (firing : (paid test deliveryCost inspectionCost).Instance site) :
    ¬ (paid test deliveryCost inspectionCost).Enables
      (paidTested test session provider client value budget) firing := by
  intro enabled
  exact tested_stuck test session provider client value firing
    ((funded_enables_iff (system test) (@price X Providers Clients test deliveryCost inspectionCost)
      (tested test session provider client value) (purse budget) firing).1 enabled).1

def deliveryRun (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (value : X) (budget : Nat)
    (affordable : deliveryCost value ≤ budget) :
    OccurrencePath (paid test deliveryCost inspectionCost).presentation
      (paidOffered session provider client value budget)
      (paidReceived session provider client value (budget - deliveryCost value)) :=
  .cons ⟨.inr ⟨()⟩, ⟨deliver session provider client value,
    (delivery_enabled_iff test deliveryCost inspectionCost session provider client value budget).2 affordable,
    (delivery_fire_paid test deliveryCost inspectionCost session provider client value budget).symm⟩⟩ (.refl _)

def inspectionRun (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (value : X) (budget : Nat)
    (affordable : inspectionCost value ≤ budget) :
    OccurrencePath (paid test deliveryCost inspectionCost).presentation
      (paidReceived session provider client value budget)
      (paidTested test session provider client value (budget - inspectionCost value)) :=
  .cons ⟨.inl ⟨⟨verdictOf (test value)⟩⟩, ⟨⟨ComplementaryAssay.selected test session client value⟩,
    (inspection_enabled_iff test deliveryCost inspectionCost session provider client value budget).2 affordable,
    (inspection_fire_paid test deliveryCost inspectionCost session provider client value budget).symm⟩⟩ (.refl _)

def completeRun (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (value : X) (budget : Nat)
    (deliveryAffordable : deliveryCost value ≤ budget)
    (inspectionAffordable : inspectionCost value ≤ budget - deliveryCost value) :
    OccurrencePath (paid test deliveryCost inspectionCost).presentation
      (paidOffered session provider client value budget)
      (paidTested test session provider client value ((budget - deliveryCost value) - inspectionCost value)) :=
  OccurrencePath.append
    (deliveryRun test deliveryCost inspectionCost session provider client value budget deliveryAffordable)
    (inspectionRun test deliveryCost inspectionCost session provider client value
      (budget - deliveryCost value) inspectionAffordable)

end Decidable

end Mettapedia.GSLT.Causality.AssayProbeDelivery
