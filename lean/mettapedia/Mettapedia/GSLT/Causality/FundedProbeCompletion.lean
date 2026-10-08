import Mettapedia.GSLT.Causality.FundedProbeAssay

/-!
# Complete probe/assay prefixes and their two-entry ledger

Every finite execution from the single offered response has zero, one or two
interactions: no delivery yet, delivery without testing, or delivery followed
by its complementary verdict. With both prices affordable, a maximal prefix
must complete both. The generic funded occurrence ledger holds for every
prefix, while the complete run records the exact ordered delivery/test pair.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.AssayProbeDelivery

open ResourceInteraction OccurrenceHistory
open ComplementaryAssay (Verdict verdictOf purse)

universe u v w

variable {X : Type u} {Providers : Type v} {Clients : Type w}
variable [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]

def Maximal (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (target : Multiset (Resources X Providers Clients ⊕ Unit)) : Prop :=
  ∀ {site : (paid (Providers := Providers) test deliveryCost inspectionCost).Site}
    (firing : (paid test deliveryCost inspectionCost).Instance site),
      ¬ (paid test deliveryCost inspectionCost).Enables target firing

theorem received_path_cases (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (value : X) (budget : Nat)
    : ∀ {target : Multiset (Resources X Providers Clients ⊕ Unit)}
      (path : OccurrencePath (paid test deliveryCost inspectionCost).presentation
        (paidReceived session provider client value budget) target),
    (target = paidReceived session provider client value budget ∧
      (paid test deliveryCost inspectionCost).pathEntries path = []) ∨
    (target = paidTested test session provider client value (budget - inspectionCost value) ∧
      ((paid test deliveryCost inspectionCost).pathEntries path).length = 1 ∧
        inspectionCost value ≤ budget)
  | _, .refl _ => .inl ⟨rfl, rfl⟩
  | _, @OccurrencePath.cons _ _ _ middle _ occurrence rest => by
    have step : (paid test deliveryCost inspectionCost).theory.rewrites
        (paidReceived session provider client value budget) middle :=
      ⟨occurrence.site, occurrence.evidence.val,
        occurrence.evidence.property.1, occurrence.evidence.property.2⟩
    obtain ⟨affordable, firstEndpoint⟩ :=
      (paid_received_step_iff test deliveryCost inspectionCost session provider client value budget middle).1 step
    have stuck : ∀ {site : (paid (Providers := Providers) test deliveryCost inspectionCost).Site}
        (firing : (paid test deliveryCost inspectionCost).Instance site),
        ¬ (paid test deliveryCost inspectionCost).Enables middle firing := by
      intro site firing
      rw [firstEndpoint]
      exact paid_tested_stuck test deliveryCost inspectionCost session provider client value
        (budget - inspectionCost value) firing
    obtain ⟨sameEndpoint, emptyTail⟩ := ComplementaryAssay.path_of_stuck
      (paid test deliveryCost inspectionCost) rest stuck
    refine .inr ⟨sameEndpoint.trans firstEndpoint, ?_, affordable⟩
    change (⟨occurrence.site, occurrence.evidence.val⟩ ::
      (paid test deliveryCost inspectionCost).pathEntries rest).length = 1
    rw [emptyTail]
    rfl

theorem offered_path_cases (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (value : X) (budget : Nat)
    : ∀ {target : Multiset (Resources X Providers Clients ⊕ Unit)}
      (path : OccurrencePath (paid test deliveryCost inspectionCost).presentation
        (paidOffered session provider client value budget) target),
    (target = paidOffered session provider client value budget ∧
      (paid test deliveryCost inspectionCost).pathEntries path = []) ∨
    (target = paidReceived session provider client value (budget - deliveryCost value) ∧
      ((paid test deliveryCost inspectionCost).pathEntries path).length = 1 ∧
        deliveryCost value ≤ budget) ∨
    (target = paidTested test session provider client value
        ((budget - deliveryCost value) - inspectionCost value) ∧
      ((paid test deliveryCost inspectionCost).pathEntries path).length = 2 ∧
        deliveryCost value + inspectionCost value ≤ budget)
  | _, .refl _ => .inl ⟨rfl, rfl⟩
  | _, @OccurrencePath.cons _ _ _ middle _ occurrence rest => by
    have step : (paid test deliveryCost inspectionCost).theory.rewrites
        (paidOffered session provider client value budget) middle :=
      ⟨occurrence.site, occurrence.evidence.val,
        occurrence.evidence.property.1, occurrence.evidence.property.2⟩
    obtain ⟨deliveryAffordable, firstEndpoint⟩ :=
      (paid_offered_step_iff test deliveryCost inspectionCost session provider client value budget middle).1 step
    subst middle
    rcases received_path_cases test deliveryCost inspectionCost session provider client value
      (budget - deliveryCost value) rest with ⟨sameEndpoint, emptyTail⟩ | ⟨sameEndpoint, oneTail, affordable⟩
    · refine .inr (.inl ⟨sameEndpoint, ?_, deliveryAffordable⟩)
      change (⟨occurrence.site, occurrence.evidence.val⟩ ::
        (paid test deliveryCost inspectionCost).pathEntries rest).length = 1
      rw [emptyTail]
      rfl
    · refine .inr (.inr ⟨sameEndpoint, ?_, by omega⟩)
      change (⟨occurrence.site, occurrence.evidence.val⟩ ::
        (paid test deliveryCost inspectionCost).pathEntries rest).length = 2
      simp only [List.length_cons, oneTail]

theorem maximal_affordable_verdict (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (value : X) (budget : Nat)
    (affordable : deliveryCost value + inspectionCost value ≤ budget)
    {target : Multiset (Resources X Providers Clients ⊕ Unit)}
    (path : OccurrencePath (paid test deliveryCost inspectionCost).presentation
      (paidOffered session provider client value budget) target)
    (maximal : Maximal test deliveryCost inspectionCost target) :
    outputs (leftPart target) = { (session, verdictOf (test value), client, value) } ∧
      ((paid test deliveryCost inspectionCost).pathEntries path).length = 2 ∧
      rightPart (leftPart target) = {ProbeResource.delivered session provider client value} ∧
      budget = (rightPart target).card + deliveryCost value + inspectionCost value := by
  rcases offered_path_cases test deliveryCost inspectionCost session provider client value budget path with
    ⟨sameEndpoint, _⟩ | ⟨sameEndpoint, _, _⟩ | ⟨sameEndpoint, entries, _⟩
  · have disabled := maximal (site := .inr ⟨()⟩) (deliver session provider client value)
    rw [sameEndpoint] at disabled
    exact False.elim (disabled
      ((delivery_enabled_iff test deliveryCost inspectionCost session provider client value budget).2 (by omega)))
  · have disabled := maximal (site := .inl ⟨⟨verdictOf (test value)⟩⟩)
      ⟨ComplementaryAssay.selected test session client value⟩
    rw [sameEndpoint] at disabled
    exact False.elim (disabled
      ((inspection_enabled_iff test deliveryCost inspectionCost session provider client value
        (budget - deliveryCost value)).2 (by omega)))
  · refine ⟨?_, entries, ?_, ?_⟩
    · rw [sameEndpoint, paidTested, leftPart_marking, outputs_tested]
    · rw [sameEndpoint, paidTested, leftPart_marking, tested, rightPart_marking]
    · rw [sameEndpoint, paidTested, rightPart_marking]
      simp only [purse, Multiset.card_replicate]
      omega

theorem prefix_ledger (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (value : X) (budget : Nat)
    {target : Multiset (Resources X Providers Clients ⊕ Unit)}
    (path : OccurrencePath (paid test deliveryCost inspectionCost).presentation
      (paidOffered session provider client value budget) target) :
    purse budget = rightPart target +
      ((paid test deliveryCost inspectionCost).instanceValuation
        (@price X Providers Clients test deliveryCost inspectionCost)).onPath path :=
  funded_run_conserved (system test) (@price X Providers Clients test deliveryCost inspectionCost) path

theorem completeRun_entries (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (value : X) (budget : Nat)
    (deliveryAffordable : deliveryCost value ≤ budget)
    (inspectionAffordable : inspectionCost value ≤ budget - deliveryCost value) :
    (paid test deliveryCost inspectionCost).pathEntries
      (completeRun test deliveryCost inspectionCost session provider client value budget
        deliveryAffordable inspectionAffordable) =
      [⟨.inr ⟨()⟩, deliver session provider client value⟩,
        ⟨.inl ⟨⟨verdictOf (test value)⟩⟩, ⟨ComplementaryAssay.selected test session client value⟩⟩] := rfl

theorem completeRun_spent (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (value : X) (budget : Nat)
    (deliveryAffordable : deliveryCost value ≤ budget)
    (inspectionAffordable : inspectionCost value ≤ budget - deliveryCost value) :
    ((paid test deliveryCost inspectionCost).instanceValuation
      (@price X Providers Clients test deliveryCost inspectionCost)).onPath
        (completeRun test deliveryCost inspectionCost session provider client value budget
          deliveryAffordable inspectionAffordable) =
      purse (deliveryCost value) + purse (inspectionCost value) := by
  change purse (deliveryCost value) + (0 + (purse (inspectionCost value) + 0)) = _
  simp only [zero_add, add_zero]

end Mettapedia.GSLT.Causality.AssayProbeDelivery
