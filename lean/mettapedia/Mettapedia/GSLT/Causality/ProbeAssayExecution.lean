import Mettapedia.GSLT.Causality.FundedProbeCompletion

/-!
# Attempted probe handling and independently read assay outputs

The controller executes the offered response's delivery and then its guard
test when their respective prices fit the remaining purse. Its result is an
actual endpoint together with the occurrence path that reaches it. Observing
that endpoint gives a verdict precisely when both interactions complete.

An absent offer, unaffordable delivery and unaffordable testing are distinct
resource states. Their common empty verdict readout licenses none of the
positive or negative hypothesis certificates.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.AssayProbeDelivery

open ResourceInteraction OccurrenceHistory
open ComplementaryAssay (Verdict verdictOf purse)

universe u v w

variable {X : Type u} {Providers : Type v} {Clients : Type w}
variable [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]

def initial (session : Nat) (provider : Providers) (client : Clients) (arrival : Option X)
    (budget : Nat) : Multiset (Resources X Providers Clients ⊕ Unit) :=
  match arrival with
  | none => marking (waiting session client) (purse budget)
  | some value => paidOffered session provider client value budget

def execute (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (arrival : Option X) (budget : Nat) :
    Σ target, OccurrencePath (paid test deliveryCost inspectionCost).presentation
      (initial session provider client arrival budget) target :=
  match arrival with
  | none => ⟨_, .refl _⟩
  | some value => if deliveryAffordable : deliveryCost value ≤ budget then
      if inspectionAffordable : inspectionCost value ≤ budget - deliveryCost value then
        ⟨_, completeRun test deliveryCost inspectionCost session provider client value budget
          deliveryAffordable inspectionAffordable⟩
      else ⟨_, deliveryRun test deliveryCost inspectionCost session provider client value budget deliveryAffordable⟩
    else ⟨_, .refl _⟩

def observed (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (arrival : Option X) (budget : Nat) :
    Multiset (Nat × Verdict × Clients × X) :=
  outputs (leftPart (execute test deliveryCost inspectionCost session provider client arrival budget).1)

theorem observed_none (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (budget : Nat) :
    observed test deliveryCost inspectionCost session provider client none budget = 0 := by
  simp only [observed, execute, initial, leftPart_marking, outputs, waiting,
    leftPart_marking, ComplementaryAssay.outputs_pending]

theorem observed_some (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (value : X) (budget : Nat) :
    observed test deliveryCost inspectionCost session provider client (some value) budget =
      if deliveryCost value + inspectionCost value ≤ budget then
        { (session, verdictOf (test value), client, value) } else 0 := by
  by_cases deliveryAffordable : deliveryCost value ≤ budget
  · by_cases inspectionAffordable : inspectionCost value ≤ budget - deliveryCost value
    · have total : deliveryCost value + inspectionCost value ≤ budget := by omega
      simp only [observed, execute, dif_pos deliveryAffordable, dif_pos inspectionAffordable,
        paidTested, leftPart_marking, outputs_tested, if_pos total]
    · have total : ¬ deliveryCost value + inspectionCost value ≤ budget := by omega
      simp only [observed, execute, dif_pos deliveryAffordable, dif_neg inspectionAffordable,
        paidReceived, leftPart_marking, outputs_received, if_neg total]
  · have total : ¬ deliveryCost value + inspectionCost value ≤ budget := by omega
    simp only [observed, execute, dif_neg deliveryAffordable, initial, paidOffered,
      leftPart_marking, outputs_offered, if_neg total]

theorem observed_iff_affordable (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (value : X) (budget : Nat) :
    observed test deliveryCost inspectionCost session provider client (some value) budget ≠ 0 ↔
      deliveryCost value + inspectionCost value ≤ budget := by
  rw [observed_some]
  split_ifs <;> simp_all

theorem delivery_underfunded_prefix (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (value : X) (budget : Nat)
    (underfunded : budget < deliveryCost value)
    {target : Multiset (Resources X Providers Clients ⊕ Unit)}
    (path : OccurrencePath (paid test deliveryCost inspectionCost).presentation
      (paidOffered session provider client value budget) target) :
    target = paidOffered session provider client value budget ∧
      outputs (leftPart target) = 0 ∧ (paid test deliveryCost inspectionCost).pathEntries path = [] := by
  rcases offered_path_cases test deliveryCost inspectionCost session provider client value budget path with
    ⟨endpoint, noEntries⟩ | ⟨_, _, affordable⟩ | ⟨_, _, affordable⟩
  · exact ⟨endpoint, by rw [endpoint, paidOffered, leftPart_marking, outputs_offered], noEntries⟩
  · omega
  · omega

theorem inspection_underfunded_prefix (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (value : X) (budget : Nat)
    (underfunded : budget < inspectionCost value)
    {target : Multiset (Resources X Providers Clients ⊕ Unit)}
    (path : OccurrencePath (paid test deliveryCost inspectionCost).presentation
      (paidReceived session provider client value budget) target) :
    target = paidReceived session provider client value budget ∧
      outputs (leftPart target) = 0 ∧ (paid test deliveryCost inspectionCost).pathEntries path = [] := by
  rcases received_path_cases test deliveryCost inspectionCost session provider client value budget path with
    ⟨endpoint, noEntries⟩ | ⟨_, _, affordable⟩
  · exact ⟨endpoint, by rw [endpoint, paidReceived, leftPart_marking, outputs_received], noEntries⟩
  · omega

theorem absent_offer_prefix (test : X → Bool) (deliveryCost inspectionCost : X → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (budget : Nat)
    {target : Multiset (Resources X Providers Clients ⊕ Unit)}
    (path : OccurrencePath (paid test deliveryCost inspectionCost).presentation
      (initial session provider client none budget) target) :
    target = initial session provider client none budget ∧
      outputs (leftPart target) = 0 ∧ (paid test deliveryCost inspectionCost).pathEntries path = [] := by
  have stuck : ∀ {site : (paid (Providers := Providers) test deliveryCost inspectionCost).Site}
      (firing : (paid test deliveryCost inspectionCost).Instance site),
      ¬ (paid test deliveryCost inspectionCost).Enables (initial session provider client none budget) firing := by
    intro site firing enabled
    exact waiting_stuck test session client firing
      ((funded_enables_iff (system test) (@price X Providers Clients test deliveryCost inspectionCost)
        (waiting session client) (purse budget) firing).1 enabled).1
  obtain ⟨endpoint, noEntries⟩ := ComplementaryAssay.path_of_stuck
    (paid test deliveryCost inspectionCost) path stuck
  exact ⟨endpoint, by
    rw [endpoint, initial, leftPart_marking, outputs, waiting,
      leftPart_marking, ComplementaryAssay.outputs_pending], noEntries⟩

end Mettapedia.GSLT.Causality.AssayProbeDelivery
