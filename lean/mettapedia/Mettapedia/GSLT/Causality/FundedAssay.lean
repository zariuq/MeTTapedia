import Mettapedia.GSLT.Causality.ComplementaryAssay
import Mathlib.Data.Multiset.Replicate

/-!
# Paid guard firings and completed assay observations

The complementary receiver system is synchronized with the existing token
purse. A step is enabled exactly when its selected receiver is present and
its declared testing price is available. Actual firings emit the addressed
verdict and subtract that price, while occurrence histories retain origins.

The controller below either performs an authenticated funded firing or
retains the current state and an empty path. Its output is read independently
from the resulting resources. Missing messages and insufficient funds both
leave no verdict; neither is a refutation. Prices are supplied schedules,
without a claim that formula depth determines execution work.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ComplementaryAssay

open ResourceInteraction OccurrenceHistory

universe u v

variable {X : Type u} {Origins : Type v}

def price (test : X → Bool) (cost : X → Nat)
    {site : (system (Origins := Origins) test).Site}
    (firing : (system (Origins := Origins) test).Instance site) : Multiset Unit :=
  Multiset.replicate (cost firing.value) ()

def paid (test : X → Bool) (cost : X → Nat) :
    System.{max u v, max u v} (Resource X Origins ⊕ Unit) :=
  funded (system test) (@price X Origins test cost)

def purse (budget : Nat) : Multiset Unit := Multiset.replicate budget ()

theorem paid_selected_enabled_iff (test : X → Bool) (cost : X → Nat)
    (session : Nat) (origin : Origins) (value : X) (budget : Nat) :
    (paid test cost).Enables (marking (ready session origin value) (purse budget))
      (selected test session origin value) ↔ cost value ≤ budget := by
  exact (funded_enables_iff (system test) (@price X Origins test cost)
    (ready session origin value) (purse budget) (selected test session origin value)).trans
    ⟨fun enabled => (Multiset.replicate_le_replicate ()).1 enabled.2,
      fun affordable => ⟨selected_enabled test session origin value,
        (Multiset.replicate_le_replicate ()).2 affordable⟩⟩

section DecidableResources

variable [DecidableEq X] [DecidableEq Origins]

def completed (test : X → Bool) (cost : X → Nat)
    (session : Nat) (origin : Origins) (value : X) (budget : Nat) :
    Multiset (Resource X Origins ⊕ Unit) :=
  marking (finished test session origin value) (purse budget - purse (cost value))

theorem paid_selected_fire (test : X → Bool) (cost : X → Nat)
    (session : Nat) (origin : Origins) (value : X) (budget : Nat) :
    (paid test cost).fire (marking (ready session origin value) (purse budget))
      (selected test session origin value) = completed test cost session origin value budget := by
  exact (funded_fire (system test) (@price X Origins test cost)
    (ready session origin value) (purse budget) (selected test session origin value)).trans
    (congrArg (fun resources => marking resources (purse budget - purse (cost value)))
      (selected_fire test session origin value))

/-- This characterizes every actual step, including independently supplied instances. -/
theorem paid_ready_step_iff (test : X → Bool) (cost : X → Nat)
    (session : Nat) (origin : Origins) (value : X) (budget : Nat)
    (target : Multiset (Resource X Origins ⊕ Unit)) :
    (paid test cost).theory.rewrites (marking (ready session origin value) (purse budget)) target ↔
      cost value ≤ budget ∧ target = completed test cost session origin value budget := by
  constructor
  · rintro ⟨⟨branch⟩, firing, enabled, rfl⟩
    have baseEnabled := (funded_enables_iff (system test) (@price X Origins test cost)
      (ready session origin value) (purse budget) firing).mp enabled
    obtain ⟨_, _, sameValue, _⟩ := enabled_fields test firing baseEnabled.1
    constructor
    · simpa only [price, sameValue, purse, Multiset.replicate_le_replicate] using baseEnabled.2
    · calc
        (paid test cost).fire (marking (ready session origin value) (purse budget)) firing =
            marking ((system test).fire (ready session origin value) firing)
              (purse budget - price test cost firing) :=
          funded_fire (system test) (@price X Origins test cost)
            (ready session origin value) (purse budget) firing
        _ = marking (finished test session origin value) (purse budget - price test cost firing) :=
          congrArg (fun resources => marking resources (purse budget - price test cost firing))
            (enabled_fire test firing baseEnabled.1)
        _ = completed test cost session origin value budget :=
          congrArg (fun payload => marking (finished test session origin value)
            (purse budget - purse (cost payload))) sameValue
  · rintro ⟨affordable, rfl⟩
    exact ⟨⟨verdictOf (test value)⟩, selected test session origin value,
      (paid_selected_enabled_iff test cost session origin value budget).2 affordable,
      (paid_selected_fire test cost session origin value budget).symm⟩

omit [DecidableEq X] [DecidableEq Origins] in
theorem paid_pending_stuck (test : X → Bool) (cost : X → Nat)
    (session : Nat) (origin : Origins) (tokens : Multiset Unit)
    {site : (paid (Origins := Origins) test cost).Site}
    (firing : (paid (Origins := Origins) test cost).Instance site) :
    ¬ (paid test cost).Enables (marking (pending (X := X) session origin) tokens) firing := by
  intro enabled
  cases site with
  | up branch =>
    exact no_pending_enabled test session origin firing
      ((funded_enables_iff (system test) (@price X Origins test cost)
        (pending session origin) tokens firing).mp enabled).1

omit [DecidableEq X] [DecidableEq Origins] in
theorem paid_finished_stuck (test : X → Bool) (cost : X → Nat)
    (session : Nat) (origin : Origins) (value : X) (tokens : Multiset Unit)
    {site : (paid (Origins := Origins) test cost).Site}
    (firing : (paid (Origins := Origins) test cost).Instance site) :
    ¬ (paid test cost).Enables (marking (finished test session origin value) tokens) firing := by
  intro enabled
  cases site with
  | up branch =>
    exact no_finished_enabled test session origin value firing
      ((funded_enables_iff (system test) (@price X Origins test cost)
        (finished test session origin value) tokens firing).mp enabled).1

def paidRun (test : X → Bool) (cost : X → Nat)
    (session : Nat) (origin : Origins) (value : X) (budget : Nat)
    (affordable : cost value ≤ budget) :
    OccurrencePath (paid test cost).presentation (marking (ready session origin value) (purse budget))
      (completed test cost session origin value budget) :=
  .cons ⟨⟨verdictOf (test value)⟩,
    ⟨selected test session origin value,
      (paid_selected_enabled_iff test cost session origin value budget).2 affordable,
      (paid_selected_fire test cost session origin value budget).symm⟩⟩ (.refl _)

theorem paidRun_entries (test : X → Bool) (cost : X → Nat)
    (session : Nat) (origin : Origins) (value : X) (budget : Nat)
    (affordable : cost value ≤ budget) :
    (paid test cost).pathEntries (paidRun test cost session origin value budget affordable) =
      [⟨⟨verdictOf (test value)⟩, selected test session origin value⟩] := rfl

omit [DecidableEq X] [DecidableEq Origins] in
theorem paidRun_conserved (test : X → Bool) (cost : X → Nat)
    (session : Nat) (origin : Origins) (value : X) (budget : Nat)
    (affordable : cost value ≤ budget) :
    budget = (rightPart (completed test cost session origin value budget)).card + cost value := by
  have conserved := funded_tokens_conserved (system test) (@price X Origins test cost)
    (ready session origin value) (purse budget) (selected test session origin value)
    ((paid_selected_enabled_iff test cost session origin value budget).2 affordable)
  have counted := congrArg Multiset.card conserved
  simpa only [completed, rightPart_marking, purse, price, selected,
    Multiset.card_add, Multiset.card_replicate] using counted

def initial (session : Nat) (origin : Origins) (arrival : Option X) (budget : Nat) :
    Multiset (Resource X Origins ⊕ Unit) :=
  marking (arrival.elim (pending session origin) (ready session origin)) (purse budget)

/-- Endpoint and occurrence history of an attempted handling of the delivered message. -/
def execute (test : X → Bool) (cost : X → Nat)
    (session : Nat) (origin : Origins) (arrival : Option X) (budget : Nat) :
    Σ target, OccurrencePath (paid test cost).presentation (initial session origin arrival budget)
      target :=
  match arrival with
  | none => ⟨_, .refl _⟩
  | some value => if affordable : cost value ≤ budget then
      ⟨_, paidRun test cost session origin value budget affordable⟩
    else ⟨_, .refl _⟩

/-- The observation reads the actual endpoint rather than a stored predicted verdict. -/
def observed (test : X → Bool) (cost : X → Nat)
    (session : Nat) (origin : Origins) (arrival : Option X) (budget : Nat) :
    Multiset (Nat × Verdict × Origins × X) :=
  outputs (leftPart (execute test cost session origin arrival budget).1)

theorem observed_none (test : X → Bool) (cost : X → Nat)
    (session : Nat) (origin : Origins) (budget : Nat) :
    observed test cost session origin none budget = 0 := by
  simp only [observed, execute, initial, Option.elim_none, leftPart_marking, outputs_pending]

theorem observed_some (test : X → Bool) (cost : X → Nat)
    (session : Nat) (origin : Origins) (value : X) (budget : Nat) :
    observed test cost session origin (some value) budget =
      if cost value ≤ budget then { (session, verdictOf (test value), origin, value) } else 0 := by
  by_cases affordable : cost value ≤ budget
  · simp only [observed, execute, dif_pos affordable, completed, leftPart_marking,
      outputs_finished, if_pos affordable]
  · simp only [observed, execute, dif_neg affordable, initial, Option.elim_some,
      leftPart_marking, outputs_ready, if_neg affordable]

end DecidableResources

end Mettapedia.GSLT.Causality.ComplementaryAssay
