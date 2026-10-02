import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ResourceWave
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.AtomicResourceJoin

/-!
# Exact operational meaning of located resource events

The resource system and the ordinary funded rho relation have the same
transitions. The comparison retains the event's location, exact debit and
residual configuration. Resource enablement supplies support for a scheduler;
it does not specify priorities, rates or a complete candidate catalogue.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open Mettapedia.GSLT.Causality.ResourceInteraction

universe u

namespace CostResourceWave

variable {Ground : Type u}

@[simp] theorem enables_iff_consumed_le (source : CostConfig Ground)
    (entry : (costResourceSystem Ground).Entry) :
    (costResourceSystem Ground).Enables source entry.2 ↔
      (event entry).consumed ≤ source := by
  simp only [System.Enables, costResourceSystem, add_zero]
  rfl

@[simp] theorem fire_eq [DecidableEq Ground] (source : CostConfig Ground)
    (entry : (costResourceSystem Ground).Entry) :
    (costResourceSystem Ground).fire source entry.2 =
      source - (event entry).consumed + (event entry).produced := rfl

end CostResourceWave

namespace AtomicResourceJoin

variable {Ground : Type u} [DecidableEq Ground]
  {source target : CostConfig Ground} {event : CostedEvent Ground}

/-- The frame decomposition and the resource system's enable/fire contract
are equivalent for the same complete funded event. -/
theorem iff_enabled_fire :
    AtomicResourceJoin source event target ↔
      (costResourceSystem Ground).Enables source event.resourceEntry.2 ∧
        target = (costResourceSystem Ground).fire source event.resourceEntry.2 := by
  rw [CostResourceWave.enables_iff_consumed_le,
    CostResourceWave.fire_eq, CostResourceWave.event_resourceEntry]
  constructor
  · rintro ⟨frame, sourceEq, targetEq⟩
    refine ⟨?_, ?_⟩
    · rw [sourceEq]
      exact Multiset.le_add_left _ _
    · rw [sourceEq, targetEq, add_tsub_cancel_right]
  · rintro ⟨fits, targetEq⟩
    exact ⟨source - event.consumed, (tsub_add_cancel_of_le fits).symm, targetEq⟩

end AtomicResourceJoin

/-- Every ordinary funded step is exactly an enabled resource event, with
the original location and debit, and conversely. -/
theorem costStep_iff_exists_enabled_resource
    {Ground : Type u} [DecidableEq Ground]
    {source target : CostConfig Ground} {location : CostName Ground}
    {spend : CostSig Ground} :
    CostStep source location spend target ↔
      ∃ entry : (costResourceSystem Ground).Entry,
        entry.1 = location ∧ (CostResourceWave.event entry).spend = spend ∧
          (costResourceSystem Ground).Enables source entry.2 ∧
            target = (costResourceSystem Ground).fire source entry.2 := by
  constructor
  · intro step
    obtain ⟨event, located, spent, join⟩ := step.exists_atomicResourceJoin
    obtain ⟨enabled, targetEq⟩ := AtomicResourceJoin.iff_enabled_fire.mp join
    exact ⟨event.resourceEntry, located, spent, enabled, targetEq⟩
  · rintro ⟨entry, rfl, rfl, enabled, rfl⟩
    exact CostResourceWave.enabled_costStep source entry enabled

/-- Forgetting the labels gives the existing resource system's GSLT rewrite
relation. The labelled theorem above retains the funding observations. -/
theorem resource_rewrites_iff_costStep
    {Ground : Type u} [DecidableEq Ground]
    {source target : CostConfig Ground} :
    (costResourceSystem Ground).theory.rewrites source target ↔
      ∃ location spend, CostStep source location spend target := by
  constructor
  · rintro ⟨location, resourceInstance, enabled, rfl⟩
    exact ⟨location, (CostResourceWave.event ⟨location, resourceInstance⟩).spend,
      CostResourceWave.enabled_costStep source ⟨location, resourceInstance⟩ enabled⟩
  · rintro ⟨location, spend, step⟩
    obtain ⟨entry, _located, _spent, enabled, targetEq⟩ :=
      costStep_iff_exists_enabled_resource.mp step
    exact ⟨entry.1, entry.2, enabled, targetEq⟩

/-- Quiescence over all resource instances is exactly absence of a funded
transition. A finite catalogue needs its own completeness theorem. -/
theorem no_costStep_iff_no_enabled_resource
    {Ground : Type u} [DecidableEq Ground] (source : CostConfig Ground) :
    (∀ location spend target, ¬ CostStep source location spend target) ↔
      ∀ entry : (costResourceSystem Ground).Entry,
        ¬ (costResourceSystem Ground).Enables source entry.2 := by
  constructor
  · intro none entry enabled
    exact none entry.1 (CostResourceWave.event entry).spend _
      (CostResourceWave.enabled_costStep source entry enabled)
  · intro none location spend target step
    obtain ⟨entry, _located, _spent, enabled, _target⟩ :=
      costStep_iff_exists_enabled_resource.mp step
    exact none entry enabled

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
