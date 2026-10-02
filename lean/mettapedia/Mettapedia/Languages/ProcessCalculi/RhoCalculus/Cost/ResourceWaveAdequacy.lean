import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ResourceOperationalEquivalence
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.AtomicResourceJoinRuntimeBridge
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimeWave

/-!
# Runtime candidates and enabled resource instances

`ResourceOperationalEquivalence` shows that a funded step is exactly an enabled
instance of the resource system. This module carries that statement to the
runtime: a candidate of the raw reducer enables one instance with the same
decoded labels, and every enabled instance over a canonical supported encoding
is enumerated.

The runtime comparisons retain their existing normalization boundary:
successors structurally represent the resource target. They do not identify
ordinary unmetered rho reduction with a funded transition, or infer that a
finite scheduling catalogue exhausts the enabled relation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open Mettapedia.GSLT.Causality.ResourceInteraction

universe u

/-- An actual runtime candidate enables one resource instance with the same
decoded labels. Its normalized residual represents exactly that instance's
computed target, under the established raw/declarative comparison. -/
theorem runtimeCandidate_has_enabled_resourceEntry
    {config : RawCostConfig} (canonical : config.Canonical)
    (config_ok : config.Forall (fun term => term.wellFormed = true))
    {step : RawRuntimeStep}
    (enabled : step ∈ runtimeCostCandidatesFromConfig config) :
    ∃ entry : (costResourceSystem String).Entry,
      entry.1 = decodeCostName step.location ∧
      (CostResourceWave.event entry).spend = decodeCostSig step.spend ∧
      (costResourceSystem String).Enables (decodeRawConfig config) entry.2 ∧
      step.residual.normalizeConfig.StructurallyRepresents
        ((costResourceSystem String).fire (decodeRawConfig config) entry.2) := by
  obtain ⟨target, e, join, locationEq, spendEq, represented, _, _⟩ :=
    atomicResourceJoin_sound_runtime canonical config_ok enabled
  obtain ⟨resourceEnabled, targetEq⟩ := AtomicResourceJoin.iff_enabled_fire.mp join
  exact ⟨e.resourceEntry, locationEq, spendEq, resourceEnabled,
    targetEq ▸ represented⟩

/-- Conversely, every enabled resource instance over a canonical supported
encoding is enumerated, with unchanged location and debit and the existing
structural successor comparison. -/
theorem enabled_resourceEntry_complete_runtime
    {config : RawCostConfig} (canonical : config.Canonical)
    (encoding : config.Forall RawCostTerm.EncodingCanonical)
    (config_ok : config.Forall (fun term => term.wellFormed = true))
    (entry : (costResourceSystem String).Entry)
    (enabled : (costResourceSystem String).Enables (decodeRawConfig config) entry.2) :
    RuntimeCostStepComplete config entry.1 (CostResourceWave.event entry).spend
      ((costResourceSystem String).fire (decodeRawConfig config) entry.2) :=
  costStep_complete_runtime_up_to_struct canonical encoding config_ok
    (CostResourceWave.enabled_costStep _ entry enabled)

namespace RuntimeEventEmbedding

/-- Every claimed source occurrence contributes exactly one decoded consumed
resource. Equal syntax values are still counted separately. -/
theorem consumed_card {config : RawCostConfig} (embedding : RuntimeEventEmbedding config) :
    embedding.event.consumed.card = embedding.step.consumedIndices.length := by
  rw [← embedding.consumed_eq]
  have count := congrArg List.length embedding.indices_eq
  simpa only [decodeRawConfig, Multiset.coe_card, List.length_map] using count

/-- The complete consumption count agrees with the raw occurrence claims,
even for a family that has not passed the disjointness check. -/
theorem consumed_sum_card {config : RawCostConfig}
    (embeddings : List (RuntimeEventEmbedding config)) :
    ((embeddings.map fun (embedding : RuntimeEventEmbedding config) =>
      embedding.event.consumed).sum).card =
      (embeddings.flatMap indices).length := by
  induction embeddings with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons, Multiset.card_add,
        consumed_card, ih, List.flatMap_cons, List.length_append, indices]

end RuntimeEventEmbedding

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
