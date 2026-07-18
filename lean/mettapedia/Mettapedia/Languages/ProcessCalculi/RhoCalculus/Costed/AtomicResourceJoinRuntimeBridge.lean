import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.AtomicResourceJoin
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.Bridge

/-!
# Runtime correspondence for atomic located-resource joins

The executable raw frontier and the atomic resource decomposition remain
independently defined.  Their correspondence factors through the declarative
`CostStep` relation, so executable enumeration is neither the definition nor
the proof of the semantic join.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed

/-- A raw runtime candidate denotes one atomic located-resource join with the
same decoded surface and spend, and its residual represents the join target. -/
def RuntimeAtomicResourceJoinSound (config : RawCostConfig)
    (step : RawRuntimeStep) : Prop :=
  ∃ target : CostConfig String, ∃ event : CostedEvent String,
    AtomicResourceJoin (decodeRawConfig config) event target ∧
      event.surface = decodeCostName step.surface ∧
      event.spend = decodeCostSig step.spend ∧
      step.residual.normalizeConfig.StructurallyRepresents target

/-- Every independently enumerated raw candidate is one atomic resource
join. -/
theorem atomicResourceJoin_sound_runtime
    {config : RawCostConfig} (canonical : config.Canonical)
    (config_ok : config.Forall (fun term => term.wellFormed = true))
    {step : RawRuntimeStep}
    (enabled : step ∈ runtimeCostCandidatesFromConfig config) :
    RuntimeAtomicResourceJoinSound config step := by
  obtain ⟨target, declarative, represented⟩ :=
    costStep_sound_runtime canonical config_ok enabled
  obtain ⟨event, surface_eq, spend_eq, join⟩ :=
    declarative.exists_atomicResourceJoin
  exact ⟨target, event, join, surface_eq, spend_eq, represented⟩

/-- Every atomic resource join over a canonical supported raw configuration
is enumerated by the raw runtime, modulo only the established structural
representation of the successor. -/
theorem atomicResourceJoin_complete_runtime_up_to_struct
    {config : RawCostConfig} (canonical : config.Canonical)
    (encoding : config.Forall RawCostTerm.EncodingCanonical)
    (config_ok : config.Forall (fun term => term.wellFormed = true))
    {event : CostedEvent String} {target : CostConfig String}
    (join : AtomicResourceJoin (decodeRawConfig config) event target) :
    RuntimeCostStepComplete config event.surface event.spend target :=
  costStep_complete_runtime_up_to_struct canonical encoding config_ok
    join.toCostStep

/-- Normalization supplies the raw invariants needed to enumerate any atomic
join represented by a supported executable input term. -/
theorem runtimeAtomicResourceJoin_complete_up_to_struct
    {term : RawCostTerm} (supported : term.wellFormed = true)
    {event : CostedEvent String} {target : CostConfig String}
    (join : AtomicResourceJoin
      (decodeRawConfig term.normalizeConfig) event target) :
    RuntimeCostStepComplete term.normalizeConfig event.surface event.spend target :=
  runtimeCostCandidates_complete_up_to_struct supported join.toCostStep

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
