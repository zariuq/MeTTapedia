import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSerializationRuntime

/-!
# Parser readback throughout actual finite executions

Every existing finite occurrence-bearing path preserves serialized admission.
Starting from the actual parser image, initial normalization fixes the funding
location once. Later firings preserve that exact raw location. Endpoint readback
uses the original parser with the original external location index, comparing
the complete normalized raw component multiset rather than quotation-erasing
or receipt-only observations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open ActivationGenerated.SerializationAdmission

namespace CostPath

/-- This invariant is propagated by the actual path constructors. -/
theorem serialized_admission :
    ∀ {nextId components finalId finalComponents}
      (_path : CostPath nextId components finalId finalComponents)
      {location : RawCostName},
      (components.map RawTraceComponent.term).Forall (ConfigAdmitted location) →
      (finalComponents.map RawTraceComponent.term).Forall (ConfigAdmitted location) := by
  intro nextId components finalId finalComponents path
  induction path with
  | done supported bounded => intro location images; exact images
  | @fire nextId components finalId finalComponents supported bounded step enabled rest ih =>
      intro location images
      exact ih (applyTracedStep_admitted images enabled nextId)

theorem serialized_canonical_admission :
    ∀ {nextId components finalId finalComponents}
      (_path : CostPath nextId components finalId finalComponents)
      {location : RawCostName},
      TraceComponentsCanonical components →
      (components.map RawTraceComponent.term).Forall (ConfigAdmitted location) →
      TraceComponentsCanonical finalComponents ∧
        (finalComponents.map RawTraceComponent.term).Forall (ConfigAdmitted location) := by
  intro nextId components finalId finalComponents path
  induction path with
  | done supported bounded => intro location canonical images; exact ⟨canonical, images⟩
  | @fire nextId components finalId finalComponents supported bounded step enabled rest ih =>
      intro location canonical images
      exact ih (applyTracedStep_canonical canonical enabled nextId)
        (applyTracedStep_admitted images enabled nextId)

end CostPath

namespace ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax

theorem ConfigImage.initial_serialized_admission {location : CostName LiteralAuthority}
    {source : Pattern} {term : CostTerm LiteralAuthority} (image : ConfigImage location source term) :
    ((initialTraceComponents (literalEncodeTerm term)).map RawTraceComponent.term).Forall
      (SerializationAdmission.ConfigAdmitted (literalEncodeName location).normalize) := by
  rw [initialTraceComponents_terms]
  exact image.serialized.normalizeConfig

/-- Any actual finite execution from an existing parser image has an actual
old-parser endpoint witness with the same complete normalized component bag. -/
theorem ConfigImage.finite_path_parser_readback {channelSource source : Pattern}
    {location : CostName LiteralAuthority} {term : CostTerm LiteralAuthority}
    (channelImage : NameImage 0 channelSource location) (image : ConfigImage location source term)
    {finalId : Nat} {finalComponents : List RawTraceComponent}
    (path : CostPath 0 (initialTraceComponents (literalEncodeTerm term)) finalId finalComponents) :
    ∃ finalSource decoded fuel,
      (config? location channelImage.purseInventory_zero channelImage.runtimeSupported fuel finalSource).map
        Subtype.val = some decoded ∧
      ((literalEncodeTerm decoded).normalizeConfig : Multiset RawCostTerm) =
        (finalComponents.map RawTraceComponent.term : Multiset RawCostTerm) := by
  obtain ⟨canonical, admitted⟩ := path.serialized_canonical_admission
    (initialTraceComponents_canonical _) image.initial_serialized_admission
  exact SerializationAdmission.configuration_parser_readback channelImage
    (RawCostName.normalize_idempotent _) _ admitted canonical.terms canonical.normalized

end ActivationGenerated
end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
