import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSerializationPaths
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSplitControls

/-!
# Serialized-admission execution and rejection controls

The positive control reuses an actual generated split firing with a bound-name
receiver, a signed nonempty payload, a nonempty quoted channel and ordered
nonempty purse tails. Its actual runtime endpoint is read by the old parser.
Negative controls exclude multi-atom cells, raw signature names, purse-bearing
quoted code and open quoted names from this explicit parser domain.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated.SerializationAdmission

open Mettapedia.OSLF.MeTTaIL.Syntax

theorem two_atom_signature_rejected (first second : String) :
    ¬SignatureAdmitted [first, second] := by
  intro image
  have one := image.length_eq_one
  simp at one

theorem raw_signature_name_rejected (signature : RawCostSig) :
    ¬NameAdmitted 0 (.signature signature) := by
  intro image
  cases image

theorem quoted_purse_rejected (location : RawCostName) (stack : RawCostStack) :
    ¬NameAdmitted 0 (.quote (.purse location stack)) := by
  intro image
  cases image with
  | quote code => cases code

theorem open_quoted_name_rejected : ¬NameAdmitted 0 (.quote (.drop (.bvar 0))) := by
  intro image
  cases image with
  | quote code =>
      cases code with
      | drop name =>
          cases name with
          | bvar bound => omega

theorem code_parser_cannot_return_purse {fuel depth : Nat} {source : Pattern}
    {decoded : DecodedCode depth source} (parsed : code? fuel depth source = some decoded)
    (location : CostName LiteralAuthority) (stack : CostStack LiteralAuthority) :
    decoded.val ≠ .purse location stack := by
  intro same
  have parsedValue : (code? fuel depth source).map Subtype.val = some decoded.val := by rw [parsed]; rfl
  have admitted := (code_parser_image parsedValue).serialized
  rw [same] at admitted
  cases admitted

theorem open_quoted_runtime_rejected :
    runtimeCostCandidates (.drop (.quote (.drop (.bvar 0)))) = none := by
  decide +kernel

open ActivationLocatedControls ActivationSplitControls

/-- A real generated split occurrence has an actual parser-readable endpoint
with all normalized raw components retained exactly, including temporal tails. -/
theorem actual_split_endpoint_readback :
    ∃ (step : RawRuntimeStep),
      ∃ (path : CostPath 0 (initialTraceComponents (literalEncodeTerm ActivationSplitControls.source)) 1
        (applyTracedStep (initialTraceComponents (literalEncodeTerm ActivationSplitControls.source)) step 0)),
      ∃ finalSource decoded fuel,
      step ∈ runtimeCostCandidatesFromConfig (literalEncodeTerm ActivationSplitControls.source).normalizeConfig ∧
      path.depth = 1 ∧
      (config? channel channel_image.purseInventory_zero channel_image.runtimeSupported fuel finalSource).map
        Subtype.val = some decoded ∧
      ((literalEncodeTerm decoded).normalizeConfig : Multiset RawCostTerm) =
        ((applyTracedStep (initialTraceComponents (literalEncodeTerm ActivationSplitControls.source)) step 0).map
          RawTraceComponent.term : Multiset RawCostTerm) := by
  obtain ⟨step, enabled, _spend, _cells, ⟨path, depth⟩, _balance⟩ := actual_two_generated_purse_execution
  have image : ConfigImage channel
      (splitReceiverSource channelSource boundBodySource payloadSource unitSource productSource
        recvTailSource sendTailSource) ActivationSplitControls.source :=
    split_receiver_config_image channel_image
      (CodeImage.drop (NameImage.bvar (index := 0) (by decide +kernel))) payload_image
      unitTyped unit_accepted productTyped product_accepted recv_tail_image send_tail_image
  obtain ⟨finalSource, decoded, fuel, parsed, exactReadout⟩ :=
    image.finite_path_parser_readback channel_image path
  exact ⟨step, path, finalSource, decoded, fuel, enabled, depth, parsed, exactReadout⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated.SerializationAdmission
