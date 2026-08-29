import Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionSelectedRoot
import Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedProjection

/-!
# Executable controls for the status-indexed official projection

These controls reuse admitted official ground-CNF nodes.  They test the
format-generic projection independently of the older ground-only projection:
valid metadata is retained, malformed metadata is rejected as malformed, and
an unknown calculus rule remains unsupported.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedProjectionCanary

open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionCheckService
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionProblemAuthority
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationProgram
open Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionSelectedRoot
open Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedProjection
open Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedService

namespace GroundCanary

open TptpOfficialGroundResolutionSelectedRoot.Canary

def guest : GuestProjection Formula Rule Unit Provenance Obligation where
  formula? := fun node =>
    match decodeFormula? node with
    | some formula => .ok formula
    | none => .error .unsupported
  inputProvenance? := fun node _ =>
    match decodeInput? node with
    | some (_, provenance) => .ok provenance
    | none => .error .unsupported
  rule? := fun ruleName _ _ =>
    if ruleName = "resolution" then .ok resolutionKey
    else .error .unsupported
  evidence? := fun ruleName _ _ =>
    if ruleName = "resolution" then .ok ()
    else .error .unsupported
  root? := fun node _ =>
    match rootObligation? node with
    | some obligation => .ok obligation
    | none => .error .unsupported

theorem valid_input_receives_exact_input_origin :
    (TptpOfficialStatusIndexedProjection.input? guest leafNode).map
        (fun (formula, _) => formula.origin) =
      .ok .input := by
  decide +kernel

theorem valid_inference_retains_origin_status_assumptions_and_symbols :
    (TptpOfficialStatusIndexedProjection.infer? guest inferenceNode).map
        (fun (_, evidence, conclusion) =>
          (conclusion.origin, evidence.metadata.status,
            conclusion.openAssumptions,
            conclusion.principalSymbols)) =
      .ok (.inferred .thm, .thm, ∅, ([
        ({ kind := .functor, name := "q" } :
          Mettapedia.GSLT.LanguageDef.TptpOfficialPrincipalSymbols.PrincipalSymbolId)
        ].toFinset)) := by
  decide +kernel

def counterStatusNode :
    Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationAdmission.AdmittedNode :=
  { inferenceNode with
    source := { inferenceNode.source with
      origin := .sourced (.apply "source" [])
        (.inference
          (inferenceRule "resolution")
          (Mettapedia.GSLT.LanguageDef.TptpOfficialUsefulInfo.Canary.usefulInfo [
            Mettapedia.GSLT.LanguageDef.TptpOfficialUsefulInfo.Canary.functionTerm
              "status" [
                Mettapedia.GSLT.LanguageDef.TptpOfficialUsefulInfo.Canary.atomicTerm
                  "cth"]])
          (TptpOfficialGroundResolutionVerifier.Canary.parents
            ["p_or_q", "not_p"]))
        (.apply "optional" []) } }

theorem official_counter_status_becomes_exact_counter_origin :
    (TptpOfficialStatusIndexedProjection.infer? guest counterStatusNode).map
        (fun (_, evidence, conclusion) =>
          (conclusion.origin, evidence.metadata.status)) =
      .ok (.inferred .cth, .cth) := by
  decide +kernel

def malformedMetadataNode :
    Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationAdmission.AdmittedNode :=
  { inferenceNode with
    source := { inferenceNode.source with
      origin := .sourced (.apply "source" [])
        (.inference
          (inferenceRule "resolution")
          Mettapedia.GSLT.LanguageDef.TptpOfficialUsefulInfo.Canary.malformedAssumptions
          (TptpOfficialGroundResolutionVerifier.Canary.parents
            ["p_or_q", "not_p"]))
        (.apply "optional" []) } }

theorem malformed_metadata_is_not_reported_as_unsupported :
    TptpOfficialStatusIndexedProjection.infer? guest malformedMetadataNode =
      .error .malformed := by
  rfl

def unknownRuleNode :
    Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationAdmission.AdmittedNode :=
  { inferenceNode with
    source := { inferenceNode.source with
      origin := .sourced (.apply "source" [])
        (.inference
          (inferenceRule "magic")
          TptpOfficialGroundResolutionVerifier.Canary.statusThm
          (TptpOfficialGroundResolutionVerifier.Canary.parents
            ["p_or_q", "not_p"]))
        (.apply "optional" []) } }

theorem unknown_calculus_rule_remains_unsupported :
    TptpOfficialStatusIndexedProjection.infer? guest unknownRuleNode =
      .error .unsupported := by
  rfl

end GroundCanary

#print axioms GroundCanary.valid_input_receives_exact_input_origin
#print axioms GroundCanary.valid_inference_retains_origin_status_assumptions_and_symbols
#print axioms GroundCanary.official_counter_status_becomes_exact_counter_origin
#print axioms GroundCanary.malformed_metadata_is_not_reported_as_unsupported
#print axioms GroundCanary.unknown_calculus_rule_remains_unsupported

end Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedProjectionCanary
