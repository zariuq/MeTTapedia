import Mettapedia.GSLT.LanguageDef.CheckedSource
import Mettapedia.GSLT.LanguageDef.InferenceExtraction

/-!
# Checked admission of generated inference presentations

This is the single generic route from one `LanguageDef` root and one evidence
profile to a proof-carrying source package.  The generated presentation is not
accepted as a separate caller-supplied argument: it is recomputed from the root
immediately before ordinary checked-source admission.
-/

namespace Mettapedia.GSLT.LanguageDef.CheckedInferenceExtraction

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceExtraction
open Mettapedia.GSLT.LanguageDef.CheckedSource

structure AdmissionInput where
  identity : SourceIdentity
  assumptions : AssumptionLedger
  profiles : ProfileLedger
  evidenceProfile : EvidenceProfile
  language : LanguageDef
deriving Repr

inductive AdmissionError where
  | extractionFailed
  | validationFailed : CheckedSource.ValidationError → AdmissionError
deriving Repr, DecidableEq

def AdmissionInput.generatedSource (input : AdmissionInput) :
    Option GSLTSource := do
  let presentation ← rawPresentation? input.evidenceProfile input.language
  pure
    { identity := input.identity
      assumptions := input.assumptions
      profiles := input.profiles
      presentation }

/-- Generate and validate in one operation.  There is no parameter through
which a producer can substitute a presentation unrelated to `input.language`.
-/
def admit (input : AdmissionInput) : Except AdmissionError CheckedGSLT :=
  match input.generatedSource with
  | none => .error .extractionFailed
  | some source => source.validate.mapError .validationFailed

def admissionAccepted : Except AdmissionError CheckedGSLT → Bool
  | .ok _ => true
  | .error _ => false

def admissionError : Except AdmissionError CheckedGSLT → Option AdmissionError
  | .ok _ => none
  | .error error => some error

/-- Successful admission exposes exactly the presentation generated from the
same root and evidence profile. -/
theorem admit_presentation_is_generated {input : AdmissionInput}
    {checked : CheckedGSLT} (hadmit : admit input = .ok checked) :
    rawPresentation? input.evidenceProfile input.language =
      some checked.source.presentation := by
  cases hextraction : rawPresentation? input.evidenceProfile input.language with
  | none =>
      simp [admit, AdmissionInput.generatedSource, hextraction] at hadmit
  | some presentation =>
      let source : GSLTSource :=
        { identity := input.identity
          assumptions := input.assumptions
          profiles := input.profiles
          presentation }
      have hgenerated : input.generatedSource = some source := by
        simp [AdmissionInput.generatedSource, hextraction, source]
      cases hadmission : source.validate with
      | error error =>
          have hAdmitError :
              admit input = .error (.validationFailed error) := by
            unfold admit
            rw [hgenerated]
            change
              Except.mapError AdmissionError.validationFailed source.validate =
                .error (.validationFailed error)
            rw [hadmission]
            rfl
          rw [hAdmitError] at hadmit
          contradiction
      | ok admitted =>
          have hsource := GSLTSource.validate_source_eq hadmission
          have hAdmitOk : admit input = .ok admitted := by
            unfold admit
            rw [hgenerated]
            change
              Except.mapError AdmissionError.validationFailed source.validate =
                .ok admitted
            rw [hadmission]
            rfl
          rw [hAdmitOk] at hadmit
          have hadmitted : admitted = checked := Except.ok.inj hadmit
          subst checked
          rw [hsource]

/-! ## Generated-route admission fixtures -/

private def fixtureEvidenceProfile : EvidenceProfile :=
  { checkHead := "Check"
    okHead := "Ok"
    proofCategory := "Proof"
    evidenceCategory := "Evidence"
    derivedHead := "Derived"
    relationHeadPrefix := "Relation." }

private def fixtureInput : AdmissionInput :=
  { identity :=
      { systemId := "generated-route-fixture"
        revision := "v1"
        artifactDigest := "sha256:generated-route-fixture" }
    assumptions := { entries := [] }
    profiles :=
      { entries :=
          [{ name := "inference-extraction"
             version := "v1"
             payload := .apply "ExactPremises" [] }] }
    evidenceProfile := fixtureEvidenceProfile
    language := LanguageDef.empty "generated-route-fixture" }

/- Positive: a presentation generated from a valid root is admitted. -/
#guard admissionAccepted (admit fixtureInput)

/-- Negative: admission cannot omit the explicit source-profile ledger. -/
example :
    admissionError
        (admit { fixtureInput with profiles := { entries := [] } }) =
      some (.validationFailed .missingProfile) := by
  rfl

/-- Negative: admission cannot omit exact source identity. -/
example :
    admissionError
        (admit
          { fixtureInput with
            identity := { fixtureInput.identity with revision := "" } }) =
      some (.validationFailed .invalidIdentity) := by
  rfl

end Mettapedia.GSLT.LanguageDef.CheckedInferenceExtraction
