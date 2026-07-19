import Mettapedia.GSLT.LanguageDef.InferenceChecker

/-!
# Proof-carrying GSLT source admission

This module keeps source identity, assumptions, profiles, and the inference
presentation in one validated value.  The metadata is not an authenticity
oracle: a source-specific adequacy theorem must still connect the recorded
identity to an independently specified source relation.  Its purpose is to
prevent a validated presentation from being detached from, or replaced inside,
the source package consumed by the generic checker.
-/

namespace Mettapedia.GSLT.LanguageDef.CheckedSource

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- Exact external identity recorded for a source artifact.  Digest
verification remains an adapter/source-boundary obligation. -/
structure SourceIdentity where
  systemId : String
  revision : String
  artifactDigest : String
deriving Repr, DecidableEq

def SourceIdentity.isValid (identity : SourceIdentity) : Bool :=
  identity.systemId != "" &&
    identity.revision != "" &&
    identity.artifactDigest != ""

/-- One explicit assumption carried by the hosted source package. -/
structure SourceAssumption where
  id : String
  statement : Pattern
deriving Repr

def SourceAssumption.isValid (assumption : SourceAssumption) : Bool :=
  assumption.id != "" &&
    assumption.statement.isWellScoped &&
    assumption.statement.hasCanonicalBinderMetadata

structure AssumptionLedger where
  entries : List SourceAssumption
deriving Repr

def AssumptionLedger.ids (ledger : AssumptionLedger) : List String :=
  ledger.entries.map (fun entry => entry.id)

def AssumptionLedger.isValid (ledger : AssumptionLedger) : Bool :=
  ledger.entries.all SourceAssumption.isValid &&
    ledger.ids.eraseDups.length == ledger.ids.length

/-- Named versioned profile data.  Profile payloads remain ordinary patterns;
their source-specific meaning is established outside the generic checker. -/
structure SourceProfile where
  name : String
  version : String
  payload : Pattern
deriving Repr

def SourceProfile.isValid (profile : SourceProfile) : Bool :=
  profile.name != "" &&
    profile.version != "" &&
    profile.payload.isWellScoped &&
    profile.payload.hasCanonicalBinderMetadata

structure ProfileLedger where
  entries : List SourceProfile
deriving Repr

def ProfileLedger.names (ledger : ProfileLedger) : List String :=
  ledger.entries.map (fun entry => entry.name)

def ProfileLedger.isValid (ledger : ProfileLedger) : Bool :=
  !ledger.entries.isEmpty &&
    ledger.entries.all SourceProfile.isValid &&
    ledger.names.eraseDups.length == ledger.names.length

/-- The single source package admitted at the generic-checker boundary. -/
structure GSLTSource where
  identity : SourceIdentity
  assumptions : AssumptionLedger
  profiles : ProfileLedger
  presentation : Presentation
deriving Repr

def GSLTSource.isValid (source : GSLTSource) : Bool :=
  source.identity.isValid &&
    source.assumptions.isValid &&
    source.profiles.isValid &&
    source.presentation.isValidV2

/-- A checked source retains proofs for every generic admission condition.
Replacing any field of `source` therefore requires re-establishing the
corresponding proof rather than reusing an unrelated capability token. -/
structure CheckedGSLT where
  source : GSLTSource
  identityValid : source.identity.isValid = true
  assumptionsValid : source.assumptions.isValid = true
  profilesValid : source.profiles.isValid = true
  presentationValid : source.presentation.isValidV2 = true

inductive ValidationError where
  | invalidIdentity
  | invalidAssumptionLedger
  | missingProfile
  | invalidProfileLedger
  | invalidPresentation
deriving Repr, DecidableEq

/-- Fail-closed admission with a proof-carrying successful result. -/
def GSLTSource.validate (source : GSLTSource) :
    Except ValidationError CheckedGSLT :=
  if hIdentity : source.identity.isValid = true then
    if hAssumptions : source.assumptions.isValid = true then
      if source.profiles.entries.isEmpty then
        .error .missingProfile
      else if hProfiles : source.profiles.isValid = true then
        if hPresentation : source.presentation.isValidV2 = true then
          .ok
            { source
              identityValid := hIdentity
              assumptionsValid := hAssumptions
              profilesValid := hProfiles
              presentationValid := hPresentation }
        else
          .error .invalidPresentation
      else
        .error .invalidProfileLedger
    else
      .error .invalidAssumptionLedger
  else
    .error .invalidIdentity

def validationError : Except ValidationError CheckedGSLT →
    Option ValidationError
  | .ok _ => none
  | .error error => some error

def validationAccepted : Except ValidationError CheckedGSLT → Bool
  | .ok _ => true
  | .error _ => false

/-- The executable admission function accepts exactly the conjunction exposed
by `GSLTSource.isValid`; no capability-space state participates. -/
theorem validationAccepted_validate_eq_isValid (source : GSLTSource) :
    validationAccepted source.validate = source.isValid := by
  by_cases hIdentity : source.identity.isValid = true
  · by_cases hAssumptions : source.assumptions.isValid = true
    · by_cases hEmpty : source.profiles.entries.isEmpty = true
      · have hProfiles : source.profiles.isValid = false := by
          simp [ProfileLedger.isValid, hEmpty]
        simp [GSLTSource.validate, validationAccepted,
          GSLTSource.isValid, hIdentity, hAssumptions, hEmpty, hProfiles]
      · by_cases hProfiles : source.profiles.isValid = true
        · by_cases hPresentation : source.presentation.isValidV2 = true <;>
            simp [GSLTSource.validate, validationAccepted,
              GSLTSource.isValid, hIdentity, hAssumptions, hEmpty,
              hProfiles, hPresentation]
        · simp [GSLTSource.validate, validationAccepted,
            GSLTSource.isValid, hIdentity, hAssumptions, hEmpty, hProfiles]
    · simp [GSLTSource.validate, validationAccepted,
        GSLTSource.isValid, hIdentity, hAssumptions]
  · simp [GSLTSource.validate, validationAccepted,
      GSLTSource.isValid, hIdentity]

/-- Successful validation never changes or substitutes the source package. -/
theorem GSLTSource.validate_source_eq {source : GSLTSource}
    {checked : CheckedGSLT} (hvalidate : source.validate = .ok checked) :
    checked.source = source := by
  by_cases hIdentity : source.identity.isValid = true
  · by_cases hAssumptions : source.assumptions.isValid = true
    · by_cases hEmpty : source.profiles.entries.isEmpty = true
      · simp [GSLTSource.validate, hIdentity, hAssumptions, hEmpty] at hvalidate
      · by_cases hProfiles : source.profiles.isValid = true
        · by_cases hPresentation : source.presentation.isValidV2 = true
          · simp [GSLTSource.validate, hIdentity, hAssumptions, hEmpty,
              hProfiles, hPresentation] at hvalidate
            subst checked
            rfl
          · simp [GSLTSource.validate, hIdentity, hAssumptions, hEmpty,
              hProfiles, hPresentation] at hvalidate
        · simp [GSLTSource.validate, hIdentity, hAssumptions, hEmpty,
            hProfiles] at hvalidate
    · simp [GSLTSource.validate, hIdentity, hAssumptions] at hvalidate
  · simp [GSLTSource.validate, hIdentity] at hvalidate

namespace CheckedGSLT

theorem source_isValid (checked : CheckedGSLT) :
    checked.source.isValid = true := by
  simp [GSLTSource.isValid, checked.identityValid,
    checked.assumptionsValid, checked.profilesValid,
    checked.presentationValid]

/-- Recover the exact validated presentation stored in the checked source. -/
def presentation (checked : CheckedGSLT) : ValidatedPresentation :=
  ⟨checked.source.presentation, checked.presentationValid⟩

/-- The generic checker specialized only by a proof-carrying source package. -/
def checkRaw (checked : CheckedGSLT) (goal : Pattern) (proof : RawProof) : Bool :=
  InferenceChecker.checkRaw checked.presentation goal proof

def CheckedProof (checked : CheckedGSLT) (goal : Pattern) :=
  { proof : RawProof // checked.checkRaw goal proof = true }

theorem checkRaw_soundness {checked : CheckedGSLT}
    {goal : Pattern} {proof : RawProof}
    (hcheck : checked.checkRaw goal proof = true) :
    Nonempty (Derivation checked.presentation goal) :=
  InferenceChecker.checkRaw_soundness hcheck

theorem checkRaw_exists_derivation_with_exact_erasure
    {checked : CheckedGSLT} {goal : Pattern} {proof : RawProof}
    (hcheck : checked.checkRaw goal proof = true) :
    ∃ derivation : Derivation checked.presentation goal,
      derivation.erase = proof :=
  InferenceChecker.checkRaw_exists_derivation_with_exact_erasure hcheck

theorem checkRaw_erase {checked : CheckedGSLT} {goal : Pattern}
    (derivation : Derivation checked.presentation goal) :
    checked.checkRaw goal derivation.erase = true :=
  InferenceChecker.checkRaw_erase derivation

end CheckedGSLT

/-! ## Admission and checker boundary fixtures -/

private def fixtureRule : RuleSchema :=
  { id := ⟨"fixture-rule"⟩
    metavariables := []
    premises := []
    conclusion := .apply "Holds" [] }

private def fixturePresentation : Presentation :=
  { language :=
      { LanguageDef.empty "checked-source-fixture" with
        judgments := [{ head := "Holds", arity := 0 }]
        inferenceRules := [fixtureRule] } }

private def fixtureIdentity : SourceIdentity :=
  { systemId := "fixture-source"
    revision := "fixture-revision"
    artifactDigest := "sha256:fixture" }

private def fixtureProfiles : ProfileLedger :=
  { entries :=
      [{ name := "proof-calculus"
         version := "v1"
         payload := .apply "ExactPremises" [] }] }

private def fixtureSource : GSLTSource :=
  { identity := fixtureIdentity
    assumptions := { entries := [] }
    profiles := fixtureProfiles
    presentation := fixturePresentation }

private theorem fixtureEmptyLanguage_validate :
    (LanguageDef.empty "checked-source-fixture").validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [LanguageDef.empty, LanguageDef.typeNames]

private theorem fixturePresentation_valid :
    fixturePresentation.isValidV2 = true := by
  simp [fixturePresentation, fixtureRule,
    Presentation.isValidV2, Presentation.isValidV1,
    Presentation.ruleIds, Presentation.judgmentSignatureValid,
    Presentation.judgmentHeads, RuleSchema.isValidIn,
    Presentation.judgmentSchemaValid, Presentation.lookupJudgment?,
    fixedConstructorListsValid, RuleSchema.isValidV1,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, Pattern.isWellScoped,
    Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    fixtureEmptyLanguage_validate]
  decide

private def fixtureChecked : CheckedGSLT :=
  { source := fixtureSource
    identityValid := by rfl
    assumptionsValid := by rfl
    profilesValid := by rfl
    presentationValid := fixturePresentation_valid }

private def fixtureProof : RawProof :=
  .node { ruleId := ⟨"fixture-rule"⟩, arguments := [] } []

/- Positive: complete metadata and a valid presentation are admitted. -/
#guard (validationError fixtureSource.validate).isNone

/- Positive: source-indexed checking inherits exact generic acceptance. -/
#guard fixtureChecked.checkRaw (.apply "Holds" []) fixtureProof

/- Negative: changing the goal cannot reuse an accepted raw proof. -/
#guard !fixtureChecked.checkRaw (.apply "Other" []) fixtureProof

/-- Negative: a source without exact external identity fails closed. -/
example :
    validationError
        ({ fixtureSource with
          identity := { fixtureIdentity with artifactDigest := "" } }).validate =
      some .invalidIdentity := by
  rfl

/-- Negative: at least one explicit source profile is required. -/
example :
    validationError
        ({ fixtureSource with profiles := { entries := [] } }).validate =
      some .missingProfile := by
  rfl

/- Negative: replacing the rooted inference rules with duplicate identifiers
forces presentation revalidation and is rejected. -/
#guard
  validationError
      ({ fixtureSource with
        presentation :=
          { language :=
              { fixturePresentation.language with
                inferenceRules := [fixtureRule, fixtureRule] } } }).validate ==
    some .invalidPresentation

end Mettapedia.GSLT.LanguageDef.CheckedSource
