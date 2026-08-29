import Mettapedia.GSLT.LanguageDef.NIKDefaultProfile
import Mettapedia.GSLT.Core.CertifiedPlanning
import Mettapedia.Languages.Metamath.MMLean4Bridge
import Mettapedia.Languages.Metamath.InferenceSourceAdmission

/-!
# Whole-database Metamath authority for NIK

This module packages the verified pure `mm-lean4` byte checker as one NIK
authority.  Acceptance requires both successful sound-mode checking and the
absence of Metamath's explicit incomplete-proof marker.

The projected meaning is not final-database self-citation.  Every stored
assertion must carry the insertion-time strong origin certificate supplied by
`mm-lean4`: an axiom finish event, or a theorem finish event whose written
proof is provable in the database before insertion.  Thus ordinary and
compressed proofs share one chronology-preserving authority.
-/

namespace Mettapedia.Languages.Metamath.DatabaseNIKAuthority

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.CheckedSource
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKDefaultProfile
open Mettapedia.GSLT
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceSourceAdmission

/-! ## Executable scope and independent projection -/

def verifiedB (sourceBytes : ByteArray) : Bool :=
  let database := Metamath.Verify.checkBytes sourceBytes
    Metamath.Verify.ModeConfig.soundDefault
  database.error?.isNone && database.incompleteProofs.isEmpty

/-- Exact executable scope: accepted syntax and proof checking, with no `?`
proof admitted as a completed theorem. -/
def Verified (sourceBytes : ByteArray) : Prop :=
  verifiedB sourceBytes = true

theorem verified_iff (sourceBytes : ByteArray) :
    Verified sourceBytes <->
      let database :=
        Metamath.Verify.checkBytes sourceBytes
          Metamath.Verify.ModeConfig.soundDefault
      database.error? = none /\ database.incompleteProofs.isEmpty = true := by
  simp [Verified, verifiedB, Bool.and_eq_true, Option.isNone_iff_eq_none]

/-- Every stored assertion has the strong insertion-time certificate generated
by the verified parser/proof checker.  In particular, the theorem branch
retains pre-insertion provability rather than obtaining validity by citing the
newly inserted theorem. -/
def StoredAssertionsHaveOrigins (sourceBytes : ByteArray) : Prop :=
  let database :=
    Metamath.Verify.checkBytes sourceBytes
      Metamath.Verify.ModeConfig.soundDefault
  forall name formula frame label,
    database.find? name = some (.assert formula frame label) ->
      Metamath.PrefixWitnessCheckBytes.StrongNewAssertCertificate
        name formula frame label

theorem verified_implies_storedAssertionsHaveOrigins
    (sourceBytes : ByteArray) :
    Verified sourceBytes -> StoredAssertionsHaveOrigins sourceBytes := by
  intro verified
  have success :
      (Metamath.Verify.checkBytes sourceBytes
        Metamath.Verify.ModeConfig.soundDefault).error? =
        none :=
    (verified_iff sourceBytes).mp verified |>.1
  intro name formula frame label found
  exact
    Metamath.PrefixWitnessCheckBytes.checkBytes_new_assert_strong_classified
      sourceBytes Metamath.Verify.ModeConfig.soundDefault
      Metamath.Verify.ModeConfig.soundDefault_prefixCertified
      name formula frame label success found

def checker : Checker ByteArray Unit where
  check sourceBytes _ := verifiedB sourceBytes

@[simp] theorem checker_accepts_iff (sourceBytes : ByteArray)
    (certificate : Unit) :
    checker.check sourceBytes certificate = true <-> Verified sourceBytes := by
  rfl

theorem checker_authority : checker.Authority Verified where
  sound := by
    intro sourceBytes certificate accepted
    exact accepted
  complete := by
    intro sourceBytes verified
    exact ⟨(), verified⟩

/-! ## Compiled inference-knowledge projection -/

/-- Stable identity of the Metamath-to-calculus-language projection.
The source digest is supplied by `SourceMetadata.identityFor`; callers do not
supply rules or declarations. -/
def knowledgeMetadata : SourceMetadata :=
  { systemId := "metamath"
    revision := "mm-lean4-sound-default/inference-projection-v1"
    assumptions := { entries := [] }
    profiles :=
      { entries :=
          [{ name := "metamath-inference-projection"
             version := "v1"
             payload := .apply "ExactPremisesWithDV" [] }] } }

/-- The exact checked-source package expected from one successful V1
normalization. -/
def generatedKnowledgeSourceV1 (sourceBytes : ByteArray)
    (definition : ValidatedCalculusLanguageDef) : GSLTSource :=
  { identity := knowledgeMetadata.identityFor sourceBytes
    assumptions := knowledgeMetadata.assumptions
    profiles := knowledgeMetadata.profiles
    definition := definition.1 }

/-- Proof-carrying output of the current normalized inference profile.  Its
source bytes remain in the type, and both the generated calculus definition
and the entire checked package are tied back to those exact bytes. -/
structure CompiledKnowledgeArtifactV1 (sourceBytes : ByteArray) where
  verified : Verified sourceBytes
  definition : ValidatedCalculusLanguageDef
  definitionGenerated :
    projectForMode none
      (Metamath.Verify.checkBytes sourceBytes
        Metamath.Verify.ModeConfig.soundDefault) = some definition
  checked : CheckedGSLT
  checkedSourceEq :
    checked.source = generatedKnowledgeSourceV1 sourceBytes definition

/-- Recheck the exact source bytes and, when the current normalized inference
profile is admissible, return a proof-carrying compiled artifact.  Partiality
is an implementation/profile boundary, not a restriction on Metamath
validity; a total generic realization can later be attached with
`PartialRealization.withFallback`. -/
def compileKnowledgeArtifactV1? (sourceBytes : ByteArray) :
    Option (CompiledKnowledgeArtifactV1 sourceBytes) :=
  if hVerified : verifiedB sourceBytes then
    let database :=
      Metamath.Verify.checkBytes sourceBytes
        Metamath.Verify.ModeConfig.soundDefault
    match hDefinition : projectForMode none database with
    | none => none
    | some definition =>
        let source := generatedKnowledgeSourceV1 sourceBytes definition
        match hValidate : source.validate with
        | .error _ => none
        | .ok checked =>
            some
              { verified := hVerified
                definition
                definitionGenerated := hDefinition
                checked
                checkedSourceEq := GSLTSource.validate_source_eq hValidate }
  else
    none

/-- Compatibility projection to the checked package used by the NIK fibre. -/
def compileKnowledgeV1? (sourceBytes : ByteArray) : Option CheckedGSLT :=
  (compileKnowledgeArtifactV1? sourceBytes).map
    CompiledKnowledgeArtifactV1.checked

/-- The named compilation observation: the exact normalized calculus definition
generated from the verified runtime database. -/
def knowledgeCompilationObservationV1 (sourceBytes : ByteArray) :
    Option CalculusLanguageDef :=
  (projectForMode none
    (Metamath.Verify.checkBytes sourceBytes
      Metamath.Verify.ModeConfig.soundDefault)).map
        (fun definition => definition.1)

theorem CompiledKnowledgeArtifactV1.preservesCompilationObservation
    {sourceBytes : ByteArray}
    (artifact : CompiledKnowledgeArtifactV1 sourceBytes) :
    some artifact.checked.source.definition =
      knowledgeCompilationObservationV1 sourceBytes := by
  rw [artifact.checkedSourceEq]
  simp [generatedKnowledgeSourceV1, knowledgeCompilationObservationV1,
    artifact.definitionGenerated]

private def compiledKnowledgeArtifactV1OfAccepted
    (sourceBytes : ByteArray)
    (accepted : (compileKnowledgeArtifactV1? sourceBytes).isSome = true) :
    CompiledKnowledgeArtifactV1 sourceBytes :=
  match hArtifact : compileKnowledgeArtifactV1? sourceBytes with
  | none => by simp [hArtifact] at accepted
  | some artifact => artifact

/-- V1 is formally a partial realization of its named compilation
observation.  This theorem does not identify that observation with all
Metamath semantics; the existing inference-adequacy development supplies the
separate semantic bridge. -/
def compiledKnowledgeV1PartialRealization :
    PartialRealization (Base := ByteArray)
      (fun _ => Unit)
      (fun sourceBytes => CompiledKnowledgeArtifactV1 sourceBytes)
      (fun _ => Option CalculusLanguageDef) where
  accepts := fun sourceBytes _ =>
    (compileKnowledgeArtifactV1? sourceBytes).isSome
  compile := fun sourceBytes _ accepted =>
    compiledKnowledgeArtifactV1OfAccepted sourceBytes accepted
  observeSource := fun sourceBytes _ =>
    knowledgeCompilationObservationV1 sourceBytes
  observeArtifact := fun _ artifact =>
    some artifact.checked.source.definition
  adequate := by
    intro sourceBytes source accepted
    exact
      (compiledKnowledgeArtifactV1OfAccepted sourceBytes accepted).preservesCompilationObservation

/-- Exact scope of the compiled-knowledge profile: the database is fully
verified and the same bytes generate one admitted inference definition.
This is a realization claim, not a second Metamath semantics. -/
def CompiledKnowledgeV1 (sourceBytes : ByteArray) : Prop :=
  Verified sourceBytes /\
    exists checked, compileKnowledgeV1? sourceBytes = some checked

/-- The logical scope of V1 is exactly existence of its proof-carrying
artifact; the separate `Verified` conjunct in `CompiledKnowledgeV1` is not an
unchecked side condition. -/
theorem compiledKnowledgeV1_iff_artifact (sourceBytes : ByteArray) :
    CompiledKnowledgeV1 sourceBytes <->
      exists artifact : CompiledKnowledgeArtifactV1 sourceBytes,
        compileKnowledgeArtifactV1? sourceBytes = some artifact := by
  constructor
  · rintro ⟨_verified, checked, compiled⟩
    unfold compileKnowledgeV1? at compiled
    cases hArtifact : compileKnowledgeArtifactV1? sourceBytes with
    | none => simp [hArtifact] at compiled
    | some artifact => exact ⟨artifact, rfl⟩
  · rintro ⟨artifact, compiled⟩
    exact
      ⟨artifact.verified, artifact.checked,
        by simp [compileKnowledgeV1?, compiled]⟩

def compiledKnowledgeV1B (sourceBytes : ByteArray) : Bool :=
  verifiedB sourceBytes && (compileKnowledgeV1? sourceBytes).isSome

theorem compiledKnowledgeV1B_iff (sourceBytes : ByteArray) :
    compiledKnowledgeV1B sourceBytes = true <->
      CompiledKnowledgeV1 sourceBytes := by
  simp only [compiledKnowledgeV1B, Bool.and_eq_true, Verified,
    CompiledKnowledgeV1]
  constructor
  · rintro ⟨verified, projected⟩
    refine ⟨verified, ?_⟩
    cases projection : compileKnowledgeV1? sourceBytes with
    | none => simp [projection] at projected
    | some checked => exact ⟨checked, rfl⟩
  · rintro ⟨verified, checked, projected⟩
    exact ⟨verified, by simp [projected]⟩

/-- The public Boolean profile gate is exactly the admission gate of the
partial realization.  In particular, verification is carried by the artifact
and cannot drift from compilation acceptance. -/
theorem compiledKnowledgeV1B_eq_partialAccepts (sourceBytes : ByteArray) :
    compiledKnowledgeV1B sourceBytes =
      compiledKnowledgeV1PartialRealization.accepts sourceBytes () := by
  cases hArtifact : compileKnowledgeArtifactV1? sourceBytes with
  | none =>
      simp [compiledKnowledgeV1B, compileKnowledgeV1?,
        compiledKnowledgeV1PartialRealization, hArtifact]
  | some artifact =>
      have verified : verifiedB sourceBytes = true := artifact.verified
      simp [compiledKnowledgeV1B, compileKnowledgeV1?,
        compiledKnowledgeV1PartialRealization, hArtifact, verified]

def compiledKnowledgeV1Checker : Checker ByteArray Unit where
  check sourceBytes _ := compiledKnowledgeV1B sourceBytes

theorem compiledKnowledgeV1Checker_authority :
    compiledKnowledgeV1Checker.Authority CompiledKnowledgeV1 where
  sound := by
    intro sourceBytes certificate accepted
    exact (compiledKnowledgeV1B_iff sourceBytes).mp accepted
  complete := by
    intro sourceBytes projected
    exact ⟨(), (compiledKnowledgeV1B_iff sourceBytes).mpr projected⟩

inductive EvidenceKind where
  | verifiedDatabase
  | compiledKnowledgeV1
deriving DecidableEq

/-- Whole-database checking is one fibre of the same open NIK authority
family used by theorem-level Metamath and TPTP authorities. -/
def authorityFamily : AuthorityFamily EvidenceKind where
  Claim := fun _ => ByteArray
  Certificate := fun _ => Unit
  checker
    | .verifiedDatabase => checker
    | .compiledKnowledgeV1 => compiledKnowledgeV1Checker
  Certified
    | .verifiedDatabase => Verified
    | .compiledKnowledgeV1 => CompiledKnowledgeV1
  Meaning
    | .verifiedDatabase => StoredAssertionsHaveOrigins
    | .compiledKnowledgeV1 => CompiledKnowledgeV1
  projection
    | .verifiedDatabase =>
        { authority := checker_authority
          project := verified_implies_storedAssertionsHaveOrigins }
    | .compiledKnowledgeV1 =>
        { authority := compiledKnowledgeV1Checker_authority
          project := fun _ projected => projected }

/-! ## Statusful request boundary -/

inductive Request where
  | malformed
  | unknownAuthority (name : String)
  | verifyDatabase (sourceBytes : ByteArray)
  | compileKnowledgeV1 (sourceBytes : ByteArray)

inductive Parsed where
  | unknownAuthority (name : String)
  | submission (request : TypedSubmission authorityFamily)

def frontend : Frontend authorityFamily Request where
  Parsed := Parsed
  parse
    | .malformed => none
    | .unknownAuthority name => some (.unknownAuthority name)
    | .verifyDatabase sourceBytes =>
        some (.submission ⟨.verifiedDatabase, sourceBytes, ()⟩)
    | .compileKnowledgeV1 sourceBytes =>
        some (.submission ⟨.compiledKnowledgeV1, sourceBytes, ()⟩)
  resolve
    | .unknownAuthority _ => none
    | .submission request => some request
  encode := fun ⟨kind, sourceBytes, _certificate⟩ =>
    match kind with
    | .verifiedDatabase => .verifyDatabase sourceBytes
    | .compiledKnowledgeV1 => .compileKnowledgeV1 sourceBytes
  resolve_encode := by
    rintro ⟨kind, sourceBytes, certificate⟩
    cases kind
    · cases certificate
      exact ⟨.submission ⟨.verifiedDatabase, sourceBytes, ()⟩, rfl, rfl⟩
    · cases certificate
      exact ⟨.submission ⟨.compiledKnowledgeV1, sourceBytes, ()⟩, rfl, rfl⟩

@[simp] theorem malformed_status :
    frontend.run .malformed = .malformed :=
  rfl

@[simp] theorem unknown_authority_status (name : String) :
    frontend.run (.unknownAuthority name) = .unsupported :=
  rfl

theorem verify_database_status (sourceBytes : ByteArray) :
    frontend.run (.verifyDatabase sourceBytes) =
      if verifiedB sourceBytes then
        .accepted ⟨EvidenceKind.verifiedDatabase, sourceBytes⟩
      else
        .rejected ⟨EvidenceKind.verifiedDatabase, sourceBytes⟩ := by
  cases checked : verifiedB sourceBytes <;>
    simp [frontend, Frontend.run, authorityFamily, checker, checked,
      TypedSubmission.claim]

theorem accepted_database_has_insertion_origins
    (sourceBytes : ByteArray)
    (accepted : frontend.run (.verifyDatabase sourceBytes) =
      .accepted ⟨EvidenceKind.verifiedDatabase, sourceBytes⟩) :
    StoredAssertionsHaveOrigins sourceBytes := by
  exact frontend.accepted_implies_meaning accepted

theorem compile_knowledge_status (sourceBytes : ByteArray) :
    frontend.run (.compileKnowledgeV1 sourceBytes) =
      if compiledKnowledgeV1B sourceBytes then
        .accepted ⟨EvidenceKind.compiledKnowledgeV1, sourceBytes⟩
      else
        .rejected ⟨EvidenceKind.compiledKnowledgeV1, sourceBytes⟩ := by
  cases checked : compiledKnowledgeV1B sourceBytes <;>
    simp [frontend, Frontend.run, authorityFamily,
      compiledKnowledgeV1Checker, checked, TypedSubmission.claim]

/-- Public NIK acceptance yields the exact checked inference package
existentially, while keeping its implementation representation out of the
logical status. -/
theorem accepted_compiled_knowledge_has_checked_projection
    (sourceBytes : ByteArray)
    (accepted : frontend.run (.compileKnowledgeV1 sourceBytes) =
      .accepted ⟨EvidenceKind.compiledKnowledgeV1, sourceBytes⟩) :
    CompiledKnowledgeV1 sourceBytes := by
  exact frontend.accepted_implies_meaning accepted

/-! ## Positive and negative executable witnesses -/

namespace Canary

def verifiedSource : ByteArray :=
  "$c |- $. ax $a |- $. th $p |- $= ax $.".toUTF8

def incompleteSource : ByteArray :=
  "$c |- $. ax $a |- $. th $p |- $= ? $.".toUTF8

def malformedSource : ByteArray :=
  "$c |- $. th $p".toUTF8

#guard verifiedB verifiedSource

#guard !verifiedB incompleteSource

#guard !verifiedB malformedSource

#guard compiledKnowledgeV1B verifiedSource

#guard !compiledKnowledgeV1B incompleteSource

#guard !compiledKnowledgeV1B malformedSource

end Canary

end Mettapedia.Languages.Metamath.DatabaseNIKAuthority
