import Mettapedia.Languages.Metamath.InferenceSourceAdmission

/-!
# Executable adversarial audit for canonical Metamath admission

This executable checks source-binding failures that are awkward to express as
closed compile-time fixtures because they use real files and the include-aware
IO frontend.  It consumes paths supplied by the gate and prints no paths.
-/

namespace Mettapedia.Languages.Metamath.InferenceSourceAdmissionAudit

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.CheckedSource
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceSourceAdmission

private def metadata : SourceMetadata :=
  { systemId := "metamath-audit"
    revision := "mm-lean4-sound-default/inference-projection-v1"
    assumptions := { entries := [] }
    profiles :=
      { entries :=
          [{ name := "metamath-inference-projection"
             version := "v1"
             payload := .apply "ExactPremisesWithDV" [] }] } }

private def preparedInput (bytes : ByteArray) : Option AdmissionInput :=
  match prepareBytes
      { sourceBytes := bytes, targetLabel := some "th1", metadata } with
  | .ok input => some input
  | .error _ => none

private def changedBytesChangeIdentity (bytes : ByteArray) : Bool :=
  let changed := bytes ++ "\n$( changed-byte audit $)\n".toUTF8
  match preparedInput bytes, preparedInput changed with
  | some original, some modified =>
      original.generatedSource.identity.artifactDigest !=
        modified.generatedSource.identity.artifactDigest
  | _, _ => false

private def finalTargetIsPresentAndNotFresh (bytes : ByteArray) : Bool :=
  let database := Metamath.Verify.checkBytes bytes .soundDefault
  database.error?.isNone &&
    (database.find? "th1").isSome &&
    (projectForMode (some "th1") database).isNone

private def boundaryUsesTargetAbsentPrefix (bytes : ByteArray) : Bool :=
  match extractTargetBoundary bytes "th1" with
  | .ok boundary => (boundary.prefixDB.find? "th1").isNone
  | .error _ => false

private def replacementPresentationRejects (bytes : ByteArray) : Bool :=
  match preparedInput bytes with
  | none => false
  | some input =>
      let source := input.generatedSource
      match source.definition.rules with
      | [] => false
      | rule :: rules =>
          validationError
              ({ source with
                definition :=
                  { source.definition with rules := rule :: rule :: rules } }).validate ==
            some .invalidDefinition

private def alteredAssumptionsReject (bytes : ByteArray) : Bool :=
  match preparedInput bytes with
  | none => false
  | some input =>
      let source := input.generatedSource
      let assumption : SourceAssumption :=
        { id := "audit-assumption", statement := .apply "Audit" [] }
      validationError
          ({ source with
            assumptions := { entries := [assumption, assumption] } }).validate ==
        some .invalidAssumptionLedger

private def alteredProfilesReject (bytes : ByteArray) : Bool :=
  match preparedInput bytes with
  | none => false
  | some input =>
      validationError
          ({ input.generatedSource with
            profiles := { entries := [] } }).validate ==
        some .missingProfile

private def rejectedReaderInputRejects (bytes : ByteArray) : Bool :=
  match prepareBytes
      { sourceBytes := bytes, targetLabel := none, metadata } with
  | .error .readerRejected => true
  | _ => false

private def dvViolationRejects (bytes : ByteArray) : Bool :=
  let database := Metamath.Verify.checkBytes bytes .soundDefault
  database.parseErrorCode?.map Metamath.Verify.ParseErrorCode.toNat ==
      some Metamath.Verify.ParseErrorCode.disjointVariableViolation.toNat &&
    (database.find? "th").isNone

private def malformedIncludeRejects (path : String) : IO Bool := do
  let result <- prepare <| .canonicalFile
    { sourcePath := path
      targetLabel := none
      verifiedArtifactDigest := "sha256:audit-malformed-include"
      metadata }
  pure <| match result with
    | .error .readerRejected => true
    | _ => false

def main (arguments : List String) : IO UInt32 := do
  let (sourcePath, rejectedPath, dvViolationPath, malformedIncludePath) <-
    match arguments with
    | [sourcePath, rejectedPath, dvViolationPath, malformedIncludePath] =>
        pure (sourcePath, rejectedPath, dvViolationPath, malformedIncludePath)
    | _ =>
        IO.eprintln
          "usage: InferenceSourceAdmissionAudit <demo0.mm> <rejected.mm> <dv-violation.mm> <malformed-include.mm>"
        return 2
  let sourceBytes <- IO.FS.readBinFile sourcePath
  let rejectedBytes <- IO.FS.readBinFile rejectedPath
  let dvViolationBytes <- IO.FS.readBinFile dvViolationPath
  let checks :=
    [ changedBytesChangeIdentity sourceBytes
    , finalTargetIsPresentAndNotFresh sourceBytes
    , boundaryUsesTargetAbsentPrefix sourceBytes
    , replacementPresentationRejects sourceBytes
    , alteredAssumptionsReject sourceBytes
    , alteredProfilesReject sourceBytes
    , rejectedReaderInputRejects rejectedBytes
    , dvViolationRejects dvViolationBytes
    , (← malformedIncludeRejects malformedIncludePath) ]
  if checks.all id then
    IO.println "MMCanonicalAdmissionNegativeSummary 9 9 0"
    return 0
  else
    IO.eprintln s!"MM canonical admission audit failed: {checks}"
    return 1

end Mettapedia.Languages.Metamath.InferenceSourceAdmissionAudit

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.Metamath.InferenceSourceAdmissionAudit.main arguments
