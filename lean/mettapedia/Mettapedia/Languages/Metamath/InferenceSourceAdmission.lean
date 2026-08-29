import MeTTailCore.Crypto.SHA256
import Mettapedia.GSLT.LanguageDef.CheckedSource
import Mettapedia.Languages.Metamath.InferenceOneShotByteLog
import Mettapedia.Languages.Metamath.InferenceProjection

open Mettapedia.GSLT.LanguageDef

/-!
# Canonical Metamath source admission

This module is the checked waist from an accepted `mm-lean4` source run to a
source-indexed generic inference definition.  It does not implement a second
Metamath reader.  Exact-byte inputs use the certified token log whose erasure
is `Metamath.Verify.checkBytes`; include-bearing inputs use the canonical
include-aware `Metamath.Verify.check` entrypoint.

The caller supplies metadata, source material, and an optional theorem label.
It never supplies a rule table.  Database admission projects the accepted
database directly.  Theorem admission obtains its pre-insertion database from
an observed proof-ingress event, checks that the target is absent there, and
uses `projectForFreshTarget?`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.InferenceSourceAdmission

open Mettapedia.GSLT.LanguageDef.CheckedSource
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceProjection

abbrev TokenCall :=
  Mettapedia.Languages.Metamath.InferenceOneShotByteLog.TokenCall

abbrev CheckBytesRun :=
  Mettapedia.Languages.Metamath.InferenceOneShotByteLog.CheckBytesRun

/-! ## Exact-byte reader evidence -/

structure SourceMetadata where
  systemId : String
  revision : String
  assumptions : AssumptionLedger
  profiles : ProfileLedger
deriving Repr

def digestBytes (bytes : ByteArray) : String :=
  "sha256:" ++ MeTTailCore.Crypto.SHA256.toHexString
    (MeTTailCore.Crypto.SHA256.sha256Bytes bytes)

def SourceMetadata.identityFor (metadata : SourceMetadata)
    (bytes : ByteArray) : SourceIdentity :=
  { systemId := metadata.systemId
    revision := metadata.revision
    artifactDigest := digestBytes bytes }

structure ObservedProofToken where
  before : Metamath.Verify.ParserState
  proofState : Metamath.Verify.ProofState
  token : ByteSlice

private def tokenOfCall (call : TokenCall) : ByteSlice :=
  Mettapedia.Languages.Metamath.InferenceOneShotByteLog.Raw.TokenOrigin.token
    call.origin

def targetProofTokens (targetLabel : String)
    (calls : List TokenCall) : List ObservedProofToken :=
  calls.filterMap fun call =>
    match call.before.tokp with
    | .proof proofState =>
        let token := tokenOfCall call
        if proofState.label == targetLabel &&
            !token.eqArray "$.".toAscii && !token.eqArray "$(".toAscii then
          some { before := call.before, proofState, token }
        else
          none
    | _ => none

def proofIngressAgrees (targetLabel : String)
    (first : ObservedProofToken)
    (observed : List ObservedProofToken) : Bool :=
  observed.all fun entry =>
    entry.proofState.label == targetLabel &&
      entry.proofState.fmla == first.proofState.fmla &&
      entry.proofState.frame.dj == first.proofState.frame.dj &&
      entry.proofState.frame.hyps == first.proofState.frame.hyps

def insertedTargetAgrees (targetLabel : String)
    (database : RuntimeDB) (first : ObservedProofToken) : Bool :=
  match database.find? targetLabel with
  | some (.assert formula frame embeddedLabel) =>
      formula == first.proofState.fmla &&
        frame.dj == first.proofState.frame.dj &&
        frame.hyps == first.proofState.frame.hyps &&
        embeddedLabel == targetLabel
  | _ => false

/-- A target boundary is indexed by the exact bytes and label.  Its parser run
is a certified `checkBytes` run; the chosen ingress event is provably the head
of the filtered events from that same run. -/
structure TargetBoundary (sourceBytes : ByteArray) (targetLabel : String) where
  run : CheckBytesRun sourceBytes .soundDefault
  run_eq : run =
    Mettapedia.Languages.Metamath.InferenceOneShotByteLog.checkBytesLogged
      sourceBytes .soundDefault
  observed : List ObservedProofToken
  observed_eq : observed = targetProofTokens targetLabel run.calls
  first : ObservedProofToken
  first_is_head : observed.head? = some first
  readerAccepted : run.db.error?.isNone = true
  targetAbsent : first.before.db.find? targetLabel = none
  ingressAgrees : proofIngressAgrees targetLabel first observed = true
  insertedAgrees : insertedTargetAgrees targetLabel run.db first = true

namespace TargetBoundary

def prefixDB {sourceBytes : ByteArray} {targetLabel : String}
    (boundary : TargetBoundary sourceBytes targetLabel) : RuntimeDB :=
  boundary.first.before.db

def proofTokens {sourceBytes : ByteArray} {targetLabel : String}
    (boundary : TargetBoundary sourceBytes targetLabel) : List ByteSlice :=
  boundary.observed.map (fun entry => entry.token)

theorem readerDB_eq_checkBytes {sourceBytes : ByteArray}
    {targetLabel : String}
    (boundary : TargetBoundary sourceBytes targetLabel) :
    boundary.run.db = Metamath.Verify.checkBytes sourceBytes .soundDefault := by
  rw [boundary.run_eq]
  exact
    Mettapedia.Languages.Metamath.InferenceOneShotByteLog.checkBytesLogged_db_eq_checkBytes
      sourceBytes .soundDefault

end TargetBoundary

/-! ## Stack-bounded streaming traversal for larger exact-byte sources -/

private structure ChunkedTokenLog where
  state : Metamath.Verify.ParserState
  calls : List TokenCall

private def feedLoggedChunks (bytes : ByteArray) (offset : Nat)
    (state : Metamath.Verify.ParserState) (calls : List TokenCall) :
    ChunkedTokenLog :=
  if offset < bytes.size then
    let stop := min (offset + 4096) bytes.size
    let chunk := bytes.extract offset stop
    let run :=
      Mettapedia.Languages.Metamath.InferenceOneShotByteLog.Raw.feedAllLogged
        state offset chunk
    feedLoggedChunks bytes stop run.state (calls ++ run.calls)
  else
    { state, calls }
termination_by bytes.size - offset
decreasing_by omega

private def chunkedTokenLog (bytes : ByteArray)
    (config : Metamath.Verify.ModeConfig) :
    Mettapedia.Languages.Metamath.InferenceOneShotByteLog.Raw.CheckBytesRun :=
  let initialDB : RuntimeDB := { (default : RuntimeDB) with config }
  let initialState : Metamath.Verify.ParserState :=
    { (default : Metamath.Verify.ParserState) with db := initialDB }
  let feed := feedLoggedChunks bytes 0 initialState []
  let done :=
    Mettapedia.Languages.Metamath.InferenceOneShotByteLog.Raw.doneLogged
      feed.state bytes.size
  { db := done.db, calls := feed.calls ++ done.calls }

def frameSnapshot (frame : RuntimeFrame) : String :=
  let pairs := frame.dj.toList.map fun pair => (pair.1, pair.2)
  reprStr pairs ++ ":" ++ reprStr frame.hyps.toList

def objectSnapshot : Metamath.Verify.Object -> String
  | .const name => "C:" ++ name
  | .var name => "V:" ++ name
  | .hyp essential formula name =>
      "H:" ++ reprStr essential ++ ":" ++ reprStr formula.toList ++ ":" ++ name
  | .assert formula frame name =>
      "A:" ++ reprStr formula.toList ++ ":" ++ frameSnapshot frame ++ ":" ++ name

/-- Stable comparison of every logical database entry, the active frame, and
scope stack.  The object map is compared through the projection's sorted
entry view so hash-table bucket layout is irrelevant. -/
def databaseSnapshot (database : RuntimeDB) : String :=
  let entries := objectEntries database |>.map fun entry =>
    (entry.1, objectSnapshot entry.2)
  frameSnapshot database.frame ++ "|" ++
    reprStr database.scopes.toList ++ "|" ++ reprStr entries

structure ChunkedTargetBoundary (sourceBytes : ByteArray)
    (targetLabel : String) where
  run : Mettapedia.Languages.Metamath.InferenceOneShotByteLog.Raw.CheckBytesRun
  observed : List ObservedProofToken
  observed_eq : observed = targetProofTokens targetLabel run.calls
  first : ObservedProofToken
  first_is_head : observed.head? = some first
  readerAccepted :
    (Metamath.Verify.checkBytes sourceBytes .soundDefault).error?.isNone = true
  traversalAccepted : run.db.error?.isNone = true
  targetAbsent : first.before.db.find? targetLabel = none
  ingressAgrees : proofIngressAgrees targetLabel first observed = true
  readerInsertedAgrees :
    insertedTargetAgrees targetLabel
      (Metamath.Verify.checkBytes sourceBytes .soundDefault) first = true
  traversalInsertedAgrees :
    insertedTargetAgrees targetLabel run.db first = true
  finalDatabaseAgrees :
    (databaseSnapshot run.db ==
      databaseSnapshot
        (Metamath.Verify.checkBytes sourceBytes .soundDefault)) = true

namespace ChunkedTargetBoundary

def prefixDB {sourceBytes : ByteArray} {targetLabel : String}
    (boundary : ChunkedTargetBoundary sourceBytes targetLabel) : RuntimeDB :=
  boundary.first.before.db

def proofTokens {sourceBytes : ByteArray} {targetLabel : String}
    (boundary : ChunkedTargetBoundary sourceBytes targetLabel) :
    List ByteSlice :=
  boundary.observed.map (fun entry => entry.token)

end ChunkedTargetBoundary

inductive AdmissionError where
  | readerRejected
  | targetProofIngressMissing
  | targetAlreadyPresent
  | targetIngressDisagrees
  | targetInsertionDisagrees
  | readerTraversalDisagrees
  | projectionFailed
  | sourceValidationFailed :
      Mettapedia.GSLT.LanguageDef.CheckedSource.ValidationError ->
      AdmissionError
  | theoremTargetRequired
  | proofRejected
  | includeTargetNotAvailable
deriving Repr, DecidableEq

def extractTargetBoundary (sourceBytes : ByteArray) (targetLabel : String) :
    Except AdmissionError (TargetBoundary sourceBytes targetLabel) := do
  let run :=
    Mettapedia.Languages.Metamath.InferenceOneShotByteLog.checkBytesLogged
      sourceBytes .soundDefault
  if hAccepted : run.db.error?.isNone then
    let observed := targetProofTokens targetLabel run.calls
    match hFirst : observed.head? with
    | none => throw .targetProofIngressMissing
    | some first =>
        if hAbsent : first.before.db.find? targetLabel = none then
          if hIngress : proofIngressAgrees targetLabel first observed then
            if hInserted : insertedTargetAgrees targetLabel run.db first then
              pure
                { run
                  run_eq := rfl
                  observed
                  observed_eq := rfl
                  first
                  first_is_head := hFirst
                  readerAccepted := hAccepted
                  targetAbsent := hAbsent
                  ingressAgrees := hIngress
                  insertedAgrees := hInserted }
            else
              throw .targetInsertionDisagrees
          else
            throw .targetIngressDisagrees
        else
          throw .targetAlreadyPresent
  else
    throw .readerRejected

def extractChunkedTargetBoundary (sourceBytes : ByteArray)
    (targetLabel : String) :
    Except AdmissionError (ChunkedTargetBoundary sourceBytes targetLabel) := do
  let readerDB := Metamath.Verify.checkBytes sourceBytes .soundDefault
  if hReaderAccepted : readerDB.error?.isNone then
    let run := chunkedTokenLog sourceBytes .soundDefault
    if hTraversalAccepted : run.db.error?.isNone then
      let observed := targetProofTokens targetLabel run.calls
      match hFirst : observed.head? with
      | none => throw .targetProofIngressMissing
      | some first =>
          if hAbsent : first.before.db.find? targetLabel = none then
            if hIngress : proofIngressAgrees targetLabel first observed then
              if hReaderInserted :
                  insertedTargetAgrees targetLabel readerDB first then
                if hTraversalInserted :
                    insertedTargetAgrees targetLabel run.db first then
                  if hDatabase :
                      databaseSnapshot run.db == databaseSnapshot readerDB then
                    pure
                      { run
                        observed
                        observed_eq := rfl
                        first
                        first_is_head := hFirst
                        readerAccepted := hReaderAccepted
                        traversalAccepted := hTraversalAccepted
                        targetAbsent := hAbsent
                        ingressAgrees := hIngress
                        readerInsertedAgrees := hReaderInserted
                        traversalInsertedAgrees := hTraversalInserted
                        finalDatabaseAgrees := hDatabase }
                  else
                    throw .readerTraversalDisagrees
                else
                  throw .targetInsertionDisagrees
              else
                throw .targetInsertionDisagrees
            else
              throw .targetIngressDisagrees
          else
            throw .targetAlreadyPresent
    else
      throw .readerRejected
  else
    throw .readerRejected

/-! ## One generic exact-byte request -/

structure AdmissionRequest where
  sourceBytes : ByteArray
  targetLabel : Option String
  metadata : SourceMetadata

/-- The parsed state is indexed by the request's optional target.  There is no
constructor taking a caller-supplied database. -/
inductive ParsedSource (sourceBytes : ByteArray) : Option String -> Type where
  | database : ParsedSource sourceBytes none
  | target
      (targetLabel : String)
      (boundary : TargetBoundary sourceBytes targetLabel) :
      ParsedSource sourceBytes (some targetLabel)
  | chunkedTarget
      (targetLabel : String)
      (boundary : ChunkedTargetBoundary sourceBytes targetLabel) :
      ParsedSource sourceBytes (some targetLabel)

namespace ParsedSource

def readerDB {sourceBytes : ByteArray} {targetLabel : Option String} :
    ParsedSource sourceBytes targetLabel -> RuntimeDB
  | .database => Metamath.Verify.checkBytes sourceBytes .soundDefault
  | .target _ _ | .chunkedTarget _ _ =>
      Metamath.Verify.checkBytes sourceBytes .soundDefault

def prefixDB {sourceBytes : ByteArray} {targetLabel : Option String} :
    ParsedSource sourceBytes targetLabel -> RuntimeDB
  | .database => Metamath.Verify.checkBytes sourceBytes .soundDefault
  | .target _ boundary => boundary.prefixDB
  | .chunkedTarget _ boundary => boundary.prefixDB

theorem readerDB_eq_checkBytes {sourceBytes : ByteArray}
    {targetLabel : Option String}
    (parsed : ParsedSource sourceBytes targetLabel) :
    parsed.readerDB =
      Metamath.Verify.checkBytes sourceBytes .soundDefault := by
  cases parsed with
  | database => rfl
  | target targetLabel boundary =>
      rfl
  | chunkedTarget targetLabel boundary =>
      rfl

end ParsedSource

/-- Database-only admission explicitly starts with `projectPrefix?`; theorem
admission uses the target-absence wrapper `projectForFreshTarget?`. -/
def projectForMode (targetLabel : Option String) (database : RuntimeDB) :
    Option ValidatedCalculusLanguageDef :=
  match targetLabel with
  | none => do
      let projection <- projectPrefix? database
      let definition <- calculusLanguageDefOfProjection? projection
      definition.validate?
  | some label => projectForFreshTarget? database label

structure AdmissionInput where
  request : AdmissionRequest
  parsed : ParsedSource request.sourceBytes request.targetLabel
  definition : ValidatedCalculusLanguageDef
  definitionGenerated :
    projectForMode request.targetLabel parsed.prefixDB = some definition

private def finishPreparation (request : AdmissionRequest)
    (parsed : ParsedSource request.sourceBytes request.targetLabel) :
    Except AdmissionError AdmissionInput :=
  match hDefinition :
      projectForMode request.targetLabel parsed.prefixDB with
  | none => .error .projectionFailed
  | some definition =>
      .ok
        { request
          parsed
          definition
          definitionGenerated := hDefinition }

def AdmissionInput.generatedSource (input : AdmissionInput) : GSLTSource :=
  { identity := input.request.metadata.identityFor input.request.sourceBytes
    assumptions := input.request.metadata.assumptions
    profiles := input.request.metadata.profiles
    definition := input.definition.1 }

def prepareBytes (request : AdmissionRequest) :
    Except AdmissionError AdmissionInput :=
  match hTarget : request.targetLabel with
  | none =>
      let database :=
        Metamath.Verify.checkBytes request.sourceBytes .soundDefault
      if database.error?.isNone then
        let parsed : ParsedSource request.sourceBytes none :=
          .database
        finishPreparation request (hTarget.symm ▸ parsed)
      else
        .error .readerRejected
  | some targetLabel =>
      let extracted :=
        if request.sourceBytes.size <= 8192 then
          (extractTargetBoundary request.sourceBytes targetLabel).map fun boundary =>
            ParsedSource.target targetLabel boundary
        else
          (extractChunkedTargetBoundary request.sourceBytes targetLabel).map fun boundary =>
            ParsedSource.chunkedTarget targetLabel boundary
      match extracted with
      | .error error => .error error
      | .ok parsed =>
          finishPreparation request (hTarget.symm ▸ parsed)

def admit (input : AdmissionInput) :
    Except AdmissionError CheckedGSLT :=
  input.generatedSource.validate.mapError .sourceValidationFailed

/-- Successful admission preserves the complete generated package, including
identity, assumptions, profiles, and its calculus language definition. -/
theorem admit_source_eq_generated {input : AdmissionInput}
    {checked : CheckedGSLT} (hadmit : admit input = .ok checked) :
    checked.source = input.generatedSource := by
  unfold admit at hadmit
  cases hvalidate : input.generatedSource.validate with
  | error error =>
      simp [hvalidate, Except.mapError] at hadmit
  | ok admitted =>
      have hchecked : admitted = checked := by
        simpa [hvalidate, Except.mapError] using hadmit
      subst checked
      exact GSLTSource.validate_source_eq hvalidate

/-- The source exposed by successful admission contains exactly the calculus
language definition recomputed from the accepted parser state selected by the
same request. -/
theorem admit_definition_is_generated {input : AdmissionInput}
    {checked : CheckedGSLT} (hadmit : admit input = .ok checked) :
    (projectForMode input.request.targetLabel input.parsed.prefixDB).map
        (fun definition => definition.1) =
      some checked.source.definition := by
  unfold admit at hadmit
  cases hvalidate : input.generatedSource.validate with
  | error error =>
      simp [hvalidate, Except.mapError] at hadmit
  | ok admitted =>
      have hsource := GSLTSource.validate_source_eq hvalidate
      have hchecked : admitted = checked := by
        simpa [hvalidate, Except.mapError] using hadmit
      subst checked
      rw [input.definitionGenerated]
      simp [hsource, AdmissionInput.generatedSource]

/-- A checked theorem artifact binds the exact admitted source, target label,
goal, and raw proof, and retains the ordinary checker result as evidence. -/
structure CheckedTheoremArtifact where
  input : AdmissionInput
  checked : CheckedGSLT
  targetLabel : String
  target_eq : input.request.targetLabel = some targetLabel
  admission_eq : admit input = .ok checked
  goal : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
  proof : RawProof
  proofAccepted : checked.checkRaw goal proof = true

def bindTheoremArtifact (input : AdmissionInput)
    (goal : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) (proof : RawProof) :
    Except AdmissionError CheckedTheoremArtifact :=
  match hTarget : input.request.targetLabel with
  | none => .error .theoremTargetRequired
  | some targetLabel =>
      match hAdmission : admit input with
      | .error error => .error error
      | .ok checked =>
          if hProof : checked.checkRaw goal proof then
            .ok
              { input
                checked
                targetLabel
                target_eq := hTarget
                admission_eq := hAdmission
                goal
                proof
                proofAccepted := hProof }
          else
            .error .proofRejected

/-! ## Include-aware database admission -/

structure IncludeRequest where
  sourcePath : String
  targetLabel : Option String
  verifiedArtifactDigest : String
  metadata : SourceMetadata

structure IncludeAdmissionInput where
  rootBytes : ByteArray
  artifactDigest : String
  metadata : SourceMetadata
  readerDB : RuntimeDB
  definition : ValidatedCalculusLanguageDef
  definitionGenerated :
    projectForMode none readerDB = some definition

def IncludeAdmissionInput.generatedSource
    (input : IncludeAdmissionInput) : GSLTSource :=
  { identity :=
      { systemId := input.metadata.systemId
        revision := input.metadata.revision
        artifactDigest := input.artifactDigest }
    assumptions := input.metadata.assumptions
    profiles := input.metadata.profiles
    definition := input.definition.1 }

def admitInclude (input : IncludeAdmissionInput) :
    Except AdmissionError CheckedGSLT :=
  input.generatedSource.validate.mapError .sourceValidationFailed

theorem admitInclude_source_eq_generated
    {input : IncludeAdmissionInput} {checked : CheckedGSLT}
    (hadmit : admitInclude input = .ok checked) :
    checked.source = input.generatedSource := by
  unfold admitInclude at hadmit
  cases hvalidate : input.generatedSource.validate with
  | error error =>
      simp [hvalidate, Except.mapError] at hadmit
  | ok admitted =>
      have hchecked : admitted = checked := by
        simpa [hvalidate, Except.mapError] using hadmit
      subst checked
      exact GSLTSource.validate_source_eq hvalidate

theorem admitInclude_definition_is_generated
    {input : IncludeAdmissionInput} {checked : CheckedGSLT}
    (hadmit : admitInclude input = .ok checked) :
    (projectForMode none input.readerDB).map
        (fun definition => definition.1) =
      some checked.source.definition := by
  unfold admitInclude at hadmit
  cases hvalidate : input.generatedSource.validate with
  | error error =>
      simp [hvalidate, Except.mapError] at hadmit
  | ok admitted =>
      have hsource := GSLTSource.validate_source_eq hvalidate
      have hchecked : admitted = checked := by
        simpa [hvalidate, Except.mapError] using hadmit
      subst checked
      rw [input.definitionGenerated]
      simp [hsource, IncludeAdmissionInput.generatedSource]

inductive PreparedAdmission where
  | exactBytes (input : AdmissionInput)
  | includeDatabase (input : IncludeAdmissionInput)

inductive SourceRequest where
  | exactBytes (request : AdmissionRequest)
  | canonicalFile (request : IncludeRequest)

/-- The single public preparation operation.  Include-aware theorem-boundary
logging is not claimed: such a request reports that precise limitation instead
of switching to raw file loading or a hand-authored language definition. -/
def prepare : SourceRequest -> IO (Except AdmissionError PreparedAdmission)
  | .exactBytes request =>
      pure <| (prepareBytes request).map .exactBytes
  | .canonicalFile request => do
      if request.targetLabel.isSome then
        return .error .includeTargetNotAvailable
      let rootBytes <- IO.FS.readBinFile request.sourcePath
      let database <- Metamath.Verify.check request.sourcePath .soundDefault
      if !database.error?.isNone then
        return .error .readerRejected
      match hDefinition : projectForMode none database with
      | none => return .error .projectionFailed
      | some definition =>
          return .ok <| .includeDatabase
            { rootBytes
              artifactDigest := request.verifiedArtifactDigest
              metadata := request.metadata
              readerDB := database
              definition
              definitionGenerated := hDefinition }

end Mettapedia.Languages.Metamath.InferenceSourceAdmission
