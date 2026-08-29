import Mettapedia.Languages.Metamath.SourceGSLTParserPrefixBisimulation

open Mettapedia.GSLT.LanguageDef

/-!
# Statement outcomes for the Metamath source GSLT reader refinement

Verified proof judgments remain separate from accepted statements containing
the explicit unknown marker.  This module first characterizes the common
reader transition, then exposes the incomplete outcome without manufacturing
proof evidence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.SourceGSLTParserStatementOutcomes

open Metamath.Verify
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.InferenceOneShotByteLog
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceGSLTLexicalClosure
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceGSLTRuntimeStateAgreement
open Mettapedia.Languages.Metamath.SourceGSLTRuntimeCoEvolution
open Mettapedia.Languages.Metamath.SourceGSLTParserPrefixBisimulation

/-- A normal-proof token cannot be mistaken for any reader command or for the
compressed-proof opener.  The result follows from the authored proof-token
class: either a label whose first byte is neither `$` nor `(`, or exactly
the unknown marker `?`. -/
theorem proofTokenValid_excludes_reader_delimiters
    {bytes : List UInt8} (valid : proofTokenValid bytes = true) :
    bytes ≠ "$(".toAscii.data.toList ∧
      bytes ≠ "$[".toAscii.data.toList ∧
      bytes ≠ "$.".toAscii.data.toList ∧
      bytes ≠ "(".toAscii.data.toList := by
  have cases : labelBytesValid bytes = true ∨
      bytes =
        SourceGSLTStatementPlan.sourceStatementPlan.unknownProof.codepoints.map
          UInt8.ofNat := by
    simpa [proofTokenValid] using valid
  rcases cases with labelValid | unknownBytes
  · cases bytes with
    | nil => simp [labelBytesValid] at labelValid
    | cons head tail =>
        have headNeDollar := labelBytesValid_head_ne_dollar labelValid
        have headNeOpen := labelBytesValid_head_ne_open labelValid
        constructor
        · change head :: tail ≠ [36, 40]
          exact nonDollarHead_ne_commandPair headNeDollar
        constructor
        · change head :: tail ≠ [36, 91]
          exact nonDollarHead_ne_commandPair headNeDollar
        constructor
        · change head :: tail ≠ [36, 46]
          exact nonDollarHead_ne_commandPair headNeDollar
        · change head :: tail ≠ [40]
          intro equality
          apply headNeOpen
          have openByte : (40 : UInt8) = '('.toUInt8 := by decide
          rw [← openByte]
          exact (List.cons.inj equality).1
  · rw [unknownBytes]
    decide

/-- Successful normal-mode execution, including the permitted unknown marker,
preserves the theorem label. -/
theorem feedProof_goNormal_ok_preserves_label
    (parser : ParserState) (token : ByteSlice)
    (before after : RuntimeProofState)
    (execution : ParserState.feedProof.goNormal parser token before =
      .ok after) :
    after.label = before.label := by
  unfold ParserState.feedProof.goNormal at execution
  by_cases unknown : token.eqArray "?".toAscii
  · by_cases rejected : parser.db.config.rejectUnknownSteps
    · simp [unknown, rejected] at execution
    · simp [unknown, rejected] at execution
      injection execution with equality
      subst after
      simp [ProofState.push]
  · by_cases labelOK : (toLabel token).fst
    · have step :
          parser.db.stepNormal before (toLabel token).snd = .ok after := by
        simpa [unknown, labelOK] using execution
      exact Metamath.PrefixProvenance.stepNormal_preserves_label
        parser.db before after (toLabel token).snd step
    · simp [unknown, labelOK] at execution

/-- Successful normal-mode execution preserves normal mode. -/
theorem feedProof_goNormal_ok_preserves_mode
    (parser : ParserState) (token : ByteSlice)
    (before after : RuntimeProofState)
    (beforeNormal : before.ptp = .normal)
    (execution : ParserState.feedProof.goNormal parser token before =
      .ok after) :
    after.ptp = .normal := by
  unfold ParserState.feedProof.goNormal at execution
  by_cases unknown : token.eqArray "?".toAscii
  · by_cases rejected : parser.db.config.rejectUnknownSteps
    · simp [unknown, rejected] at execution
    · simp [unknown, rejected] at execution
      injection execution with equality
      subst after
      simpa [ProofState.push] using beforeNormal
  · by_cases labelOK : (toLabel token).fst
    · have step :
          parser.db.stepNormal before (toLabel token).snd = .ok after := by
        simpa [unknown, labelOK] using execution
      exact (Metamath.PrefixProvenance.stepNormal_preserves_ptp
        parser.db before after (toLabel token).snd step).trans beforeNormal
    · simp [unknown, labelOK] at execution

/-- One accepted normal-proof token, allowing `?`, with only the invariants
needed at the statement boundary.  The first token may arrive in `.start`;
every result is in `.normal`. -/
structure ReaderNormalTokenStep
    (db : DB) (before : RuntimeProofState)
    (final : ParserObservedState) : Type where
  after : RuntimeProofState
  final_observed : final = ⟨db, .proof after⟩
  after_normal : after.ptp = .normal
  label_eq : after.label = before.label
  formula_eq : after.fmla = before.fmla
  frame_eq : after.frame = before.frame

/-- Rebase one retained source-valid normal-proof token onto the theorem's
fixed parser anchor.  This is deliberately weaker than the verified normal
ledger: an unknown token preserves statement identity but supplies no proof
step. -/
noncomputable def retainedCall_normalTokenStep
    (anchor : ParserState)
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB}
    {before : RuntimeProofState} {bytes : List UInt8}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before = ⟨db, .proof before⟩)
    (entryBytes : entry.1.bytes = bytes)
    (valid : proofTokenValid bytes = true)
    (afterErrorFree : call.after.db.error? = none)
    (anchorDB : anchor.db = db)
    (beforeMode : before.ptp = .start ∨ before.ptp = .normal) :
    ReaderNormalTokenStep db before (parserObservedState call.after) := by
  have boundaries := proofTokenValid_excludes_reader_delimiters valid
  let feed := retainedCall_proofFeed anchor significant before_eq entryBytes
    boundaries.1 boundaries.2.1 boundaries.2.2.1 afterErrorFree anchorDB
  have notOpen : call.origin.token.eqArray "(".toAscii = false := by
    simpa [shippedToken] using
      retainedCall_eqArray_false significant (by
        rw [entryBytes]
        exact boundaries.2.2.2)
  have normalExecution :
      ParserState.feedProof.goNormal anchor call.origin.token
          { before with ptp := .normal } = .ok feed.after := by
    rcases beforeMode with beforeStart | beforeNormal
    · simpa [ParserState.feedProof.go, beforeStart, notOpen] using feed.go
    · have normalBefore : { before with ptp := .normal } = before := by
        cases before
        simp_all
      rw [normalBefore]
      simpa [ParserState.feedProof.go, beforeNormal] using feed.go
  have core := Metamath.ParserOps.feedProof_goNormal_ok_preserves_core
    anchor call.origin.token { before with ptp := .normal } feed.after
      normalExecution
  have label := feedProof_goNormal_ok_preserves_label anchor
    call.origin.token { before with ptp := .normal } feed.after
      normalExecution
  have mode := feedProof_goNormal_ok_preserves_mode anchor
    call.origin.token { before with ptp := .normal } feed.after rfl
      normalExecution
  exact
    { after := feed.after
      final_observed := feed.observed_eq
      after_normal := mode
      label_eq := label
      formula_eq := core.1
      frame_eq := core.2 }

/-- Identity information retained after a nonempty accepted normal-proof body.
The stack is intentionally absent: once an unknown marker occurs, its contents
have no proof-theoretic authority. -/
structure ReaderNormalTokenRun
    (db : DB) (before : RuntimeProofState)
    (final : ParserObservedState) : Type where
  after : RuntimeProofState
  final_observed : final = ⟨db, .proof after⟩
  after_normal : after.ptp = .normal
  label_eq : after.label = before.label
  formula_eq : after.fmla = before.fmla
  frame_eq : after.frame = before.frame

/-- Iterate ordinary or unknown normal-proof tokens after normal mode has
already begun. -/
noncomputable def SpelledCallTrace.normalTokenTail
    (anchor : ParserState) {fileId : String} {db : DB}
    {before : RuntimeProofState} {names : List LocatedName}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId ⟨db, .proof before⟩
      (names.map LocatedName.name) entries final)
    (anchorDB : anchor.db = db)
    (beforeNormal : before.ptp = .normal)
    (charsets : ∀ name ∈ names, NameCharset proofTokenValid name) :
    ReaderNormalTokenRun db before final := by
  induction names generalizing before entries final with
  | nil =>
      simp only [List.map_nil] at trace
      cases trace
      exact
        { after := before
          final_observed := rfl
          after_normal := beforeNormal
          label_eq := rfl
          formula_eq := rfl
          frame_eq := rfl }
  | cons name rest ih =>
      simp only [List.map_cons] at trace
      cases trace with
      | @cons _ _ texts tailEntries text entry spelling significant
          afterErrorFree before_eq tail =>
          have nameCharset : NameCharset proofTokenValid name :=
            charsets name (by simp)
          let bytes := Classical.choose nameCharset
          have charsetFacts := Classical.choose_spec nameCharset
          have entryBytes : entry.1.bytes = bytes :=
            tokenText_injective (spelling.trans charsetFacts.2)
          let head := retainedCall_normalTokenStep anchor significant
            before_eq entryBytes charsetFacts.1 afterErrorFree anchorDB
              (.inr beforeNormal)
          have tail' := tail.reindexInitial head.final_observed
          have restCharsets :
              ∀ next ∈ rest, NameCharset proofTokenValid next := by
            intro next member
            exact charsets next (by simp [member])
          let result := ih tail' head.after_normal restCharsets
          exact
            { after := result.after
              final_observed := result.final_observed
              after_normal := result.after_normal
              label_eq := result.label_eq.trans head.label_eq
              formula_eq := result.formula_eq.trans head.formula_eq
              frame_eq := result.frame_eq.trans head.frame_eq }

/-- Execute a nonempty normal-proof body from the theorem anchor.  The first
token is handled separately because it performs the real `.start` to
`.normal` transition, including when that first token is `?`. -/
noncomputable def SpelledCallTrace.normalTokenBody
    (anchor : ParserState) {fileId : String} {db : DB}
    {before : RuntimeProofState} {first : LocatedName}
    {rest : List LocatedName}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId ⟨db, .proof before⟩
      ((first :: rest).map LocatedName.name) entries final)
    (anchorDB : anchor.db = db)
    (beforeStart : before.ptp = .start)
    (charsets : ∀ name ∈ first :: rest,
      NameCharset proofTokenValid name) :
    ReaderNormalTokenRun db before final := by
  simp only [List.map_cons] at trace
  cases trace with
  | @cons _ _ texts tailEntries text entry spelling significant
      afterErrorFree before_eq tail =>
      have firstCharset : NameCharset proofTokenValid first :=
        charsets first (by simp)
      let bytes := Classical.choose firstCharset
      have charsetFacts := Classical.choose_spec firstCharset
      have entryBytes : entry.1.bytes = bytes :=
        tokenText_injective (spelling.trans charsetFacts.2)
      let head := retainedCall_normalTokenStep anchor significant before_eq
        entryBytes charsetFacts.1 afterErrorFree anchorDB (.inl beforeStart)
      have tail' := tail.reindexInitial head.final_observed
      have restCharsets :
          ∀ next ∈ rest, NameCharset proofTokenValid next := by
        intro next member
        exact charsets next (by simp [member])
      let result :=
        Mettapedia.Languages.Metamath.SourceGSLTParserStatementOutcomes.SpelledCallTrace.normalTokenTail
          anchor tail' anchorDB head.after_normal restCharsets
      exact
        { after := result.after
          final_observed := result.final_observed
          after_normal := result.after_normal
          label_eq := result.label_eq.trans head.label_eq
          formula_eq := result.formula_eq.trans head.formula_eq
          frame_eq := result.frame_eq.trans head.frame_eq }

/-- Common reader acceptance for a nonempty normal `$p` body.  This proves
only the declaration transition and next prefix; proof evidence is supplied
separately when the body contains no unknown marker. -/
structure ReaderAcceptedNormalStatement
    (db : DB) (before after : SourceState) (label : String)
    (formula : ConstantHeadedFormula) (labels : List String)
    (final : ParserObservedState) : Type where
  inserted : insertAssertion? before label formula = some after
  nextPrefix : SourceParserPrefixAgrees after final

/-- Reconstruct the accepted normal statement transition directly from its
reader calls, without interpreting an unknown marker as a proof. -/
noncomputable def SpelledCallTrace.acceptedNormalStatement
    {fileId : String} {db : DB}
    {before after : SourceState}
    {label typecode firstStep : LocatedName}
    {body restSteps : List LocatedName}
    {bodySymbols : List Sym}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId ⟨db, .start⟩
      ((label.name :: "$p" ::
          (typecode :: body).map LocatedName.name ++ ["$="]) ++
        ((firstStep :: restSteps).map LocatedName.name ++ ["$."]))
      entries final)
    (agreement : RuntimeDBAgrees db before)
    (interruptEq : db.interrupt = false)
    (labelCharset : NameCharset labelBytesValid label)
    (typecodeCharset : NameCharset mathBytesValid typecode)
    (bodyCharsets :
      ∀ name ∈ body, NameCharset mathBytesValid name)
    (stepCharsets :
      ∀ name ∈ firstStep :: restSteps,
        NameCharset proofTokenValid name)
    (taggedFormula : tagBody before (typecode :: body) =
      .ok (.const typecode.name :: bodySymbols))
    (inserted : insertAssertion? before label.name
      ⟨typecode.name, bodySymbols⟩ = some after) :
    ReaderAcceptedNormalStatement db before after label.name
      ⟨typecode.name, bodySymbols⟩
      ((firstStep :: restSteps).map LocatedName.name) final := by
  let formulaPrefix : List String :=
    label.name :: "$p" ::
      (typecode :: body).map LocatedName.name ++ ["$="]
  let proofSuffix : List String :=
    (firstStep :: restSteps).map LocatedName.name ++ ["$."]
  have trace' : SpelledCallTrace fileId ⟨db, .start⟩
      (formulaPrefix ++ proofSuffix) entries final := by
    simpa [formulaPrefix, proofSuffix] using trace
  obtain ⟨proofInitial, formulaTrace, proofTrace⟩ := trace'.splitAppend
  have formulaTrace' : SpelledCallTrace fileId ⟨db, .start⟩
      (label.name :: "$p" ::
        (typecode :: body).map LocatedName.name ++ ["$="])
      (entries.take formulaPrefix.length) proofInitial := by
    simpa [formulaPrefix] using formulaTrace
  let anchored := formulaTrace'.provableFormula_parserAnchor agreement
    (insertAssertion?_valid_before inserted)
    labelCharset typecodeCharset bodyCharsets taggedFormula
  let anchor := anchored.2
  have proofTrace' : SpelledCallTrace fileId proofInitial
      ((firstStep :: restSteps).map LocatedName.name ++ ["$."])
      (entries.drop formulaPrefix.length) final := by
    simpa [proofSuffix] using proofTrace
  obtain ⟨proofFinal, bodyTrace, finishTrace⟩ :=
    proofTrace'.splitAt (firstStep :: restSteps).length
  have bodyTrace' : SpelledCallTrace fileId proofInitial
      ((firstStep :: restSteps).map LocatedName.name)
      ((entries.drop formulaPrefix.length).take
        ((firstStep :: restSteps).map LocatedName.name).length)
      proofFinal := by
    simpa using bodyTrace
  have bodyTrace'' := bodyTrace'.reindexInitial anchor.observed_canonical
  have bodyTrace''' : SpelledCallTrace fileId
      ⟨db, .proof
        (db.mkProofState anchored.1 label.name
          (ConstantHeadedFormula.toRuntime
            ⟨typecode.name, bodySymbols⟩) anchor.frame)⟩
      ((firstStep :: restSteps).map LocatedName.name)
      ((entries.drop formulaPrefix.length).take
        ((firstStep :: restSteps).map LocatedName.name).length)
      proofFinal := by
    simpa using bodyTrace''
  let bodyRun :=
    Mettapedia.Languages.Metamath.SourceGSLTParserStatementOutcomes.SpelledCallTrace.normalTokenBody
      anchor.state bodyTrace''' anchor.database_eq (by
        simp [DB.mkProofState]) stepCharsets
  have finishTrace' := finishTrace.reindexInitial bodyRun.final_observed
  have finishTrace'' : SpelledCallTrace fileId
      ⟨db, .proof bodyRun.after⟩ ["$."]
      ((entries.drop formulaPrefix.length).drop
        (firstStep :: restSteps).length) final := by
    simpa using finishTrace'
  let finished := finishTrace''.proofFinish anchor.state anchor.database_eq
  let theoremPos : Pos := bodyRun.after.pos
  have finishFacts :=
    Metamath.PrefixProvenance.finishProof_prefix_characterization
      anchor.state bodyRun.after finished.finish_success (by
        rw [anchor.database_eq]
        exact agreement.errorFree)
  have postInsert :
      (anchor.state.finishProof bodyRun.after).db =
        (db.insert theoremPos label.name
          (.assert (ConstantHeadedFormula.toRuntime
            ⟨typecode.name, bodySymbols⟩) anchor.frame)).recordIncomplete
              bodyRun.after.incomplete label.name := by
    calc
      (anchor.state.finishProof bodyRun.after).db =
          (anchor.state.db.insert bodyRun.after.pos bodyRun.after.label
            (.assert bodyRun.after.fmla bodyRun.after.frame)).recordIncomplete
              bodyRun.after.incomplete bodyRun.after.label := finishFacts.1
      _ = (db.insert bodyRun.after.pos bodyRun.after.label
            (.assert bodyRun.after.fmla bodyRun.after.frame)).recordIncomplete
              bodyRun.after.incomplete bodyRun.after.label := by
          rw [anchor.database_eq]
      _ = (db.insert theoremPos label.name
            (.assert (ConstantHeadedFormula.toRuntime
              ⟨typecode.name, bodySymbols⟩) anchor.frame)).recordIncomplete
                bodyRun.after.incomplete label.name := by
          rw [bodyRun.label_eq, bodyRun.formula_eq, bodyRun.frame_eq]
          rfl
  have mandatoryTrim := trimFrame'_eq_mandatory agreement
    ⟨typecode.name, bodySymbols⟩
      (mandatory_covered_of_insert inserted)
  have frameEq : anchor.frame =
      (mandatoryFrame before
        ⟨typecode.name, bodySymbols⟩).toRuntime :=
    Except.ok.inj (anchor.trim.symm.trans mandatoryTrim)
  have nextAgreement := RuntimeDBAgrees.insertAssertion agreement inserted
    theoremPos
  have recordedAgreement := nextAgreement.recordIncomplete
    bodyRun.after.incomplete label.name
  refine
    { inserted := inserted
      nextPrefix := ?_ }
  rw [finished.final_observed]
  refine
    { mode_eq := rfl
      database := ?_
      interrupt_eq := ?_ }
  rw [postInsert]
  have insertEq :
      db.insert theoremPos label.name
          (.assert (ConstantHeadedFormula.toRuntime
            ⟨typecode.name, bodySymbols⟩) anchor.frame) =
        db.insert theoremPos label.name
          (.assert (ConstantHeadedFormula.toRuntime
            ⟨typecode.name, bodySymbols⟩)
            (mandatoryFrame before
              ⟨typecode.name, bodySymbols⟩).toRuntime) := by
    rw [frameEq]
  rw [insertEq]
  exact recordedAgreement
  rw [postInsert]
  simpa using
    (runtimeInsert_interrupt db theoremPos label.name _).trans interruptEq

/-! ## Verified versus incomplete normal bodies -/

/-- A normal proof body with no unknown marker. -/
structure VerifiedNormalLabels (labels : List String) : Type where
  noUnknown : ∀ label ∈ labels, label ≠ "?"

/-- A normal proof body containing the explicit unknown marker. -/
structure IncompleteNormalLabels (labels : List String) : Type where
  unknown_mem : "?" ∈ labels

/-- Normal bodies are classified solely by the explicit marker. -/
def normalLabels_verifiedOrIncomplete (labels : List String) :
    VerifiedNormalLabels labels ⊕ IncompleteNormalLabels labels :=
  if unknown : "?" ∈ labels then
    .inr ⟨unknown⟩
  else
    .inl ⟨by
      intro label member equality
      subst label
      exact unknown member⟩

theorem verifiedNormalLabels_not_incomplete
    {labels : List String}
    (verified : VerifiedNormalLabels labels)
    (incomplete : IncompleteNormalLabels labels) : False :=
  verified.noUnknown "?" incomplete.unknown_mem rfl

def verifiedNormalLabels_single : VerifiedNormalLabels ["ax"] :=
  ⟨by simp⟩

theorem not_verifiedNormalLabels_unknown :
    ¬ Nonempty (VerifiedNormalLabels ["?"]) := by
  rintro ⟨verified⟩
  exact verified.noUnknown "?" (by simp) rfl

def incompleteNormalLabels_unknown : IncompleteNormalLabels ["?"] :=
  ⟨by simp⟩

theorem not_incompleteNormalLabels_single :
    ¬ Nonempty (IncompleteNormalLabels ["ax"]) := by
  rintro ⟨incomplete⟩
  simpa using incomplete.unknown_mem

/-- Accepted-but-incomplete normal theorem statement.  It advances the
database through the exact reader transition but carries no discharge. -/
structure ReaderIncompleteNormalStatement
    (before after : SourceState) (label : String)
    (formula : ConstantHeadedFormula) (labels : List String)
    (final : ParserObservedState) : Type where
  unknown_mem : "?" ∈ labels
  inserted : insertAssertion? before label formula = some after
  nextPrefix : SourceParserPrefixAgrees after final

def ReaderAcceptedNormalStatement.toIncomplete
    {db : DB} {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula} {labels : List String}
    {final : ParserObservedState}
    (accepted : ReaderAcceptedNormalStatement db before after label formula
      labels final)
    (incomplete : IncompleteNormalLabels labels) :
    ReaderIncompleteNormalStatement before after label formula labels final :=
  { unknown_mem := incomplete.unknown_mem
    inserted := accepted.inserted
    nextPrefix := accepted.nextPrefix }

/-- The semantic result of one accepted normal theorem statement. -/
inductive ReaderNormalStatementOutcome
    (before after : SourceState) (label : String)
    (formula : ConstantHeadedFormula) (labels : List String)
    (final : ParserObservedState) : Type where
  | verified
      (result : ReaderVerifiedNormalStatement before after formula labels
        final) :
      ReaderNormalStatementOutcome before after label formula labels final
  | incomplete
      (result : ReaderIncompleteNormalStatement before after label formula
        labels final) :
      ReaderNormalStatementOutcome before after label formula labels final

/-- Classify an accepted exact normal `$p` trace.  The verified branch invokes
the proof-reflection ledger; the incomplete branch uses only common reader
acceptance and cannot expose a discharge. -/
noncomputable def SpelledCallTrace.normalStatementOutcome
    {fileId : String} {db : DB}
    {before after : SourceState}
    {label typecode firstStep : LocatedName}
    {body restSteps : List LocatedName}
    {bodySymbols : List Sym}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId ⟨db, .start⟩
      ((label.name :: "$p" ::
          (typecode :: body).map LocatedName.name ++ ["$="]) ++
        ((firstStep :: restSteps).map LocatedName.name ++ ["$."]))
      entries final)
    (agreement : RuntimeDBAgrees db before)
    (interruptEq : db.interrupt = false)
    (labelCharset : NameCharset labelBytesValid label)
    (typecodeCharset : NameCharset mathBytesValid typecode)
    (bodyCharsets :
      ∀ name ∈ body, NameCharset mathBytesValid name)
    (stepCharsets :
      ∀ name ∈ firstStep :: restSteps,
        NameCharset proofTokenValid name)
    (taggedFormula : tagBody before (typecode :: body) =
      .ok (.const typecode.name :: bodySymbols))
    (inserted : insertAssertion? before label.name
      ⟨typecode.name, bodySymbols⟩ = some after)
    (runtimeTarget sourceTarget : ValidatedCalculusLanguageDef)
    (runtimePresentation :
      calculusLanguageDefOfSourcePrefix? (runtimePrefix before) =
        some runtimeTarget.1)
    (sourcePresentation :
      calculusLanguageDefOfSourcePrefix? before.toSourcePrefix =
        some sourceTarget.1) :
    ReaderNormalStatementOutcome before after label.name
      ⟨typecode.name, bodySymbols⟩
      ((firstStep :: restSteps).map LocatedName.name) final := by
  let labels := (firstStep :: restSteps).map LocatedName.name
  cases normalLabels_verifiedOrIncomplete labels with
  | inl verified =>
      have noUnknown :
          ∀ name ∈ firstStep :: restSteps, name.name ≠ "?" := by
        intro name member
        exact verified.noUnknown name.name
          (List.mem_map_of_mem member)
      exact .verified
        (trace.verifiedNormalStatement agreement interruptEq labelCharset
          typecodeCharset bodyCharsets stepCharsets noUnknown taggedFormula
          inserted runtimeTarget sourceTarget runtimePresentation
          sourcePresentation)
  | inr incomplete =>
      let accepted :=
        Mettapedia.Languages.Metamath.SourceGSLTParserStatementOutcomes.SpelledCallTrace.acceptedNormalStatement
          trace agreement interruptEq labelCharset typecodeCharset
            bodyCharsets stepCharsets taggedFormula inserted
      exact .incomplete (accepted.toIncomplete incomplete)

/-- The semantic result of one accepted compressed theorem statement. -/
inductive ReaderCompressedStatementOutcome
    (before after : SourceState) (label : String)
    (formula : ConstantHeadedFormula)
    (header : List String) (words : List (List UInt8))
    (final : ParserObservedState) : Type where
  | verified
      (result : ReaderVerifiedCompressedStatement before after label formula
        header words final) :
      ReaderCompressedStatementOutcome before after label formula header words
        final
  | incomplete
      (result : ReaderIncompleteCompressedStatement before after label formula
        header words final) :
      ReaderCompressedStatementOutcome before after label formula header words
        final

/-- Classify an accepted exact compressed `$p` trace from the decoded program
recovered from those same calls.  No caller-selected action list or outcome is
accepted. -/
noncomputable def SpelledCallTrace.compressedStatementOutcome
    {fileId : String} {db : DB}
    {before after : SourceState}
    {label typecode : LocatedName}
    {body header : List LocatedName} {words : List LocatedToken}
    {bodySymbols : List Sym}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId ⟨db, .start⟩
      ((label.name :: "$p" ::
          (typecode :: body).map LocatedName.name ++ ["$="]) ++
        (["("] ++ header.map LocatedName.name ++ [")"] ++
          words.map (fun word => tokenText word.bytes) ++ ["$."]))
      entries final)
    (agreement : RuntimeDBAgrees db before)
    (interruptEq : db.interrupt = false)
    (savePlacement : db.config.compressedSavePlacement =
      .immediatelyAfterUse)
    (labelCharset : NameCharset labelBytesValid label)
    (typecodeCharset : NameCharset mathBytesValid typecode)
    (bodyCharsets :
      ∀ name ∈ body, NameCharset mathBytesValid name)
    (headerCharsets :
      ∀ name ∈ header, NameCharset labelBytesValid name)
    (wordCharsets :
      ∀ word ∈ words, compressedWordValid word.bytes = true)
    (taggedFormula : tagBody before (typecode :: body) =
      .ok (.const typecode.name :: bodySymbols))
    (inserted : insertAssertion? before label.name
      ⟨typecode.name, bodySymbols⟩ = some after)
    (runtimeTarget sourceTarget : ValidatedCalculusLanguageDef)
    (runtimePresentation :
      calculusLanguageDefOfSourcePrefix? (runtimePrefix before) =
        some runtimeTarget.1)
    (sourcePresentation :
      calculusLanguageDefOfSourcePrefix? before.toSourcePrefix =
        some sourceTarget.1)
    (headerAdmitted : ∀ explicitLabel ∈ header.map LocatedName.name,
      explicitLabel ∉
        (mandatoryHypotheses before
          ⟨typecode.name, bodySymbols⟩).map (fun hypothesis => hypothesis.label)) :
    ReaderCompressedStatementOutcome before after label.name
      ⟨typecode.name, bodySymbols⟩
      (header.map LocatedName.name) (words.map (fun word => word.bytes))
      final := by
  let accepted := trace.acceptedCompressedStatement agreement interruptEq
    savePlacement labelCharset typecodeCharset bodyCharsets headerCharsets
      wordCharsets taggedFormula inserted
  cases decodedCompressedWords_verifiedOrIncomplete
      accepted.program.decoded with
  | inl verified =>
      exact .verified
        (accepted.toVerified verified runtimeTarget sourceTarget
          runtimePresentation sourcePresentation headerAdmitted)
  | inr incomplete =>
      exact .incomplete (accepted.toIncomplete incomplete)

end Mettapedia.Languages.Metamath.SourceGSLTParserStatementOutcomes
