import Mettapedia.Languages.Metamath.SourceGSLTParserStatementTransitions
import Mettapedia.Languages.Metamath.SourceGSLTParserStatementOutcomes
import Mettapedia.Languages.Metamath.SourceGSLTLifecycleComposition
import Mettapedia.Languages.Metamath.SourceGSLTDerivationCorrespondence

/-!
# Statement-level source/reader simulation

This module packages the exact reader transition for one accepted source
statement.  Ordinary declarations carry the next prefix agreement.  A `$p`
statement additionally carries the verified-or-incomplete outcome reconstructed
from the same reader calls; verified outcomes contain the proof discharge.

Presentation admission is explicit only at theorem boundaries.  It will be
derived from the lexicalized accepted source trace at the whole-run layer; it is
not part of the semantic validity predicate on `SourceState`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.SourceGSLTParserStatementSimulation

open Metamath.Verify
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.InferenceOneShotByteLog
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceGSLTDerivationCorrespondence
open Mettapedia.Languages.Metamath.SourceGSLTLexicalClosure
open Mettapedia.Languages.Metamath.SourceGSLTRuntimeStateAgreement
open Mettapedia.Languages.Metamath.SourceGSLTParserPrefixBisimulation
open Mettapedia.Languages.Metamath.SourceGSLTParserStatementOutcomes
open Mettapedia.Languages.Metamath.SourceGSLTLifecycleComposition

/-- Admission data needed to reflect a production-checker proof into the
source-indexed proof presentation.  The two presentations correspond to the
reader's canonical label ordering and the source statement ordering. -/
structure ProofProjectionAdmission (state : SourceState) : Type where
  runtimeTarget : ValidatedPresentation
  sourceTarget : ValidatedPresentation
  runtimePresentation :
    presentationOfSourcePrefix? (runtimePrefix state) =
      some runtimeTarget.1
  sourcePresentation :
    presentationOfSourcePrefix? state.toSourcePrefix =
      some sourceTarget.1

/-- Only theorem statements need a proof-presentation admission. -/
def StatementProjectionAdmission (state : SourceState) :
    RawStatement → Type
  | .provable _ _ _ _ _ _ _ => ProofProjectionAdmission state
  | _ => PUnit

/-- Reader validation of one source statement.  The normal and compressed
constructors retain the actual proof outcome; no proof evidence is produced for
an explicit unknown marker. -/
inductive ReaderStatementValidation
    (before after : SourceState) (final : ParserObservedState) :
    RawStatement → Type where
  | openScope {site : LocatedByteSpan}
      (nextPrefix : SourceParserPrefixAgrees after final) :
      ReaderStatementValidation before after final (.openScope site)
  | closeScope {site : LocatedByteSpan}
      (nextPrefix : SourceParserPrefixAgrees after final) :
      ReaderStatementValidation before after final (.closeScope site)
  | constDecl {site terminator : LocatedByteSpan}
      {names : List LocatedName}
      (nextPrefix : SourceParserPrefixAgrees after final) :
      ReaderStatementValidation before after final
        (.constDecl site names terminator)
  | varDecl {site terminator : LocatedByteSpan}
      {names : List LocatedName}
      (nextPrefix : SourceParserPrefixAgrees after final) :
      ReaderStatementValidation before after final
        (.varDecl site names terminator)
  | djDecl {site terminator : LocatedByteSpan}
      {names : List LocatedName}
      (nextPrefix : SourceParserPrefixAgrees after final) :
      ReaderStatementValidation before after final
        (.djDecl site names terminator)
  | floating {site terminator : LocatedByteSpan}
      {label typecode variableName : LocatedName}
      (nextPrefix : SourceParserPrefixAgrees after final) :
      ReaderStatementValidation before after final
        (.floating site label typecode variableName terminator)
  | essential {site terminator : LocatedByteSpan}
      {label typecode : LocatedName} {body : List LocatedName}
      (nextPrefix : SourceParserPrefixAgrees after final) :
      ReaderStatementValidation before after final
        (.essential site label typecode body terminator)
  | axiomatic {site terminator : LocatedByteSpan}
      {label typecode : LocatedName} {body : List LocatedName}
      (nextPrefix : SourceParserPrefixAgrees after final) :
      ReaderStatementValidation before after final
        (.axiomatic site label typecode body terminator)
  | normal {site separator terminator : LocatedByteSpan}
      {label typecode : LocatedName} {body steps : List LocatedName}
      {bodySymbols : List Sym}
      (taggedBody : tagBody before body = .ok bodySymbols)
      (stepsNonempty : steps ≠ [])
      (outcome : ReaderNormalStatementOutcome before after label.name
        ⟨typecode.name, bodySymbols⟩ (steps.map LocatedName.name) final) :
      ReaderStatementValidation before after final
        (.provable site label typecode body (.normal steps) separator
          terminator)
  | compressed {site separator terminator openParen closeParen :
        LocatedByteSpan}
      {label typecode : LocatedName}
      {body header : List LocatedName} {words : List LocatedToken}
      {bodySymbols : List Sym}
      (taggedBody : tagBody before body = .ok bodySymbols)
      (wordsNonempty : words ≠ [])
      (outcome : ReaderCompressedStatementOutcome before after label.name
        ⟨typecode.name, bodySymbols⟩ (header.map LocatedName.name)
          (words.map (fun word => word.bytes)) final) :
      ReaderStatementValidation before after final
        (.provable site label typecode body
          (.compressed openParen header closeParen words) separator
          terminator)

/-- Every validated statement returns the reader to a matching source-prefix
boundary. -/
def ReaderStatementValidation.nextPrefix
    {before after : SourceState} {final : ParserObservedState}
    {statement : RawStatement}
    (validation : ReaderStatementValidation before after final statement) :
    SourceParserPrefixAgrees after final := by
  cases validation with
  | openScope result => exact result
  | closeScope result => exact result
  | constDecl result => exact result
  | varDecl result => exact result
  | djDecl result => exact result
  | floating result => exact result
  | essential result => exact result
  | axiomatic result => exact result
  | normal _ _ outcome =>
      cases outcome with
      | verified result => exact result.nextPrefix
      | incomplete result => exact result.nextPrefix
  | compressed _ _ outcome =>
      cases outcome with
      | verified result => exact result.nextPrefix
      | incomplete result => exact result.nextPrefix

/-- One source transition and its validation by the exact production-reader
call group.  The obligation list is the source fold's own output. -/
structure ReaderStatementSimulation
    (fileId : String) (before : SourceState)
    (initial : ParserObservedState) (statement : RawStatement)
    (entries : List (LocatedToken × TokenCall))
    (after : SourceState) (obligations : List TheoremObligation)
    (final : ParserObservedState) : Type where
  trace : LocatedSignificantCallTrace fileId initial entries final
  charsets : StatementCharsets statement
  spanEq : RawStatement.tokenSpans statement =
    entries.map (fun entry => entry.1.span)
  tokenTextEq : RawStatement.tokenStrings statement =
    entries.map (fun entry => tokenText entry.1.bytes)
  sourceStep : applyStatement before statement = .ok (after, obligations)
  validation : ReaderStatementValidation before after final statement

def ReaderStatementSimulation.nextPrefix
    {fileId : String} {before after : SourceState}
    {initial final : ParserObservedState} {statement : RawStatement}
    {entries : List (LocatedToken × TokenCall)}
    {obligations : List TheoremObligation}
    (simulation : ReaderStatementSimulation fileId before initial statement
      entries after obligations final) :
    SourceParserPrefixAgrees after final :=
  simulation.validation.nextPrefix

/-- Construct the complete simulation of one accepted statement from the
statement's exact located reader calls.  Token spelling is recovered from the
trace rather than supplied as an independent parser certificate. -/
noncomputable def LocatedSignificantCallTrace.simulateStatement
    {fileId : String} {before after : SourceState}
    {statement : RawStatement} {obligations : List TheoremObligation}
    {initial final : ParserObservedState}
    {entries : List (LocatedToken × TokenCall)}
    (trace : LocatedSignificantCallTrace fileId initial entries final)
    (spanEq : RawStatement.tokenSpans statement =
      entries.map (fun entry => entry.1.span))
    (tokenTextEq : RawStatement.tokenStrings statement =
      entries.map (fun entry => tokenText entry.1.bytes))
    (charsets : StatementCharsets statement)
    (normalSteps : NormalStepsOK statement)
    (compressedWords : CompressedWordsOK statement)
    (agreement : SourceParserPrefixAgrees before initial)
    (savePlacement : initial.db.config.compressedSavePlacement =
      .immediatelyAfterUse)
    (applied : applyStatement before statement = .ok (after, obligations))
    (admission : StatementProjectionAdmission before statement) :
    ReaderStatementSimulation fileId before initial statement entries after
      obligations final := by
  rcases initial with ⟨db, mode⟩
  cases agreement.mode_eq
  let spelled := trace.toSpelledCallTrace
    (RawStatement.tokenStrings statement) tokenTextEq
  cases statement with
  | openScope site =>
      exact
        { trace := trace
          charsets := charsets
          spanEq := spanEq
          tokenTextEq := tokenTextEq
          sourceStep := applied
          validation := .openScope
            (agreement.openScope trace tokenTextEq applied) }
  | closeScope site =>
      exact
        { trace := trace
          charsets := charsets
          spanEq := spanEq
          tokenTextEq := tokenTextEq
          sourceStep := applied
          validation := .closeScope
            (agreement.closeScope trace tokenTextEq applied) }
  | constDecl site names terminator =>
      have spelled' : SpelledCallTrace fileId ⟨db, .start⟩
          ("$c" :: names.map LocatedName.name ++ ["$."]) entries final := by
        simpa [spelled, RawStatement.tokenStrings] using spelled
      exact
        { trace := trace
          charsets := charsets
          spanEq := spanEq
          tokenTextEq := tokenTextEq
          sourceStep := applied
          validation := .constDecl
            (agreement.constDecl spelled' charsets applied) }
  | varDecl site names terminator =>
      have spelled' : SpelledCallTrace fileId ⟨db, .start⟩
          ("$v" :: names.map LocatedName.name ++ ["$."]) entries final := by
        simpa [spelled, RawStatement.tokenStrings] using spelled
      exact
        { trace := trace
          charsets := charsets
          spanEq := spanEq
          tokenTextEq := tokenTextEq
          sourceStep := applied
          validation := .varDecl
            (agreement.varDecl spelled' charsets applied) }
  | djDecl site names terminator =>
      have spelled' : SpelledCallTrace fileId ⟨db, .start⟩
          ("$d" :: names.map LocatedName.name ++ ["$."]) entries final := by
        simpa [spelled, RawStatement.tokenStrings] using spelled
      exact
        { trace := trace
          charsets := charsets
          spanEq := spanEq
          tokenTextEq := tokenTextEq
          sourceStep := applied
          validation := .djDecl
            (agreement.djDecl spelled' charsets applied) }
  | floating site label typecode variableName terminator =>
      rcases charsets with ⟨labelCharset, typecodeCharset, variableCharset⟩
      have spelled' : SpelledCallTrace fileId ⟨db, .start⟩
          (label.name :: "$f" ::
            [typecode.name, variableName.name] ++ ["$."])
          entries final := by
        simpa [spelled, RawStatement.tokenStrings] using spelled
      exact
        { trace := trace
          charsets := ⟨labelCharset, typecodeCharset, variableCharset⟩
          spanEq := spanEq
          tokenTextEq := tokenTextEq
          sourceStep := applied
          validation := .floating
            (agreement.floating spelled' labelCharset typecodeCharset
              variableCharset applied) }
  | essential site label typecode body terminator =>
      rcases charsets with ⟨labelCharset, typecodeCharset, bodyCharsets⟩
      have spelled' : SpelledCallTrace fileId ⟨db, .start⟩
          (label.name :: "$e" ::
            (typecode :: body).map LocatedName.name ++ ["$."])
          entries final := by
        simpa [spelled, RawStatement.tokenStrings] using spelled
      exact
        { trace := trace
          charsets := ⟨labelCharset, typecodeCharset, bodyCharsets⟩
          spanEq := spanEq
          tokenTextEq := tokenTextEq
          sourceStep := applied
          validation := .essential
            (agreement.essential spelled' labelCharset typecodeCharset
              bodyCharsets applied) }
  | axiomatic site label typecode body terminator =>
      rcases charsets with ⟨labelCharset, typecodeCharset, bodyCharsets⟩
      have spelled' : SpelledCallTrace fileId ⟨db, .start⟩
          (label.name :: "$a" ::
            (typecode :: body).map LocatedName.name ++ ["$."])
          entries final := by
        simpa [spelled, RawStatement.tokenStrings] using spelled
      exact
        { trace := trace
          charsets := ⟨labelCharset, typecodeCharset, bodyCharsets⟩
          spanEq := spanEq
          tokenTextEq := tokenTextEq
          sourceStep := applied
          validation := .axiomatic
            (agreement.axiomatic spelled' labelCharset typecodeCharset
              bodyCharsets applied) }
  | provable site label typecode body proof separator terminator =>
      rcases charsets with
        ⟨labelCharset, typecodeCharset, bodyCharsets, proofCharsets⟩
      cases taggedBody : tagBody before body with
      | rejected rejection =>
          simp only [applyStatement, taggedBody] at applied
          exact nomatch applied
      | ok bodySymbols =>
          cases inserted : insertAssertion? before label.name
              ⟨typecode.name, bodySymbols⟩ with
          | none =>
              simp only [applyStatement, taggedBody, inserted] at applied
              exact nomatch applied
          | some insertedState =>
              simp only [applyStatement, taggedBody, inserted] at applied
              cases applied
              have taggedFormula : tagBody before (typecode :: body) =
                  .ok (.const typecode.name :: bodySymbols) :=
                tagBody_typecode_cons
                  (insertAssertion?_valid_before inserted)
                  (insertAssertion?_formula_declared inserted) taggedBody
              cases proof with
              | normal steps =>
                  cases steps with
                  | nil =>
                      simp [NormalStepsOK] at normalSteps
                  | cons firstStep restSteps =>
                      have spelled' : SpelledCallTrace fileId ⟨db, .start⟩
                          ((label.name :: "$p" ::
                              (typecode :: body).map LocatedName.name ++
                                ["$="]) ++
                            ((firstStep :: restSteps).map LocatedName.name ++
                              ["$."])) entries final := by
                        simpa [spelled, RawStatement.tokenStrings,
                          ProofPayload.tokenStrings, List.append_assoc] using
                            spelled
                      let outcome :=
                        Mettapedia.Languages.Metamath.SourceGSLTParserStatementOutcomes.SpelledCallTrace.normalStatementOutcome
                          spelled'
                        agreement.database agreement.interrupt_eq labelCharset
                        typecodeCharset bodyCharsets proofCharsets taggedFormula
                        inserted admission.runtimeTarget admission.sourceTarget
                        admission.runtimePresentation
                        admission.sourcePresentation
                      exact
                        { trace := trace
                          charsets :=
                            ⟨labelCharset, typecodeCharset, bodyCharsets,
                              proofCharsets⟩
                          spanEq := spanEq
                          tokenTextEq := tokenTextEq
                          sourceStep := by
                            simp [applyStatement, taggedBody, inserted]
                          validation :=
                            .normal taggedBody (by simp) outcome }
              | compressed openParen header closeParen words =>
                  rcases proofCharsets with ⟨headerCharsets, wordCharsets⟩
                  have wordsNonempty : words ≠ [] := by
                    simpa [CompressedWordsOK] using compressedWords
                  have spelled' : SpelledCallTrace fileId ⟨db, .start⟩
                      ((label.name :: "$p" ::
                          (typecode :: body).map LocatedName.name ++ ["$="]) ++
                        (["("] ++ header.map LocatedName.name ++ [")"] ++
                          words.map (fun word => tokenText word.bytes) ++
                            ["$."])) entries final := by
                    simpa [spelled, RawStatement.tokenStrings,
                      ProofPayload.tokenStrings, List.append_assoc] using
                        spelled
                  let outcome :=
                    Mettapedia.Languages.Metamath.SourceGSLTParserStatementOutcomes.SpelledCallTrace.compressedStatementOutcome
                      spelled'
                    agreement.database agreement.interrupt_eq savePlacement
                    labelCharset typecodeCharset bodyCharsets headerCharsets
                    wordCharsets taggedFormula inserted admission.runtimeTarget
                    admission.sourceTarget admission.runtimePresentation
                    admission.sourcePresentation
                  exact
                    { trace := trace
                      charsets :=
                        ⟨labelCharset, typecodeCharset, bodyCharsets,
                          ⟨headerCharsets, wordCharsets⟩⟩
                      spanEq := spanEq
                      tokenTextEq := tokenTextEq
                      sourceStep := by
                        simp [applyStatement, taggedBody, inserted]
                      validation :=
                        .compressed taggedBody wordsNonempty outcome }

/-! ## Chronological statement runs -/

/-- Proof-presentation admissions indexed by the source fold's actual
intermediate states.  Ordinary statements contribute `PUnit`; a theorem
contributes exactly the admission consumed by `simulateStatement`. -/
def RunProjectionAdmissions : SourceState → List RawStatement → Type
  | _, [] => PUnit
  | state, statement :: rest =>
      StatementProjectionAdmission state statement ×
        match applyStatement state statement with
        | .rejected _ => PUnit
        | .ok (next, _) => RunProjectionAdmissions next rest

/-- Prefix-wise simulation of a statement list.  Source states, reader
boundaries, located call groups, and obligation order all evolve together. -/
inductive ReaderRunSimulation (fileId : String) :
    SourceState → ParserObservedState → List RawStatement →
      List (LocatedToken × TokenCall) → SourceState →
      List TheoremObligation → ParserObservedState → Type where
  | nil (state : SourceState) (parser : ParserObservedState)
      (agreement : SourceParserPrefixAgrees state parser) :
      ReaderRunSimulation fileId state parser [] [] state [] parser
  | cons {before middle after : SourceState}
      {initial middleParser finalParser : ParserObservedState}
      {statement : RawStatement} {statements : List RawStatement}
      {statementEntries restEntries : List (LocatedToken × TokenCall)}
      {statementObligations restObligations : List TheoremObligation}
      (head : ReaderStatementSimulation fileId before initial statement
        statementEntries middle statementObligations middleParser)
      (tail : ReaderRunSimulation fileId middle middleParser statements
        restEntries after restObligations finalParser) :
      ReaderRunSimulation fileId before initial (statement :: statements)
        (statementEntries ++ restEntries) after
        (statementObligations ++ restObligations) finalParser

/-- A chronological simulation retains the executable source fold exactly. -/
theorem ReaderRunSimulation.toFold
    {fileId : String} {before after : SourceState}
    {initial final : ParserObservedState} {statements : List RawStatement}
    {entries : List (LocatedToken × TokenCall)}
    {obligations : List TheoremObligation}
    (run : ReaderRunSimulation fileId before initial statements entries after
      obligations final) :
    foldStatements before statements = .ok (after, obligations) := by
  induction run with
  | nil => rfl
  | cons head tail ih =>
      simp [foldStatements, head.sourceStep, ih]

/-- A chronological simulation retains the exact statement partition of the
located production-reader chronology. -/
noncomputable def ReaderRunSimulation.toLocatedStatementCallTrace
    {fileId : String} {before after : SourceState}
    {initial final : ParserObservedState} {statements : List RawStatement}
    {entries : List (LocatedToken × TokenCall)}
    {obligations : List TheoremObligation}
    (run : ReaderRunSimulation fileId before initial statements entries after
      obligations final) :
    LocatedStatementCallTrace fileId initial statements entries final := by
  induction run with
  | nil state parser agreement => exact .nil parser
  | cons head tail ih =>
      exact .cons _ head.charsets head.spanEq head.tokenTextEq head.trace ih

/-- The final source and reader states of a chronological simulation still
agree at a statement boundary. -/
theorem ReaderRunSimulation.finalPrefix
    {fileId : String} {before after : SourceState}
    {initial final : ParserObservedState} {statements : List RawStatement}
    {entries : List (LocatedToken × TokenCall)}
    {obligations : List TheoremObligation}
    (run : ReaderRunSimulation fileId before initial statements entries after
      obligations final) :
    SourceParserPrefixAgrees after final := by
  induction run with
  | nil _ _ agreement => exact agreement
  | cons _ _ ih => exact ih

/-! ## Construction from the exact statement partition -/

/-- Construct the prefix-wise run from the statement partition of the exact
production-reader chronology and the source fold's own successful execution.
No independently supplied token sequence or final-state agreement occurs in
the result. -/
noncomputable def LocatedStatementCallTrace.simulate
    {fileId : String} {before after : SourceState}
    {initial final : ParserObservedState} {statements : List RawStatement}
    {entries : List (LocatedToken × TokenCall)}
    {obligations : List TheoremObligation}
    (trace : LocatedStatementCallTrace fileId initial statements entries final)
    (agreement : SourceParserPrefixAgrees before initial)
    (savePlacement : initial.db.config.compressedSavePlacement =
      .immediatelyAfterUse)
    (folded : foldStatements before statements = .ok (after, obligations))
    (normalSteps : ∀ statement ∈ statements, NormalStepsOK statement)
    (compressedWords :
      ∀ statement ∈ statements, CompressedWordsOK statement)
    (admissions : RunProjectionAdmissions before statements) :
    ReaderRunSimulation fileId before initial statements entries after
      obligations final := by
  induction trace generalizing before after obligations with
  | nil parser =>
      simp only [foldStatements] at folded
      cases folded
      exact .nil before parser agreement
  | @cons initial middleParser finalParser statements statementEntries
      restEntries statement charsets spanEq tokenTextEq statementTrace tail ih =>
      cases applied : applyStatement before statement with
      | rejected rejection =>
          simp [foldStatements, applied] at folded
      | ok result =>
          obtain ⟨middleSource, statementObligations⟩ := result
          cases foldedTail : foldStatements middleSource statements with
          | rejected rejection =>
              simp [foldStatements, applied, foldedTail] at folded
          | ok result =>
              obtain ⟨finalSource, restObligations⟩ := result
              simp only [foldStatements, applied, foldedTail,
                FoldResult.ok.injEq, Prod.mk.injEq] at folded
              obtain ⟨afterEq, obligationsEq⟩ := folded
              subst afterEq
              subst obligationsEq
              have admissions' :
                  StatementProjectionAdmission before statement ×
                    RunProjectionAdmissions middleSource statements := by
                simpa [RunProjectionAdmissions, applied] using admissions
              have headNormal : NormalStepsOK statement :=
                normalSteps statement (by simp)
              have tailNormal :
                  ∀ candidate ∈ statements, NormalStepsOK candidate := by
                intro candidate member
                exact normalSteps candidate (by simp [member])
              have headCompressed : CompressedWordsOK statement :=
                compressedWords statement (by simp)
              have tailCompressed :
                  ∀ candidate ∈ statements,
                    CompressedWordsOK candidate := by
                intro candidate member
                exact compressedWords candidate (by simp [member])
              let head :=
                Mettapedia.Languages.Metamath.SourceGSLTParserStatementSimulation.LocatedSignificantCallTrace.simulateStatement
                  statementTrace spanEq tokenTextEq charsets headNormal
                    headCompressed agreement savePlacement applied admissions'.1
              have middleSavePlacement :
                  middleParser.db.config.compressedSavePlacement =
                    .immediatelyAfterUse := by
                rw [statementTrace.final_config_eq]
                exact savePlacement
              let tailRun := ih head.nextPrefix middleSavePlacement foldedTail
                tailNormal tailCompressed admissions'.2
              exact .cons head tailRun

/-! ## Kernel-checkable boundaries -/

/-- The initial empty chronology is a complete prefix-wise simulation. -/
noncomputable def initialEmptyRunSimulation :
    ReaderRunSimulation "root" initialState
      (parserObservedState
        (Mettapedia.Languages.Metamath.InferenceOneShotByteLog.initialState {}))
      [] [] initialState []
      (parserObservedState
        (Mettapedia.Languages.Metamath.InferenceOneShotByteLog.initialState {})) :=
  .nil initialState _ initial_sourceParserPrefixAgrees

/-- Negative boundary: an empty normal body cannot inhabit the statement
simulation interface. -/
theorem no_empty_normal_statement_validation
    {before after : SourceState} {final : ParserObservedState}
    {site separator terminator : LocatedByteSpan}
    {label typecode : LocatedName} {body : List LocatedName} :
    ¬ Nonempty
      (ReaderStatementValidation before after final
        (.provable site label typecode body (.normal []) separator
          terminator)) := by
  rintro ⟨validation⟩
  cases validation with
  | normal _ stepsNonempty _ => exact stepsNonempty rfl

/-- Negative boundary: an empty compressed body cannot inhabit the statement
simulation interface. -/
theorem no_empty_compressed_statement_validation
    {before after : SourceState} {final : ParserObservedState}
    {site separator terminator openParen closeParen : LocatedByteSpan}
    {label typecode : LocatedName} {body header : List LocatedName} :
    ¬ Nonempty
      (ReaderStatementValidation before after final
        (.provable site label typecode body
          (.compressed openParen header closeParen []) separator
          terminator)) := by
  rintro ⟨validation⟩
  cases validation with
  | compressed _ wordsNonempty _ => exact wordsNonempty rfl


end Mettapedia.Languages.Metamath.SourceGSLTParserStatementSimulation
