import Mettapedia.Languages.Metamath.SourceGSLTReaderTraceBinding
import Mettapedia.Languages.Metamath.SourceGSLTRuntimeCoEvolution
import Mettapedia.Languages.Metamath.SourceGSLTRuntimeProofTransport
import Mettapedia.Languages.Metamath.SourceGSLTRuntimeCompressedTransport
import Mettapedia.Languages.Metamath.SourceGSLTCompressedReflection
import Mettapedia.Languages.Metamath.InferenceNormalByteReflection

/-!
# Prefix bisimulation for the Metamath source GSLT and shipped reader

The byte log records each real `ParserState.feedToken` call before the
subsequent whitespace/line update.  This module first erases precisely those
administrative fields, retaining the live database and token-parser mode.
The resulting proof-relevant chronology is the induction rail for relating
statement prefixes, source states, and proof discharges.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.SourceGSLTParserPrefixBisimulation

open Metamath.Verify
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.InferenceOneShotByteLog
open Mettapedia.Languages.Metamath.SourceGSLTReaderTraceBinding
open Mettapedia.Languages.Metamath.SourceGSLTCheckerAlignment
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceGSLTDerivationCorrespondence
open Mettapedia.Languages.Metamath.SourceGSLTLexicalClosure
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTIncludeDAG
open Mettapedia.Languages.Metamath.SourceGSLTCompressedMMLean4
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceGSLTCompressedReflection
open Mettapedia.Languages.Metamath.SourceGSLTCompressedParserMMLean4
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceGSLTRuntimeStateAgreement
open Mettapedia.Languages.Metamath.SourceGSLTRuntimeCoEvolution
open Mettapedia.Languages.Metamath.SourceGSLTRuntimeProofTransport
open Mettapedia.Languages.Metamath.SourceGSLTRuntimeCompressedTransport
open Mettapedia.Languages.Metamath.ByteSliceForInSupport
open Mettapedia.Languages.Metamath.SourceGSLTCompressedExecutionMMLean4
open Mettapedia.Languages.Metamath.SourceGSLTCompressedParserComposition
open Mettapedia.Languages.Metamath.ByteSliceForInSupport
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceNormalByteLedger
open Mettapedia.Languages.Metamath.InferenceNormalParserTrace
open Mettapedia.Languages.Metamath.InferenceNormalByteReflection
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.SourceInferenceExecution
open Mettapedia.Languages.Metamath.SourceGSLTLifecycleComposition

/-- The semantically relevant projection of the shipped parser state at a
token-call boundary.  Character-scanner and line-accounting fields determine
locations but do not change the database or statement/proof mode. -/
structure ParserSemanticState where
  db : DB
  mode : TokenParser

def parserSemanticState (state : ParserState) : ParserSemanticState :=
  ⟨state.db, state.tokp⟩

@[simp] theorem parserSemanticState_updateLine
    (state : ParserState) (position : Nat) (byte : UInt8) :
    parserSemanticState (state.updateLine position byte) =
      parserSemanticState state := by
  unfold ParserState.updateLine parserSemanticState
  split <;> rfl

/-- Complete semantic chronology of a call list.  The next call begins from
the database and token-parser mode produced by the previous call; line updates
between calls are erased, but no semantic transition is inserted or dropped. -/
inductive CallSemanticTrace :
    ParserSemanticState → List TokenCall → Type where
  | nil (state : ParserSemanticState) : CallSemanticTrace state []
  | cons {initial : ParserSemanticState} {calls : List TokenCall}
      (call : TokenCall)
      (before_eq : parserSemanticState call.before = initial)
      (tail : CallSemanticTrace (parserSemanticState call.after) calls) :
      CallSemanticTrace initial (call :: calls)

/-- The semantic state after the last recorded call (or the initial state for
an empty chronology). -/
def CallSemanticTrace.final :
    {initial : ParserSemanticState} → {calls : List TokenCall} →
      CallSemanticTrace initial calls → ParserSemanticState
  | _, _, .nil state => state
  | _, _, .cons _ _ tail => tail.final

/-- A call chronology whose last semantic state is fixed. -/
structure CallSemanticRun (initial : ParserSemanticState)
    (calls : List TokenCall) (final : ParserSemanticState) : Type where
  trace : CallSemanticTrace initial calls
  final_eq : trace.final = final

def CallSemanticRun.reindexInitial
    {initial next final : ParserSemanticState} {calls : List TokenCall}
    (run : CallSemanticRun initial calls final)
    (equality : initial = next) :
    CallSemanticRun next calls final :=
  equality ▸ run

def CallSemanticRun.cons
    {initial final : ParserSemanticState} {calls : List TokenCall}
    (call : TokenCall)
    (before_eq : parserSemanticState call.before = initial)
    (tail : CallSemanticRun (parserSemanticState call.after) calls final) :
    CallSemanticRun initial (call :: calls) final :=
  { trace := .cons call before_eq tail.trace
    final_eq := tail.final_eq }

/-- Concatenating two adjacent semantic traces neither inserts a synthetic
transition nor loses the boundary state. -/
noncomputable def CallSemanticTrace.append
    {initial : ParserSemanticState} {leftCalls rightCalls : List TokenCall}
    (left : CallSemanticTrace initial leftCalls)
    (right : CallSemanticTrace left.final rightCalls) :
    CallSemanticTrace initial (leftCalls ++ rightCalls) := by
  induction left with
  | nil state => exact right
  | cons call before_eq tail ih =>
      exact .cons call before_eq (ih right)

theorem CallSemanticTrace.final_append
    {initial : ParserSemanticState} {leftCalls rightCalls : List TokenCall}
    (left : CallSemanticTrace initial leftCalls)
    (right : CallSemanticTrace left.final rightCalls) :
    (left.append right).final = right.final := by
  induction left with
  | nil => rfl
  | cons call before_eq tail ih => exact ih right

/-- Composition law for adjacent call runs. -/
noncomputable def CallSemanticRun.append
    {initial middle final : ParserSemanticState}
    {leftCalls rightCalls : List TokenCall}
    (left : CallSemanticRun initial leftCalls middle)
    (right : CallSemanticRun middle rightCalls final) :
    CallSemanticRun initial (leftCalls ++ rightCalls) final := by
  let rightAtBoundary := right.reindexInitial left.final_eq.symm
  exact
    { trace := left.trace.append rightAtBoundary.trace
      final_eq := by
        rw [CallSemanticTrace.final_append]
        exact rightAtBoundary.final_eq }

def CallSemanticRun.reindexCalls
    {initial final : ParserSemanticState} {calls next : List TokenCall}
    (run : CallSemanticRun initial calls final)
    (equality : calls = next) :
    CallSemanticRun initial next final :=
  equality ▸ run

def CallSemanticRun.reindexFinal
    {initial final next : ParserSemanticState} {calls : List TokenCall}
    (run : CallSemanticRun initial calls final)
    (equality : final = next) :
    CallSemanticRun initial calls next :=
  equality ▸ run

/-- The structurally complete byte-loop trace determines the database/mode
chronology of every real token call. -/
noncomputable def feedTraceCallSemanticTrace
    {base : Nat} {bytes : ByteArray} {cursor : Nat}
    {scan : ParserState.FeedState} {before final : ParserState}
    {calls : List TokenCall}
    (trace : FeedTrace base bytes cursor scan before final calls) :
    CallSemanticTrace (parserSemanticState before) calls := by
  induction trace with
  | endWs => exact .nil _
  | endCurrent => exact .nil _
  | endCarried => exact .nil _
  | whitespaceWs cursor before final calls inBounds isSpace rest ih =>
      simpa using ih
  | currentStop cursor start before error previousConsumed
      inBounds isSpace tokenError =>
      exact .cons (currentCall base bytes start cursor before) rfl (.nil _)
  | currentContinue cursor start before final calls
      inBounds isSpace tokenOk rest ih =>
      refine .cons (currentCall base bytes start cursor before) rfl ?_
      simpa [afterCurrentLine] using ih
  | carriedStop cursor oldBase start oldBytes before error previousConsumed
      inBounds isSpace tokenError =>
      exact .cons
        (carriedCall oldBase oldBytes start base bytes cursor before)
        rfl (.nil _)
  | carriedContinue cursor oldBase start oldBytes before final calls
      inBounds isSpace tokenOk rest ih =>
      refine .cons
        (carriedCall oldBase oldBytes start base bytes cursor before) rfl ?_
      simpa [afterCarriedLine] using ih
  | nonWhitespaceWs cursor before final calls inBounds notSpace rest ih =>
      exact ih
  | nonWhitespaceToken cursor oldToken before final calls
      inBounds notSpace rest ih =>
      exact ih

/-- On a successful byte-loop branch, the semantic chronology ends in the
actual returned database/mode.  Error-stop branches are eliminated rather
than identified with their consumed-byte metadata rewrite. -/
noncomputable def feedTraceCallSemanticRun
    {base : Nat} {bytes : ByteArray} {cursor : Nat}
    {scan : ParserState.FeedState} {before final : ParserState}
    {calls : List TokenCall}
    (trace : FeedTrace base bytes cursor scan before final calls)
    (errorFree : final.db.error? = none) :
    CallSemanticRun (parserSemanticState before) calls
      (parserSemanticState final) := by
  induction trace with
  | endWs => exact ⟨.nil _, rfl⟩
  | endCurrent => exact ⟨.nil _, rfl⟩
  | endCarried => exact ⟨.nil _, rfl⟩
  | whitespaceWs cursor before final calls inBounds isSpace rest ih =>
      exact (ih errorFree).reindexInitial
        (parserSemanticState_updateLine before (base + cursor)
          bytes[cursor]!)
  | currentStop cursor start before error previousConsumed
      inBounds isSpace tokenError =>
      simp [stopWithConsumed] at errorFree
  | currentContinue cursor start before final calls
      inBounds isSpace tokenOk rest ih =>
      let call := currentCall base bytes start cursor before
      have tail : CallSemanticRun (parserSemanticState call.after) calls
          (parserSemanticState final) :=
        (ih errorFree).reindexInitial (by
          simp [call, afterCurrentLine])
      exact tail.cons call rfl
  | carriedStop cursor oldBase start oldBytes before error previousConsumed
      inBounds isSpace tokenError =>
      simp [stopWithConsumed] at errorFree
  | carriedContinue cursor oldBase start oldBytes before final calls
      inBounds isSpace tokenOk rest ih =>
      let call := carriedCall oldBase oldBytes start base bytes cursor before
      have tail : CallSemanticRun (parserSemanticState call.after) calls
          (parserSemanticState final) :=
        (ih errorFree).reindexInitial (by
          simp [call, afterCarriedLine])
      exact tail.cons call rfl
  | nonWhitespaceWs cursor before final calls inBounds notSpace rest ih =>
      exact ih errorFree
  | nonWhitespaceToken cursor oldToken before final calls
      inBounds notSpace rest ih =>
      exact ih errorFree

/-- In a successful byte loop, every logged `feedToken` call itself
succeeded.  This is stronger than final acceptance and is what later permits
each theorem occurrence to be reflected independently. -/
theorem feedTrace_calls_after_errorFree
    {base : Nat} {bytes : ByteArray} {cursor : Nat}
    {scan : ParserState.FeedState} {before final : ParserState}
    {calls : List TokenCall}
    (trace : FeedTrace base bytes cursor scan before final calls)
    (errorFree : final.db.error? = none) :
    ∀ call ∈ calls, call.after.db.error? = none := by
  induction trace with
  | endWs => simp
  | endCurrent => simp
  | endCarried => simp
  | whitespaceWs cursor before final calls inBounds isSpace rest ih =>
      exact ih errorFree
  | currentStop cursor start before error previousConsumed
      inBounds isSpace tokenError =>
      simp [stopWithConsumed] at errorFree
  | currentContinue cursor start before final calls
      inBounds isSpace tokenOk rest ih =>
      intro call member
      rcases List.mem_cons.mp member with rfl | tailMember
      · simpa [afterCurrentLine] using tokenOk
      · exact ih errorFree call tailMember
  | carriedStop cursor oldBase start oldBytes before error previousConsumed
      inBounds isSpace tokenError =>
      simp [stopWithConsumed] at errorFree
  | carriedContinue cursor oldBase start oldBytes before final calls
      inBounds isSpace tokenOk rest ih =>
      intro call member
      rcases List.mem_cons.mp member with rfl | tailMember
      · simpa [afterCarriedLine] using tokenOk
      · exact ih errorFree call tailMember
  | nonWhitespaceWs cursor before final calls inBounds notSpace rest ih =>
      exact ih errorFree
  | nonWhitespaceToken cursor oldToken before final calls
      inBounds notSpace rest ih =>
      exact ih errorFree

/-- `feedAll` carries the same semantic chronology through its optional
carried-token entry branch. -/
noncomputable def feedAllTraceCallSemanticTrace
    {before final : ParserState} {base : Nat} {bytes : ByteArray}
    {calls : List TokenCall}
    (trace : FeedAllTrace before base bytes final calls) :
    CallSemanticTrace (parserSemanticState before) calls := by
  cases trace with
  | ws final calls initialChar feed => exact feedTraceCallSemanticTrace feed
  | carried oldBase token final calls initialChar feed =>
      simpa [parserSemanticState] using feedTraceCallSemanticTrace feed

/-- Successful `feedAll` execution is a semantic run from its actual input
state to its actual output state. -/
noncomputable def feedAllTraceCallSemanticRun
    {before final : ParserState} {base : Nat} {bytes : ByteArray}
    {calls : List TokenCall}
    (trace : FeedAllTrace before base bytes final calls)
    (errorFree : final.db.error? = none) :
    CallSemanticRun (parserSemanticState before) calls
      (parserSemanticState final) := by
  cases trace with
  | ws final calls initialChar feed =>
      exact feedTraceCallSemanticRun feed errorFree
  | carried oldBase token final calls initialChar feed =>
      exact (feedTraceCallSemanticRun feed errorFree).reindexInitial (by
        simp [parserSemanticState])

/-- Successful `feedAll` makes every contained call successful. -/
theorem feedAllTrace_calls_after_errorFree
    {before final : ParserState} {base : Nat} {bytes : ByteArray}
    {calls : List TokenCall}
    (trace : FeedAllTrace before base bytes final calls)
    (errorFree : final.db.error? = none) :
    ∀ call ∈ calls, call.after.db.error? = none := by
  cases trace with
  | ws final calls initialChar feed =>
      exact feedTrace_calls_after_errorFree feed errorFree
  | carried oldBase token final calls initialChar feed =>
      exact feedTrace_calls_after_errorFree feed errorFree

/-- Successful EOF closure cannot alter the database.  Every non-start mode,
and an open scope in start mode, would create an EOF error. -/
theorem closeAtEOF_eq_of_errorFree (state : ParserState) (offset : Nat)
    (errorFree : (closeAtEOF state offset).error? = none) :
    closeAtEOF state offset = state.db := by
  cases modeEq : state.tokp with
  | start =>
      by_cases openScope : state.db.scopes.size > 0
      · simp [Raw.closeAtEOF, modeEq, openScope, DB.mkParseError,
          DB.mkErrorFromEvidence, DB.mkErrorWithEvidence] at errorFree
      · simp [Raw.closeAtEOF, modeEq, openScope]
  | comment inner =>
      simp [Raw.closeAtEOF, modeEq, DB.mkParseError,
        DB.mkErrorFromEvidence, DB.mkErrorWithEvidence] at errorFree
  | const =>
      simp [Raw.closeAtEOF, modeEq, DB.mkParseError,
        DB.mkErrorFromEvidence, DB.mkErrorWithEvidence] at errorFree
  | var =>
      simp [Raw.closeAtEOF, modeEq, DB.mkParseError,
        DB.mkErrorFromEvidence, DB.mkErrorWithEvidence] at errorFree
  | djvars names =>
      simp [Raw.closeAtEOF, modeEq, DB.mkParseError,
        DB.mkErrorFromEvidence, DB.mkErrorWithEvidence] at errorFree
  | math symbols parser =>
      cases parser with
      | mk kind position label =>
          cases kind with
          | float =>
              simp [Raw.closeAtEOF, modeEq, DB.mkParseError,
                DB.mkErrorFromEvidence, DB.mkErrorWithEvidence] at errorFree
          | ess =>
              simp [Raw.closeAtEOF, modeEq, DB.mkParseError,
                DB.mkErrorFromEvidence, DB.mkErrorWithEvidence] at errorFree
          | ax =>
              simp [Raw.closeAtEOF, modeEq, DB.mkParseError,
                DB.mkErrorFromEvidence, DB.mkErrorWithEvidence] at errorFree
          | thm =>
              simp [Raw.closeAtEOF, modeEq, DB.mkParseError,
                DB.mkErrorFromEvidence, DB.mkErrorWithEvidence] at errorFree
  | label position label =>
      simp [Raw.closeAtEOF, modeEq, DB.mkErrorFromEvidence,
        DB.mkErrorWithEvidence] at errorFree
  | includePath resume position =>
      simp [Raw.closeAtEOF, modeEq, DB.mkErrorFromEvidence,
        DB.mkErrorWithEvidence] at errorFree
  | includeClose resume position path =>
      simp [Raw.closeAtEOF, modeEq, DB.mkErrorFromEvidence,
        DB.mkErrorWithEvidence] at errorFree
  | proof proof =>
      simp [Raw.closeAtEOF, modeEq, DB.mkParseError,
        DB.mkErrorFromEvidence, DB.mkErrorWithEvidence] at errorFree

/-- Successful EOF handling contributes either no call or its one exact
trailing call, and ends at the database returned by `done`. -/
noncomputable def doneTraceCallSemanticRun
    {before : ParserState} {eofOffset : Nat} {database : DB}
    {calls : List TokenCall}
    (trace : DoneTrace before eofOffset database calls)
    (errorFree : database.error? = none) :
    Σ finalMode : TokenParser,
      CallSemanticRun (parserSemanticState before) calls
        ⟨database, finalMode⟩ := by
  cases trace with
  | priorError priorError =>
      simp [DB.error, errorFree] at priorError
  | whitespace priorError initialChar =>
      have databaseEq := closeAtEOF_eq_of_errorFree before eofOffset errorFree
      exact ⟨before.tokp,
        { trace := .nil _
          final_eq := by
            exact congrArg
              (fun db => (⟨db, before.tokp⟩ : ParserSemanticState))
              databaseEq.symm }⟩
  | trailingError parserOffset token priorError initialChar afterError =>
      simp [DB.error, errorFree] at afterError
  | trailingClose parserOffset token priorError initialChar afterOk =>
      let call := trailingCall parserOffset eofOffset token before
      have databaseEq := closeAtEOF_eq_of_errorFree call.after eofOffset
        errorFree
      exact ⟨call.after.tokp,
        { trace := .cons call rfl (.nil _)
          final_eq := by
            exact congrArg
              (fun db => (⟨db, call.after.tokp⟩ : ParserSemanticState))
              databaseEq.symm }⟩

/-- `DB.error = false` is exactly absence of an interrupt. -/
theorem db_error_eq_false_iff (database : DB) :
    database.error = false ↔ database.error? = none := by
  constructor
  · intro errorFalse
    cases errorEq : database.error? with
    | none => rfl
    | some error => simp [DB.error, errorEq] at errorFalse
  · intro errorFree
    simp [DB.error, errorFree]

/-- A successful `done` result implies that its input database was already
error-free; EOF handling never repairs an earlier error. -/
theorem doneTrace_before_errorFree
    {before : ParserState} {eofOffset : Nat} {database : DB}
    {calls : List TokenCall}
    (trace : DoneTrace before eofOffset database calls)
    (errorFree : database.error? = none) :
    before.db.error? = none := by
  cases trace with
  | priorError priorError =>
      simp [DB.error, errorFree] at priorError
  | whitespace priorError initialChar =>
      exact (db_error_eq_false_iff before.db).mp priorError
  | trailingError parserOffset token priorError initialChar afterError =>
      exact (db_error_eq_false_iff before.db).mp priorError
  | trailingClose parserOffset token priorError initialChar afterOk =>
      exact (db_error_eq_false_iff before.db).mp priorError

/-- Successful EOF handling likewise makes its optional trailing token call
successful. -/
theorem doneTrace_calls_after_errorFree
    {before : ParserState} {eofOffset : Nat} {database : DB}
    {calls : List TokenCall}
    (trace : DoneTrace before eofOffset database calls)
    (errorFree : database.error? = none) :
    ∀ call ∈ calls, call.after.db.error? = none := by
  cases trace with
  | priorError priorError =>
      simp [DB.error, errorFree] at priorError
  | whitespace priorError initialChar => simp
  | trailingError parserOffset token priorError initialChar afterError =>
      simp [DB.error, errorFree] at afterError
  | trailingClose parserOffset token priorError initialChar afterOk =>
      intro call member
      have callEq : call = trailingCall parserOffset eofOffset token before := by
        simpa using member
      subst call
      exact (db_error_eq_false_iff _).mp afterOk

/-- A successful structurally logged core check is one adjacent semantic run
from the shipped initial parser state through every actual token call. -/
noncomputable def checkBytesCoreRun_callSemanticRun
    {bytes : ByteArray} {config : ModeConfig}
    (run : CheckBytesCoreRun bytes config)
    (errorFree : run.db.error? = none) :
    Σ finalMode : TokenParser,
      CallSemanticRun (parserSemanticState (initialState config)) run.calls
        ⟨run.db, finalMode⟩ := by
  have doneErrorFree : run.doneRun.db.error? = none := by
    rw [← run.db_eq]
    exact errorFree
  have feedErrorFree : run.feedRun.final.db.error? = none :=
    doneTrace_before_errorFree run.doneRun.trace doneErrorFree
  let feedRun := feedAllTraceCallSemanticRun run.feedRun.trace feedErrorFree
  let doneRun := doneTraceCallSemanticRun run.doneRun.trace doneErrorFree
  let combined := feedRun.append doneRun.2
  refine ⟨doneRun.1, ?_⟩
  exact (combined.reindexCalls run.calls_eq.symm).reindexFinal
    (congrArg (fun db => (⟨db, doneRun.1⟩ : ParserSemanticState))
      run.db_eq.symm)

/-- Every call in a successful core run succeeded at its own occurrence. -/
theorem checkBytesCoreRun_calls_after_errorFree
    {bytes : ByteArray} {config : ModeConfig}
    (run : CheckBytesCoreRun bytes config)
    (errorFree : run.db.error? = none) :
    ∀ call ∈ run.calls, call.after.db.error? = none := by
  have doneErrorFree : run.doneRun.db.error? = none := by
    rw [← run.db_eq]
    exact errorFree
  have feedErrorFree : run.feedRun.final.db.error? = none :=
    doneTrace_before_errorFree run.doneRun.trace doneErrorFree
  intro call member
  rw [run.calls_eq] at member
  rcases List.mem_append.mp member with feedMember | doneMember
  · exact feedAllTrace_calls_after_errorFree run.feedRun.trace
      feedErrorFree call feedMember
  · exact doneTrace_calls_after_errorFree run.doneRun.trace
      doneErrorFree call doneMember

/-- Passing the public post-check gate means that it left the core database
unchanged. -/
theorem publicGateTrace_final_eq_core_of_errorFree
    {core final : DB} (trace : PublicGateTrace core final)
    (errorFree : final.error? = none) :
    final = core := by
  cases trace with
  | priorError priorError => rfl
  | accepted coreErrorFree gateAccepted => rfl
  | rejected coreErrorFree gateRejected =>
      simp [DB.mkErrorFromEvidence, DB.mkErrorWithEvidence] at errorFree

/-- A successful public checker run retains the core run's exact semantic
chronology; the consistency gate contributes no token or database step. -/
noncomputable def checkBytesRun_callSemanticRun
    {bytes : ByteArray} {config : ModeConfig}
    (run : CheckBytesRun bytes config)
    (errorFree : run.db.error? = none) :
    Σ finalMode : TokenParser,
      CallSemanticRun (parserSemanticState (initialState config)) run.calls
        ⟨run.db, finalMode⟩ := by
  have databaseEq : run.db = run.coreRun.db :=
    publicGateTrace_final_eq_core_of_errorFree run.gateTrace errorFree
  have coreErrorFree : run.coreRun.db.error? = none := by
    rw [← databaseEq]
    exact errorFree
  let coreRun := checkBytesCoreRun_callSemanticRun run.coreRun coreErrorFree
  refine ⟨coreRun.1, ?_⟩
  exact (coreRun.2.reindexCalls run.calls_eq.symm).reindexFinal
    (congrArg (fun db => (⟨db, coreRun.1⟩ : ParserSemanticState))
      databaseEq.symm)

/-- The computed shipped reader therefore exposes a complete semantic call
run on every accepted byte array. -/
noncomputable def checkBytesLogged_callSemanticRun
    (bytes : ByteArray) (config : ModeConfig := {})
    (errorFree : (checkBytesLogged bytes config).db.error? = none) :
    Σ finalMode : TokenParser,
      CallSemanticRun (parserSemanticState (initialState config))
        (checkBytesLogged bytes config).calls
        ⟨(checkBytesLogged bytes config).db, finalMode⟩ :=
  checkBytesRun_callSemanticRun (checkBytesLogged bytes config) errorFree

/-- Every token call made by an accepted public reader run succeeded at that
exact prefix. -/
theorem checkBytesRun_calls_after_errorFree
    {bytes : ByteArray} {config : ModeConfig}
    (run : CheckBytesRun bytes config)
    (errorFree : run.db.error? = none) :
    ∀ call ∈ run.calls, call.after.db.error? = none := by
  have databaseEq : run.db = run.coreRun.db :=
    publicGateTrace_final_eq_core_of_errorFree run.gateTrace errorFree
  have coreErrorFree : run.coreRun.db.error? = none := by
    rw [← databaseEq]
    exact errorFree
  intro call member
  exact checkBytesCoreRun_calls_after_errorFree run.coreRun coreErrorFree call
    (by simpa [run.calls_eq] using member)

/-! ## Erasing comment administration -/

/-- Any call erased by the reader's significant-token projection is
database-transparent on an accepted run.  A nested opener would create an
error, so the success premise eliminates precisely that malformed branch. -/
theorem insignificantCall_db_eq (call : TokenCall)
    (afterErrorFree : call.after.db.error? = none)
    (insignificant : significantCall? call = none) :
    call.after.db = call.before.db := by
  rw [call.after_eq] at afterErrorFree ⊢
  cases modeEq : call.before.tokp with
  | comment inner =>
      by_cases closeToken : call.origin.token.eqArray "$)".toAscii = true
      · simp [ParserState.feedToken, modeEq, closeToken]
      · by_cases nestedOpen :
            call.origin.token.eqArray "$(".toAscii = true
        · simp [ParserState.feedToken, modeEq, closeToken, nestedOpen,
            ParserState.mkErrorFromEvidence, ParserState.withDB,
            DB.mkErrorFromEvidence, DB.mkErrorWithEvidence] at afterErrorFree
        · simp [ParserState.feedToken, modeEq, closeToken, nestedOpen]
  | start =>
      have commentOpen : call.origin.token.eqArray "$(".toAscii = true := by
        simp [significantCall?, significantToken?, modeEq] at insignificant
        change call.origin.token.eqArray "$(".toAscii = true at insignificant
        exact insignificant
      simp [ParserState.feedToken, modeEq, commentOpen]
  | const =>
      have commentOpen : call.origin.token.eqArray "$(".toAscii = true := by
        simp [significantCall?, significantToken?, modeEq] at insignificant
        change call.origin.token.eqArray "$(".toAscii = true at insignificant
        exact insignificant
      simp [ParserState.feedToken, modeEq, commentOpen]
  | var =>
      have commentOpen : call.origin.token.eqArray "$(".toAscii = true := by
        simp [significantCall?, significantToken?, modeEq] at insignificant
        change call.origin.token.eqArray "$(".toAscii = true at insignificant
        exact insignificant
      simp [ParserState.feedToken, modeEq, commentOpen]
  | djvars names =>
      have commentOpen : call.origin.token.eqArray "$(".toAscii = true := by
        simp [significantCall?, significantToken?, modeEq] at insignificant
        change call.origin.token.eqArray "$(".toAscii = true at insignificant
        exact insignificant
      simp [ParserState.feedToken, modeEq, commentOpen]
  | math symbols parser =>
      have commentOpen : call.origin.token.eqArray "$(".toAscii = true := by
        simp [significantCall?, significantToken?, modeEq] at insignificant
        change call.origin.token.eqArray "$(".toAscii = true at insignificant
        exact insignificant
      simp [ParserState.feedToken, modeEq, commentOpen]
  | label position label =>
      have commentOpen : call.origin.token.eqArray "$(".toAscii = true := by
        simp [significantCall?, significantToken?, modeEq] at insignificant
        change call.origin.token.eqArray "$(".toAscii = true at insignificant
        exact insignificant
      simp [ParserState.feedToken, modeEq, commentOpen]
  | includePath resume position =>
      have commentOpen : call.origin.token.eqArray "$(".toAscii = true := by
        simp [significantCall?, significantToken?, modeEq] at insignificant
        change call.origin.token.eqArray "$(".toAscii = true at insignificant
        exact insignificant
      simp [ParserState.feedToken, modeEq, commentOpen]
  | includeClose resume position path =>
      have commentOpen : call.origin.token.eqArray "$(".toAscii = true := by
        simp [significantCall?, significantToken?, modeEq] at insignificant
        change call.origin.token.eqArray "$(".toAscii = true at insignificant
        exact insignificant
      simp [ParserState.feedToken, modeEq, commentOpen]
  | proof proof =>
      have commentOpen : call.origin.token.eqArray "$(".toAscii = true := by
        simp [significantCall?, significantToken?, modeEq] at insignificant
        change call.origin.token.eqArray "$(".toAscii = true at insignificant
        exact insignificant
      simp [ParserState.feedToken, modeEq, commentOpen]

/-- Quotient the temporary comment wrapper while retaining every other parser
mode.  This is the semantic observation at statement boundaries. -/
def logicalTokenMode : TokenParser → TokenParser
  | .comment inner => logicalTokenMode inner
  | mode => mode

structure ParserObservedState where
  db : DB
  mode : TokenParser

def observedSemanticState (state : ParserSemanticState) :
    ParserObservedState :=
  ⟨state.db, logicalTokenMode state.mode⟩

def parserObservedState (state : ParserState) : ParserObservedState :=
  observedSemanticState (parserSemanticState state)

/-- The concrete refinement relation at statement-prefix boundaries.  It is
the source/runtime instance from which a generic implementation-refinement
interface can later be extracted: the source state agrees with the shipped
database, and token-level administrative work has returned to `.start`. -/
structure SourceParserPrefixAgrees
    (source : SourceState) (parser : ParserObservedState) : Prop where
  mode_eq : parser.mode = .start
  database : RuntimeDBAgrees parser.db source
  interrupt_eq : parser.db.interrupt = false

/-- The concrete parser state created by a successful theorem delimiter,
with its observed boundary and proof-state data retained together. -/
structure ParserProofAnchor (db : DB) (formula : RuntimeFormula)
    (labelPos : Pos) (label : String)
    (observed : ParserObservedState) : Type where
  state : ParserState
  frame : RuntimeFrame
  trim : db.trimFrame' formula = .ok frame
  database_eq : state.db = db
  mode_eq : state.tokp =
    .proof (db.mkProofState labelPos label formula frame)
  observed_eq : parserObservedState state = observed

/-- The observed side of a theorem anchor is exactly its canonical initial
proof state; scanner and source-position fields are intentionally absent. -/
theorem ParserProofAnchor.observed_canonical
    {db : DB} {formula : RuntimeFormula} {labelPos : Pos} {label : String}
    {observed : ParserObservedState}
    (anchor : ParserProofAnchor db formula labelPos label observed) :
    observed = ⟨db, .proof
      (db.mkProofState labelPos label formula anchor.frame)⟩ := by
  calc
    observed = parserObservedState anchor.state := anchor.observed_eq.symm
    _ = ⟨db, .proof
        (db.mkProofState labelPos label formula anchor.frame)⟩ := by
      simp [parserObservedState, observedSemanticState, parserSemanticState,
        anchor.database_eq, anchor.mode_eq, logicalTokenMode]

/-- The authored source machine and shipped parser begin in the refinement
relation without a supplied correspondence witness. -/
theorem initial_sourceParserPrefixAgrees :
    SourceParserPrefixAgrees SourceGSLTState.initialState
      (parserObservedState (InferenceOneShotByteLog.initialState {})) := by
  exact
    { mode_eq := rfl
      database := default_initial_runtimeDBAgrees
      interrupt_eq := rfl }

/-- Erased comment calls are also transparent after quotienting the temporary
comment wrapper. -/
theorem insignificantCall_logicalMode_eq (call : TokenCall)
    (afterErrorFree : call.after.db.error? = none)
    (insignificant : significantCall? call = none) :
    logicalTokenMode call.after.tokp =
      logicalTokenMode call.before.tokp := by
  rw [call.after_eq] at afterErrorFree ⊢
  cases modeEq : call.before.tokp with
  | comment inner =>
      by_cases closeToken : call.origin.token.eqArray "$)".toAscii = true
      · simp [ParserState.feedToken, modeEq, closeToken, logicalTokenMode]
      · by_cases nestedOpen :
            call.origin.token.eqArray "$(".toAscii = true
        · simp [ParserState.feedToken, modeEq, closeToken, nestedOpen,
            ParserState.mkErrorFromEvidence, ParserState.withDB,
            DB.mkErrorFromEvidence, DB.mkErrorWithEvidence] at afterErrorFree
        · simp [ParserState.feedToken, modeEq, closeToken, nestedOpen,
            logicalTokenMode]
  | start =>
      have commentOpen : call.origin.token.eqArray "$(".toAscii = true := by
        simp [significantCall?, significantToken?, modeEq] at insignificant
        change call.origin.token.eqArray "$(".toAscii = true at insignificant
        exact insignificant
      simp [ParserState.feedToken, modeEq, commentOpen, logicalTokenMode]
  | const =>
      have commentOpen : call.origin.token.eqArray "$(".toAscii = true := by
        simp [significantCall?, significantToken?, modeEq] at insignificant
        change call.origin.token.eqArray "$(".toAscii = true at insignificant
        exact insignificant
      simp [ParserState.feedToken, modeEq, commentOpen, logicalTokenMode]
  | var =>
      have commentOpen : call.origin.token.eqArray "$(".toAscii = true := by
        simp [significantCall?, significantToken?, modeEq] at insignificant
        change call.origin.token.eqArray "$(".toAscii = true at insignificant
        exact insignificant
      simp [ParserState.feedToken, modeEq, commentOpen, logicalTokenMode]
  | djvars names =>
      have commentOpen : call.origin.token.eqArray "$(".toAscii = true := by
        simp [significantCall?, significantToken?, modeEq] at insignificant
        change call.origin.token.eqArray "$(".toAscii = true at insignificant
        exact insignificant
      simp [ParserState.feedToken, modeEq, commentOpen, logicalTokenMode]
  | math symbols parser =>
      have commentOpen : call.origin.token.eqArray "$(".toAscii = true := by
        simp [significantCall?, significantToken?, modeEq] at insignificant
        change call.origin.token.eqArray "$(".toAscii = true at insignificant
        exact insignificant
      simp [ParserState.feedToken, modeEq, commentOpen, logicalTokenMode]
  | label position label =>
      have commentOpen : call.origin.token.eqArray "$(".toAscii = true := by
        simp [significantCall?, significantToken?, modeEq] at insignificant
        change call.origin.token.eqArray "$(".toAscii = true at insignificant
        exact insignificant
      simp [ParserState.feedToken, modeEq, commentOpen, logicalTokenMode]
  | includePath resume position =>
      have commentOpen : call.origin.token.eqArray "$(".toAscii = true := by
        simp [significantCall?, significantToken?, modeEq] at insignificant
        change call.origin.token.eqArray "$(".toAscii = true at insignificant
        exact insignificant
      simp [ParserState.feedToken, modeEq, commentOpen, logicalTokenMode]
  | includeClose resume position path =>
      have commentOpen : call.origin.token.eqArray "$(".toAscii = true := by
        simp [significantCall?, significantToken?, modeEq] at insignificant
        change call.origin.token.eqArray "$(".toAscii = true at insignificant
        exact insignificant
      simp [ParserState.feedToken, modeEq, commentOpen, logicalTokenMode]
  | proof proof =>
      have commentOpen : call.origin.token.eqArray "$(".toAscii = true := by
        simp [significantCall?, significantToken?, modeEq] at insignificant
        change call.origin.token.eqArray "$(".toAscii = true at insignificant
        exact insignificant
      simp [ParserState.feedToken, modeEq, commentOpen, logicalTokenMode]

theorem insignificantCall_observedState_eq (call : TokenCall)
    (afterErrorFree : call.after.db.error? = none)
    (insignificant : significantCall? call = none) :
    parserObservedState call.after = parserObservedState call.before := by
  exact congrArg₂
    (fun db mode => (⟨db, mode⟩ : ParserObservedState))
    (insignificantCall_db_eq call afterErrorFree insignificant)
    (insignificantCall_logicalMode_eq call afterErrorFree insignificant)

/-- Chronology after quotienting comment administration.  Each retained entry
is still the exact shipped `feedToken` call that produced the transition. -/
inductive SignificantCallTrace :
    ParserObservedState → List (String × TokenCall) →
      ParserObservedState → Type where
  | nil (state : ParserObservedState) : SignificantCallTrace state [] state
  | cons {initial final : ParserObservedState}
      {entries : List (String × TokenCall)}
      (entry : String × TokenCall)
      (significant : significantCall? entry.2 = some entry)
      (before_eq : parserObservedState entry.2.before = initial)
      (tail : SignificantCallTrace (parserObservedState entry.2.after)
        entries final) :
      SignificantCallTrace initial (entry :: entries) final

def SignificantCallTrace.reindexInitial
    {initial next final : ParserObservedState}
    {entries : List (String × TokenCall)}
    (trace : SignificantCallTrace initial entries final)
    (equality : initial = next) :
    SignificantCallTrace next entries final :=
  equality ▸ trace

def SignificantCallTrace.reindexFinal
    {initial final next : ParserObservedState}
    {entries : List (String × TokenCall)}
    (trace : SignificantCallTrace initial entries final)
    (equality : final = next) :
    SignificantCallTrace initial entries next :=
  equality ▸ trace

theorem significantCall?_some_second {call : TokenCall}
    {entry : String × TokenCall}
    (significant : significantCall? call = some entry) :
    entry.2 = call := by
  unfold significantCall? at significant
  cases tokenEq : significantToken? call with
  | none => simp [tokenEq] at significant
  | some token =>
      simp [tokenEq] at significant
      cases significant
      rfl

/-- The full semantic call chronology canonically quotients to the exact
significant-call chronology.  Comment erasure is derived from successful
calls, not assumed as token equality. -/
noncomputable def CallSemanticTrace.toSignificantCallTrace
    {initial : ParserSemanticState} {calls : List TokenCall}
    (trace : CallSemanticTrace initial calls)
    (callsSuccessful : ∀ call ∈ calls, call.after.db.error? = none) :
    SignificantCallTrace (observedSemanticState initial)
      (calls.filterMap significantCall?)
      (observedSemanticState trace.final) := by
  induction trace with
  | nil state => exact .nil _
  | @cons initial calls call before_eq tail ih =>
      have headSuccessful : call.after.db.error? = none :=
        callsSuccessful call (by simp)
      have tailSuccessful :
          ∀ next ∈ calls, next.after.db.error? = none := by
        intro next member
        exact callsSuccessful next (by simp [member])
      let tailTrace := ih tailSuccessful
      have beforeObserved :
          parserObservedState call.before =
            observedSemanticState initial :=
        congrArg observedSemanticState before_eq
      cases significantEq : significantCall? call with
      | none =>
          have stutter := insignificantCall_observedState_eq call
            headSuccessful significantEq
          have boundary :
              parserObservedState call.after =
                observedSemanticState initial :=
            stutter.trans beforeObserved
          simpa [List.filterMap_cons, significantEq, CallSemanticTrace.final]
            using
            tailTrace.reindexInitial boundary
      | some entry =>
          have entryCall : entry.2 = call :=
            significantCall?_some_second significantEq
          obtain ⟨token, retainedCall⟩ := entry
          change retainedCall = call at entryCall
          subst retainedCall
          simpa [List.filterMap_cons, significantEq, CallSemanticTrace.final]
            using
            SignificantCallTrace.cons (token, call) significantEq
              beforeObserved tailTrace

/-- Accepted public-reader execution, with comments quotiented as
administrative stutters, yields the exact significant-call transition
history from the shipped initial state. -/
noncomputable def checkBytesRun_significantCallTrace
    {bytes : ByteArray} {config : ModeConfig}
    (run : CheckBytesRun bytes config)
    (errorFree : run.db.error? = none) :
    Σ finalMode : TokenParser,
      SignificantCallTrace (parserObservedState (initialState config))
        (run.calls.filterMap significantCall?)
        ⟨run.db, logicalTokenMode finalMode⟩ := by
  let semanticRun := checkBytesRun_callSemanticRun run errorFree
  let significantTrace := semanticRun.2.trace.toSignificantCallTrace
    (checkBytesRun_calls_after_errorFree run errorFree)
  refine ⟨semanticRun.1, ?_⟩
  exact significantTrace.reindexFinal
    (congrArg observedSemanticState semanticRun.2.final_eq)

/-- Default-profile specialization in the vocabulary used by the checked
reader/source boundary. -/
noncomputable def loggedSignificantCallTrace (bytes : ByteArray)
    (errorFree : (checkBytesLogged bytes).db.error? = none) :
    Σ finalMode : TokenParser,
      SignificantCallTrace (parserObservedState (initialState {}))
        (loggedSignificantCalls bytes)
        ⟨(checkBytesLogged bytes).db, logicalTokenMode finalMode⟩ :=
  checkBytesRun_significantCallTrace (checkBytesLogged bytes) errorFree

/-! ## Statement partition of the significant chronology -/

/-- Split a significant chronology at any entry index, retaining the exact
intermediate observed state. -/
noncomputable def SignificantCallTrace.splitAt :
    {initial final : ParserObservedState} →
    {entries : List (String × TokenCall)} →
    (count : Nat) → SignificantCallTrace initial entries final →
    Σ middle : ParserObservedState,
      SignificantCallTrace initial (entries.take count) middle ×'
      SignificantCallTrace middle (entries.drop count) final
  | initial, _, _, 0, trace =>
      ⟨initial, .nil _, trace⟩
  | _, _, _, _ + 1, .nil state =>
      ⟨state, .nil _, .nil _⟩
  | _, _, _, count + 1, .cons entry significant before_eq tail => by
      obtain ⟨middle, left, right⟩ := tail.splitAt count
      exact ⟨middle, .cons entry significant before_eq left, right⟩

/-- Statement-level grouping of the production reader's exact retained calls.
The token spellings of each group are fixed by the corresponding authored
statement occurrence. -/
inductive StatementCallTrace :
    ParserObservedState → List RawStatement →
      List (String × TokenCall) → ParserObservedState → Type where
  | nil (state : ParserObservedState) : StatementCallTrace state [] [] state
  | cons {initial middle final : ParserObservedState}
      {statements : List RawStatement}
      {statementEntries restEntries : List (String × TokenCall)}
      (statement : RawStatement)
      (tokenText_eq : RawStatement.tokenStrings statement =
        statementEntries.map Prod.fst)
      (statementTrace : SignificantCallTrace initial statementEntries middle)
      (tail : StatementCallTrace middle statements restEntries final) :
      StatementCallTrace initial (statement :: statements)
        (statementEntries ++ restEntries) final

/-- Exact ledger text determines the unique statement grouping of a retained
call chronology. -/
noncomputable def SignificantCallTrace.toStatementCallTrace :
    {initial final : ParserObservedState} →
    {entries : List (String × TokenCall)} →
    (statements : List RawStatement) →
    (trace : SignificantCallTrace initial entries final) →
    statements.flatMap RawStatement.tokenStrings = entries.map Prod.fst →
    StatementCallTrace initial statements entries final
  | _, _, entries, [], trace, tokenText_eq => by
      cases entries with
      | nil =>
          cases trace
          exact .nil _
      | cons entry rest => simp at tokenText_eq
  | initial, final, entries, statement :: statements, trace, tokenText_eq => by
      let count := (RawStatement.tokenStrings statement).length
      let statementEntries := entries.take count
      let restEntries := entries.drop count
      obtain ⟨middle, statementTrace, restTrace⟩ := trace.splitAt count
      have statementText :
          RawStatement.tokenStrings statement =
            statementEntries.map Prod.fst := by
        have taken := congrArg (List.take count) tokenText_eq
        simpa [count, statementEntries] using taken
      have restText :
          statements.flatMap RawStatement.tokenStrings =
            restEntries.map Prod.fst := by
        have dropped := congrArg (List.drop count) tokenText_eq
        simpa [count, restEntries] using dropped
      have tail := restTrace.toStatementCallTrace statements restText
      simpa [statementEntries, restEntries, count] using
        StatementCallTrace.cons statement statementText statementTrace tail

/-- **Constructed statement-prefix chronology for one physical source.**
The same-buffer lexical theorem and accepted segmentation determine the
statement grouping of the shipped reader's actual successful calls.  No
caller-provided token equality or parser trace appears in the interface. -/
noncomputable def monolithicStatementCallTrace
    (fileId : String) (bytes : ByteArray)
    (errorFree : (checkBytesLogged bytes).db.error? = none)
    {openSite : LocatedByteSpan} {output : List LocatedByteSpan}
    {statements : List RawStatement}
    (stripped : stripComments bytes.data.toList
      (tokenizeIncrementally fileId bytes) false openSite = .ok output)
    (segmented : segmentStatements (output.map (locatedSpan bytes)) =
      .ok statements) :
    Σ finalMode : TokenParser,
      StatementCallTrace (parserObservedState (initialState {})) statements
        (loggedSignificantCalls bytes)
        ⟨(checkBytesLogged bytes).db, logicalTokenMode finalMode⟩ := by
  let callsTrace := loggedSignificantCallTrace bytes errorFree
  have tokenText_eq :
      statements.flatMap RawStatement.tokenStrings =
        (loggedSignificantCalls bytes).map Prod.fst := by
    rw [← pipelineSource_ledger]
    rw [pipelineSource_ledger_eq_loggedSignificantTokens fileId bytes
      errorFree stripped segmented]
    rfl
  exact ⟨callsTrace.1,
    callsTrace.2.toStatementCallTrace statements tokenText_eq⟩

/-! ## Byte- and provenance-preserving statement chronology

The textual partition above is useful for the grammar boundary, but proof
reflection must retain the exact byte slices consumed by the shipped reader.
The following refinement keeps each source-located token beside its real
`feedToken` call.  Text and spans are both conserved, so downstream theorem
discharge never reconstructs bytes from strings.
-/

/-- Retain a significant located token together with the exact shipped call
that consumed it. -/
def significantLocatedEntry? (fileId : String) (call : TokenCall) :
    Option (LocatedToken × TokenCall) :=
  (significantLocatedCall? fileId call).map fun token => (token, call)

theorem significantLocatedEntry?_some_second
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall}
    (h : significantLocatedEntry? fileId call = some entry) :
    entry.2 = call := by
  unfold significantLocatedEntry? at h
  cases hlocated : significantLocatedCall? fileId call with
  | none => simp [hlocated] at h
  | some token =>
      simp [hlocated] at h
      cases h
      rfl

theorem significantLocatedEntry?_none_significantCall?_none
    {fileId : String} {call : TokenCall}
    (h : significantLocatedEntry? fileId call = none) :
    significantCall? call = none := by
  have hlocated : significantLocatedCall? fileId call = none := by
    unfold significantLocatedEntry? at h
    cases hoption : significantLocatedCall? fileId call with
    | none => rfl
    | some token => simp [hoption] at h
  have htoken : significantToken? call = none := by
    have htext := significantLocatedCall?_text fileId call
    rw [hlocated] at htext
    exact htext.symm
  simp [significantCall?, htoken]

/-- The ASCII-byte rendering used by the source pipeline is injective.  This
lets fixed authored literals be recovered from text conservation without
assuming a second byte decoder. -/
theorem tokenText_injective : Function.Injective tokenText := by
  intro left right equality
  apply (show Function.Injective
      (List.map fun byte : UInt8 => Char.ofNat byte.toNat) from ?_)
  · exact String.ofList_injective equality
  · apply Function.Injective.list_map
    intro leftByte rightByte charEquality
    dsimp only at charEquality
    have ofNat_eq_ofUInt8 (byte : UInt8) :
        Char.ofNat byte.toNat = Char.ofUInt8 byte := by
      have valid : byte.toNat.isValidChar :=
        Or.inl (lt_trans byte.toNat_lt (by decide))
      rw [Char.ofNat, dif_pos valid]
      apply Char.ext
      rfl
    rw [ofNat_eq_ofUInt8 leftByte, ofNat_eq_ofUInt8 rightByte]
      at charEquality
    exact UInt8.toUInt32_inj.mp (congrArg Char.val charEquality)

/-- A retained located entry carries precisely the bytes submitted by its
shipped call. -/
theorem significantLocatedEntry?_some_bytes
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall}
    (h : significantLocatedEntry? fileId call = some entry) :
    entry.1.bytes = callBytes call := by
  unfold significantLocatedEntry? at h
  cases hlocated : significantLocatedCall? fileId call with
  | none => simp [hlocated] at h
  | some token =>
      simp [hlocated] at h
      cases h
      unfold significantLocatedCall? at hlocated
      cases modeEq : call.before.tokp <;> simp [modeEq] at hlocated
      all_goals
        rcases hlocated with ⟨_, rfl⟩
        rfl

/-- The exact byte slice submitted by a logged call. -/
def shippedToken (call : TokenCall) : ByteSlice :=
  InferenceOneShotByteLog.Raw.TokenOrigin.token call.origin

@[simp] theorem callBytes_eq_shippedToken (call : TokenCall) :
    callBytes call = sliceBytes (shippedToken call) := rfl

/-- Exact two-byte content determines every fixed-command observation made
by the shipped parser.  This is the small extensionality boundary needed for
statement dispatch; it does not identify slices or their backing buffers. -/
theorem sliceBytes_eq_pair_fields
    {token : ByteSlice} {first second : UInt8}
    (bytes_eq : sliceBytes token = [first, second]) :
    token.len = 2 ∧ token[0]! = first ∧ token[1]! = second := by
  have size_eq : token.size = 2 := by
    have lengths := congrArg List.length bytes_eq
    simpa [sliceBytes_length] using lengths
  have bytes_eq' := bytes_eq
  unfold sliceBytes at bytes_eq'
  simp only [size_eq] at bytes_eq'
  simp only [sliceBytesLoop] at bytes_eq'
  have fields : token[0] = first ∧ token[1] = second := by
    simpa [size_eq] using List.cons.inj bytes_eq'
  simpa [ByteSlice.len, size_eq] using fields

/-- The head observation of a nonempty slice is determined by its extracted
byte list. -/
theorem sliceBytes_eq_cons_fields
    {token : ByteSlice} {head : UInt8} {tail : List UInt8}
    (bytes_eq : sliceBytes token = head :: tail) :
    token.len = tail.length + 1 ∧ token[0]! = head := by
  have size_eq : token.size = tail.length + 1 := by
    have lengths := congrArg List.length bytes_eq
    simpa [sliceBytes_length, Nat.add_comm] using lengths
  have bytes_eq' := bytes_eq
  unfold sliceBytes at bytes_eq'
  simp only [size_eq] at bytes_eq'
  simp only [sliceBytesLoop] at bytes_eq'
  have head_eq : token[0] = head := by
    have := (List.cons.inj bytes_eq').1
    simpa [size_eq] using this
  have head_in_bounds : 0 < token.size := by omega
  exact ⟨by simpa [ByteSlice.len] using size_eq,
    by rw [getElem!_pos token 0 head_in_bounds]; exact head_eq⟩

/-- Source label bytes cannot begin with the Metamath command marker. -/
theorem labelBytesValid_head_ne_dollar {head : UInt8} {tail : List UInt8}
    (valid : labelBytesValid (head :: tail) = true) :
    head ≠ '$'.toUInt8 := by
  intro head_eq
  subst head
  simp only [labelBytesValid, List.isEmpty_cons, Bool.not_false,
    Bool.true_and, List.all_cons, Bool.and_eq_true] at valid
  have dollarInvalid : labelByte '$'.toUInt8 = false := by decide
  rw [dollarInvalid] at valid
  exact Bool.noConfusion valid.1

/-- A source-valid label cannot begin with the compressed-proof opener. -/
theorem labelBytesValid_head_ne_open {head : UInt8} {tail : List UInt8}
    (valid : labelBytesValid (head :: tail) = true) :
    head ≠ '('.toUInt8 := by
  intro head_eq
  subst head
  simp only [labelBytesValid, List.isEmpty_cons, Bool.not_false,
    Bool.true_and, List.all_cons, Bool.and_eq_true] at valid
  have openInvalid : labelByte '('.toUInt8 = false := by decide
  rw [openInvalid] at valid
  exact Bool.noConfusion valid.1

/-- Source math bytes cannot begin with the Metamath command marker. -/
theorem mathBytesValid_head_ne_dollar {head : UInt8} {tail : List UInt8}
    (valid : mathBytesValid (head :: tail) = true) :
    head ≠ '$'.toUInt8 := by
  intro head_eq
  subst head
  simp only [mathBytesValid, List.isEmpty_cons, Bool.not_false,
    Bool.true_and, List.all_cons, Bool.and_eq_true] at valid
  have dollarInvalid : mathByte '$'.toUInt8 = false := by decide
  rw [dollarInvalid] at valid
  exact Bool.noConfusion valid.1

/-- A byte list whose head is not `$` cannot be any two-byte command. -/
theorem nonDollarHead_ne_commandPair {head : UInt8} {tail : List UInt8}
    {second : UInt8} (headNeDollar : head ≠ '$'.toUInt8) :
    head :: tail ≠ [36, second] := by
  intro equality
  have dollarByte : (36 : UInt8) = '$'.toUInt8 := by decide
  apply headNeDollar
  rw [← dollarByte]
  exact (List.cons.inj equality).1

/-- Away from the authored unknown marker, the normal-proof charset is
exactly the label charset. -/
theorem proofNameCharset_to_label {name : LocatedName}
    (charset : NameCharset proofTokenValid name)
    (notUnknown : name.name ≠ "?") :
    NameCharset labelBytesValid name := by
  obtain ⟨bytes, valid, name_eq⟩ := charset
  refine ⟨bytes, ?_, name_eq⟩
  have cases : labelBytesValid bytes = true ∨
      bytes =
        SourceGSLTStatementPlan.sourceStatementPlan.unknownProof.codepoints.map
          UInt8.ofNat := by
    simpa [proofTokenValid] using valid
  rcases cases with labelValid | unknownBytes
  · exact labelValid
  · exfalso
    apply notUnknown
    rw [name_eq, unknownBytes]
    rfl

/-- Every source-valid math byte is accepted by the shipped token-local
classifier.  The converse is intentionally false for space: token splitting,
not `toMath`, excludes whitespace from a submitted token. -/
theorem mathByte_implies_isMathChar (byte : UInt8)
    (valid : mathByte byte = true) :
    Metamath.Verify.isMathChar byte = true := by
  have exhaustive : ∀ index : Fin 256,
      mathByte (UInt8.ofNat index.val) = true →
        Metamath.Verify.isMathChar (UInt8.ofNat index.val) = true := by
    set_option maxRecDepth 100000 in
      decide
  have byte_lt : byte.toNat < 256 := byte.toBitVec.isLt
  have valid' : mathByte (UInt8.ofNat byte.toNat) = true := by
    simpa [UInt8.ofNat_toNat] using valid
  simpa [UInt8.ofNat_toNat] using
    exhaustive ⟨byte.toNat, byte_lt⟩ valid'

example :
    mathByte ' '.toUInt8 = false ∧
      Metamath.Verify.isMathChar ' '.toUInt8 = true := by
  decide

/-- The shipped math lexer as a fold over the exact slice contents. -/
theorem toMath_eq_fold (token : ByteSlice) :
    Metamath.Verify.toMath token =
      (((sliceBytes token).foldl
          (fun (result : MProd Bool String) byte =>
            ⟨if Metamath.Verify.isMathChar byte then result.fst else false,
              result.snd.push (Metamath.Verify.uint8ToChar byte)⟩)
          ⟨true, ""⟩).fst,
        ((sliceBytes token).foldl
          (fun (result : MProd Bool String) byte =>
            ⟨if Metamath.Verify.isMathChar byte then result.fst else false,
              result.snd.push (Metamath.Verify.uint8ToChar byte)⟩)
          ⟨true, ""⟩).snd) := by
  have run_eq : Metamath.Verify.toMath token =
      (fun (result : MProd Bool String) => (result.fst, result.snd))
        (ByteSlice.forIn (m := Id) token
          (⟨true, ""⟩ : MProd Bool String)
          (fun byte result =>
            if Metamath.Verify.isMathChar byte = true then
              pure (ForInStep.yield
                (⟨result.fst,
                  result.snd.push (Metamath.Verify.uint8ToChar byte)⟩ :
                    MProd Bool String))
            else
              pure (ForInStep.yield
                (⟨false,
                  result.snd.push (Metamath.Verify.uint8ToChar byte)⟩ :
                    MProd Bool String)))) := rfl
  rw [run_eq, byteSlice_forIn_yield (β := MProd Bool String) token _
    (fun byte result =>
      ⟨if Metamath.Verify.isMathChar byte then result.fst else false,
        result.snd.push (Metamath.Verify.uint8ToChar byte)⟩)
    (fun byte result => by
      by_cases valid : Metamath.Verify.isMathChar byte = true
      · rw [if_pos valid, if_pos valid]
      · rw [if_neg valid, if_neg (by simpa using valid)]),
    ← SourceGSLTCompressedMMLean4.sliceBytes_eq_sliceList]

theorem mathFold_fst (bytes : List UInt8) :
    ∀ (initialValid : Bool) (initialText : String),
      (bytes.foldl
          (fun (result : MProd Bool String) byte =>
            ⟨if Metamath.Verify.isMathChar byte then result.fst else false,
              result.snd.push (Metamath.Verify.uint8ToChar byte)⟩)
          ⟨initialValid, initialText⟩).fst =
        (initialValid && bytes.all Metamath.Verify.isMathChar)
  | initialValid, initialText => by
      induction bytes generalizing initialValid initialText with
      | nil => simp
      | cons byte rest inductionHypothesis =>
          simp only [List.foldl_cons, List.all_cons]
          rw [inductionHypothesis]
          by_cases valid : Metamath.Verify.isMathChar byte = true <;>
            simp [valid]

theorem mathFold_snd (bytes : List UInt8) :
    ∀ (initialValid : Bool) (initialText : String),
      (bytes.foldl
          (fun (result : MProd Bool String) byte =>
            ⟨if Metamath.Verify.isMathChar byte then result.fst else false,
              result.snd.push (Metamath.Verify.uint8ToChar byte)⟩)
          ⟨initialValid, initialText⟩).snd =
        bytes.foldl
          (fun text byte =>
            text.push (Metamath.Verify.uint8ToChar byte)) initialText
  | initialValid, initialText => by
      induction bytes generalizing initialValid initialText with
      | nil => rfl
      | cons byte rest inductionHypothesis =>
          simp only [List.foldl_cons]
          rw [inductionHypothesis]

/-- On source-valid math bytes, the shipped lexer returns exactly the source
token text. -/
theorem toMath_of_mathBytes {token : ByteSlice}
    (valid : mathBytesValid (sliceBytes token) = true) :
    Metamath.Verify.toMath token =
      (true, tokenText (sliceBytes token)) := by
  have allValid :
      (sliceBytes token).all Metamath.Verify.isMathChar = true := by
    have sourceAll : (sliceBytes token).all mathByte = true := by
      simp only [mathBytesValid, Bool.and_eq_true] at valid
      exact valid.2
    rw [List.all_eq_true] at sourceAll ⊢
    intro byte member
    exact mathByte_implies_isMathChar byte (sourceAll byte member)
  rw [toMath_eq_fold, mathFold_fst, mathFold_snd,
    SourceGSLTCompressedParserComposition.foldl_push_eq_tokenText,
    allValid]
  apply Prod.ext <;> [skip; apply String.ext] <;> simp

/-- A retained call cannot begin inside the reader's temporary comment
wrapper. -/
theorem significantLocatedEntry?_some_before_not_comment
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall}
    (h : significantLocatedEntry? fileId call = some entry) :
    ∀ inner, call.before.tokp ≠ .comment inner := by
  intro inner modeEq
  unfold significantLocatedEntry? significantLocatedCall? at h
  simp [modeEq] at h

/-- At retained-token boundaries the logical mode is the actual parser mode;
the quotient changes only calls that were erased. -/
theorem actualMode_eq_of_logicalMode_eq_of_significant
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {mode : TokenParser}
    (significant : significantLocatedEntry? fileId call = some entry)
    (logical : logicalTokenMode call.before.tokp = mode) :
    call.before.tokp = mode := by
  cases modeEq : call.before.tokp with
  | start => simpa [modeEq, logicalTokenMode] using logical
  | comment inner =>
      exact absurd modeEq
        (significantLocatedEntry?_some_before_not_comment significant inner)
  | const => simpa [modeEq, logicalTokenMode] using logical
  | var => simpa [modeEq, logicalTokenMode] using logical
  | djvars values => simpa [modeEq, logicalTokenMode] using logical
  | math values parser => simpa [modeEq, logicalTokenMode] using logical
  | label position label => simpa [modeEq, logicalTokenMode] using logical
  | includePath resume position =>
      simpa [modeEq, logicalTokenMode] using logical
  | includeClose resume position path =>
      simpa [modeEq, logicalTokenMode] using logical
  | proof proof => simpa [modeEq, logicalTokenMode] using logical

/-- An observed-state boundary plus retention recovers the call's exact live
database and non-comment parser mode. -/
theorem call_before_fields_of_observed
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall}
    {db : DB} {mode : TokenParser}
    (significant : significantLocatedEntry? fileId call = some entry)
    (observed : parserObservedState call.before = ⟨db, mode⟩) :
    call.before.db = db ∧ call.before.tokp = mode := by
  have database := congrArg ParserObservedState.db observed
  have logical := congrArg ParserObservedState.mode observed
  refine ⟨database, ?_⟩
  exact actualMode_eq_of_logicalMode_eq_of_significant significant logical

/-- Exact located bytes decide the shipped fixed-literal comparison. -/
theorem retainedCall_eqArray_true
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {literal : ByteArray}
    (significant : significantLocatedEntry? fileId call = some entry)
    (bytes_eq : entry.1.bytes = literal.data.toList) :
    (shippedToken call).eqArray literal = true := by
  rw [SourceGSLTCompressedParserComposition.eqArray_true_iff]
  rw [← callBytes_eq_shippedToken]
  exact (significantLocatedEntry?_some_bytes significant).symm.trans bytes_eq

/-- Exact located bytes also decide a negative fixed-literal comparison. -/
theorem retainedCall_eqArray_false
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {literal : ByteArray}
    (significant : significantLocatedEntry? fileId call = some entry)
    (bytes_ne : entry.1.bytes ≠ literal.data.toList) :
    (shippedToken call).eqArray literal = false := by
  apply SourceGSLTCompressedParserComposition.eqArray_eq_false_of_ne
  rw [← callBytes_eq_shippedToken]
  intro equality
  exact bytes_ne
    ((significantLocatedEntry?_some_bytes significant).trans equality)

/-- Exact two-byte content of a retained entry determines the fixed-command
fields observed by `ParserState.feedToken`. -/
theorem retainedCall_pair_fields
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {first second : UInt8}
    (significant : significantLocatedEntry? fileId call = some entry)
    (bytes_eq : entry.1.bytes = [first, second]) :
    (shippedToken call).len = 2 ∧
      (shippedToken call)[0]! = first ∧
      (shippedToken call)[1]! = second := by
  apply sliceBytes_eq_pair_fields
  rw [← callBytes_eq_shippedToken]
  exact (significantLocatedEntry?_some_bytes significant).symm.trans
    bytes_eq

/-- A spelling equality against an authored byte literal recovers those exact
bytes. -/
theorem retainedBytes_eq_of_spelling
    {entry : LocatedToken × TokenCall} {text : String}
    {bytes : List UInt8}
    (spelling : tokenText entry.1.bytes = text)
    (authored : tokenText bytes = text) :
    entry.1.bytes = bytes :=
  tokenText_injective (spelling.trans authored.symm)

/-- Charset provenance and exact spelling characterize the shipped label
lexer on the retained call. -/
theorem retainedCall_toLabel
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {name : LocatedName}
    (significant : significantLocatedEntry? fileId call = some entry)
    (spelling : tokenText entry.1.bytes = name.name)
    (charset : NameCharset labelBytesValid name) :
    Metamath.Verify.toLabel (shippedToken call) = (true, name.name) := by
  obtain ⟨bytes, valid, name_eq⟩ := charset
  have entryBytes : entry.1.bytes = bytes :=
    tokenText_injective (spelling.trans name_eq)
  have sliceBytesEq : sliceBytes (shippedToken call) = bytes := by
    rw [← callBytes_eq_shippedToken]
    exact (significantLocatedEntry?_some_bytes significant).symm.trans
      entryBytes
  rw [SourceGSLTCompressedParserComposition.toLabel_of_labelBytes
    (by rw [sliceBytesEq]
        exact SourceGSLTCompressedParserComposition.labelBytesValid_all_isLabelChar
          valid)]
  rw [sliceBytesEq, ← name_eq]

/-- Charset provenance and exact spelling characterize the shipped math
lexer on the retained call. -/
theorem retainedCall_toMath
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {name : LocatedName}
    (significant : significantLocatedEntry? fileId call = some entry)
    (spelling : tokenText entry.1.bytes = name.name)
    (charset : NameCharset mathBytesValid name) :
    Metamath.Verify.toMath (shippedToken call) = (true, name.name) := by
  obtain ⟨bytes, valid, name_eq⟩ := charset
  have entryBytes : entry.1.bytes = bytes :=
    tokenText_injective (spelling.trans name_eq)
  have sliceBytesEq : sliceBytes (shippedToken call) = bytes := by
    rw [← callBytes_eq_shippedToken]
    exact (significantLocatedEntry?_some_bytes significant).symm.trans
      entryBytes
  rw [toMath_of_mathBytes (by rw [sliceBytesEq]; exact valid)]
  rw [sliceBytesEq, ← name_eq]

/-- A retained source-label token in `.start` enters the shipped label
state with the reader's own position.  The proof derives the fixed-command
branch exclusion from the authored label charset. -/
theorem retainedCall_startLabel
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB} {name : LocatedName}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before = ⟨db, .start⟩)
    (spelling : tokenText entry.1.bytes = name.name)
    (charset : NameCharset labelBytesValid name) :
    parserObservedState call.after =
      ⟨db, .label (call.before.mkPos call.origin.parserOffset) name.name⟩ := by
  obtain ⟨bytes, valid, name_eq⟩ := charset
  have entryBytes : entry.1.bytes = bytes :=
    tokenText_injective (spelling.trans name_eq)
  cases bytes with
  | nil => simp [labelBytesValid] at valid
  | cons head tail =>
      have headNeDollar := labelBytesValid_head_ne_dollar valid
      have sliceBytesEq : sliceBytes (shippedToken call) = head :: tail := by
        rw [← callBytes_eq_shippedToken]
        exact (significantLocatedEntry?_some_bytes significant).symm.trans
          entryBytes
      have headField := (sliceBytes_eq_cons_fields sliceBytesEq).2
      have headField' : call.origin.token[0]! = head := by
        simpa [shippedToken] using headField
      have dollarByte : (36 : UInt8) = '$'.toUInt8 := by decide
      have notCommentBytes :
          entry.1.bytes ≠ "$(".toAscii.data.toList := by
        intro equality
        rw [entryBytes] at equality
        change head :: tail = [36, 40] at equality
        apply headNeDollar
        rw [← dollarByte]
        exact (List.cons.inj equality).1
      have notIncludeBytes :
          entry.1.bytes ≠ "$[".toAscii.data.toList := by
        intro equality
        rw [entryBytes] at equality
        change head :: tail = [36, 91] at equality
        apply headNeDollar
        rw [← dollarByte]
        exact (List.cons.inj equality).1
      have notComment :
          call.origin.token.eqArray "$(".toAscii = false := by
        simpa [shippedToken] using
          retainedCall_eqArray_false significant notCommentBytes
      have notInclude :
          call.origin.token.eqArray "$[".toAscii = false := by
        simpa [shippedToken] using
          retainedCall_eqArray_false significant notIncludeBytes
      have lexed : Metamath.Verify.toLabel call.origin.token =
          (true, name.name) := by
        simpa [shippedToken] using
          retainedCall_toLabel significant spelling
            ⟨head :: tail, valid, name_eq⟩
      obtain ⟨beforeDb, beforeMode⟩ :=
        call_before_fields_of_observed significant before_eq
      rw [call.after_eq]
      simp [ParserState.feedToken, ParserState.label, beforeDb, beforeMode,
        notComment, notInclude, headField', headNeDollar, lexed,
        parserObservedState, observedSemanticState, parserSemanticState,
        logicalTokenMode]

/-- A retained source math token advances the shipped math accumulator.
`isConstant` chooses the exact runtime lookup branch; source/runtime
agreement supplies that lookup in the corollaries below. -/
theorem retainedCall_mathDeclaredSymbol
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB} {name : LocatedName}
    {symbols : Array Sym} {parser : TokensParser}
    (isConstant : Bool)
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before =
      ⟨db, .math symbols parser⟩)
    (spelling : tokenText entry.1.bytes = name.name)
    (charset : NameCharset mathBytesValid name)
    (lookup : db.find? name.name =
      if isConstant then some (.const name.name)
      else some (.var name.name))
    (active : isConstant = false →
      db.isActiveVar name.name = true) :
    parserObservedState call.after =
      ⟨db, .math (symbols.push
        (if isConstant then .const name.name else .var name.name)) parser⟩ := by
  obtain ⟨bytes, valid, name_eq⟩ := charset
  have entryBytes : entry.1.bytes = bytes :=
    tokenText_injective (spelling.trans name_eq)
  cases bytes with
  | nil => simp [mathBytesValid] at valid
  | cons head tail =>
      have headNeDollar := mathBytesValid_head_ne_dollar valid
      have notCommentBytes :
          entry.1.bytes ≠ "$(".toAscii.data.toList := by
        rw [entryBytes]
        change head :: tail ≠ [36, 40]
        exact nonDollarHead_ne_commandPair headNeDollar
      have notIncludeBytes :
          entry.1.bytes ≠ "$[".toAscii.data.toList := by
        rw [entryBytes]
        change head :: tail ≠ [36, 91]
        exact nonDollarHead_ne_commandPair headNeDollar
      have notDelimiterBytes :
          entry.1.bytes ≠ parser.k.delim.data.toList := by
        rw [entryBytes]
        cases parser.k <;>
          first
          | (change head :: tail ≠ [36, 46];
             exact nonDollarHead_ne_commandPair headNeDollar)
          | (change head :: tail ≠ [36, 61];
             exact nonDollarHead_ne_commandPair headNeDollar)
      have notComment :
          call.origin.token.eqArray "$(".toAscii = false := by
        simpa [shippedToken] using
          retainedCall_eqArray_false significant notCommentBytes
      have notInclude :
          call.origin.token.eqArray "$[".toAscii = false := by
        simpa [shippedToken] using
          retainedCall_eqArray_false significant notIncludeBytes
      have notDelimiter :
          call.origin.token.eqArray parser.k.delim = false := by
        simpa [shippedToken] using
          retainedCall_eqArray_false significant notDelimiterBytes
      have lexed : Metamath.Verify.toMath call.origin.token =
          (true, name.name) := by
        simpa [shippedToken] using
          retainedCall_toMath significant spelling
            ⟨head :: tail, valid, name_eq⟩
      obtain ⟨beforeDb, beforeMode⟩ :=
        call_before_fields_of_observed significant before_eq
      rw [call.after_eq]
      cases isConstant with
      | false =>
          have active' := active rfl
          simp [ParserState.feedToken, ParserState.withMath, beforeDb,
            beforeMode, notComment, notInclude, notDelimiter, lexed, lookup,
            active', parserObservedState, observedSemanticState,
            parserSemanticState, logicalTokenMode]
          change db = db ∧ _ = _
          exact ⟨rfl, rfl⟩
      | true =>
          simp [ParserState.feedToken, ParserState.withMath, beforeDb,
            beforeMode, notComment, notInclude, notDelimiter, lexed, lookup,
            parserObservedState, observedSemanticState, parserSemanticState,
            logicalTokenMode]
          change db = db ∧ _ = _
          exact ⟨rfl, rfl⟩

theorem retainedCall_mathConstant
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB} {name : LocatedName}
    {symbols : Array Sym} {parser : TokensParser}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before =
      ⟨db, .math symbols parser⟩)
    (spelling : tokenText entry.1.bytes = name.name)
    (charset : NameCharset mathBytesValid name)
    (lookup : db.find? name.name = some (.const name.name)) :
    parserObservedState call.after =
      ⟨db, .math (symbols.push (.const name.name)) parser⟩ := by
  simpa using retainedCall_mathDeclaredSymbol true significant before_eq
    spelling charset lookup (by simp)

theorem retainedCall_mathVariable
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB} {name : LocatedName}
    {symbols : Array Sym} {parser : TokensParser}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before =
      ⟨db, .math symbols parser⟩)
    (spelling : tokenText entry.1.bytes = name.name)
    (charset : NameCharset mathBytesValid name)
    (lookup : db.find? name.name = some (.var name.name))
    (active : db.isActiveVar name.name = true) :
    parserObservedState call.after =
      ⟨db, .math (symbols.push (.var name.name)) parser⟩ := by
  simpa using retainedCall_mathDeclaredSymbol false significant before_eq
    spelling charset lookup (by simpa)

/-! ## Fixed statement-boundary transitions -/

/-- Generic fixed-command dispatch from `.start`, derived from exact retained
bytes.  The fallback remains the shipped label transition rather than a
second source-side dispatcher. -/
theorem retainedCall_startCommand
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB} {second : UInt8}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before = ⟨db, .start⟩)
    (bytes_eq : entry.1.bytes = [36, second])
    (notCommentBytes : entry.1.bytes ≠ "$(".toAscii.data.toList)
    (notIncludeBytes : entry.1.bytes ≠ "$[".toAscii.data.toList) :
    parserObservedState call.after =
      match Metamath.Verify.uint8ToChar second with
      | '{' => ⟨db.pushScope, .start⟩
      | '}' =>
          ⟨db.popScope (call.before.mkPos call.origin.parserOffset), .start⟩
      | 'c' => ⟨db, .const false⟩
      | 'v' => ⟨db, .var false⟩
      | 'd' => ⟨db, .djvars #[]⟩
      | _ => parserObservedState
          (call.before.label (call.before.mkPos call.origin.parserOffset)
            call.origin.token) := by
  have commandFields := retainedCall_pair_fields significant bytes_eq
  have notComment :=
    retainedCall_eqArray_false significant notCommentBytes
  have notInclude :=
    retainedCall_eqArray_false significant notIncludeBytes
  have commandFields' : call.origin.token.len = 2 ∧
      call.origin.token[0]! = 36 ∧
      call.origin.token[1]! = second := by
    simpa [shippedToken] using commandFields
  have notComment' : call.origin.token.eqArray "$(".toAscii = false := by
    simpa [shippedToken] using notComment
  have notInclude' : call.origin.token.eqArray "$[".toAscii = false := by
    simpa [shippedToken] using notInclude
  have dollarByte : (36 : UInt8) = '$'.toUInt8 := by decide
  obtain ⟨beforeDb, beforeMode⟩ :=
    call_before_fields_of_observed significant before_eq
  rw [call.after_eq]
  simp [ParserState.feedToken, beforeDb, beforeMode, notComment',
    notInclude', commandFields'.1, commandFields'.2.1,
    commandFields'.2.2, dollarByte, parserObservedState,
    observedSemanticState, parserSemanticState, ParserState.withDB]
  split <;> simp_all [logicalTokenMode]

/-- Generic `$f`/`$e`/`$a`/`$p` dispatch from the shipped label state.
The statement kind is data, and its expected command character is the only
branch-specific premise. -/
theorem retainedCall_statementKeyword
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB}
    {label : String} {labelPos : Pos} {second : UInt8}
    (kind : TokensKind)
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before =
      ⟨db, .label labelPos label⟩)
    (bytes_eq : entry.1.bytes = [36, second])
    (notCommentBytes : entry.1.bytes ≠ "$(".toAscii.data.toList)
    (notIncludeBytes : entry.1.bytes ≠ "$[".toAscii.data.toList)
    (command_eq : Metamath.Verify.uint8ToChar second =
      match kind with
      | .float => 'f'
      | .ess => 'e'
      | .ax => 'a'
      | .thm => 'p') :
    parserObservedState call.after =
      ⟨db, .math #[] ⟨kind, labelPos, label⟩⟩ := by
  have commandFields := retainedCall_pair_fields significant bytes_eq
  have commandFields' : call.origin.token.len = 2 ∧
      call.origin.token[0]! = 36 ∧
      call.origin.token[1]! = second := by
    simpa [shippedToken] using commandFields
  have notComment : call.origin.token.eqArray "$(".toAscii = false := by
    simpa [shippedToken] using
      retainedCall_eqArray_false significant notCommentBytes
  have notInclude : call.origin.token.eqArray "$[".toAscii = false := by
    simpa [shippedToken] using
      retainedCall_eqArray_false significant notIncludeBytes
  have dollarByte : (36 : UInt8) = '$'.toUInt8 := by decide
  obtain ⟨beforeDb, beforeMode⟩ :=
    call_before_fields_of_observed significant before_eq
  rw [call.after_eq]
  cases kind <;>
    simp [ParserState.feedToken, beforeDb, beforeMode, notComment,
      notInclude, commandFields'.1, commandFields'.2.1,
      commandFields'.2.2, dollarByte, command_eq, parserObservedState,
      observedSemanticState, parserSemanticState, logicalTokenMode]

theorem retainedCall_floatKeyword
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB}
    {label : String} {labelPos : Pos}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before =
      ⟨db, .label labelPos label⟩)
    (spelling : tokenText entry.1.bytes = "$f") :
    parserObservedState call.after =
      ⟨db, .math #[] ⟨.float, labelPos, label⟩⟩ := by
  have entryBytes : entry.1.bytes = floatKeywordBytes :=
    retainedBytes_eq_of_spelling spelling (by rfl)
  have entryPair : entry.1.bytes = [36, 102] := by
    change entry.1.bytes = [36, 102] at entryBytes
    exact entryBytes
  exact retainedCall_statementKeyword .float significant before_eq
    entryPair (by rw [entryPair]; decide) (by rw [entryPair]; decide)
    (by decide)

theorem retainedCall_essentialKeyword
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB}
    {label : String} {labelPos : Pos}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before =
      ⟨db, .label labelPos label⟩)
    (spelling : tokenText entry.1.bytes = "$e") :
    parserObservedState call.after =
      ⟨db, .math #[] ⟨.ess, labelPos, label⟩⟩ := by
  have entryBytes : entry.1.bytes = essentialKeywordBytes :=
    retainedBytes_eq_of_spelling spelling (by rfl)
  have entryPair : entry.1.bytes = [36, 101] := by
    change entry.1.bytes = [36, 101] at entryBytes
    exact entryBytes
  exact retainedCall_statementKeyword .ess significant before_eq
    entryPair (by rw [entryPair]; decide) (by rw [entryPair]; decide)
    (by decide)

theorem retainedCall_axiomKeyword
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB}
    {label : String} {labelPos : Pos}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before =
      ⟨db, .label labelPos label⟩)
    (spelling : tokenText entry.1.bytes = "$a") :
    parserObservedState call.after =
      ⟨db, .math #[] ⟨.ax, labelPos, label⟩⟩ := by
  have entryBytes : entry.1.bytes = axiomKeywordBytes :=
    retainedBytes_eq_of_spelling spelling (by rfl)
  have entryPair : entry.1.bytes = [36, 97] := by
    change entry.1.bytes = [36, 97] at entryBytes
    exact entryBytes
  exact retainedCall_statementKeyword .ax significant before_eq
    entryPair (by rw [entryPair]; decide) (by rw [entryPair]; decide)
    (by decide)

theorem retainedCall_provableKeyword
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB}
    {label : String} {labelPos : Pos}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before =
      ⟨db, .label labelPos label⟩)
    (spelling : tokenText entry.1.bytes = "$p") :
    parserObservedState call.after =
      ⟨db, .math #[] ⟨.thm, labelPos, label⟩⟩ := by
  have entryBytes : entry.1.bytes = provableKeywordBytes :=
    retainedBytes_eq_of_spelling spelling (by rfl)
  have entryPair : entry.1.bytes = [36, 112] := by
    change entry.1.bytes = [36, 112] at entryBytes
    exact entryBytes
  exact retainedCall_statementKeyword .thm significant before_eq
    entryPair (by rw [entryPair]; decide) (by rw [entryPair]; decide)
    (by decide)

/-- A retained `$=` token at the end of a theorem formula constructs the
canonical shipped proof-state anchor.  Frame trimming and the exact reader
position are recovered from the real successful call. -/
theorem retainedCall_theoremDelimiter
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB}
    {formula : RuntimeFormula} {label : String} {labelPos : Pos}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before =
      ⟨db, .math formula ⟨.thm, labelPos, label⟩⟩)
    (spelling : tokenText entry.1.bytes = "$=")
    (after_errorFree : call.after.db.error? = none) :
    ∃ frame,
      db.trimFrame' formula = .ok frame ∧
        call.after.db = db ∧
        call.after.tokp =
          .proof (db.mkProofState labelPos label formula frame) ∧
        parserObservedState call.after =
          ⟨db, .proof (db.mkProofState labelPos label formula frame)⟩ := by
  have entryBytes : entry.1.bytes = proofSeparatorBytes :=
    retainedBytes_eq_of_spelling spelling (by rfl)
  have delimiter : call.origin.token.eqArray TokensKind.thm.delim = true := by
    simpa [shippedToken] using retainedCall_eqArray_true significant
      (entryBytes.trans (by rfl))
  have notComment : call.origin.token.eqArray "$(".toAscii = false := by
    simpa [shippedToken] using retainedCall_eqArray_false significant (by
      rw [entryBytes]
      decide)
  have notInclude : call.origin.token.eqArray "$[".toAscii = false := by
    simpa [shippedToken] using retainedCall_eqArray_false significant (by
      rw [entryBytes]
      decide)
  obtain ⟨beforeDb, beforeMode⟩ :=
    call_before_fields_of_observed significant before_eq
  have success :
      (call.before.feedToken call.origin.parserOffset
        call.origin.token).db.error? = none := by
    rw [← call.after_eq]
    exact after_errorFree
  obtain ⟨frame, trimAfter, proofMode, databaseEq⟩ :=
    feedToken_math_thm_delim_anchor_exact call.before
      call.origin.parserOffset call.origin.token formula labelPos label
      beforeMode notComment notInclude delimiter success
  have databaseEq' :
      (call.before.feedToken call.origin.parserOffset
        call.origin.token).db = db :=
    databaseEq.trans beforeDb
  refine ⟨frame, ?_, ?_, ?_, ?_⟩
  · rw [databaseEq'] at trimAfter
    exact trimAfter
  · rw [call.after_eq]
    exact databaseEq'
  · rw [call.after_eq, proofMode, databaseEq']
  · rw [call.after_eq]
    simp only [parserObservedState, observedSemanticState,
      parserSemanticState]
    rw [proofMode, databaseEq']
    rfl

/-- The exact fixed-anchor result of one retained ordinary normal-proof
label.  Unlike `NormalTokenStep`, this also covers the first proof label,
whose incoming proof mode is `.start`; it therefore supplies the separate
first-token fields required by `NormalTokenLedger`. -/
structure RetainedNormalProofFeed
    (anchor : ParserState) (db : DB) (before : RuntimeProofState)
    (token : ByteSlice) (observedAfter : ParserObservedState) : Type where
  after : RuntimeProofState
  observed_eq : observedAfter = ⟨db, .proof after⟩
  success : (anchor.feedProof token before).db.error? = none
  result : (anchor.feedProof token before).tokp = .proof after
  token_not_open : ¬ token.eqArray "(".toAscii
  token_not_unknown : ¬ token.eqArray "?".toAscii

/-- Rebase one retained, source-valid non-unknown proof-label call onto the
fixed pre-insertion parser anchor.  Line, scanner, and live token-parser
fields are administrative; only exact database equality is used. -/
noncomputable def retainedCall_normalProofFeed
    (anchor : ParserState)
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB}
    {before : RuntimeProofState} {name : LocatedName}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before = ⟨db, .proof before⟩)
    (spelling : tokenText entry.1.bytes = name.name)
    (charset : NameCharset proofTokenValid name)
    (notUnknownName : name.name ≠ "?")
    (after_errorFree : call.after.db.error? = none)
    (anchor_db : anchor.db = db) :
    RetainedNormalProofFeed anchor db before call.origin.token
      (parserObservedState call.after) := by
  have labelCharset := proofNameCharset_to_label charset notUnknownName
  let bytes := Classical.choose labelCharset
  have charsetFacts := Classical.choose_spec labelCharset
  have valid := charsetFacts.1
  have name_eq := charsetFacts.2
  have entryBytes : entry.1.bytes = bytes :=
    tokenText_injective (spelling.trans name_eq)
  cases bytesEq : bytes with
  | nil =>
      have impossible : labelBytesValid [] = true := by
        rw [← bytesEq]
        exact valid
      simp [labelBytesValid] at impossible
  | cons head tail =>
      have validCons : labelBytesValid (head :: tail) = true := by
        rw [← bytesEq]
        exact valid
      have entryBytesCons : entry.1.bytes = head :: tail :=
        entryBytes.trans bytesEq
      have headNeDollar := labelBytesValid_head_ne_dollar validCons
      have headNeOpen := labelBytesValid_head_ne_open validCons
      have notCommentBytes : entry.1.bytes ≠ "$(".toAscii.data.toList := by
        rw [entryBytesCons]
        change head :: tail ≠ [36, 40]
        exact nonDollarHead_ne_commandPair headNeDollar
      have notIncludeBytes : entry.1.bytes ≠ "$[".toAscii.data.toList := by
        rw [entryBytesCons]
        change head :: tail ≠ [36, 91]
        exact nonDollarHead_ne_commandPair headNeDollar
      have notFinishBytes : entry.1.bytes ≠ "$.".toAscii.data.toList := by
        rw [entryBytesCons]
        change head :: tail ≠ [36, 46]
        exact nonDollarHead_ne_commandPair headNeDollar
      have notOpenBytes : entry.1.bytes ≠ "(".toAscii.data.toList := by
        rw [entryBytesCons]
        change head :: tail ≠ [40]
        intro equality
        have openByte : (40 : UInt8) = '('.toUInt8 := by decide
        apply headNeOpen
        rw [← openByte]
        exact (List.cons.inj equality).1
      have notUnknownBytes : entry.1.bytes ≠ "?".toAscii.data.toList := by
        intro equality
        apply notUnknownName
        rw [← spelling, equality]
        rfl
      have notComment : call.origin.token.eqArray "$(".toAscii = false := by
        simpa [shippedToken] using
          retainedCall_eqArray_false significant notCommentBytes
      have notInclude : call.origin.token.eqArray "$[".toAscii = false := by
        simpa [shippedToken] using
          retainedCall_eqArray_false significant notIncludeBytes
      have notFinish : call.origin.token.eqArray "$.".toAscii = false := by
        simpa [shippedToken] using
          retainedCall_eqArray_false significant notFinishBytes
      have notOpen : call.origin.token.eqArray "(".toAscii = false := by
        simpa [shippedToken] using
          retainedCall_eqArray_false significant notOpenBytes
      have notUnknownEq : call.origin.token.eqArray "?".toAscii = false := by
        simpa [shippedToken] using
          retainedCall_eqArray_false significant notUnknownBytes
      obtain ⟨beforeDb, beforeMode⟩ :=
        call_before_fields_of_observed significant before_eq
      have liveSuccess :
          (call.before.feedToken call.origin.parserOffset
            call.origin.token).db.error? = none := by
        rw [← call.after_eq]
        exact after_errorFree
      let cleared : ParserState := { call.before with tokp := default }
      have exactStep := feedToken_proof_step_exact call.before
        call.origin.parserOffset call.origin.token before beforeMode
        notComment notInclude notFinish
      have clearedSuccess :
          (cleared.feedProof call.origin.token before).db.error? = none := by
        rw [← exactStep]
        exact liveSuccess
      let successWitness :=
        Metamath.PrefixTraceCompressed.feedProof_success_go_ok cleared
          call.origin.token before clearedSuccess
      let after := Classical.choose successWitness
      have successFacts := Classical.choose_spec successWitness
      have liveResult :
          (call.before.feedToken call.origin.parserOffset
            call.origin.token).tokp = .proof after := by
        rw [exactStep]
        exact successFacts.2
      have afterDb : call.after.db = db := by
        rw [call.after_eq, exactStep]
        rw [Metamath.ParserOps.feedProof_success_db cleared
          call.origin.token before clearedSuccess]
        exact beforeDb
      have afterMode : call.after.tokp = .proof after := by
        rw [call.after_eq]
        exact liveResult
      have observedAfter :
          parserObservedState call.after = ⟨db, .proof after⟩ := by
        simp only [parserObservedState, observedSemanticState,
          parserSemanticState]
        rw [afterDb, afterMode]
        rfl
      have liveAnchorDb : call.before.db = anchor.db :=
        beforeDb.trans anchor_db.symm
      have clearedAnchorDb : cleared.db = anchor.db := by
        simpa [cleared] using liveAnchorDb
      have rebased := feedProof_success_result_rebase cleared anchor
        call.origin.token before after clearedAnchorDb clearedSuccess
          successFacts.2
      exact
        { after := after
          observed_eq := observedAfter
          success := rebased.1
          result := rebased.2
          token_not_open := by simpa using notOpen
          token_not_unknown := by simpa using notUnknownEq }

/-- A retained non-unknown normal-proof token yields both the next actual
proof state and one fixed-anchor `NormalTokenStep`.  The live reader state
and the ledger anchor may differ in administrative fields, but their
databases are exactly equal. -/
noncomputable def retainedCall_normalProofStep
    (anchor : ParserState)
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB}
    {before : RuntimeProofState} {name : LocatedName}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before = ⟨db, .proof before⟩)
    (spelling : tokenText entry.1.bytes = name.name)
    (charset : NameCharset proofTokenValid name)
    (notUnknownName : name.name ≠ "?")
    (after_errorFree : call.after.db.error? = none)
    (anchor_db : anchor.db = db)
    (beforeNormal : before.ptp = .normal) :
    Σ after : RuntimeProofState,
      (parserObservedState call.after = ⟨db, .proof after⟩) ×'
        NormalTokenStep anchor before call.origin.token after := by
  let feed := retainedCall_normalProofFeed anchor significant before_eq
    spelling charset notUnknownName after_errorFree anchor_db
  exact ⟨feed.after, feed.observed_eq,
    { success := feed.success
      result := feed.result
      before_normal := beforeNormal
      token_not_unknown := feed.token_not_unknown }⟩

/-- The retained `$c` keyword enters the shipped constant-declaration mode. -/
theorem retainedCall_constKeyword
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before = ⟨db, .start⟩)
    (spelling : tokenText entry.1.bytes = "$c") :
    parserObservedState call.after = ⟨db, .const false⟩ := by
  have entryBytes : entry.1.bytes = constKeywordBytes :=
    retainedBytes_eq_of_spelling spelling (by rfl)
  have entryPair : entry.1.bytes = [36, 99] := by
    change entry.1.bytes = [36, 99] at entryBytes
    exact entryBytes
  have dispatched := retainedCall_startCommand significant before_eq
    entryPair (by rw [entryPair]; decide) (by rw [entryPair]; decide)
  have commandByte : Metamath.Verify.uint8ToChar 99 = 'c' := by decide
  simpa [commandByte] using dispatched

/-- The retained `$v` keyword enters the shipped variable-declaration mode. -/
theorem retainedCall_varKeyword
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before = ⟨db, .start⟩)
    (spelling : tokenText entry.1.bytes = "$v") :
    parserObservedState call.after = ⟨db, .var false⟩ := by
  have entryBytes : entry.1.bytes = varKeywordBytes :=
    retainedBytes_eq_of_spelling spelling (by rfl)
  have entryPair : entry.1.bytes = [36, 118] := by
    change entry.1.bytes = [36, 118] at entryBytes
    exact entryBytes
  have dispatched := retainedCall_startCommand significant before_eq
    entryPair (by rw [entryPair]; decide) (by rw [entryPair]; decide)
  have commandByte : Metamath.Verify.uint8ToChar 118 = 'v' := by decide
  simpa [commandByte] using dispatched

/-- The retained `$d` keyword enters the shipped disjoint-list mode. -/
theorem retainedCall_djKeyword
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before = ⟨db, .start⟩)
    (spelling : tokenText entry.1.bytes = "$d") :
    parserObservedState call.after = ⟨db, .djvars #[]⟩ := by
  have entryBytes : entry.1.bytes = djKeywordBytes :=
    retainedBytes_eq_of_spelling spelling (by rfl)
  have entryPair : entry.1.bytes = [36, 100] := by
    change entry.1.bytes = [36, 100] at entryBytes
    exact entryBytes
  have dispatched := retainedCall_startCommand significant before_eq
    entryPair (by rw [entryPair]; decide) (by rw [entryPair]; decide)
  have commandByte : Metamath.Verify.uint8ToChar 100 = 'd' := by decide
  simpa [commandByte] using dispatched

/-- The actual retained `${` call is exactly the shipped scope-push
transition.  Its backing slice remains the reader's original slice; only the
observations used by the fixed-command dispatch are characterized. -/
theorem retainedCall_scopeOpen
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before = ⟨db, .start⟩)
    (spelling : tokenText entry.1.bytes = "${") :
    parserObservedState call.after = ⟨db.pushScope, .start⟩ := by
  have entryBytes : entry.1.bytes =
      SourceGSLTRawSourceComposition.scopeOpenBytes :=
    retainedBytes_eq_of_spelling spelling (by rfl)
  have entryPair : entry.1.bytes = [36, 123] := by
    change entry.1.bytes = [36, 123] at entryBytes
    exact entryBytes
  have commandFields := retainedCall_pair_fields significant entryPair
  have notComment :
      (shippedToken call).eqArray "$(".toAscii = false :=
    retainedCall_eqArray_false significant (by
      rw [entryBytes]
      decide)
  have notInclude :
      (shippedToken call).eqArray "$[".toAscii = false :=
    retainedCall_eqArray_false significant (by
      rw [entryBytes]
      decide)
  have commandFields' : call.origin.token.len = 2 ∧
      call.origin.token[0]! = 36 ∧ call.origin.token[1]! = 123 := by
    simpa [shippedToken] using commandFields
  have notComment' : call.origin.token.eqArray "$(".toAscii = false := by
    simpa [shippedToken] using notComment
  have notInclude' : call.origin.token.eqArray "$[".toAscii = false := by
    simpa [shippedToken] using notInclude
  have dollarByte : (36 : UInt8) = '$'.toUInt8 := by decide
  have openByte : Metamath.Verify.uint8ToChar 123 = '{' := by decide
  obtain ⟨beforeDb, beforeMode⟩ :=
    call_before_fields_of_observed significant before_eq
  rw [call.after_eq]
  simp [parserObservedState, observedSemanticState, parserSemanticState,
    ParserState.feedToken, ParserState.withDB, beforeDb, beforeMode,
    notComment', notInclude',
    commandFields'.1, commandFields'.2.1, commandFields'.2.2,
    dollarByte, openByte, logicalTokenMode]

/-- The actual retained `$}` call is exactly the shipped scope-pop
transition at the reader's own position. -/
theorem retainedCall_scopeClose
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before = ⟨db, .start⟩)
    (spelling : tokenText entry.1.bytes = "$}") :
    parserObservedState call.after =
      ⟨db.popScope (call.before.mkPos call.origin.parserOffset), .start⟩ := by
  have entryBytes : entry.1.bytes =
      SourceGSLTRawSourceComposition.scopeCloseBytes :=
    retainedBytes_eq_of_spelling spelling (by rfl)
  have entryPair : entry.1.bytes = [36, 125] := by
    change entry.1.bytes = [36, 125] at entryBytes
    exact entryBytes
  have commandFields := retainedCall_pair_fields significant entryPair
  have notComment :
      (shippedToken call).eqArray "$(".toAscii = false :=
    retainedCall_eqArray_false significant (by
      rw [entryBytes]
      decide)
  have notInclude :
      (shippedToken call).eqArray "$[".toAscii = false :=
    retainedCall_eqArray_false significant (by
      rw [entryBytes]
      decide)
  have commandFields' : call.origin.token.len = 2 ∧
      call.origin.token[0]! = 36 ∧ call.origin.token[1]! = 125 := by
    simpa [shippedToken] using commandFields
  have notComment' : call.origin.token.eqArray "$(".toAscii = false := by
    simpa [shippedToken] using notComment
  have notInclude' : call.origin.token.eqArray "$[".toAscii = false := by
    simpa [shippedToken] using notInclude
  have dollarByte : (36 : UInt8) = '$'.toUInt8 := by decide
  have closeByte : Metamath.Verify.uint8ToChar 125 = '}' := by decide
  obtain ⟨beforeDb, beforeMode⟩ :=
    call_before_fields_of_observed significant before_eq
  rw [call.after_eq]
  simp [parserObservedState, observedSemanticState, parserSemanticState,
    ParserState.feedToken, ParserState.withDB, beforeDb, beforeMode,
    notComment', notInclude', commandFields'.1, commandFields'.2.1,
    commandFields'.2.2, dollarByte, closeByte, logicalTokenMode]

/-- Located significant calls are the located-token projection of the same
filter, with no reordering or reconstruction. -/
theorem significantLocatedEntries_fst
    (fileId : String) (calls : List TokenCall) :
    (calls.filterMap (significantLocatedEntry? fileId)).map Prod.fst =
      calls.filterMap (significantLocatedCall? fileId) := by
  rw [List.map_filterMap]
  apply congrArg (fun selector => calls.filterMap selector)
  funext call
  unfold significantLocatedEntry?
  cases significantLocatedCall? fileId call <;> rfl

/-- The comment-quotiented chronology with exact located bytes and spans. -/
inductive LocatedSignificantCallTrace (fileId : String) :
    ParserObservedState → List (LocatedToken × TokenCall) →
      ParserObservedState → Type where
  | nil (state : ParserObservedState) :
      LocatedSignificantCallTrace fileId state [] state
  | cons {initial final : ParserObservedState}
      {entries : List (LocatedToken × TokenCall)}
      (entry : LocatedToken × TokenCall)
      (significant : significantLocatedEntry? fileId entry.2 =
        some entry)
      (after_errorFree : entry.2.after.db.error? = none)
      (before_eq : parserObservedState entry.2.before = initial)
      (tail : LocatedSignificantCallTrace fileId
        (parserObservedState entry.2.after) entries final) :
      LocatedSignificantCallTrace fileId initial (entry :: entries) final

def LocatedSignificantCallTrace.reindexInitial
    {fileId : String}
    {initial next final : ParserObservedState}
    {entries : List (LocatedToken × TokenCall)}
    (trace : LocatedSignificantCallTrace fileId initial entries final)
    (equality : initial = next) :
    LocatedSignificantCallTrace fileId next entries final :=
  equality ▸ trace

def LocatedSignificantCallTrace.reindexFinal
    {fileId : String}
    {initial final next : ParserObservedState}
    {entries : List (LocatedToken × TokenCall)}
    (trace : LocatedSignificantCallTrace fileId initial entries final)
    (equality : final = next) :
    LocatedSignificantCallTrace fileId initial entries next :=
  equality ▸ trace

/-- The public reader's mode configuration is immutable across a located
token chronology.  Parser calls may change the database contents, proof mode,
or error fields, but never the policy under which those calls are decoded. -/
theorem LocatedSignificantCallTrace.final_config_eq
    {fileId : String}
    {initial final : ParserObservedState}
    {entries : List (LocatedToken × TokenCall)}
    (trace : LocatedSignificantCallTrace fileId initial entries final) :
    final.db.config = initial.db.config := by
  induction trace with
  | nil => rfl
  | @cons initial final entries entry significant afterErrorFree beforeEq
      tail ih =>
      calc
        final.db.config = entry.2.after.db.config := ih
        _ = entry.2.before.db.config := by
          rw [entry.2.after_eq]
          exact ParserState.feedToken_db_config _ _ _
        _ = initial.db.config :=
          congrArg (fun state : ParserObservedState => state.db.config)
            beforeEq

/-- A one-token chronology spelled `${` is the scope-push transition. -/
theorem LocatedSignificantCallTrace.scopeOpen_final
    {fileId : String} {db : DB} {final : ParserObservedState}
    {entries : List (LocatedToken × TokenCall)}
    (trace : LocatedSignificantCallTrace fileId ⟨db, .start⟩ entries final)
    (text_eq : ["${"] =
      entries.map (fun entry => tokenText entry.1.bytes)) :
    final = ⟨db.pushScope, .start⟩ := by
  cases trace with
  | nil state => simp at text_eq
  | @cons initial final entries entry significant after_errorFree
      before_eq tail =>
      cases tail with
      | nil state =>
          simp only [List.map_cons, List.map_nil, List.cons.injEq] at text_eq
          exact retainedCall_scopeOpen significant before_eq text_eq.1.symm
      | cons next significantNext nextErrorFree nextBefore rest =>
          simp at text_eq

/-- A one-token chronology spelled `$}` is the scope-pop transition. -/
theorem LocatedSignificantCallTrace.scopeClose_final
    {fileId : String} {db : DB} {final : ParserObservedState}
    {entries : List (LocatedToken × TokenCall)}
    (trace : LocatedSignificantCallTrace fileId ⟨db, .start⟩ entries final)
    (text_eq : ["$}"] =
      entries.map (fun entry => tokenText entry.1.bytes)) :
    ∃ call : TokenCall,
      final =
        ⟨db.popScope (call.before.mkPos call.origin.parserOffset), .start⟩ := by
  cases trace with
  | nil state => simp at text_eq
  | @cons initial final entries entry significant after_errorFree
      before_eq tail =>
      cases tail with
      | nil state =>
          simp only [List.map_cons, List.map_nil, List.cons.injEq] at text_eq
          exact ⟨entry.2,
            retainedCall_scopeClose significant before_eq text_eq.1.symm⟩
      | cons next significantNext nextErrorFree nextBefore rest =>
          simp at text_eq

/-- The concrete source/parser refinement relation composes across `${`. -/
theorem SourceParserPrefixAgrees.openScope
    {fileId : String} {source next : SourceState}
    {site : LocatedByteSpan}
    {obligations : List TheoremObligation}
    {initial final : ParserObservedState}
    {entries : List (LocatedToken × TokenCall)}
    (agreement : SourceParserPrefixAgrees source initial)
    (trace : LocatedSignificantCallTrace fileId initial entries final)
    (text_eq : ["${"] =
      entries.map (fun entry => tokenText entry.1.bytes))
    (applied : applyStatement source (.openScope site) =
      .ok (next, obligations)) :
    SourceParserPrefixAgrees next final := by
  rcases initial with ⟨db, mode⟩
  cases agreement.mode_eq
  have final_eq := trace.scopeOpen_final text_eq
  cases opened : applyLocalPayload? .openScope source with
  | none =>
      simp only [applyStatement, opened] at applied
      exact nomatch applied
  | some middle =>
      simp only [applyStatement, opened] at applied
      cases applied
      rw [final_eq]
      refine
        { mode_eq := rfl
          database := RuntimeDBAgrees.pushScope agreement.database opened
          interrupt_eq := ?_ }
      calc
        (db.pushScope).interrupt = db.interrupt := by
          simpa [runtimeApplyPayload] using
            runtimeApplyPayload_interrupt ⟨0, 0⟩ .openScope db
        _ = false := agreement.interrupt_eq

/-- The concrete source/parser refinement relation composes across `$}` and
the source-only block-completion marker. -/
theorem SourceParserPrefixAgrees.closeScope
    {fileId : String} {source next : SourceState}
    {site : LocatedByteSpan}
    {obligations : List TheoremObligation}
    {initial final : ParserObservedState}
    {entries : List (LocatedToken × TokenCall)}
    (agreement : SourceParserPrefixAgrees source initial)
    (trace : LocatedSignificantCallTrace fileId initial entries final)
    (text_eq : ["$}"] =
      entries.map (fun entry => tokenText entry.1.bytes))
    (applied : applyStatement source (.closeScope site) =
      .ok (next, obligations)) :
    SourceParserPrefixAgrees next final := by
  rcases initial with ⟨db, mode⟩
  cases agreement.mode_eq
  obtain ⟨call, final_eq⟩ := trace.scopeClose_final text_eq
  cases closed : applyLocalPayload? .closeScope source with
  | none =>
      simp only [applyStatement, closed] at applied
      exact nomatch applied
  | some middle =>
      simp only [applyStatement, closed] at applied
      cases completed : applyLocalPayload? .completeBlock middle with
      | none =>
          simp only [completed] at applied
          exact nomatch applied
      | some after =>
          simp only [completed] at applied
          cases applied
          change closeScope? source = some middle at closed
          change completeBlock? middle = some next at completed
          have popped : RuntimeDBAgrees
              (db.popScope (call.before.mkPos call.origin.parserOffset))
              middle :=
            RuntimeDBAgrees.popScope' (before := source)
              (after := middle) agreement.database
              (call.before.mkPos call.origin.parserOffset) closed
          have finished : RuntimeDBAgrees
              (db.popScope (call.before.mkPos call.origin.parserOffset))
              next :=
            RuntimeDBAgrees.completeBlock (before := middle)
              (after := next) popped completed
          rw [final_eq]
          refine
            { mode_eq := rfl
              database := finished
              interrupt_eq := ?_ }
          calc
            (db.popScope
                (call.before.mkPos call.origin.parserOffset)).interrupt =
                db.interrupt := by
              simpa [runtimeApplyPayload] using
                runtimeApplyPayload_interrupt
                  (call.before.mkPos call.origin.parserOffset)
                  .closeScope db
            _ = false := agreement.interrupt_eq

/-- A successful full call chronology canonically erases comment
administration while retaining the exact source location and call object of
every logical token. -/
noncomputable def CallSemanticTrace.toLocatedSignificantCallTrace
    (fileId : String)
    {initial : ParserSemanticState} {calls : List TokenCall}
    (trace : CallSemanticTrace initial calls)
    (callsSuccessful : ∀ call ∈ calls, call.after.db.error? = none) :
    LocatedSignificantCallTrace fileId (observedSemanticState initial)
      (calls.filterMap (significantLocatedEntry? fileId))
      (observedSemanticState trace.final) := by
  induction trace with
  | nil state => exact .nil _
  | @cons initial calls call before_eq tail ih =>
      have headSuccessful : call.after.db.error? = none :=
        callsSuccessful call (by simp)
      have tailSuccessful :
          ∀ next ∈ calls, next.after.db.error? = none := by
        intro next member
        exact callsSuccessful next (by simp [member])
      let tailTrace := ih tailSuccessful
      have beforeObserved :
          parserObservedState call.before =
            observedSemanticState initial :=
        congrArg observedSemanticState before_eq
      cases locatedEq : significantLocatedEntry? fileId call with
      | none =>
          have insignificant : significantCall? call = none :=
            significantLocatedEntry?_none_significantCall?_none locatedEq
          have stutter := insignificantCall_observedState_eq call
            headSuccessful insignificant
          have boundary :
              parserObservedState call.after =
                observedSemanticState initial :=
            stutter.trans beforeObserved
          simpa [List.filterMap_cons, locatedEq, CallSemanticTrace.final]
            using tailTrace.reindexInitial boundary
      | some entry =>
          have entryCall : entry.2 = call :=
            significantLocatedEntry?_some_second locatedEq
          obtain ⟨token, retainedCall⟩ := entry
          change retainedCall = call at entryCall
          subst retainedCall
          simpa [List.filterMap_cons, locatedEq, CallSemanticTrace.final]
            using LocatedSignificantCallTrace.cons (token, call)
              locatedEq headSuccessful beforeObserved tailTrace

/-- Accepted public-reader execution yields its exact located significant
chronology from the shipped initial state. -/
noncomputable def checkBytesRun_locatedSignificantCallTrace
    (fileId : String) {bytes : ByteArray} {config : ModeConfig}
    (run : CheckBytesRun bytes config)
    (errorFree : run.db.error? = none) :
    Σ finalMode : TokenParser,
      LocatedSignificantCallTrace fileId
        (parserObservedState (initialState config))
        (run.calls.filterMap (significantLocatedEntry? fileId))
        ⟨run.db, logicalTokenMode finalMode⟩ := by
  let semanticRun := checkBytesRun_callSemanticRun run errorFree
  let locatedTrace := semanticRun.2.trace.toLocatedSignificantCallTrace
    fileId (checkBytesRun_calls_after_errorFree run errorFree)
  refine ⟨semanticRun.1, ?_⟩
  exact locatedTrace.reindexFinal
    (congrArg observedSemanticState semanticRun.2.final_eq)

/-- Default-profile specialization of the located chronology. -/
noncomputable def loggedLocatedSignificantCallTrace
    (fileId : String) (bytes : ByteArray)
    (errorFree : (checkBytesLogged bytes).db.error? = none) :
    Σ finalMode : TokenParser,
      LocatedSignificantCallTrace fileId
        (parserObservedState (initialState {}))
        ((checkBytesLogged bytes).calls.filterMap
          (significantLocatedEntry? fileId))
        ⟨(checkBytesLogged bytes).db, logicalTokenMode finalMode⟩ :=
  checkBytesRun_locatedSignificantCallTrace fileId
    (checkBytesLogged bytes) errorFree

/-- Split a located chronology at an arbitrary logical-token boundary. -/
noncomputable def LocatedSignificantCallTrace.splitAt :
    {fileId : String} →
    {initial final : ParserObservedState} →
    {entries : List (LocatedToken × TokenCall)} →
    (count : Nat) → LocatedSignificantCallTrace fileId initial entries final →
    Σ middle : ParserObservedState,
      LocatedSignificantCallTrace fileId initial (entries.take count) middle ×'
      LocatedSignificantCallTrace fileId middle (entries.drop count) final
  | _, initial, _, _, 0, trace =>
      ⟨initial, .nil _, trace⟩
  | _, _, _, _, _ + 1, .nil state =>
      ⟨state, .nil _, .nil _⟩
  | _, _, _, _, count + 1,
      .cons entry significant after_errorFree before_eq tail => by
      obtain ⟨middle, left, right⟩ := tail.splitAt count
      exact ⟨middle,
        .cons entry significant after_errorFree before_eq left, right⟩

/-- A located call chronology indexed simultaneously by the exact token
spellings consumed at this layer. -/
inductive SpelledCallTrace (fileId : String) :
    ParserObservedState → List String →
      List (LocatedToken × TokenCall) → ParserObservedState → Type where
  | nil (state : ParserObservedState) :
      SpelledCallTrace fileId state [] [] state
  | cons {initial final : ParserObservedState}
      {texts : List String}
      {entries : List (LocatedToken × TokenCall)}
      (text : String) (entry : LocatedToken × TokenCall)
      (spelling : tokenText entry.1.bytes = text)
      (significant : significantLocatedEntry? fileId entry.2 = some entry)
      (after_errorFree : entry.2.after.db.error? = none)
      (before_eq : parserObservedState entry.2.before = initial)
      (tail : SpelledCallTrace fileId
        (parserObservedState entry.2.after) texts entries final) :
      SpelledCallTrace fileId initial (text :: texts)
        (entry :: entries) final

def SpelledCallTrace.reindexInitial
    {fileId : String} {initial next final : ParserObservedState}
    {texts : List String} {entries : List (LocatedToken × TokenCall)}
    (trace : SpelledCallTrace fileId initial texts entries final)
    (equality : initial = next) :
    SpelledCallTrace fileId next texts entries final :=
  equality ▸ trace

def SpelledCallTrace.reindexFinal
    {fileId : String} {initial final next : ParserObservedState}
    {texts : List String} {entries : List (LocatedToken × TokenCall)}
    (trace : SpelledCallTrace fileId initial texts entries final)
    (equality : final = next) :
    SpelledCallTrace fileId initial texts entries next :=
  equality ▸ trace

/-- Split a spelling-indexed chronology at an arbitrary token boundary. -/
noncomputable def SpelledCallTrace.splitAt :
    {fileId : String} →
    {initial final : ParserObservedState} →
    {texts : List String} →
    {entries : List (LocatedToken × TokenCall)} →
    (count : Nat) → SpelledCallTrace fileId initial texts entries final →
    Σ middle : ParserObservedState,
      SpelledCallTrace fileId initial (texts.take count)
          (entries.take count) middle ×'
        SpelledCallTrace fileId middle (texts.drop count)
          (entries.drop count) final
  | _, initial, _, _, _, 0, trace =>
      ⟨initial, .nil _, trace⟩
  | _, _, _, _, _, _ + 1, .nil state =>
      ⟨state, .nil _, .nil _⟩
  | _, _, _, _, _, count + 1,
      .cons text entry spelling significant after_errorFree before_eq tail => by
      obtain ⟨middle, left, right⟩ := tail.splitAt count
      exact ⟨middle,
        .cons text entry spelling significant after_errorFree before_eq left,
        right⟩

/-- Split a spelling-indexed chronology at a statically known concatenation
boundary.  Unlike raw `take`/`drop` normalization, the result exposes the
two authored lists directly. -/
noncomputable def SpelledCallTrace.splitAppend
    {fileId : String} {initial final : ParserObservedState}
    {left right : List String}
    {entries : List (LocatedToken × TokenCall)}
    (trace : SpelledCallTrace fileId initial (left ++ right) entries final) :
    Σ middle : ParserObservedState,
      SpelledCallTrace fileId initial left
          (entries.take left.length) middle ×'
        SpelledCallTrace fileId middle right
          (entries.drop left.length) final := by
  obtain ⟨middle, leftTrace, rightTrace⟩ := trace.splitAt left.length
  exact ⟨middle, by simpa using leftTrace, by simpa using rightTrace⟩

/-- A one-token source label chronology enters the exact shipped label
state, retaining the reader-computed position. -/
theorem SpelledCallTrace.startLabel_final
    {fileId : String} {db : DB} {name : LocatedName}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId ⟨db, .start⟩ [name.name]
      entries final)
    (charset : NameCharset labelBytesValid name) :
    ∃ labelPos,
      final = ⟨db, .label labelPos name.name⟩ := by
  cases trace with
  | @cons _ _ texts tailEntries text entry spelling significant
      after_errorFree before_eq tail =>
      cases tail with
      | nil state =>
          exact ⟨entry.2.before.mkPos entry.2.origin.parserOffset,
            retainedCall_startLabel significant before_eq spelling charset⟩

/-- A one-token `$p` chronology enters theorem-formula collection. -/
theorem SpelledCallTrace.provableKeyword_final
    {fileId : String} {db : DB} {label : String} {labelPos : Pos}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId ⟨db, .label labelPos label⟩
      ["$p"] entries final) :
    final = ⟨db, .math #[] ⟨.thm, labelPos, label⟩⟩ := by
  cases trace with
  | @cons _ _ texts tailEntries text entry spelling significant
      after_errorFree before_eq tail =>
      cases tail with
      | nil state =>
          exact retainedCall_provableKeyword significant before_eq spelling

/-- A one-token `$=` chronology produces the canonical theorem proof
anchor. -/
theorem SpelledCallTrace.theoremDelimiter_final
    {fileId : String} {db : DB} {formula : RuntimeFormula}
    {label : String} {labelPos : Pos}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId
      ⟨db, .math formula ⟨.thm, labelPos, label⟩⟩
      ["$="] entries final) :
    ∃ frame,
      db.trimFrame' formula = .ok frame ∧
        final = ⟨db, .proof
          (db.mkProofState labelPos label formula frame)⟩ := by
  cases trace with
  | @cons _ _ texts tailEntries text entry spelling significant
      after_errorFree before_eq tail =>
      cases tail with
      | nil state =>
          obtain ⟨frame, trim, database_eq, mode_eq, observed_eq⟩ :=
            retainedCall_theoremDelimiter significant before_eq spelling
              after_errorFree
          exact ⟨frame, trim, observed_eq⟩

/-- Rich form of `theoremDelimiter_final`, retaining the actual parser state
needed as the fixed anchor of the normal-token ledger. -/
noncomputable def SpelledCallTrace.theoremDelimiter_anchor
    {fileId : String} {db : DB} {formula : RuntimeFormula}
    {label : String} {labelPos : Pos}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId
      ⟨db, .math formula ⟨.thm, labelPos, label⟩⟩
      ["$="] entries final) :
    ParserProofAnchor db formula labelPos label final := by
  cases trace with
  | @cons _ _ texts tailEntries text entry spelling significant
      after_errorFree before_eq tail =>
      cases tail with
      | nil state =>
          let witness := retainedCall_theoremDelimiter significant
            before_eq spelling after_errorFree
          let frame := Classical.choose witness
          have facts := Classical.choose_spec witness
          exact
            { state := entry.2.after
              frame := frame
              trim := facts.1
              database_eq := facts.2.1
              mode_eq := facts.2.2.1
              observed_eq := rfl }

/-- Append source-tagged math symbols to the shipped array in token order. -/
def appendMathSymbols (initial : Array Sym) (symbols : List Sym) :
    Array Sym :=
  symbols.foldl Array.push initial

@[simp] theorem appendMathSymbols_eq_append
    (initial : Array Sym) (symbols : List Sym) :
    appendMathSymbols initial symbols = initial ++ symbols.toArray := by
  simp [appendMathSymbols]

/-- A spelling-indexed run over a source-tagged math body reaches exactly
the corresponding shipped math accumulator.  This is the reusable
many-token administrative leg for `$f`, `$e`, `$a`, and `$p`. -/
theorem SpelledCallTrace.mathSymbols_final
    {fileId : String} {source : SourceState} {db : DB}
    {parser : TokensParser} {initialSymbols : Array Sym}
    {names : List LocatedName} {tagged : List Sym}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId ⟨db, .math initialSymbols parser⟩
      (names.map LocatedName.name) entries final)
    (agreement : RuntimeDBAgrees db source)
    (sourceValid : sourceStateValid source = true)
    (charsets : ∀ name ∈ names, NameCharset mathBytesValid name)
    (tagged_eq : tagBody source names = .ok tagged) :
    final = ⟨db, .math (appendMathSymbols initialSymbols tagged) parser⟩ := by
  induction names generalizing initialSymbols tagged entries final with
  | nil =>
      simp only [List.map_nil] at trace
      cases trace
      simp [tagBody] at tagged_eq
      subst tagged
      rfl
  | cons name rest ih =>
      simp only [List.map_cons] at trace
      cases trace with
      | @cons _ _ texts tailEntries text entry spelling significant
          after_errorFree before_eq tail =>
          cases symbol_eq : tagSymbol source name with
          | rejected rejection =>
              simp [tagBody, symbol_eq] at tagged_eq
          | ok symbol =>
              cases rest_eq : tagBody source rest with
              | rejected rejection =>
                  simp [tagBody, symbol_eq, rest_eq] at tagged_eq
              | ok restSymbols =>
                  simp only [tagBody, symbol_eq, rest_eq,
                    FoldResult.ok.injEq] at tagged_eq
                  subst tagged
                  have nameCharset : NameCharset mathBytesValid name :=
                    charsets name (by simp)
                  have restCharsets :
                      ∀ next ∈ rest, NameCharset mathBytesValid next := by
                    intro next member
                    exact charsets next (by simp [member])
                  cases symbol with
                  | const embedded =>
                      have variableAbsent :
                          source.activeVariables.contains name.name ≠ true := by
                        intro variablePresent
                        unfold tagSymbol at symbol_eq
                        rw [if_pos variablePresent] at symbol_eq
                        exact nomatch symbol_eq
                      have constantPresent :
                          source.declaredConstants.contains name.name = true := by
                        unfold tagSymbol at symbol_eq
                        rw [if_neg variableAbsent] at symbol_eq
                        by_cases present :
                            source.declaredConstants.contains name.name = true
                        · exact present
                        · rw [if_neg present] at symbol_eq
                          exact nomatch symbol_eq
                      have embedded_eq : embedded = name.name := by
                        unfold tagSymbol at symbol_eq
                        rw [if_neg variableAbsent, if_pos constantPresent]
                          at symbol_eq
                        exact Sym.const.inj
                          (FoldResult.ok.inj symbol_eq).symm
                      subst embedded
                      have lookup := find?_const_of_mem_declaredConstants
                        agreement (by
                          simpa [List.contains_iff_mem] using constantPresent)
                      have headFinal := retainedCall_mathConstant significant
                        before_eq spelling nameCharset lookup
                      have tail' := tail.reindexInitial headFinal
                      have finalEq := ih tail' restCharsets rest_eq
                      simpa [appendMathSymbols] using finalEq
                  | var embedded =>
                      have variablePresent :
                          source.activeVariables.contains name.name = true := by
                        unfold tagSymbol at symbol_eq
                        by_cases present :
                            source.activeVariables.contains name.name = true
                        · exact present
                        · rw [if_neg present] at symbol_eq
                          by_cases constantPresent :
                              source.declaredConstants.contains name.name = true
                          · rw [if_pos constantPresent] at symbol_eq
                            exact nomatch symbol_eq
                          · rw [if_neg constantPresent] at symbol_eq
                            exact nomatch symbol_eq
                      have embedded_eq : embedded = name.name := by
                        unfold tagSymbol at symbol_eq
                        rw [if_pos variablePresent] at symbol_eq
                        exact Sym.var.inj
                          (FoldResult.ok.inj symbol_eq).symm
                      subst embedded
                      have activeMem :
                          name.name ∈ source.activeVariables := by
                        simpa [List.contains_iff_mem] using variablePresent
                      have lookup := find?_var_of_mem_declaredVariables
                        agreement
                          (activeVariable_declared_of_sourceStateValid
                            sourceValid activeMem)
                      have runtimeActive : db.isActiveVar name.name = true := by
                        unfold DB.isActiveVar
                        have isVar : db.isVar name.name = true := by
                          simp [DB.isVar, lookup]
                        have activeStack :
                            db.activeVars.any
                              (fun entry => entry.1 == name.name) = true :=
                          (activeVars_any_name_eq_true_iff agreement
                            name.name).2 activeMem
                        simp [isVar, activeStack]
                      have headFinal := retainedCall_mathVariable significant
                        before_eq spelling nameCharset lookup runtimeActive
                      have tail' := tail.reindexInitial headFinal
                      have finalEq := ih tail' restCharsets rest_eq
                      simpa [appendMathSymbols] using finalEq

/-- A spelling-indexed run of ordinary normal-proof labels constructs the
exact fixed-anchor token-step ledger, in reader order. -/
theorem SpelledCallTrace.decodedNormalLabels_eq
    {fileId : String} {initial final : ParserObservedState}
    {names : List LocatedName}
    {entries : List (LocatedToken × TokenCall)}
    (trace : SpelledCallTrace fileId initial
      (names.map LocatedName.name) entries final)
    (charsets : ∀ name ∈ names, NameCharset proofTokenValid name)
    (noUnknown : ∀ name ∈ names, name.name ≠ "?") :
    entries.map (fun entry =>
        (Metamath.Verify.toLabel entry.2.origin.token).2) =
      names.map LocatedName.name := by
  induction names generalizing initial entries final with
  | nil =>
      simp only [List.map_nil] at trace ⊢
      cases trace
      rfl
  | cons name rest ih =>
      simp only [List.map_cons] at trace ⊢
      cases trace with
      | @cons _ _ texts tailEntries text entry spelling significant
          after_errorFree before_eq tail =>
          have nameCharset : NameCharset proofTokenValid name :=
            charsets name (by simp)
          have labelCharset : NameCharset labelBytesValid name :=
            proofNameCharset_to_label nameCharset
              (noUnknown name (by simp))
          have decoded := retainedCall_toLabel significant spelling
            labelCharset
          have decoded' :
              Metamath.Verify.toLabel entry.2.origin.token =
                (true, name.name) := by
            simpa [shippedToken] using decoded
          have restCharsets :
              ∀ next ∈ rest, NameCharset proofTokenValid next := by
            intro next member
            exact charsets next (by simp [member])
          have restNoUnknown :
              ∀ next ∈ rest, next.name ≠ "?" := by
            intro next member
            exact noUnknown next (by simp [member])
          change
            (Metamath.Verify.toLabel entry.2.origin.token).2 ::
                tailEntries.map (fun next =>
                  (Metamath.Verify.toLabel next.2.origin.token).2) =
              name.name :: rest.map LocatedName.name
          rw [show (Metamath.Verify.toLabel entry.2.origin.token).2 =
              name.name by simpa using congrArg Prod.snd decoded']
          exact congrArg (List.cons name.name)
            (ih tail restCharsets restNoUnknown)

noncomputable def SpelledCallTrace.normalProofSteps
    (anchor : ParserState)
    {fileId : String} {db : DB} {initial : RuntimeProofState}
    {names : List LocatedName}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId ⟨db, .proof initial⟩
      (names.map LocatedName.name) entries final)
    (anchor_db : anchor.db = db)
    (initialNormal : initial.ptp = .normal)
    (charsets : ∀ name ∈ names, NameCharset proofTokenValid name)
    (noUnknown : ∀ name ∈ names, name.name ≠ "?") :
    Σ finalProof : RuntimeProofState,
      (final = ⟨db, .proof finalProof⟩) ×'
        NormalTokenSteps anchor initial
          (entries.map (fun entry => entry.2.origin.token)) finalProof := by
  induction names generalizing initial entries final with
  | nil =>
      simp only [List.map_nil] at trace
      cases trace
      exact ⟨initial, rfl, .nil initial⟩
  | cons name rest ih =>
      simp only [List.map_cons] at trace
      cases trace with
      | @cons _ _ texts tailEntries text entry spelling significant
          after_errorFree before_eq tail =>
          have nameCharset : NameCharset proofTokenValid name :=
            charsets name (by simp)
          have nameNotUnknown : name.name ≠ "?" :=
            noUnknown name (by simp)
          have restCharsets :
              ∀ next ∈ rest, NameCharset proofTokenValid next := by
            intro next member
            exact charsets next (by simp [member])
          have restNoUnknown :
              ∀ next ∈ rest, next.name ≠ "?" := by
            intro next member
            exact noUnknown next (by simp [member])
          let headResult := retainedCall_normalProofStep anchor significant
            before_eq spelling nameCharset nameNotUnknown after_errorFree
            anchor_db initialNormal
          have tail' := tail.reindexInitial headResult.2.1
          let tailResult := ih tail' headResult.2.2.after_normal
            restCharsets restNoUnknown
          exact ⟨tailResult.1, tailResult.2.1,
            .cons entry.2.origin.token headResult.1 headResult.2.2
              tailResult.2.2⟩

/-- A normal-proof ledger constructed from the production reader chronology.
The equalities retain its exact theorem anchor, submitted byte slices, and
final observed proof state rather than merely asserting that some ledger
exists. -/
structure ReaderNormalProofLedger
    {db : DB} {formula : RuntimeFormula} {labelPos : Pos} {label : String}
    {initial : ParserObservedState}
    (anchor : ParserProofAnchor db formula labelPos label initial)
    (entries : List (LocatedToken × TokenCall))
    (final : ParserObservedState) : Type where
  ledger : NormalTokenLedger
  anchor_eq : ledger.anchor = anchor.state
  position_eq : ledger.pos = labelPos
  target_label_eq : ledger.targetLabel = label
  target_formula_eq : ledger.targetFormula = formula
  target_frame_eq : ledger.targetFrame = anchor.frame
  tokens_eq : ledger.firstToken :: ledger.remainingTokens =
    entries.map (fun entry => entry.2.origin.token)
  final_observed : final = ⟨db, .proof ledger.final⟩

/-- A nonempty, source-valid normal proof becomes the exact existing native
ledger.  The first label is handled separately because it changes proof mode
from `.start` to `.normal`; the remaining labels use `NormalTokenSteps`. -/
noncomputable def SpelledCallTrace.normalProofLedger
    {fileId : String} {db : DB} {formula : RuntimeFormula}
    {labelPos : Pos} {label : String}
    {initial final : ParserObservedState}
    {first : LocatedName} {rest : List LocatedName}
    {entries : List (LocatedToken × TokenCall)}
    (trace : SpelledCallTrace fileId initial
      ((first :: rest).map LocatedName.name) entries final)
    (anchor : ParserProofAnchor db formula labelPos label initial)
    (charsets : ∀ name ∈ first :: rest,
      NameCharset proofTokenValid name)
    (noUnknown : ∀ name ∈ first :: rest, name.name ≠ "?") :
    ReaderNormalProofLedger anchor entries final := by
  have trace' := trace.reindexInitial anchor.observed_canonical
  simp only [List.map_cons] at trace'
  cases trace' with
  | @cons _ _ texts tailEntries text entry spelling significant
      after_errorFree before_eq tail =>
      have firstCharset : NameCharset proofTokenValid first :=
        charsets first (by simp)
      have firstNotUnknown : first.name ≠ "?" :=
        noUnknown first (by simp)
      have restCharsets :
          ∀ name ∈ rest, NameCharset proofTokenValid name := by
        intro name member
        exact charsets name (by simp [member])
      have restNoUnknown : ∀ name ∈ rest, name.name ≠ "?" := by
        intro name member
        exact noUnknown name (by simp [member])
      let firstFeed := retainedCall_normalProofFeed anchor.state significant
        before_eq spelling firstCharset firstNotUnknown after_errorFree
          anchor.database_eq
      have firstAfterNormal : firstFeed.after.ptp = .normal :=
        feedProof_first_normal_after_normal anchor.state
          entry.2.origin.token
          (db.mkProofState labelPos label formula anchor.frame)
          firstFeed.after firstFeed.success firstFeed.result (by
            simp [DB.mkProofState]) firstFeed.token_not_open
              firstFeed.token_not_unknown
      have tail' := tail.reindexInitial firstFeed.observed_eq
      let tailResult := tail'.normalProofSteps anchor.state
        anchor.database_eq firstAfterNormal restCharsets restNoUnknown
      let ledger : NormalTokenLedger :=
        { anchor := anchor.state
          pos := labelPos
          targetLabel := label
          targetFormula := formula
          targetFrame := anchor.frame
          trim_origin := by
            simpa [anchor.database_eq] using anchor.trim
          firstToken := entry.2.origin.token
          afterFirst := firstFeed.after
          first_success := by
            simpa [anchor.database_eq] using firstFeed.success
          first_not_open := firstFeed.token_not_open
          first_not_unknown := firstFeed.token_not_unknown
          first_result := by
            simpa [anchor.database_eq] using firstFeed.result
          remainingTokens :=
            tailEntries.map (fun tailEntry => tailEntry.2.origin.token)
          final := tailResult.1
          remaining := tailResult.2.2 }
      exact
        { ledger := ledger
          anchor_eq := rfl
          position_eq := rfl
          target_label_eq := rfl
          target_formula_eq := rfl
          target_frame_eq := rfl
          tokens_eq := rfl
          final_observed := tailResult.2.1 }

/-- The successful result of the reader's actual `$.' call, rebased onto the
fixed pre-insertion proof anchor. -/
structure ReaderProofFinish
    (anchor : ParserState) (proof : RuntimeProofState)
    (final : ParserObservedState) : Type where
  finish_success : (anchor.finishProof proof).db.error? = none
  final_observed : final =
    ⟨(anchor.finishProof proof).db, .start⟩

/-- A one-token `$.' chronology closes the exact retained proof state through
the shipped `finishProof`; no post-insertion database is supplied. -/
def SpelledCallTrace.proofFinish
    {fileId : String} {db : DB} {proof : RuntimeProofState}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId ⟨db, .proof proof⟩
      ["$."] entries final)
    (anchor : ParserState) (anchor_db : anchor.db = db) :
    ReaderProofFinish anchor proof final := by
  cases trace with
  | @cons _ _ texts tailEntries text entry spelling significant
      after_errorFree before_eq tail =>
      cases tail with
      | nil state =>
          have entryBytes : entry.1.bytes =
              SourceGSLTRawSourceComposition.statementEndBytes :=
            retainedBytes_eq_of_spelling spelling (by rfl)
          have notComment :
              entry.2.origin.token.eqArray "$(".toAscii = false := by
            simpa [shippedToken] using
              retainedCall_eqArray_false significant (by
                rw [entryBytes]
                decide)
          have notInclude :
              entry.2.origin.token.eqArray "$[".toAscii = false := by
            simpa [shippedToken] using
              retainedCall_eqArray_false significant (by
                rw [entryBytes]
                decide)
          have isFinish :
              entry.2.origin.token.eqArray "$.".toAscii = true := by
            simpa [shippedToken] using
              retainedCall_eqArray_true significant (by
                rw [entryBytes]
                rfl)
          obtain ⟨beforeDb, beforeMode⟩ :=
            call_before_fields_of_observed significant before_eq
          have liveSuccess :
              (entry.2.before.feedToken entry.2.origin.parserOffset
                entry.2.origin.token).db.error? = none := by
            rw [← entry.2.after_eq]
            exact after_errorFree
          have liveAnchorDb : entry.2.before.db = anchor.db :=
            beforeDb.trans anchor_db.symm
          have rebased := feedToken_proof_finish_rebase anchor
            entry.2.before entry.2.origin.parserOffset entry.2.origin.token
            proof liveAnchorDb beforeMode notComment notInclude isFinish
              liveSuccess
          have afterDb : entry.2.after.db =
              (anchor.finishProof proof).db := by
            rw [entry.2.after_eq]
            exact rebased.2
          have exactFinish := feedToken_proof_finish_exact entry.2.before
            entry.2.origin.parserOffset entry.2.origin.token proof beforeMode
              notComment notInclude isFinish
          have afterMode : entry.2.after.tokp = .start := by
            rw [entry.2.after_eq, exactFinish]
            exact Metamath.ParserOps.finishProof_tokp_start
              { entry.2.before with tokp := default } proof
          have observedAfter : parserObservedState entry.2.after =
              ⟨(anchor.finishProof proof).db, .start⟩ := by
            simp only [parserObservedState, observedSemanticState,
              parserSemanticState]
            rw [afterDb, afterMode]
            rfl
          exact
            { finish_success := rebased.1
              final_observed := observedAfter }

/-- The complete reader-derived normal proof, split at its unique `$.' call.
The prefix contains all submitted proof-label calls; the final component is
the production reader's actual proof finalization. -/
structure ReaderFinishedNormalProof
    {db : DB} {formula : RuntimeFormula} {labelPos : Pos} {label : String}
    {initial : ParserObservedState}
    (anchor : ParserProofAnchor db formula labelPos label initial)
    (sourceLabels : List String)
    (entries : List (LocatedToken × TokenCall))
    (final : ParserObservedState) : Type where
  proof_final : ParserObservedState
  ledger : ReaderNormalProofLedger anchor
    (entries.take sourceLabels.length) proof_final
  finish : ReaderProofFinish anchor.state ledger.ledger.final final
  labels_eq :
    submittedNormalLabels ledger.ledger.firstToken
      ledger.ledger.remainingTokens = sourceLabels

/-- Split a nonempty normal-proof chronology at its final `$.' and construct
both the exact native ledger and the successful shipped finalization. -/
noncomputable def SpelledCallTrace.finishedNormalProof
    {fileId : String} {db : DB} {formula : RuntimeFormula}
    {labelPos : Pos} {label : String}
    {initial final : ParserObservedState}
    {first : LocatedName} {rest : List LocatedName}
    {entries : List (LocatedToken × TokenCall)}
    (trace : SpelledCallTrace fileId initial
      (((first :: rest).map LocatedName.name) ++ ["$."])
      entries final)
    (anchor : ParserProofAnchor db formula labelPos label initial)
    (charsets : ∀ name ∈ first :: rest,
      NameCharset proofTokenValid name)
    (noUnknown : ∀ name ∈ first :: rest, name.name ≠ "?") :
    ReaderFinishedNormalProof anchor
      ((first :: rest).map LocatedName.name) entries final := by
  obtain ⟨proofFinal, proofTrace, finishTrace⟩ :=
    trace.splitAt (first :: rest).length
  have proofTrace' : SpelledCallTrace fileId initial
      ((first :: rest).map LocatedName.name)
      (entries.take ((first :: rest).map LocatedName.name).length)
      proofFinal := by
    simpa using proofTrace
  let ledger := proofTrace'.normalProofLedger anchor charsets noUnknown
  have decodedLabels :=
    proofTrace'.decodedNormalLabels_eq charsets noUnknown
  have labelsEq :
      submittedNormalLabels ledger.ledger.firstToken
          ledger.ledger.remainingTokens =
        (first :: rest).map LocatedName.name := by
    unfold submittedNormalLabels
    rw [ledger.tokens_eq]
    rw [List.map_map]
    have functionsEq :
        ((fun token : ByteSlice => (Metamath.Verify.toLabel token).2) ∘
            (fun entry : LocatedToken × TokenCall =>
              entry.2.origin.token)) =
          (fun entry : LocatedToken × TokenCall =>
            (Metamath.Verify.toLabel entry.2.origin.token).2) := by
      funext entry
      rfl
    rw [functionsEq]
    exact decodedLabels
  have finishTrace' := finishTrace.reindexInitial ledger.final_observed
  have finishTrace'' : SpelledCallTrace fileId
      ⟨db, .proof ledger.ledger.final⟩ ["$."]
      (entries.drop (first :: rest).length) final := by
    simpa using finishTrace'
  exact
    { proof_final := proofFinal
      ledger := ledger
      finish := finishTrace''.proofFinish anchor.state anchor.database_eq
      labels_eq := labelsEq }

/-- Reflect the production reader's completed normal proof into the source
lifecycle witness over the authored declaration order.  The runtime object
map is first reflected through its canonical projection; every proof node is
then rebuilt against the authored prefix by its assertion-application
semantics, preserving the exact submitted label list. -/
noncomputable def ReaderFinishedNormalProof.toNormalDischarge
    {db : DB} {runtimeFormula : RuntimeFormula}
    {labelPos : Pos} {label : String}
    {initial final : ParserObservedState}
    {sourceLabels : List String}
    {entries : List (LocatedToken × TokenCall)}
    {before : SourceState}
    (anchor : ParserProofAnchor db runtimeFormula labelPos label initial)
    (finished : ReaderFinishedNormalProof anchor sourceLabels entries final)
    (agreement : RuntimeDBAgrees db before)
    (runtimeTarget sourceTarget : ValidatedPresentation)
    (runtimePresentation :
      presentationOfSourcePrefix? (runtimePrefix before) =
        some runtimeTarget.1)
    (sourcePresentation :
      presentationOfSourcePrefix? before.toSourcePrefix =
        some sourceTarget.1)
    (formula : ConstantHeadedFormula)
    (formula_eq : runtimeFormula = formula.toRuntime) :
    NormalDischarge before formula sourceLabels := by
  let ledger := finished.ledger.ledger
  have finishSuccess :
      (ledger.anchor.finishProof ledger.final).db.error? = none := by
    rw [finished.ledger.anchor_eq]
    exact finished.finish.finish_success
  have projectEq :
      projectPrefix? ledger.anchor.db =
        some (runtimePrefix before).toProjection := by
    rw [finished.ledger.anchor_eq, anchor.database_eq]
    exact agreement.projectPrefix_eq
  have runtimeProjection :
      presentationOfProjection? (runtimePrefix before).toProjection =
        some runtimeTarget.1 := by
    rw [← presentationOfSourcePrefix?_eq_runtime]
    exact runtimePresentation
  have targetFormulaEq : ledger.targetFormula = formula.toRuntime :=
    finished.ledger.target_formula_eq.trans formula_eq
  let reflection :=
    Mettapedia.Languages.Metamath.InferenceNormalByteReflection.NormalTokenLedger.reflectNative
      ledger finishSuccess (runtimePrefix before).toProjection
        runtimeTarget formula projectEq runtimeProjection targetFormulaEq
  let runtimeWitness := runtimeTree_exists_source reflection.tree
  let runtimeTree := Classical.choose runtimeWitness
  have runtimeTreeEq : runtimeTree.toRuntime = reflection.tree :=
    Classical.choose_spec runtimeWitness
  let sourceTree := runtimePrefixTreeToSource runtimePresentation
    sourcePresentation runtimeTree
  have runtimeLabelsEq : runtimeTree.labels = reflection.tree.labels := by
    calc
      runtimeTree.labels = runtimeTree.toRuntime.labels :=
        runtimeTree.labels_toRuntime.symm
      _ = reflection.tree.labels :=
        congrArg GeneratedProvesTree.labels runtimeTreeEq
  have sourceLabelsEq : sourceTree.labels = sourceLabels := by
    calc
      sourceTree.labels = runtimeTree.labels :=
        runtimePrefixTreeToSource_labels runtimePresentation
          sourcePresentation runtimeTree
      _ = reflection.tree.labels := runtimeLabelsEq
      _ = submittedNormalLabels ledger.firstToken ledger.remainingTokens :=
        reflection.labels_eq
      _ = sourceLabels := finished.labels_eq
  exact
    { target := sourceTarget
      presentation_eq := sourcePresentation
      tree := sourceTree
      labels_eq := sourceLabelsEq }

/-- Result of replaying one verified normal `$p` statement through the real
reader.  Proof discharge and the post-insertion prefix relation are produced
together, at the statement's actual byte boundary. -/
structure ReaderVerifiedNormalStatement
    (before after : SourceState) (formula : ConstantHeadedFormula)
    (labels : List String) (final : ParserObservedState) : Type where
  discharge : NormalDischarge before formula labels
  nextPrefix : SourceParserPrefixAgrees after final

theorem ReaderVerifiedNormalStatement.final_mode_eq
    {before after : SourceState} {formula : ConstantHeadedFormula}
    {labels : List String} {final : ParserObservedState}
    (result : ReaderVerifiedNormalStatement before after formula labels final) :
    final.mode = .start :=
  result.nextPrefix.mode_eq

/-- Negative boundary: a completed normal statement cannot remain in any
proof mode. -/
theorem ReaderVerifiedNormalStatement.final_mode_ne_proof
    {before after : SourceState} {formula : ConstantHeadedFormula}
    {labels : List String} {final : ParserObservedState}
    (result : ReaderVerifiedNormalStatement before after formula labels final)
    (proof : RuntimeProofState) :
    final.mode ≠ .proof proof := by
  rw [result.final_mode_eq]
  intro equality
  cases equality

/-- Internal formula-prefix replay used by the complete normal-statement
transition below and exposed publicly after that transition. -/
private noncomputable def SpelledCallTrace.provableFormulaAnchorCore
    {fileId : String} {source : SourceState} {db : DB}
    {label typecode : LocatedName} {body : List LocatedName}
    {bodySymbols : List Sym}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId ⟨db, .start⟩
      (label.name :: "$p" ::
        (typecode :: body).map LocatedName.name ++ ["$="])
      entries final)
    (agreement : RuntimeDBAgrees db source)
    (sourceValid : sourceStateValid source = true)
    (labelCharset : NameCharset labelBytesValid label)
    (typecodeCharset : NameCharset mathBytesValid typecode)
    (bodyCharsets :
      ∀ name ∈ body, NameCharset mathBytesValid name)
    (taggedFormula : tagBody source (typecode :: body) =
      .ok (.const typecode.name :: bodySymbols)) :
    Σ labelPos : Pos,
      ParserProofAnchor db
        (ConstantHeadedFormula.toRuntime ⟨typecode.name, bodySymbols⟩)
        labelPos label.name final := by
  obtain ⟨afterLabel, labelTrace, afterLabelTrace⟩ := trace.splitAt 1
  have labelTrace' : SpelledCallTrace fileId ⟨db, .start⟩
      [label.name] (entries.take 1) afterLabel := by
    simpa using labelTrace
  let labelWitness := labelTrace'.startLabel_final labelCharset
  let labelPos := Classical.choose labelWitness
  have afterLabel_eq := Classical.choose_spec labelWitness
  have afterLabelTrace' := afterLabelTrace.reindexInitial afterLabel_eq
  obtain ⟨afterKeyword, keywordTrace, afterKeywordTrace⟩ :=
    afterLabelTrace'.splitAt 1
  have keywordTrace' : SpelledCallTrace fileId
      ⟨db, .label labelPos label.name⟩ ["$p"]
      ((entries.drop 1).take 1) afterKeyword := by
    simpa using keywordTrace
  have afterKeyword_eq := keywordTrace'.provableKeyword_final
  have afterKeywordTrace' :=
    afterKeywordTrace.reindexInitial afterKeyword_eq
  let formulaNames := typecode :: body
  obtain ⟨afterFormula, formulaTrace, delimiterTrace⟩ :=
    afterKeywordTrace'.splitAt formulaNames.length
  have formulaTrace' : SpelledCallTrace fileId
      ⟨db, .math #[] ⟨.thm, labelPos, label.name⟩⟩
      (formulaNames.map LocatedName.name)
      (((entries.drop 1).drop 1).take formulaNames.length)
      afterFormula := by
    simpa [formulaNames] using formulaTrace
  have formulaCharsets :
      ∀ name ∈ formulaNames, NameCharset mathBytesValid name := by
    intro name member
    rcases List.mem_cons.mp member with rfl | member
    · exact typecodeCharset
    · exact bodyCharsets name member
  have afterFormula_eq := formulaTrace'.mathSymbols_final agreement
    sourceValid formulaCharsets taggedFormula
  have afterFormula_eq' : afterFormula =
      ⟨db, .math
        (ConstantHeadedFormula.toRuntime ⟨typecode.name, bodySymbols⟩)
        ⟨.thm, labelPos, label.name⟩⟩ := by
    simpa [formulaNames, ConstantHeadedFormula.toRuntime] using
      afterFormula_eq
  have delimiterTrace' := delimiterTrace.reindexInitial afterFormula_eq'
  have delimiterTrace'' : SpelledCallTrace fileId
      ⟨db, .math
        (ConstantHeadedFormula.toRuntime ⟨typecode.name, bodySymbols⟩)
        ⟨.thm, labelPos, label.name⟩⟩
      ["$="]
      (((entries.drop 1).drop 1).drop formulaNames.length) final := by
    simpa [formulaNames] using delimiterTrace'
  exact ⟨labelPos, delimiterTrace''.theoremDelimiter_anchor⟩

/-- An exact spelling-indexed normal `$p` statement constructs its source
proof witness and advances the source/runtime prefix relation.  The theorem
uses the first proof label's `.start → .normal` transition and the unique
terminating `$.' call; no final-state agreement is supplied. -/
noncomputable def SpelledCallTrace.verifiedNormalStatement
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
    (noUnknown :
      ∀ name ∈ firstStep :: restSteps, name.name ≠ "?")
    (taggedFormula : tagBody before (typecode :: body) =
      .ok (.const typecode.name :: bodySymbols))
    (inserted : insertAssertion? before label.name
      ⟨typecode.name, bodySymbols⟩ = some after)
    (runtimeTarget sourceTarget : ValidatedPresentation)
    (runtimePresentation :
      presentationOfSourcePrefix? (runtimePrefix before) =
        some runtimeTarget.1)
    (sourcePresentation :
      presentationOfSourcePrefix? before.toSourcePrefix =
        some sourceTarget.1) :
    ReaderVerifiedNormalStatement before after
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
  obtain ⟨proofInitial, formulaTrace, proofTrace⟩ :=
    trace'.splitAppend
  have formulaTrace' : SpelledCallTrace fileId ⟨db, .start⟩
      (label.name :: "$p" ::
        (typecode :: body).map LocatedName.name ++ ["$="])
      (entries.take formulaPrefix.length) proofInitial := by
    simpa [formulaPrefix] using formulaTrace
  let anchored := formulaTrace'.provableFormulaAnchorCore agreement
    (insertAssertion?_valid_before inserted)
    labelCharset typecodeCharset bodyCharsets taggedFormula
  let anchor := anchored.2
  have proofTrace' : SpelledCallTrace fileId proofInitial
      ((firstStep :: restSteps).map LocatedName.name ++ ["$."])
      (entries.drop formulaPrefix.length) final := by
    simpa [proofSuffix] using proofTrace
  let finished := proofTrace'.finishedNormalProof
    (first := firstStep) (rest := restSteps) anchor
    stepCharsets noUnknown
  let discharge := finished.toNormalDischarge anchor agreement
    runtimeTarget sourceTarget runtimePresentation sourcePresentation
      ⟨typecode.name, bodySymbols⟩ rfl
  let ledger := finished.ledger.ledger
  have finishSuccess :
      (ledger.anchor.finishProof ledger.final).db.error? = none := by
    rw [finished.ledger.anchor_eq]
    exact finished.finish.finish_success
  have postInsert :=
    (ledger.toExactNormalParserTrace.accepted_prefix_boundary
      finishSuccess).2.2.2.2.2.2.1
  have postInsert' :
      (anchor.state.finishProof ledger.final).db =
        db.insert ledger.final.pos label.name
          (.assert (ConstantHeadedFormula.toRuntime
              ⟨typecode.name, bodySymbols⟩) anchor.frame) := by
    rw [finished.ledger.anchor_eq,
      finished.ledger.target_label_eq,
      finished.ledger.target_formula_eq,
      finished.ledger.target_frame_eq,
      anchor.database_eq] at postInsert
    exact postInsert
  have mandatoryTrim := trimFrame'_eq_mandatory agreement
    ⟨typecode.name, bodySymbols⟩
      (mandatory_covered_of_insert inserted)
  have frameEq : anchor.frame =
      (mandatoryFrame before ⟨typecode.name, bodySymbols⟩).toRuntime :=
    Except.ok.inj (anchor.trim.symm.trans mandatoryTrim)
  have nextAgreement := RuntimeDBAgrees.insertAssertion agreement inserted
    ledger.final.pos
  refine
    { discharge := discharge
      nextPrefix := ?_ }
  rw [finished.finish.final_observed]
  refine
    { mode_eq := rfl
      database := ?_
      interrupt_eq := ?_ }
  rw [postInsert', frameEq]
  exact nextAgreement
  rw [postInsert']
  exact (runtimeInsert_interrupt db ledger.final.pos label.name _).trans
    interruptEq

/-! ## Compressed proof reflection at one statement boundary -/

/-- A retained proof-token call rebased onto a fixed parser anchor.  This is
the phase-neutral core used for `(`, explicit-header labels, `)`, and
compressed body words. -/
structure RetainedProofFeed
    (anchor : ParserState) (db : DB) (before : RuntimeProofState)
    (token : ByteSlice) (observedAfter : ParserObservedState) : Type where
  after : RuntimeProofState
  observed_eq : observedAfter = ⟨db, .proof after⟩
  success : (anchor.feedProof token before).db.error? = none
  result : (anchor.feedProof token before).tokp = .proof after
  go : ParserState.feedProof.go anchor token before = .ok after

/-- Rebase one retained proof token after the outer `feedToken` dispatcher has
ruled out comments, includes, and theorem termination.  The byte inequalities
come from the authored token class at each caller. -/
noncomputable def retainedCall_proofFeed
    (anchor : ParserState)
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB}
    {before : RuntimeProofState} {bytes : List UInt8}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before = ⟨db, .proof before⟩)
    (entryBytes : entry.1.bytes = bytes)
    (notCommentBytes : bytes ≠ "$(".toAscii.data.toList)
    (notIncludeBytes : bytes ≠ "$[".toAscii.data.toList)
    (notFinishBytes : bytes ≠ "$.".toAscii.data.toList)
    (after_errorFree : call.after.db.error? = none)
    (anchor_db : anchor.db = db) :
    RetainedProofFeed anchor db before call.origin.token
      (parserObservedState call.after) := by
  have notComment : call.origin.token.eqArray "$(".toAscii = false := by
    simpa [shippedToken] using retainedCall_eqArray_false significant
      (entryBytes ▸ notCommentBytes)
  have notInclude : call.origin.token.eqArray "$[".toAscii = false := by
    simpa [shippedToken] using retainedCall_eqArray_false significant
      (entryBytes ▸ notIncludeBytes)
  have notFinish : call.origin.token.eqArray "$.".toAscii = false := by
    simpa [shippedToken] using retainedCall_eqArray_false significant
      (entryBytes ▸ notFinishBytes)
  obtain ⟨beforeDb, beforeMode⟩ :=
    call_before_fields_of_observed significant before_eq
  have liveSuccess :
      (call.before.feedToken call.origin.parserOffset
        call.origin.token).db.error? = none := by
    rw [← call.after_eq]
    exact after_errorFree
  let cleared : ParserState := { call.before with tokp := default }
  have exactStep := feedToken_proof_step_exact call.before
    call.origin.parserOffset call.origin.token before beforeMode
    notComment notInclude notFinish
  have clearedSuccess :
      (cleared.feedProof call.origin.token before).db.error? = none := by
    rw [← exactStep]
    exact liveSuccess
  let successWitness :=
    Metamath.PrefixTraceCompressed.feedProof_success_go_ok cleared
      call.origin.token before clearedSuccess
  let after := Classical.choose successWitness
  have successFacts := Classical.choose_spec successWitness
  have liveResult :
      (call.before.feedToken call.origin.parserOffset
        call.origin.token).tokp = .proof after := by
    rw [exactStep]
    exact successFacts.2
  have afterDb : call.after.db = db := by
    rw [call.after_eq, exactStep]
    rw [Metamath.ParserOps.feedProof_success_db cleared
      call.origin.token before clearedSuccess]
    exact beforeDb
  have afterMode : call.after.tokp = .proof after := by
    rw [call.after_eq]
    exact liveResult
  have observedAfter :
      parserObservedState call.after = ⟨db, .proof after⟩ := by
    simp only [parserObservedState, observedSemanticState,
      parserSemanticState]
    rw [afterDb, afterMode]
    rfl
  have liveAnchorDb : call.before.db = anchor.db :=
    beforeDb.trans anchor_db.symm
  have clearedAnchorDb : cleared.db = anchor.db := by
    simpa [cleared] using liveAnchorDb
  have rebased := feedProof_success_result_rebase cleared anchor
    call.origin.token before after clearedAnchorDb clearedSuccess
      successFacts.2
  have anchorGo :
      ParserState.feedProof.go anchor call.origin.token before = .ok after := by
    rw [← feedProof_go_eq_of_db_eq cleared anchor call.origin.token before
      clearedAnchorDb]
    exact successFacts.1
  exact
    { after := after
      observed_eq := observedAfter
      success := rebased.1
      result := rebased.2
      go := anchorGo }

/-- Reader evidence for the opening `(` of a compressed proof.  The bulk
mandatory preload is retained separately from the `.preload` phase update. -/
structure ReaderCompressedOpen
    {db : DB} {formula : RuntimeFormula} {labelPos : Pos} {label : String}
    {initial : ParserObservedState}
    (anchor : ParserProofAnchor db formula labelPos label initial)
    (final : ParserObservedState) : Type where
  mandatory : RuntimeProofState
  mandatoryExecution :
    db.preloadMandatoryHyps
      (db.mkProofState labelPos label formula anchor.frame) = .ok mandatory
  final_observed : final =
    ⟨db, .proof { mandatory with ptp := .preload }⟩

/-- The retained opening delimiter executes the shipped mandatory-hypothesis
preload and enters the explicit-header phase. -/
noncomputable def SpelledCallTrace.compressedOpen
    {fileId : String} {db : DB} {formula : RuntimeFormula}
    {labelPos : Pos} {label : String}
    {initial final : ParserObservedState}
    {entries : List (LocatedToken × TokenCall)}
    (trace : SpelledCallTrace fileId initial ["("] entries final)
    (anchor : ParserProofAnchor db formula labelPos label initial) :
    ReaderCompressedOpen anchor final := by
  cases trace with
  | @cons _ _ texts tailEntries text entry spelling significant
      after_errorFree before_eq tail =>
      cases tail with
      | nil state =>
          have entryBytes : entry.1.bytes = "(".toAscii.data.toList :=
            retainedBytes_eq_of_spelling spelling (by rfl)
          let feed := retainedCall_proofFeed anchor.state significant
            (before_eq.trans anchor.observed_canonical) entryBytes
            (by decide) (by decide) (by decide)
            after_errorFree anchor.database_eq
          have isOpen :
              entry.2.origin.token.eqArray "(".toAscii = true := by
            simpa [shippedToken] using
              retainedCall_eqArray_true significant entryBytes
          let extraction :=
            Metamath.PrefixTraceCompressed.go_start_open_extracts
              anchor.state entry.2.origin.token
              (db.mkProofState labelPos label formula anchor.frame)
              feed.after feed.go (by rfl) (by simpa using isOpen)
          let mandatory := Classical.choose extraction
          have extractionFacts := Classical.choose_spec extraction
          have mandatoryExecution :
              db.preloadMandatoryHyps
                (db.mkProofState labelPos label formula anchor.frame) =
                .ok mandatory := by
            change db.preloadMandatoryHyps
                (db.mkProofState labelPos label formula anchor.frame) =
              .ok (Classical.choose extraction)
            calc
              db.preloadMandatoryHyps
                    (db.mkProofState labelPos label formula anchor.frame) =
                  anchor.state.db.preloadMandatoryHyps
                    (db.mkProofState labelPos label formula anchor.frame) :=
                congrArg
                  (fun runtimeDb : DB => runtimeDb.preloadMandatoryHyps
                    (db.mkProofState labelPos label formula anchor.frame))
                  anchor.database_eq.symm
              _ = .ok (Classical.choose extraction) := extractionFacts.1
          exact
            { mandatory := mandatory
              mandatoryExecution := mandatoryExecution
              final_observed := by
                rw [feed.observed_eq, extractionFacts.2] }

/-- Ordered explicit-header preloading extracted from retained reader calls. -/
structure ReaderCompressedHeader
    (db : DB) (before : RuntimeProofState) (labels : List String)
    (final : ParserObservedState) : Type where
  after : RuntimeProofState
  execution : labels.foldlM (db.preload) before = .ok after
  after_preload : after.ptp = .preload
  final_observed : final = ⟨db, .proof after⟩

/-- A retained sequence of header labels is exactly the shipped ordered
`DB.preload` fold. -/
noncomputable def SpelledCallTrace.compressedHeader :
    {fileId : String} → {db : DB} →
    {before : RuntimeProofState} → {names : List LocatedName} →
    {entries : List (LocatedToken × TokenCall)} →
    {final : ParserObservedState} →
    (anchor : ParserState) →
    anchor.db = db → before.ptp = .preload →
    (trace : SpelledCallTrace fileId ⟨db, .proof before⟩
      (names.map LocatedName.name) entries final) →
    (∀ name ∈ names, NameCharset labelBytesValid name) →
    ReaderCompressedHeader db before (names.map LocatedName.name) final
  | _, db, before, [], _, _, anchor, anchorDb, beforePreload, trace, _ => by
      cases trace
      exact
        { after := before
          execution := rfl
          after_preload := beforePreload
          final_observed := rfl }
  | fileId, db, before, name :: rest, _, final, anchor, anchorDb,
      beforePreload, trace, charsets => by
      simp only [List.map_cons] at trace ⊢
      cases trace with
      | @cons _ _ texts tailEntries text entry spelling significant
          after_errorFree before_eq tail =>
          let charset := charsets name (by simp)
          let bytes := Classical.choose charset
          have charsetFacts := Classical.choose_spec charset
          have valid : labelBytesValid bytes = true := charsetFacts.1
          have name_eq : tokenText bytes = name.name := charsetFacts.2.symm
          have entryBytes : entry.1.bytes = bytes :=
            tokenText_injective (spelling.trans name_eq.symm)
          have notCommentBytes : bytes ≠ "$(".toAscii.data.toList := by
            intro equality
            rw [equality] at valid
            have invalid :
                labelBytesValid "$(".toAscii.data.toList = false := by
              decide
            rw [invalid] at valid
            cases valid
          have notIncludeBytes : bytes ≠ "$[".toAscii.data.toList := by
            intro equality
            rw [equality] at valid
            have invalid :
                labelBytesValid "$[".toAscii.data.toList = false := by
              decide
            rw [invalid] at valid
            cases valid
          have notFinishBytes : bytes ≠ "$.".toAscii.data.toList := by
            intro equality
            rw [equality] at valid
            have invalid :
                labelBytesValid "$.".toAscii.data.toList = false := by
              decide
            rw [invalid] at valid
            cases valid
          have notCloseBytes : bytes ≠ ")".toAscii.data.toList := by
            intro equality
            rw [equality] at valid
            have invalid :
                labelBytesValid ")".toAscii.data.toList = false := by
              decide
            rw [invalid] at valid
            cases valid
          let feed := retainedCall_proofFeed anchor significant before_eq
            entryBytes notCommentBytes notIncludeBytes notFinishBytes
              after_errorFree anchorDb
          have decoded := retainedCall_toLabel significant spelling charset
          have notClose :
              ¬ entry.2.origin.token.eqArray ")".toAscii := by
            have falseEq :
                entry.2.origin.token.eqArray ")".toAscii = false := by
              simpa [shippedToken] using retainedCall_eqArray_false significant
                (entryBytes ▸ notCloseBytes)
            simpa using falseEq
          have extracted :=
            Metamath.PrefixTraceCompressed.go_preload_label_extracts
              anchor entry.2.origin.token before feed.after feed.go
                beforePreload notClose
          have preloadExecution :
              db.preload before name.name = .ok feed.after := by
            rw [anchorDb] at extracted
            have labelEq :
                (Metamath.Verify.toLabel entry.2.origin.token).2 =
                  name.name := by
              simpa [shippedToken] using congrArg Prod.snd decoded
            simpa [labelEq] using extracted.2
          have feedAfterPreload : feed.after.ptp = .preload :=
            (Metamath.PrefixTraceCompressed.preload_preserves_ptp
              db before feed.after name.name preloadExecution).trans
                beforePreload
          have tail' := tail.reindexInitial feed.observed_eq
          let restResult := tail'.compressedHeader anchor anchorDb
            feedAfterPreload
            (fun next member => charsets next (by simp [member]))
          exact
            { after := restResult.after
              execution := by
                simp only [List.foldlM_cons, bind, Except.bind]
                rw [preloadExecution]
                exact restResult.execution
              after_preload := restResult.after_preload
              final_observed := restResult.final_observed }

/-- The retained closing `)` changes only the proof-token phase and enters
compressed decoding between proof steps. -/
noncomputable def SpelledCallTrace.compressedClose_final
    {fileId : String} {db : DB} {before : RuntimeProofState}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId ⟨db, .proof before⟩
      [")"] entries final)
    (anchor : ParserState) (anchorDb : anchor.db = db)
    (beforePreload : before.ptp = .preload) :
    final = ⟨db, .proof { before with
      ptp := .compressed .betweenSteps }⟩ := by
  cases trace with
  | @cons _ _ texts tailEntries text entry spelling significant
      after_errorFree before_eq tail =>
      cases tail with
      | nil state =>
          have entryBytes : entry.1.bytes = ")".toAscii.data.toList :=
            retainedBytes_eq_of_spelling spelling (by rfl)
          let feed := retainedCall_proofFeed anchor significant before_eq
            entryBytes (by decide) (by decide) (by decide)
              after_errorFree anchorDb
          have isClose :
              entry.2.origin.token.eqArray ")".toAscii = true := by
            simpa [shippedToken] using
              retainedCall_eqArray_true significant entryBytes
          have after_eq :=
            Metamath.PrefixTraceCompressed.go_preload_close_extracts
              anchor entry.2.origin.token before feed.after feed.go
                beforePreload (by simpa using isClose)
          rw [feed.observed_eq, after_eq]

/-- The authored compressed-word byte class contains exactly bytes for which
the invalid-byte policy is observationally irrelevant. -/
theorem compressedWordByte_upper_or_question (byte : UInt8)
    (valid : compressedWordByte byte = true) :
    ('A'.toUInt8 ≤ byte ∧ byte ≤ 'Z'.toUInt8) ∨
      byte = '?'.toUInt8 := by
  have exhaustive : ∀ index : Fin 256,
      compressedWordByte (UInt8.ofNat index.val) = true →
        ('A'.toUInt8 ≤ UInt8.ofNat index.val ∧
          UInt8.ofNat index.val ≤ 'Z'.toUInt8) ∨
        UInt8.ofNat index.val = '?'.toUInt8 := by
    set_option maxRecDepth 100000 in
      decide
  have byte_lt : byte.toNat < 256 := byte.toBitVec.isLt
  have valid' :
      compressedWordByte (UInt8.ofNat byte.toNat) = true := by
    simpa [UInt8.ofNat_toNat] using valid
  simpa [UInt8.ofNat_toNat] using
    exhaustive ⟨byte.toNat, byte_lt⟩ valid'

/-- On an authored compressed-word byte, every configured decoder policy
executes the same step as the rejecting, specification-faithful policy. -/
theorem decodeCompressedStep_policy_eq_of_compressedWordByte
    (policy : CompressedInvalidBytePolicy)
    (initial : MProd (List ParserState.CompressedAction)
      Metamath.Verify.CompressedPhase)
    (byte : UInt8) (valid : compressedWordByte byte = true) :
    decodeCompressedStep policy .immediatelyAfterUse initial byte =
      decodeCompressedStep .reject .immediatelyAfterUse initial byte := by
  rcases compressedWordByte_upper_or_question byte valid with
      uppercase | question
  · rcases uppercase with ⟨lower, upper⟩
    simp [decodeCompressedStep, lower, upper]
  · subst byte
    simp [decodeCompressedStep]

/-- A whole authored compressed word has policy-independent fold semantics. -/
theorem decodeFold_policy_eq_of_all_compressedWordByte
    (policy : CompressedInvalidBytePolicy) (bytes : List UInt8)
    (valid : bytes.all compressedWordByte = true)
    (initial : MProd (List ParserState.CompressedAction)
      Metamath.Verify.CompressedPhase) :
    bytes.foldlM
        (decodeCompressedStep policy .immediatelyAfterUse) initial =
      bytes.foldlM
        (decodeCompressedStep .reject .immediatelyAfterUse) initial := by
  induction bytes generalizing initial with
  | nil => rfl
  | cons byte bytes ih =>
      simp only [List.all_cons, Bool.and_eq_true] at valid
      simp only [List.foldlM_cons]
      rw [decodeCompressedStep_policy_eq_of_compressedWordByte
        policy initial byte valid.1]
      cases head : decodeCompressedStep .reject .immediatelyAfterUse
          initial byte with
      | error error => rfl
      | ok next => exact ih valid.2 next

/-- For a source-valid compressed word, the reader configuration cannot
change decoding.  This is the exact bridge needed when reflecting a live
reader run back into the authored rejecting decoder. -/
theorem decodeCompressed_policy_eq_of_compressedWordValid
    (tk : ByteSlice) (phase : Metamath.Verify.CompressedPhase)
    (policy : CompressedInvalidBytePolicy)
    (valid : compressedWordValid (sliceBytes tk) = true) :
    ParserState.decodeCompressed tk phase policy .immediatelyAfterUse =
      ParserState.decodeCompressed tk phase := by
  have valid' := valid
  rw [SourceGSLTCompressedMMLean4.sliceBytes_eq_sliceList] at valid'
  simp only [compressedWordValid, Bool.and_eq_true] at valid'
  rw [decodeCompressed_eq_fold, decodeCompressed_eq_fold]
  rw [decodeFold_policy_eq_of_all_compressedWordByte
    policy (sliceList tk) valid'.2]

/-- The actual compressed-body calls, retained as one fused inner-parser run
and tied to the exact authored word bytes. -/
structure ReaderCompressedBody
    (anchor : ParserState) (db : DB) (before : RuntimeProofState)
    (words : List (List UInt8))
    (entries : List (LocatedToken × TokenCall))
    (final : ParserObservedState) : Type where
  after : RuntimeProofState
  execution :
    runCompressedTokenGo anchor
      (entries.map (fun entry => entry.2.origin.token)) before = .ok after
  bytes_eq :
    (entries.map (fun entry => entry.2.origin.token)).map sliceBytes = words
  valid : ∀ word ∈ words, compressedWordValid word = true
  final_observed : final = ⟨db, .proof after⟩

/-- Retained compressed-word calls compose to the implementation's fused
compressed-token loop. -/
noncomputable def SpelledCallTrace.compressedBody :
    {fileId : String} → {db : DB} →
    {before : RuntimeProofState} → {words : List LocatedToken} →
    {entries : List (LocatedToken × TokenCall)} →
    {final : ParserObservedState} →
    (anchor : ParserState) → anchor.db = db →
    (trace : SpelledCallTrace fileId ⟨db, .proof before⟩
      (words.map (fun word => tokenText word.bytes)) entries final) →
    (∀ word ∈ words, compressedWordValid word.bytes = true) →
    ReaderCompressedBody anchor db before (words.map (fun word => word.bytes))
      entries final
  | _, db, before, [], _, _, anchor, anchorDb, trace, _ => by
      cases trace
      exact
        { after := before
          execution := rfl
          bytes_eq := rfl
          valid := by simp
          final_observed := rfl }
  | fileId, db, before, word :: rest, _, final, anchor, anchorDb,
      trace, charsets => by
      simp only [List.map_cons] at trace ⊢
      cases trace with
      | @cons _ _ texts tailEntries text entry spelling significant
          after_errorFree before_eq tail =>
          have entryBytes : entry.1.bytes = word.bytes :=
            tokenText_injective spelling
          have valid : compressedWordValid word.bytes = true :=
            charsets word (by simp)
          have notCommentBytes :
              word.bytes ≠ "$(".toAscii.data.toList := by
            intro equality
            rw [equality] at valid
            have invalid :
                compressedWordValid "$(".toAscii.data.toList = false := by
              decide
            rw [invalid] at valid
            cases valid
          have notIncludeBytes :
              word.bytes ≠ "$[".toAscii.data.toList := by
            intro equality
            rw [equality] at valid
            have invalid :
                compressedWordValid "$[".toAscii.data.toList = false := by
              decide
            rw [invalid] at valid
            cases valid
          have notFinishBytes :
              word.bytes ≠ "$.".toAscii.data.toList := by
            intro equality
            rw [equality] at valid
            have invalid :
                compressedWordValid "$.".toAscii.data.toList = false := by
              decide
            rw [invalid] at valid
            cases valid
          let feed := retainedCall_proofFeed anchor significant before_eq
            entryBytes notCommentBytes notIncludeBytes notFinishBytes
              after_errorFree anchorDb
          have tail' := tail.reindexInitial feed.observed_eq
          let restResult := tail'.compressedBody anchor anchorDb
            (fun next member => charsets next (by simp [member]))
          have headBytes : sliceBytes entry.2.origin.token = word.bytes := by
            change sliceBytes (shippedToken entry.2) = word.bytes
            rw [← callBytes_eq_shippedToken]
            exact (significantLocatedEntry?_some_bytes significant).symm.trans
              entryBytes
          exact
            { after := restResult.after
              execution := by
                simp only [runCompressedTokenGo, List.map_cons,
                  List.foldlM_cons, bind, Except.bind]
                rw [feed.go]
                exact restResult.execution
              bytes_eq := by
                simp only [List.map_cons]
                rw [headBytes, restResult.bytes_eq]
              valid := by
                intro bytes member
                rcases List.mem_cons.mp member with rfl | tailMember
                · exact valid
                · exact restResult.valid bytes tailMember
              final_observed := restResult.final_observed }

/-- Converse of compressed-token fusion.  A successful token-by-token inner
run exposes the one-shot decoder result and the one-shot action application;
the final accumulator remains explicit. -/
theorem runCompressedTokenGo_reflect
    (parser : ParserState) :
    ∀ (tokens : List ByteSlice)
      (phase : Metamath.Verify.CompressedPhase)
      (initial final : RuntimeProofState),
      (∀ token ∈ tokens,
        compressedWordValid (sliceBytes token) = true) →
      parser.db.config.compressedSavePlacement =
        .immediatelyAfterUse →
      runCompressedTokenGo parser tokens
          { initial with ptp := .compressed phase } = .ok final →
      ∃ (actions : List ParserState.CompressedAction)
        (finalPhase : Metamath.Verify.CompressedPhase)
        (result : RuntimeProofState),
        decodeCompressedTokens tokens phase =
            .ok (actions, finalPhase) ∧
          ParserState.applyCompressedActions parser.db initial actions =
            .ok result ∧
          final = { result with ptp := .compressed finalPhase } := by
  intro tokens
  induction tokens with
  | nil =>
      intro phase initial final _ _ execution
      simp only [runCompressedTokenGo, List.foldlM_nil, pure,
        Except.pure] at execution
      have finalEq := Except.ok.inj execution
      subst final
      have emptyApplied :
          ParserState.applyCompressedActions parser.db initial [] =
            .ok initial := by
        unfold ParserState.applyCompressedActions
        rfl
      exact ⟨[], phase, initial, by simp [decodeCompressedTokens],
        emptyApplied, rfl⟩
  | cons token tokens ih =>
      intro phase initial final valid savePlacement execution
      have tokenValid :
          compressedWordValid (sliceBytes token) = true :=
        valid token (by simp)
      have tailValid : ∀ next ∈ tokens,
          compressedWordValid (sliceBytes next) = true := by
        intro next member
        exact valid next (by simp [member])
      have policyEq :=
        decodeCompressed_policy_eq_of_compressedWordValid token phase
          parser.db.config.compressedInvalidBytes tokenValid
      cases decoded : ParserState.decodeCompressed token phase with
      | error error =>
          simp only [runCompressedTokenGo, List.foldlM_cons,
            ParserState.feedProof.go, savePlacement, policyEq, decoded, bind,
            Except.bind] at execution
          cases execution
      | ok decodedResult =>
          obtain ⟨headActions, nextAccumulator⟩ := decodedResult
          cases applied : ParserState.applyCompressedActions parser.db
              { initial with ptp := .compressed phase } headActions with
          | error error =>
              simp only [runCompressedTokenGo, List.foldlM_cons,
                ParserState.feedProof.go, savePlacement, policyEq, decoded,
                applied, bind,
                Except.bind] at execution
              cases execution
          | ok middle =>
              have tailExecution :
                  runCompressedTokenGo parser tokens
                      { middle with ptp := .compressed nextAccumulator } =
                    .ok final := by
                simpa only [runCompressedTokenGo, List.foldlM_cons,
                  ParserState.feedProof.go, savePlacement, policyEq, decoded,
                  applied, bind,
                  Except.bind, Functor.map, Except.map, pure,
                  Except.pure] using execution
              let middleCore : RuntimeProofState :=
                { middle with ptp := initial.ptp }
              have headApplied :
                  ParserState.applyCompressedActions parser.db initial
                      headActions = .ok middleCore := by
                simpa [middleCore] using
                  (Metamath.PrefixTraceCompressed.applyCA_ptp_ok parser.db
                    { initial with ptp := .compressed phase }
                    headActions initial.ptp middle applied)
              have tailExecution' :
                  runCompressedTokenGo parser tokens
                      { middleCore with ptp := .compressed nextAccumulator } =
                    .ok final := by
                simpa [middleCore] using tailExecution
              obtain ⟨tailActions, finalPhase, result,
                tailDecoded, tailApplied, final_eq⟩ :=
                ih nextAccumulator middleCore final tailValid savePlacement
                  tailExecution'
              refine ⟨headActions ++ tailActions, finalPhase, result,
                ?_, ?_, final_eq⟩
              · simp [decodeCompressedTokens, decoded, tailDecoded,
                  bind, Except.bind, pure, Except.pure]
              · unfold ParserState.applyCompressedActions at headApplied tailApplied ⊢
                rw [List.foldlM_append, headApplied]
                exact tailApplied

/-- Type-valued packaging of `runCompressedTokenGo_reflect`, for composing
the reflected decoder and executor with source proof objects. -/
structure CompressedTokenGoReflection
    (parser : ParserState) (tokens : List ByteSlice)
    (phase : Metamath.Verify.CompressedPhase)
    (initial final : RuntimeProofState) : Type where
  actions : List ParserState.CompressedAction
  finalPhase : Metamath.Verify.CompressedPhase
  result : RuntimeProofState
  decoded : decodeCompressedTokens tokens phase =
    .ok (actions, finalPhase)
  applied : ParserState.applyCompressedActions parser.db initial actions =
    .ok result
  final_eq : final = { result with ptp := .compressed finalPhase }

noncomputable def compressedTokenGoReflection
    (parser : ParserState) (tokens : List ByteSlice)
    (phase : Metamath.Verify.CompressedPhase)
    (initial final : RuntimeProofState)
    (valid : ∀ token ∈ tokens,
      compressedWordValid (sliceBytes token) = true)
    (savePlacement : parser.db.config.compressedSavePlacement =
      .immediatelyAfterUse)
    (execution : runCompressedTokenGo parser tokens
      { initial with ptp := .compressed phase } = .ok final) :
    CompressedTokenGoReflection parser tokens phase initial final := by
  let witness := runCompressedTokenGo_reflect parser tokens phase
    initial final valid savePlacement execution
  let actions := Classical.choose witness
  let witness₁ := Classical.choose_spec witness
  let finalPhase := Classical.choose witness₁
  let witness₂ := Classical.choose_spec witness₁
  let result := Classical.choose witness₂
  let facts := Classical.choose_spec witness₂
  exact
    { actions := actions
      finalPhase := finalPhase
      result := result
      decoded := facts.1
      applied := facts.2.1
      final_eq := facts.2.2 }

/-- Source-level decoding and the shipped one-shot action execution recovered
from the actual body calls and a successful compressed finalization. -/
structure ReaderReflectedCompressedProgram
    (parser : ParserState) (initial : RuntimeProofState)
    (words : List (List UInt8)) (final : RuntimeProofState) : Type where
  actions : List CompressedAction
  runtimeFinal : RuntimeProofState
  decoded : decodeProgram words = some actions
  execution :
    ParserState.applyCompressedActions parser.db initial
      (actions.map toMMLean4Action) = .ok runtimeFinal
  finalPhase : Metamath.Verify.CompressedPhase
  finalPhaseComplete : finalPhase = .betweenSteps ∨
    finalPhase = .justCompletedStep
  final_eq : final = { runtimeFinal with ptp := .compressed finalPhase }

/-- Successful reflected compressed execution preserves the theorem formula
and mandatory frame. -/
theorem ReaderReflectedCompressedProgram.preservesCore
    {parser : ParserState} {initial final : RuntimeProofState}
    {words : List (List UInt8)}
    (program : ReaderReflectedCompressedProgram parser initial words final) :
    program.runtimeFinal.fmla = initial.fmla ∧
      program.runtimeFinal.frame = initial.frame :=
  Metamath.ParserOps.applyCompressedActions_ok_preserves_core parser.db
    initial program.runtimeFinal (program.actions.map toMMLean4Action)
      program.execution

/-- Successful reflected compressed execution also preserves the theorem
label carried by the proof state. -/
theorem ReaderReflectedCompressedProgram.preservesLabel
    {parser : ParserState} {initial final : RuntimeProofState}
    {words : List (List UInt8)}
    (program : ReaderReflectedCompressedProgram parser initial words final) :
    program.runtimeFinal.label = initial.label :=
  Metamath.PrefixTraceCompressed.applyCA_preserves_label parser.db initial
    (program.actions.map toMMLean4Action) program.runtimeFinal
      program.execution

/-- Stable, parser-independent indices for one accepted runtime compressed
program.  This prevents downstream records from repeatedly normalizing the
full byte-trace construction merely to recover its action execution. -/
structure RuntimeCompressedProgramEvidence
    (db : DB) (formula : ConstantHeadedFormula)
    (words : List (List UInt8)) : Type where
  initial : RuntimeProofState
  final : RuntimeProofState
  actions : List CompressedAction
  decoded : decodeProgram words = some actions
  execution :
    ParserState.applyCompressedActions db initial
      (actions.map toMMLean4Action) = .ok final
  finalStack : final.stack = #[formula.toRuntime]

/-- Forget parser-local indexing while retaining the exact decoded execution. -/
def ReaderReflectedCompressedProgram.toRuntimeEvidence
    {parser : ParserState} {initial bodyFinal : RuntimeProofState}
    {formula : ConstantHeadedFormula} {words : List (List UInt8)}
    (program : ReaderReflectedCompressedProgram parser initial words bodyFinal)
    (db : DB) (database_eq : parser.db = db)
    (finalStack : program.runtimeFinal.stack = #[formula.toRuntime]) :
    RuntimeCompressedProgramEvidence db formula words :=
  { initial := initial
    final := program.runtimeFinal
    actions := program.actions
    decoded := program.decoded
    execution := by
      rw [← database_eq]
      exact program.execution
    finalStack := finalStack }

/-- Complete-program reflection for the retained body.  Successful
`finishProof` supplies the otherwise-missing phase-completeness fact. -/
noncomputable def ReaderCompressedBody.reflectProgram
    {parser : ParserState} {db : DB} {initial : RuntimeProofState}
    {words : List (List UInt8)}
    {entries : List (LocatedToken × TokenCall)}
    {observed : ParserObservedState}
    (body : ReaderCompressedBody parser db
      { initial with ptp := .compressed .betweenSteps }
        words entries observed)
    (savePlacement : parser.db.config.compressedSavePlacement =
      .immediatelyAfterUse)
    (finishSuccess :
      (parser.finishProof body.after).db.error? = none) :
    ReaderReflectedCompressedProgram parser initial words body.after := by
  let tokens := entries.map (fun entry => entry.2.origin.token)
  have tokensValid : ∀ token ∈ tokens,
      compressedWordValid (sliceBytes token) = true := by
    intro token member
    have bytesMember : sliceBytes token ∈ tokens.map sliceBytes :=
      List.mem_map_of_mem member
    rw [body.bytes_eq] at bytesMember
    exact body.valid (sliceBytes token) bytesMember
  let reflected := compressedTokenGoReflection parser tokens .betweenSteps
    initial body.after tokensValid savePlacement
      (by simpa [tokens] using body.execution)
  have finishConditions :=
    Metamath.ParserAnyModeEquivalence.finishProof_success_stack_conditions
      parser body.after finishSuccess
  have finalPhaseComplete : reflected.finalPhase = .betweenSteps ∨
      reflected.finalPhase = .justCompletedStep := by
    rcases finishConditions.2.2 with normalMode |
        compressedBetween | compressedCompleted
    · rw [reflected.final_eq] at normalMode
      cases normalMode
    · left
      rw [reflected.final_eq] at compressedBetween
      exact ProofTokenParser.compressed.inj compressedBetween
    · right
      rw [reflected.final_eq] at compressedCompleted
      exact ProofTokenParser.compressed.inj compressedCompleted
  have implementationDecoded :
      decodeCompressedProgram tokens = .ok reflected.actions := by
    unfold decodeCompressedProgram
    rw [reflected.decoded]
    rcases finalPhaseComplete with finalPhase | finalPhase <;>
      simp [finalPhase]
  have decoderAgreement :
      (.ok reflected.actions : Except ProofCheckFail
        (List ParserState.CompressedAction)) =
        toMMLean4ProgramResult (decodeProgram words) := by
    calc
      (.ok reflected.actions : Except ProofCheckFail
          (List ParserState.CompressedAction)) =
          decodeCompressedProgram tokens := implementationDecoded.symm
      _ = toMMLean4ProgramResult
          (decodeProgram (tokens.map sliceBytes)) :=
        decodeCompressedProgram_mmLean4_agrees tokens
      _ = toMMLean4ProgramResult (decodeProgram words) := by
        rw [body.bytes_eq]
  cases sourceDecoded : decodeProgram words with
  | none =>
      simp [sourceDecoded, toMMLean4ProgramResult] at decoderAgreement
  | some sourceActions =>
      have actions_eq :
          reflected.actions = sourceActions.map toMMLean4Action := by
        simpa [sourceDecoded, toMMLean4ProgramResult] using decoderAgreement
      exact
        { actions := sourceActions
          runtimeFinal := reflected.result
          decoded := sourceDecoded
          execution := by
            rw [← actions_eq]
            exact reflected.applied
          finalPhase := reflected.finalPhase
          finalPhaseComplete
          final_eq := reflected.final_eq }

/-- Ordered preloading commutes with changing only the proof-token phase. -/
theorem preloadFold_withPtp
    (db : DB) (labels : List String) (before after : RuntimeProofState)
    (phase : ProofTokenParser)
    (execution : labels.foldlM (db.preload) before = .ok after) :
    labels.foldlM (db.preload) { before with ptp := phase } =
      .ok { after with ptp := phase } := by
  induction labels generalizing before with
  | nil =>
      simp only [List.foldlM_nil, pure, Except.pure] at execution ⊢
      cases execution
      rfl
  | cons label labels ih =>
      simp only [List.foldlM_cons, bind, Except.bind] at execution ⊢
      cases first : db.preload before label with
      | error error =>
          simp [first] at execution
      | ok middle =>
          have rest : labels.foldlM (db.preload) middle = .ok after := by
            simpa [first] using execution
          rw [preload_withPtp db before middle label phase first]
          exact ih middle rest

/-- Singleton-array extensionality used at the common proof-finality gate. -/
theorem array_eq_singleton_of_size_getElem
    {alpha : Type} (array : Array alpha) (value : alpha)
    (size_eq : array.size = 1) (value_eq : array[0]? = some value) :
    array = #[value] := by
  obtain ⟨index, element_eq⟩ := Array.getElem_of_getElem? value_eq
  apply Array.ext'
  have length_eq : array.toList.length = 1 := by
    rwa [Array.length_toList]
  rw [List.eq_getElem_of_length_eq_one array.toList length_eq]
  simp
  exact element_eq

/-- A compressed body is proof-producing when it decodes and every decoded
action is executable proof evidence.  Decode success is carried explicitly,
so malformed programs cannot satisfy this predicate vacuously. -/
structure VerifiedCompressedWords (words : List (List UInt8)) : Type where
  actions : List CompressedAction
  decoded : decodeProgram words = some actions
  verified : actionsVerified actions

/-- A compressed body is incomplete when it decodes and contains the explicit
unknown action.  This admits the source statement without manufacturing a
proof DAG. -/
structure IncompleteCompressedWords (words : List (List UInt8)) : Type where
  actions : List CompressedAction
  decoded : decodeProgram words = some actions
  unknown_mem : .unknown ∈ actions

def verifiedCompressedWords_single_step :
    VerifiedCompressedWords [[65]] := by
  exact ⟨[.step 0], decode_single_index, by simp [actionsVerified]⟩

/-- Negative calibration: `?` is accepted by the decoder but cannot inhabit
the proof-producing compressed judgment. -/
theorem not_verifiedCompressedWords_unknown :
    ¬ Nonempty (VerifiedCompressedWords [[63]]) := by
  rintro ⟨⟨actions, decoded, verified⟩⟩
  have actions_eq : actions = [.unknown] :=
    Option.some.inj (decoded.symm.trans decode_unknown_is_explicit)
  subst actions
  exact verified .unknown (by simp) rfl

def incompleteCompressedWords_unknown :
    IncompleteCompressedWords [[63]] :=
  ⟨[.unknown], decode_unknown_is_explicit, by simp⟩

theorem not_incompleteCompressedWords_single_step :
    ¬ Nonempty (IncompleteCompressedWords [[65]]) := by
  rintro ⟨⟨actions, decoded, unknown_mem⟩⟩
  have actions_eq : actions = [.step 0] :=
    Option.some.inj (decoded.symm.trans decode_single_index)
  subst actions
  simp at unknown_mem

/-- Every successfully decoded compressed body is classified, and the class
is decided solely by the presence of the explicit unknown action. -/
def decodedCompressedWords_verifiedOrIncomplete
    {words : List (List UInt8)} {actions : List CompressedAction}
    (decoded : decodeProgram words = some actions) :
    VerifiedCompressedWords words ⊕ IncompleteCompressedWords words :=
  if unknown_mem : .unknown ∈ actions then
    .inr ⟨actions, decoded, unknown_mem⟩
  else
    .inl
      { actions := actions
        decoded := decoded
        verified := by
          intro action member
          cases action with
          | step index => simp
          | save => simp
          | unknown => exact (unknown_mem member).elim }

theorem verifiedCompressedWords_not_incomplete
    {words : List (List UInt8)}
    (verified : VerifiedCompressedWords words)
    (incomplete : IncompleteCompressedWords words) : False := by
  have actions_eq : verified.actions = incomplete.actions :=
    Option.some.inj (verified.decoded.symm.trans incomplete.decoded)
  have unknown_mem : .unknown ∈ verified.actions := by
    simpa [actions_eq] using incomplete.unknown_mem
  exact verified.verified .unknown unknown_mem rfl

/-- Negative decode boundary: an unterminated numeric index is neither a
verified proof nor an admitted incomplete proof. -/
theorem invalidCompressedWords_neither :
    ¬ Nonempty (VerifiedCompressedWords [[85]]) ∧
      ¬ Nonempty (IncompleteCompressedWords [[85]]) := by
  constructor
  · rintro ⟨⟨actions, decoded, verified⟩⟩
    rw [decode_incomplete_index_rejected] at decoded
    exact nomatch decoded
  · rintro ⟨⟨actions, decoded, unknown_mem⟩⟩
    rw [decode_incomplete_index_rejected] at decoded
    exact nomatch decoded

/-- Result of one verified compressed theorem statement at its actual reader
boundary.  The source proof DAG and the next source/runtime prefix are
constructed together. -/
structure ReaderVerifiedCompressedStatement
    (before after : SourceState) (label : String)
    (formula : ConstantHeadedFormula)
    (header : List String) (words : List (List UInt8))
    (final : ParserObservedState) : Type where
  step : CompressedTheoremStep before after label formula header words
  nextPrefix : SourceParserPrefixAgrees after final

/-- Runtime evidence common to verified and incomplete compressed statements.
It is reconstructed from the actual reader trace and contains the exact
decoded program, header/action executions, final singleton stack, and next
database prefix. -/
structure ReaderAcceptedCompressedStatement
    (db : DB) (before after : SourceState) (label : String)
    (formula : ConstantHeadedFormula)
    (header : List String) (words : List (List UInt8))
    (final : ParserObservedState) : Type where
  inserted : insertAssertion? before label formula = some after
  projectEq : projectPrefix? db =
    some (runtimePrefix before).toProjection
  runtimeBase : RuntimeProofState
  program : RuntimeCompressedProgramEvidence db formula words
  headerExecution :
    (((headerItems before formula header).map headerRuntimeLabel).foldlM
      (fun state name => db.preload state name)
      { runtimeBase with heap := #[], stack := #[] }) =
        .ok program.initial
  nextPrefix : SourceParserPrefixAgrees after final

/-- An exact spelling-indexed compressed theorem statement reconstructs the
runtime evidence shared by its verified and incomplete outcomes. -/
noncomputable def SpelledCallTrace.acceptedCompressedStatement
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
      ⟨typecode.name, bodySymbols⟩ = some after) :
    ReaderAcceptedCompressedStatement db before after label.name
      ⟨typecode.name, bodySymbols⟩
      (header.map LocatedName.name) (words.map (fun word => word.bytes))
      final := by
  let formula : ConstantHeadedFormula :=
    ⟨typecode.name, bodySymbols⟩
  let formulaPrefix : List String :=
    label.name :: "$p" ::
      (typecode :: body).map LocatedName.name ++ ["$="]
  let compressedTexts : List String :=
    ["("] ++ header.map LocatedName.name ++ [")"] ++
      words.map (fun word => tokenText word.bytes) ++ ["$."]
  have trace' : SpelledCallTrace fileId ⟨db, .start⟩
      (formulaPrefix ++ compressedTexts) entries final := by
    simpa [formulaPrefix, compressedTexts, List.append_assoc] using trace
  obtain ⟨proofInitial, formulaTrace, compressedTrace⟩ :=
    trace'.splitAppend
  have formulaTrace' : SpelledCallTrace fileId ⟨db, .start⟩
      (label.name :: "$p" ::
        (typecode :: body).map LocatedName.name ++ ["$="])
      (entries.take formulaPrefix.length) proofInitial := by
    simpa [formulaPrefix] using formulaTrace
  let anchored := formulaTrace'.provableFormulaAnchorCore agreement
    (insertAssertion?_valid_before inserted)
    labelCharset typecodeCharset bodyCharsets taggedFormula
  let labelPos := anchored.1
  let anchor := anchored.2
  have compressedTrace' : SpelledCallTrace fileId proofInitial
      compressedTexts (entries.drop formulaPrefix.length) final := by
    simpa using compressedTrace
  let afterOpenTexts : List String :=
    header.map LocatedName.name ++ [")"] ++
      words.map (fun word => tokenText word.bytes) ++ ["$."]
  have compressedTrace'' : SpelledCallTrace fileId proofInitial
      (["("] ++ afterOpenTexts) (entries.drop formulaPrefix.length) final := by
    simpa [compressedTexts, afterOpenTexts, List.append_assoc] using
      compressedTrace'
  obtain ⟨afterOpen, openTrace, afterOpenTrace⟩ :=
    compressedTrace''.splitAppend
  let opened := openTrace.compressedOpen anchor
  have afterOpenTrace' := afterOpenTrace.reindexInitial opened.final_observed
  let afterHeaderTexts : List String :=
    [")"] ++ words.map (fun word => tokenText word.bytes) ++ ["$."]
  have afterOpenTrace'' : SpelledCallTrace fileId
      ⟨db, .proof { opened.mandatory with ptp := .preload }⟩
      (header.map LocatedName.name ++ afterHeaderTexts)
      ((entries.drop formulaPrefix.length).drop 1) final := by
    simpa [afterOpenTexts, afterHeaderTexts, List.append_assoc] using
      afterOpenTrace'
  obtain ⟨afterHeader, headerTrace, afterHeaderTrace⟩ :=
    afterOpenTrace''.splitAppend
  let loaded := headerTrace.compressedHeader anchor.state
    anchor.database_eq rfl headerCharsets
  have afterHeaderTrace' :=
    afterHeaderTrace.reindexInitial loaded.final_observed
  let afterCloseTexts : List String :=
    words.map (fun word => tokenText word.bytes) ++ ["$."]
  have afterHeaderTrace'' : SpelledCallTrace fileId
      ⟨db, .proof loaded.after⟩
      ([")"] ++ afterCloseTexts)
      (((entries.drop formulaPrefix.length).drop 1).drop header.length)
      final := by
    simpa [afterHeaderTexts, afterCloseTexts, List.append_assoc] using
      afterHeaderTrace'
  obtain ⟨afterClose, closeTrace, afterCloseTrace⟩ :=
    afterHeaderTrace''.splitAppend
  have closed := closeTrace.compressedClose_final anchor.state
    anchor.database_eq loaded.after_preload
  have afterCloseTrace' := afterCloseTrace.reindexInitial closed
  have afterCloseTrace'' : SpelledCallTrace fileId
      ⟨db, .proof { loaded.after with ptp := .compressed .betweenSteps }⟩
      (words.map (fun word => tokenText word.bytes) ++ ["$."])
      ((((entries.drop formulaPrefix.length).drop 1).drop header.length).drop 1)
      final := by
    simpa [afterCloseTexts] using afterCloseTrace'
  obtain ⟨afterBody, bodyTrace, finishTrace⟩ :=
    afterCloseTrace''.splitAppend
  let bodyRun := bodyTrace.compressedBody anchor.state
    anchor.database_eq wordCharsets
  have finishTrace' := finishTrace.reindexInitial bodyRun.final_observed
  have finishTrace'' : SpelledCallTrace fileId
      ⟨db, .proof bodyRun.after⟩ ["$."]
      (((((entries.drop formulaPrefix.length).drop 1).drop header.length).drop 1)
        |>.drop words.length) final := by
    simpa using finishTrace'
  let finished := finishTrace''.proofFinish anchor.state anchor.database_eq
  have anchorSavePlacement :
      anchor.state.db.config.compressedSavePlacement =
        .immediatelyAfterUse := by
    rw [anchor.database_eq]
    exact savePlacement
  let program := bodyRun.reflectProgram anchorSavePlacement
    finished.finish_success

  have projectEq :
      projectPrefix? db = some (runtimePrefix before).toProjection :=
    agreement.projectPrefix_eq
  have mandatoryTrim := trimFrame'_eq_mandatory agreement formula
    (mandatory_covered_of_insert inserted)
  have frameEq : anchor.frame = (mandatoryFrame before formula).toRuntime :=
    Except.ok.inj (anchor.trim.symm.trans mandatoryTrim)
  let sourceStart :=
    sourceProofStart db labelPos label.name before formula
  have startEq :
      db.mkProofState labelPos label.name formula.toRuntime anchor.frame =
        sourceStart := by
    simp [sourceStart, sourceProofStart, frameEq,
      Metamath.Verify.DB.mkProofState]
  have bulkMandatory :
      db.preloadMandatoryHyps sourceStart = .ok opened.mandatory := by
    rw [← startEq]
    exact opened.mandatoryExecution
  let mandatoryLabels :=
    (mandatoryHypotheses before formula).map HypothesisView.label
  have mandatoryLabels_eq_frame :
      mandatoryLabels = sourceStart.frame.hyps.toList := by
    simp [mandatoryLabels, sourceStart, sourceProofStart, mandatoryFrame,
      SourceFrame.toRuntime, Metamath.Verify.DB.mkProofState]
  have mandatoryExecution :
      mandatoryLabels.foldlM (db.preload) sourceStart =
        .ok opened.mandatory := by
    calc
      mandatoryLabels.foldlM (db.preload) sourceStart =
          mandatoryLabels.foldlM (mandatoryPreloadStep db) sourceStart :=
        (mandatoryPreloadFold_eq_preloadFold_runtimePrefix db before formula
          sourceStart
          projectEq).symm
      _ = sourceStart.frame.hyps.toList.foldlM
          (mandatoryPreloadStep db) sourceStart := by
        rw [← mandatoryLabels_eq_frame]
      _ = sourceStart.frame.hyps.foldlM
          (mandatoryPreloadStep db) sourceStart :=
        Array.foldlM_toList
      _ = db.preloadMandatoryHyps sourceStart :=
        (preloadMandatoryHyps_eq_mandatoryFold db sourceStart).symm
      _ = .ok opened.mandatory := bulkMandatory
  let runtimeBase : RuntimeProofState :=
    { sourceStart with ptp := .preload }
  have mandatoryPhaseExecution :
      mandatoryLabels.foldlM (db.preload) runtimeBase =
        .ok { opened.mandatory with ptp := .preload } := by
    simpa [runtimeBase] using preloadFold_withPtp db mandatoryLabels
      sourceStart opened.mandatory .preload mandatoryExecution
  have combinedHeaderExecution :
      (mandatoryLabels ++ header.map LocatedName.name).foldlM
          (db.preload) runtimeBase = .ok loaded.after := by
    rw [List.foldlM_append, mandatoryPhaseExecution]
    exact loaded.execution
  have runtimeBase_empty :
      { runtimeBase with heap := #[], stack := #[] } = runtimeBase := by
    rfl
  have headerLabels_eq :
      (headerItems before formula (header.map LocatedName.name)).map
          headerRuntimeLabel =
        mandatoryLabels ++ header.map LocatedName.name := by
    unfold headerItems
    rw [List.map_append, List.map_map, List.map_map]
    simp [Function.comp_def, headerRuntimeLabel, mandatoryLabels]
  have fullHeaderExecution :
      (((headerItems before formula (header.map LocatedName.name)).map
          headerRuntimeLabel).foldlM
        (fun state name => db.preload state name)
        { runtimeBase with heap := #[], stack := #[] }) =
          .ok loaded.after := by
    rw [headerLabels_eq, runtimeBase_empty]
    exact combinedHeaderExecution
  have headerIdentity := preloadFold_preserves_identity db
    (mandatoryLabels ++ header.map LocatedName.name) runtimeBase loaded.after
      combinedHeaderExecution
  have actionIdentity := program.preservesCore
  have runtimeFinalFormula : program.runtimeFinal.fmla = formula.toRuntime := by
    exact actionIdentity.1.trans (headerIdentity.2.1.trans (by rfl))
  have runtimeFinalFrame : program.runtimeFinal.frame =
      (mandatoryFrame before formula).toRuntime := by
    exact actionIdentity.2.trans (headerIdentity.2.2.trans (by rfl))
  have runtimeFinalLabel : program.runtimeFinal.label = label.name := by
    have actionLabel := program.preservesLabel
    exact actionLabel.trans (headerIdentity.1.trans (by rfl))
  have finishConditions :=
    Metamath.ParserAnyModeEquivalence.finishProof_success_stack_conditions
      anchor.state bodyRun.after finished.finish_success
  have bodyStack : bodyRun.after.stack = #[bodyRun.after.fmla] :=
    array_eq_singleton_of_size_getElem bodyRun.after.stack
      bodyRun.after.fmla finishConditions.1 finishConditions.2.1
  have runtimeFinalStack :
      program.runtimeFinal.stack = #[formula.toRuntime] := by
    have stackEq := congrArg
      (fun state : RuntimeProofState => state.stack) program.final_eq
    have formulaEq := congrArg
      (fun state : RuntimeProofState => state.fmla) program.final_eq
    calc
      program.runtimeFinal.stack = bodyRun.after.stack := by
        simpa using stackEq.symm
      _ = #[bodyRun.after.fmla] := bodyStack
      _ = #[program.runtimeFinal.fmla] := by
        rw [show bodyRun.after.fmla = program.runtimeFinal.fmla by
          simpa using formulaEq]
      _ = #[formula.toRuntime] := by rw [runtimeFinalFormula]
  have bodyLabel : bodyRun.after.label = label.name := by
    rw [program.final_eq]
    exact runtimeFinalLabel
  have bodyFormula : bodyRun.after.fmla = formula.toRuntime := by
    rw [program.final_eq]
    exact runtimeFinalFormula
  have bodyFrame : bodyRun.after.frame =
      (mandatoryFrame before formula).toRuntime := by
    rw [program.final_eq]
    exact runtimeFinalFrame
  have finishInsert := Metamath.ParserOps.finishProof_success_insert
    anchor.state bodyRun.after finished.finish_success
  have finishDB :
      (anchor.state.finishProof bodyRun.after).db =
        (db.insert bodyRun.after.pos label.name
          (.assert formula.toRuntime
            (mandatoryFrame before formula).toRuntime)).recordIncomplete
              bodyRun.after.incomplete label.name := by
    calc
      (anchor.state.finishProof bodyRun.after).db =
          (anchor.state.db.insert bodyRun.after.pos bodyRun.after.label
            (.assert bodyRun.after.fmla bodyRun.after.frame)).recordIncomplete
              bodyRun.after.incomplete bodyRun.after.label := finishInsert.1
      _ = (db.insert bodyRun.after.pos label.name
          (.assert formula.toRuntime
            (mandatoryFrame before formula).toRuntime)).recordIncomplete
              bodyRun.after.incomplete label.name := by
        rw [anchor.database_eq, bodyLabel, bodyFormula, bodyFrame]
  have nextAgreement := RuntimeDBAgrees.insertAssertion agreement inserted
    bodyRun.after.pos
  have recordedAgreement := nextAgreement.recordIncomplete
    bodyRun.after.incomplete label.name
  let runtimeProgram := program.toRuntimeEvidence db anchor.database_eq
    runtimeFinalStack
  refine
    { inserted := inserted
      projectEq := projectEq
      runtimeBase := runtimeBase
      program := runtimeProgram
      headerExecution := by
        simpa [runtimeProgram,
          ReaderReflectedCompressedProgram.toRuntimeEvidence] using
          fullHeaderExecution
      nextPrefix := ?_ }
  rw [finished.final_observed]
  refine
    { mode_eq := rfl
      database := ?_
      interrupt_eq := ?_ }
  rw [finishDB]
  exact recordedAgreement
  rw [finishDB]
  simpa using
    (runtimeInsert_interrupt db bodyRun.after.pos label.name _).trans
      interruptEq

/-- Promote common reader acceptance to proof-producing acceptance only after
the decoded words supply a non-vacuous verified-program witness. -/
noncomputable def ReaderAcceptedCompressedStatement.toVerified
    {db : DB} {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {header : List String} {words : List (List UInt8)}
    {final : ParserObservedState}
    (accepted : ReaderAcceptedCompressedStatement db before after label
      formula header words final)
    (verifiedWords : VerifiedCompressedWords words)
    (runtimeTarget sourceTarget : ValidatedPresentation)
    (runtimePresentation :
      presentationOfSourcePrefix? (runtimePrefix before) =
        some runtimeTarget.1)
    (sourcePresentation :
      presentationOfSourcePrefix? before.toSourcePrefix =
        some sourceTarget.1) :
    ReaderVerifiedCompressedStatement before after label formula header words
      final := by
  have actions_eq : accepted.program.actions = verifiedWords.actions :=
    Option.some.inj
      (accepted.program.decoded.symm.trans verifiedWords.decoded)
  have actions_verified : actionsVerified accepted.program.actions := by
    rw [actions_eq]
    exact verifiedWords.verified
  let step := compressedTheoremStep_of_runtimePrefix runtimeTarget
    sourceTarget (insertAssertion?_valid_before accepted.inserted)
      runtimePresentation sourcePresentation accepted.inserted
      accepted.program.decoded actions_verified db accepted.projectEq
      accepted.runtimeBase accepted.headerExecution
      accepted.program.execution accepted.program.finalStack
  exact ⟨step, accepted.nextPrefix⟩

/-- Accepted-but-incomplete compressed theorem statement.  It advances the
database exactly as the shipped reader does, while retaining an explicit
unknown action and exposing no proof DAG. -/
structure ReaderIncompleteCompressedStatement
    (before after : SourceState) (label : String)
    (formula : ConstantHeadedFormula)
    (header : List String) (words : List (List UInt8))
    (final : ParserObservedState) : Type where
  actions : List CompressedAction
  decoded : decodeProgram words = some actions
  unknown_mem : .unknown ∈ actions
  inserted : insertAssertion? before label formula = some after
  nextPrefix : SourceParserPrefixAgrees after final

theorem ReaderIncompleteCompressedStatement.final_mode_eq
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {header : List String} {words : List (List UInt8)}
    {final : ParserObservedState}
    (result : ReaderIncompleteCompressedStatement before after label formula
      header words final) :
    final.mode = .start :=
  result.nextPrefix.mode_eq

/-- An incomplete accepted occurrence cannot also inhabit the verified
compressed theorem judgment for the same words. -/
theorem ReaderIncompleteCompressedStatement.noTheoremStep
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {header : List String} {words : List (List UInt8)}
    {final : ParserObservedState}
    (result : ReaderIncompleteCompressedStatement before after label formula
      header words final) :
    ¬ Nonempty
      (CompressedTheoremStep before after label formula header words) := by
  rintro ⟨step⟩
  have actions_eq : step.actions = result.actions :=
    Option.some.inj (step.decoded.symm.trans result.decoded)
  have unknown_mem : .unknown ∈ step.actions := by
    simpa [actions_eq] using result.unknown_mem
  exact step.actions_complete .unknown unknown_mem rfl

/-- Project common reader acceptance to the incomplete outcome. -/
def ReaderAcceptedCompressedStatement.toIncomplete
    {db : DB} {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {header : List String} {words : List (List UInt8)}
    {final : ParserObservedState}
    (accepted : ReaderAcceptedCompressedStatement db before after label
      formula header words final)
    (incompleteWords : IncompleteCompressedWords words) :
    ReaderIncompleteCompressedStatement before after label formula header
      words final := by
  have actions_eq : accepted.program.actions = incompleteWords.actions :=
    Option.some.inj
      (accepted.program.decoded.symm.trans incompleteWords.decoded)
  exact
    { actions := accepted.program.actions
      decoded := accepted.program.decoded
      unknown_mem := by simpa [actions_eq] using incompleteWords.unknown_mem
      inserted := accepted.inserted
      nextPrefix := accepted.nextPrefix }

/-- Direct proof-producing interface from an exact reader trace. -/
noncomputable def SpelledCallTrace.verifiedCompressedStatement
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
    (bodyCharsets : ∀ name ∈ body, NameCharset mathBytesValid name)
    (headerCharsets :
      ∀ name ∈ header, NameCharset labelBytesValid name)
    (wordCharsets :
      ∀ word ∈ words, compressedWordValid word.bytes = true)
    (verifiedWords : VerifiedCompressedWords
      (words.map (fun word => word.bytes)))
    (taggedFormula : tagBody before (typecode :: body) =
      .ok (.const typecode.name :: bodySymbols))
    (inserted : insertAssertion? before label.name
      ⟨typecode.name, bodySymbols⟩ = some after)
    (runtimeTarget sourceTarget : ValidatedPresentation)
    (runtimePresentation :
      presentationOfSourcePrefix? (runtimePrefix before) =
        some runtimeTarget.1)
    (sourcePresentation :
      presentationOfSourcePrefix? before.toSourcePrefix =
        some sourceTarget.1) :
    ReaderVerifiedCompressedStatement before after label.name
      ⟨typecode.name, bodySymbols⟩
      (header.map LocatedName.name) (words.map (fun word => word.bytes))
      final :=
  (trace.acceptedCompressedStatement agreement interruptEq savePlacement
    labelCharset typecodeCharset
    bodyCharsets headerCharsets wordCharsets taggedFormula inserted).toVerified
      verifiedWords runtimeTarget sourceTarget runtimePresentation
        sourcePresentation

/-- Direct incomplete-admission interface from an exact reader trace. -/
noncomputable def SpelledCallTrace.incompleteCompressedStatement
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
    (bodyCharsets : ∀ name ∈ body, NameCharset mathBytesValid name)
    (headerCharsets :
      ∀ name ∈ header, NameCharset labelBytesValid name)
    (wordCharsets :
      ∀ word ∈ words, compressedWordValid word.bytes = true)
    (incompleteWords : IncompleteCompressedWords
      (words.map (fun word => word.bytes)))
    (taggedFormula : tagBody before (typecode :: body) =
      .ok (.const typecode.name :: bodySymbols))
    (inserted : insertAssertion? before label.name
      ⟨typecode.name, bodySymbols⟩ = some after) :
    ReaderIncompleteCompressedStatement before after label.name
      ⟨typecode.name, bodySymbols⟩
      (header.map LocatedName.name) (words.map (fun word => word.bytes))
      final :=
  (trace.acceptedCompressedStatement agreement interruptEq savePlacement
    labelCharset typecodeCharset
    bodyCharsets headerCharsets wordCharsets taggedFormula inserted).toIncomplete
      incompleteWords

/-- The label, `$p`, tagged formula, and `$=` prefix of an accepted theorem
statement constructs the actual shipped proof-state anchor over exactly the
same source/runtime database.  Proof-body calls begin only after this
boundary. -/
noncomputable def SpelledCallTrace.provableFormula_parserAnchor
    {fileId : String} {source : SourceState} {db : DB}
    {label typecode : LocatedName} {body : List LocatedName}
    {bodySymbols : List Sym}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId ⟨db, .start⟩
      (label.name :: "$p" ::
        (typecode :: body).map LocatedName.name ++ ["$="])
      entries final)
    (agreement : RuntimeDBAgrees db source)
    (sourceValid : sourceStateValid source = true)
    (labelCharset : NameCharset labelBytesValid label)
    (typecodeCharset : NameCharset mathBytesValid typecode)
    (bodyCharsets :
      ∀ name ∈ body, NameCharset mathBytesValid name)
    (taggedFormula : tagBody source (typecode :: body) =
      .ok (.const typecode.name :: bodySymbols)) :
    Σ labelPos : Pos,
      ParserProofAnchor db
        (ConstantHeadedFormula.toRuntime ⟨typecode.name, bodySymbols⟩)
        labelPos label.name final :=
  trace.provableFormulaAnchorCore agreement sourceValid labelCharset
    typecodeCharset bodyCharsets taggedFormula

/-- Proposition-valued projection of `provableFormula_parserAnchor`. -/
theorem SpelledCallTrace.provableFormula_anchor
    {fileId : String} {source : SourceState} {db : DB}
    {label typecode : LocatedName} {body : List LocatedName}
    {bodySymbols : List Sym}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId ⟨db, .start⟩
      (label.name :: "$p" ::
        (typecode :: body).map LocatedName.name ++ ["$="])
      entries final)
    (agreement : RuntimeDBAgrees db source)
    (sourceValid : sourceStateValid source = true)
    (labelCharset : NameCharset labelBytesValid label)
    (typecodeCharset : NameCharset mathBytesValid typecode)
    (bodyCharsets :
      ∀ name ∈ body, NameCharset mathBytesValid name)
    (taggedFormula : tagBody source (typecode :: body) =
      .ok (.const typecode.name :: bodySymbols)) :
    ∃ (labelPos : Pos) (frame : RuntimeFrame),
      db.trimFrame'
          (ConstantHeadedFormula.toRuntime
            ⟨typecode.name, bodySymbols⟩) = .ok frame ∧
        final = ⟨db, .proof
          (db.mkProofState labelPos label.name
            (ConstantHeadedFormula.toRuntime
              ⟨typecode.name, bodySymbols⟩) frame)⟩ := by
  let result := trace.provableFormula_parserAnchor agreement sourceValid
    labelCharset typecodeCharset bodyCharsets taggedFormula
  let anchor := result.2
  refine ⟨result.1, anchor.frame, anchor.trim, ?_⟩
  calc
    final = parserObservedState anchor.state := anchor.observed_eq.symm
    _ = ⟨db, .proof
          (db.mkProofState result.1 label.name
            (ConstantHeadedFormula.toRuntime
              ⟨typecode.name, bodySymbols⟩) anchor.frame)⟩ := by
      simp only [parserObservedState, observedSemanticState,
        parserSemanticState]
      rw [anchor.database_eq, anchor.mode_eq]
      rfl

/-- Text conservation upgrades a located chronology to the spelling-indexed
form without changing any call or state. -/
noncomputable def LocatedSignificantCallTrace.toSpelledCallTrace
    {fileId : String} {initial final : ParserObservedState}
    {entries : List (LocatedToken × TokenCall)}
    (texts : List String)
    (trace : LocatedSignificantCallTrace fileId initial entries final)
    (text_eq : texts =
      entries.map (fun entry => tokenText entry.1.bytes)) :
    SpelledCallTrace fileId initial texts entries final := by
  induction trace generalizing texts with
  | nil state =>
      simp at text_eq
      subst texts
      exact .nil _
  | @cons initial final entries entry significant after_errorFree
      before_eq tail ih =>
      cases texts with
      | nil => simp at text_eq
      | cons text texts =>
          simp only [List.map_cons, List.cons.injEq] at text_eq
          exact .cons text entry text_eq.1.symm significant
            after_errorFree before_eq (ih texts text_eq.2)

theorem proofPayload_tokenStrings_length_eq_tokenSpans
    (proof : ProofPayload) :
    (SourceGSLTDerivationCorrespondence.ProofPayload.tokenStrings
      proof).length = proof.tokenSpans.length := by
  cases proof <;>
    simp [SourceGSLTDerivationCorrespondence.ProofPayload.tokenStrings,
      ProofPayload.tokenSpans]

theorem rawStatement_tokenStrings_length_eq_tokenSpans
    (statement : RawStatement) :
    (SourceGSLTDerivationCorrespondence.RawStatement.tokenStrings
      statement).length = statement.tokenSpans.length := by
  cases statement <;>
    simp [SourceGSLTDerivationCorrespondence.RawStatement.tokenStrings,
      RawStatement.tokenSpans,
      proofPayload_tokenStrings_length_eq_tokenSpans]

/-- Statement grouping of located calls.  Each group retains both exact span
and exact token text agreement with its authored statement witness. -/
inductive LocatedStatementCallTrace (fileId : String) :
    ParserObservedState → List RawStatement →
      List (LocatedToken × TokenCall) → ParserObservedState → Type where
  | nil (state : ParserObservedState) :
      LocatedStatementCallTrace fileId state [] [] state
  | cons {initial middle final : ParserObservedState}
      {statements : List RawStatement}
      {statementEntries restEntries : List (LocatedToken × TokenCall)}
      (statement : RawStatement)
      (charsets : StatementCharsets statement)
      (span_eq : RawStatement.tokenSpans statement =
        statementEntries.map (fun entry => entry.1.span))
      (tokenText_eq : RawStatement.tokenStrings statement =
        statementEntries.map (fun entry => tokenText entry.1.bytes))
      (statementTrace : LocatedSignificantCallTrace fileId initial
        statementEntries middle)
      (tail : LocatedStatementCallTrace fileId middle statements restEntries final) :
      LocatedStatementCallTrace fileId initial (statement :: statements)
        (statementEntries ++ restEntries) final

/-- Exact span and text conservation uniquely partition a located chronology
at statement boundaries. -/
noncomputable def LocatedSignificantCallTrace.toLocatedStatementCallTrace :
    {fileId : String} →
    {initial final : ParserObservedState} →
    {entries : List (LocatedToken × TokenCall)} →
    (statements : List RawStatement) →
    (trace : LocatedSignificantCallTrace fileId initial entries final) →
    (charsets : ∀ statement ∈ statements,
      StatementCharsets statement) →
    statements.flatMap RawStatement.tokenSpans =
      entries.map (fun entry => entry.1.span) →
    statements.flatMap RawStatement.tokenStrings =
      entries.map (fun entry => tokenText entry.1.bytes) →
    LocatedStatementCallTrace fileId initial statements entries final
  | _, _, _, entries, [], trace, _, span_eq, _ => by
      cases entries with
      | nil =>
          cases trace
          exact .nil _
      | cons entry rest => simp at span_eq
  | _, initial, final, entries, statement :: statements, trace, charsets,
      span_eq, tokenText_eq => by
      let count := statement.tokenSpans.length
      let statementEntries := entries.take count
      let restEntries := entries.drop count
      obtain ⟨middle, statementTrace, restTrace⟩ := trace.splitAt count
      have statementSpans :
          statement.tokenSpans =
            statementEntries.map (fun entry => entry.1.span) := by
        have taken := congrArg (List.take count) span_eq
        simpa [count, statementEntries] using taken
      have restSpans :
          statements.flatMap RawStatement.tokenSpans =
            restEntries.map (fun entry => entry.1.span) := by
        have dropped := congrArg (List.drop count) span_eq
        simpa [count, restEntries] using dropped
      have statementText :
          RawStatement.tokenStrings statement =
            statementEntries.map
              (fun entry => tokenText entry.1.bytes) := by
        have taken := congrArg (List.take count) tokenText_eq
        simpa [count, statementEntries,
          rawStatement_tokenStrings_length_eq_tokenSpans] using taken
      have restText :
          statements.flatMap RawStatement.tokenStrings =
            restEntries.map (fun entry => tokenText entry.1.bytes) := by
        have dropped := congrArg (List.drop count) tokenText_eq
        simpa [count, restEntries,
          rawStatement_tokenStrings_length_eq_tokenSpans] using dropped
      have tail := restTrace.toLocatedStatementCallTrace statements
        (fun next member => charsets next (List.Mem.tail _ member))
        restSpans restText
      simpa [statementEntries, restEntries, count] using
        LocatedStatementCallTrace.cons statement
          (charsets statement (List.Mem.head _)) statementSpans
          statementText statementTrace tail

/-- **Byte-preserving monolithic statement-prefix chronology.**  A successful
reader run, comment pass, and source segmentation construct the grouping of
the shipped calls by authored statement, retaining exact bytes, spans, and
observed prefix states. -/
noncomputable def monolithicLocatedStatementCallTrace
    (fileId : String) (bytes : ByteArray)
    (errorFree : (checkBytesLogged bytes).db.error? = none)
    {openSite : LocatedByteSpan} {output : List LocatedByteSpan}
    {statements : List RawStatement}
    (stripped : stripComments bytes.data.toList
      (tokenizeIncrementally fileId bytes) false openSite = .ok output)
    (segmented : segmentStatements (output.map (locatedSpan bytes)) =
      .ok statements) :
    Σ finalMode : TokenParser,
      LocatedStatementCallTrace fileId
        (parserObservedState (initialState {})) statements
        ((checkBytesLogged bytes).calls.filterMap
          (significantLocatedEntry? fileId))
        ⟨(checkBytesLogged bytes).db, logicalTokenMode finalMode⟩ := by
  let callsTrace := loggedLocatedSignificantCallTrace fileId bytes errorFree
  have locatedTokens_eq :
      ((checkBytesLogged bytes).calls.filterMap
          (significantLocatedEntry? fileId)).map Prod.fst =
        output.map (locatedSpan bytes) := by
    rw [significantLocatedEntries_fst]
    exact checkBytesLogged_significantLocatedCalls_eq_stripComments
      fileId bytes {} errorFree stripped
  have span_eq :
      statements.flatMap RawStatement.tokenSpans =
        ((checkBytesLogged bytes).calls.filterMap
          (significantLocatedEntry? fileId)).map
            (fun entry => entry.1.span) := by
    rw [segmentStatements_tokenSpans segmented]
    simpa [List.map_map, Function.comp_def] using
      congrArg (List.map LocatedToken.span) locatedTokens_eq.symm
  have tokenText_eq :
      statements.flatMap RawStatement.tokenStrings =
        ((checkBytesLogged bytes).calls.filterMap
          (significantLocatedEntry? fileId)).map
            (fun entry => tokenText entry.1.bytes) := by
    rw [segmentStatements_tokenStrings segmented]
    simpa [List.map_map, Function.comp_def] using
      congrArg (List.map (fun token : LocatedToken => tokenText token.bytes))
        locatedTokens_eq.symm
  exact ⟨callsTrace.1,
    callsTrace.2.toLocatedStatementCallTrace statements
      (segmentStatements_charsets segmented) span_eq
      tokenText_eq⟩

end Mettapedia.Languages.Metamath.SourceGSLTParserPrefixBisimulation
