import Mettapedia.Languages.Metamath.SourceGSLTParserPrefixBisimulation

/-!
# Ordinary Metamath statement transitions in the shipped reader

This module relates complete non-proof statement call groups to the source
state operations they implement.  Token positions remain available for
diagnostics while successful database insertion is compared through its
position-independent semantic result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.SourceGSLTParserPrefixBisimulation

open Metamath.Verify
open Mettapedia.Languages.Metamath.InferenceOneShotByteLog
open Mettapedia.Languages.Metamath.SourceGSLTReaderTraceBinding
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceGSLTDerivationCorrespondence
open Mettapedia.Languages.Metamath.SourceGSLTLexicalClosure
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceGSLTRuntimeStateAgreement
open Mettapedia.Languages.Metamath.SourceGSLTRuntimeCoEvolution
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceProjection

/-! ## `$c` and `$v` token transitions -/

/-- A source-valid constant name is inserted by the actual retained reader
call, at the reader-computed diagnostic position. -/
theorem retainedCall_constSymbol
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB} {name : LocatedName}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before = ⟨db, .const⟩)
    (spelling : tokenText entry.1.bytes = name.name)
    (charset : NameCharset mathBytesValid name) :
    parserObservedState call.after =
      ⟨db.insert (call.before.mkPos call.origin.parserOffset) name.name
          (fun label => .const label), .const⟩ := by
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
      have notEndBytes :
          entry.1.bytes ≠ "$.".toAscii.data.toList := by
        rw [entryBytes]
        change head :: tail ≠ [36, 46]
        exact nonDollarHead_ne_commandPair headNeDollar
      have notComment :
          call.origin.token.eqArray "$(".toAscii = false := by
        simpa [shippedToken] using
          retainedCall_eqArray_false significant notCommentBytes
      have notInclude :
          call.origin.token.eqArray "$[".toAscii = false := by
        simpa [shippedToken] using
          retainedCall_eqArray_false significant notIncludeBytes
      have notEnd :
          call.origin.token.eqArray "$.".toAscii = false := by
        simpa [shippedToken] using
          retainedCall_eqArray_false significant notEndBytes
      have lexed : Metamath.Verify.toMath call.origin.token =
          (true, name.name) := by
        simpa [shippedToken] using
          retainedCall_toMath significant spelling
            ⟨head :: tail, valid, name_eq⟩
      obtain ⟨beforeDb, beforeMode⟩ :=
        call_before_fields_of_observed significant before_eq
      rw [call.after_eq]
      simp [ParserState.feedToken, ParserState.sym, ParserState.withMath,
        ParserState.withDB, beforeDb, beforeMode, notComment, notInclude,
        notEnd, lexed, parserObservedState, observedSemanticState,
        parserSemanticState, logicalTokenMode]

/-- A source-valid variable name is inserted by the actual retained reader
call, at the reader-computed diagnostic position. -/
theorem retainedCall_varSymbol
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB} {name : LocatedName}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before = ⟨db, .var⟩)
    (spelling : tokenText entry.1.bytes = name.name)
    (charset : NameCharset mathBytesValid name) :
    parserObservedState call.after =
      ⟨db.insert (call.before.mkPos call.origin.parserOffset) name.name
          (fun label => .var label), .var⟩ := by
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
      have notEndBytes :
          entry.1.bytes ≠ "$.".toAscii.data.toList := by
        rw [entryBytes]
        change head :: tail ≠ [36, 46]
        exact nonDollarHead_ne_commandPair headNeDollar
      have notComment :
          call.origin.token.eqArray "$(".toAscii = false := by
        simpa [shippedToken] using
          retainedCall_eqArray_false significant notCommentBytes
      have notInclude :
          call.origin.token.eqArray "$[".toAscii = false := by
        simpa [shippedToken] using
          retainedCall_eqArray_false significant notIncludeBytes
      have notEnd :
          call.origin.token.eqArray "$.".toAscii = false := by
        simpa [shippedToken] using
          retainedCall_eqArray_false significant notEndBytes
      have lexed : Metamath.Verify.toMath call.origin.token =
          (true, name.name) := by
        simpa [shippedToken] using
          retainedCall_toMath significant spelling
            ⟨head :: tail, valid, name_eq⟩
      obtain ⟨beforeDb, beforeMode⟩ :=
        call_before_fields_of_observed significant before_eq
      rw [call.after_eq]
      simp [ParserState.feedToken, ParserState.sym, ParserState.withMath,
        ParserState.withDB, beforeDb, beforeMode, notComment, notInclude,
        notEnd, lexed, parserObservedState, observedSemanticState,
        parserSemanticState, logicalTokenMode]

/-- The retained terminator returns constant collection to a statement
boundary without changing the database. -/
theorem retainedCall_constTerminator
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before = ⟨db, .const⟩)
    (spelling : tokenText entry.1.bytes = "$." ) :
    parserObservedState call.after = ⟨db, .start⟩ := by
  have entryBytes : entry.1.bytes = statementEndBytes :=
    retainedBytes_eq_of_spelling spelling (by rfl)
  have notComment : call.origin.token.eqArray "$(".toAscii = false := by
    simpa [shippedToken] using
      retainedCall_eqArray_false significant (by rw [entryBytes]; decide)
  have notInclude : call.origin.token.eqArray "$[".toAscii = false := by
    simpa [shippedToken] using
      retainedCall_eqArray_false significant (by rw [entryBytes]; decide)
  have isEnd : call.origin.token.eqArray "$.".toAscii = true := by
    simpa [shippedToken] using
      retainedCall_eqArray_true significant (by rw [entryBytes]; rfl)
  obtain ⟨beforeDb, beforeMode⟩ :=
    call_before_fields_of_observed significant before_eq
  rw [call.after_eq]
  simp [ParserState.feedToken, ParserState.sym, beforeDb, beforeMode,
    notComment, notInclude, isEnd, parserObservedState,
    observedSemanticState, parserSemanticState, logicalTokenMode]

/-- The retained terminator returns variable collection to a statement
boundary without changing the database. -/
theorem retainedCall_varTerminator
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before = ⟨db, .var⟩)
    (spelling : tokenText entry.1.bytes = "$." ) :
    parserObservedState call.after = ⟨db, .start⟩ := by
  have entryBytes : entry.1.bytes = statementEndBytes :=
    retainedBytes_eq_of_spelling spelling (by rfl)
  have notComment : call.origin.token.eqArray "$(".toAscii = false := by
    simpa [shippedToken] using
      retainedCall_eqArray_false significant (by rw [entryBytes]; decide)
  have notInclude : call.origin.token.eqArray "$[".toAscii = false := by
    simpa [shippedToken] using
      retainedCall_eqArray_false significant (by rw [entryBytes]; decide)
  have isEnd : call.origin.token.eqArray "$.".toAscii = true := by
    simpa [shippedToken] using
      retainedCall_eqArray_true significant (by rw [entryBytes]; rfl)
  obtain ⟨beforeDb, beforeMode⟩ :=
    call_before_fields_of_observed significant before_eq
  rw [call.after_eq]
  simp [ParserState.feedToken, ParserState.sym, beforeDb, beforeMode,
    notComment, notInclude, isEnd, parserObservedState,
    observedSemanticState, parserSemanticState, logicalTokenMode]

/-! ## Complete `$c` and `$v` bodies -/

/-- A complete `$c` body executes the same database fold as the source
payload, even though the production reader computes a distinct diagnostic
position for each token. -/
theorem SpelledCallTrace.constNames_final
    {fileId : String} {db : DB} {names : List LocatedName}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId ⟨db, .const⟩
      (names.map LocatedName.name ++ ["$."]) entries final)
    (charsets : ∀ name ∈ names, NameCharset mathBytesValid name)
    (position : Pos) :
    final =
      ⟨names.map LocatedName.name |>.foldl
          (fun current name =>
            current.insert position name (fun label => .const label)) db,
        .start⟩ := by
  induction names generalizing db entries final with
  | nil =>
      simp only [List.map_nil, List.nil_append] at trace
      cases trace with
      | @cons _ _ texts tailEntries text entry spelling significant
          after_errorFree before_eq tail =>
          cases tail with
          | nil state =>
              simpa using retainedCall_constTerminator significant before_eq
                spelling
  | cons name rest inductionHypothesis =>
      simp only [List.map_cons, List.cons_append] at trace
      cases trace with
      | @cons _ _ texts tailEntries text entry spelling significant
          after_errorFree before_eq tail =>
          have nameCharset : NameCharset mathBytesValid name :=
            charsets name (by simp)
          have restCharsets :
              ∀ next ∈ rest, NameCharset mathBytesValid next := by
            intro next member
            exact charsets next (by simp [member])
          let tokenPosition :=
            entry.2.before.mkPos entry.2.origin.parserOffset
          have headFinal := retainedCall_constSymbol significant before_eq
            spelling nameCharset
          have insertedErrorFree :
              (db.insert tokenPosition name.name
                (fun label => .const label)).error? = none := by
            have databaseEq :=
              congrArg ParserObservedState.db headFinal
            change entry.2.after.db =
                db.insert tokenPosition name.name
                  (fun label => .const label) at databaseEq
            rw [← databaseEq]
            exact after_errorFree
          have positionEq := runtimeInsert_eq_of_errorFree db tokenPosition
            position name.name (fun label => .const label) insertedErrorFree
          have tailAtToken := tail.reindexInitial headFinal
          have tailAtPosition := tailAtToken.reindexInitial
            (congrArg (fun nextDb =>
              (⟨nextDb, .const⟩ : ParserObservedState)) positionEq)
          have result := inductionHypothesis tailAtPosition restCharsets
          simpa [List.foldl_cons] using result

/-- A complete `$v` body executes the same database fold as the source
payload, with successful token positions erased only after the reader has
validated each insertion. -/
theorem SpelledCallTrace.varNames_final
    {fileId : String} {db : DB} {names : List LocatedName}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId ⟨db, .var⟩
      (names.map LocatedName.name ++ ["$."]) entries final)
    (charsets : ∀ name ∈ names, NameCharset mathBytesValid name)
    (position : Pos) :
    final =
      ⟨names.map LocatedName.name |>.foldl
          (fun current name =>
            current.insert position name (fun label => .var label)) db,
        .start⟩ := by
  induction names generalizing db entries final with
  | nil =>
      simp only [List.map_nil, List.nil_append] at trace
      cases trace with
      | @cons _ _ texts tailEntries text entry spelling significant
          after_errorFree before_eq tail =>
          cases tail with
          | nil state =>
              simpa using retainedCall_varTerminator significant before_eq
                spelling
  | cons name rest inductionHypothesis =>
      simp only [List.map_cons, List.cons_append] at trace
      cases trace with
      | @cons _ _ texts tailEntries text entry spelling significant
          after_errorFree before_eq tail =>
          have nameCharset : NameCharset mathBytesValid name :=
            charsets name (by simp)
          have restCharsets :
              ∀ next ∈ rest, NameCharset mathBytesValid next := by
            intro next member
            exact charsets next (by simp [member])
          let tokenPosition :=
            entry.2.before.mkPos entry.2.origin.parserOffset
          have headFinal := retainedCall_varSymbol significant before_eq
            spelling nameCharset
          have insertedErrorFree :
              (db.insert tokenPosition name.name
                (fun label => .var label)).error? = none := by
            have databaseEq :=
              congrArg ParserObservedState.db headFinal
            change entry.2.after.db =
                db.insert tokenPosition name.name
                  (fun label => .var label) at databaseEq
            rw [← databaseEq]
            exact after_errorFree
          have positionEq := runtimeInsert_eq_of_errorFree db tokenPosition
            position name.name (fun label => .var label) insertedErrorFree
          have tailAtToken := tail.reindexInitial headFinal
          have tailAtPosition := tailAtToken.reindexInitial
            (congrArg (fun nextDb =>
              (⟨nextDb, .var⟩ : ParserObservedState)) positionEq)
          have result := inductionHypothesis tailAtPosition restCharsets
          simpa [List.foldl_cons] using result

/-- A complete retained `$c` statement is exactly one source payload at a
position already present in the reader trace. -/
theorem SpelledCallTrace.constStatement_final
    {fileId : String} {db : DB} {names : List LocatedName}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId ⟨db, .start⟩
      ("$c" :: names.map LocatedName.name ++ ["$."]) entries final)
    (charsets : ∀ name ∈ names, NameCharset mathBytesValid name) :
    ∃ position : Pos,
      final =
        ⟨runtimeApplyPayload position
            (.declareConstants (names.map LocatedName.name)) db,
          .start⟩ := by
  cases trace with
  | @cons _ _ texts tailEntries text entry spelling significant
      after_errorFree before_eq tail =>
      let position := entry.2.before.mkPos entry.2.origin.parserOffset
      have afterKeyword := retainedCall_constKeyword significant before_eq
        spelling
      have tail' := tail.reindexInitial afterKeyword
      have finalEq := tail'.constNames_final charsets position
      exact ⟨position, by
        simpa [runtimeApplyPayload] using finalEq⟩

/-- A complete retained `$v` statement is exactly one source payload at a
position already present in the reader trace. -/
theorem SpelledCallTrace.varStatement_final
    {fileId : String} {db : DB} {names : List LocatedName}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId ⟨db, .start⟩
      ("$v" :: names.map LocatedName.name ++ ["$."]) entries final)
    (charsets : ∀ name ∈ names, NameCharset mathBytesValid name) :
    ∃ position : Pos,
      final =
        ⟨runtimeApplyPayload position
            (.declareVariables (names.map LocatedName.name)) db,
          .start⟩ := by
  cases trace with
  | @cons _ _ texts tailEntries text entry spelling significant
      after_errorFree before_eq tail =>
      let position := entry.2.before.mkPos entry.2.origin.parserOffset
      have afterKeyword := retainedCall_varKeyword significant before_eq
        spelling
      have tail' := tail.reindexInitial afterKeyword
      have finalEq := tail'.varNames_final charsets position
      exact ⟨position, by
        simpa [runtimeApplyPayload] using finalEq⟩

/-! ## Source/parser boundary transitions -/

/-- An accepted source `$c` statement and its exact reader call group advance
the refinement relation to the same successor. -/
theorem SourceParserPrefixAgrees.constDecl
    {fileId : String} {source next : SourceState}
    {site terminator : LocatedByteSpan} {names : List LocatedName}
    {initial final : ParserObservedState}
    {entries : List (LocatedToken × TokenCall)}
    (agreement : SourceParserPrefixAgrees source initial)
    (trace : SpelledCallTrace fileId initial
      ("$c" :: names.map LocatedName.name ++ ["$."]) entries final)
    (charsets : ∀ name ∈ names, NameCharset mathBytesValid name)
    (applied : applyStatement source (.constDecl site names terminator) =
      .ok (next, [])) :
    SourceParserPrefixAgrees next final := by
  rcases initial with ⟨db, mode⟩
  cases agreement.mode_eq
  obtain ⟨position, finalEq⟩ := trace.constStatement_final charsets
  cases payloadApplied : applyLocalPayload?
      (.declareConstants (names.map LocatedName.name)) source with
  | none =>
      simp only [applyStatement, payloadApplied] at applied
      exact nomatch applied
  | some after =>
      simp only [applyStatement, payloadApplied] at applied
      cases applied
      rw [finalEq]
      exact
        { mode_eq := rfl
          database :=
            SourceGSLTRuntimeCoEvolution.RuntimeDBAgrees.applyPayload
              agreement.database payloadApplied agreement.interrupt_eq position
          interrupt_eq :=
            (runtimeApplyPayload_interrupt position
              (.declareConstants (names.map LocatedName.name)) db).trans
              agreement.interrupt_eq }

/-- An accepted source `$v` statement and its exact reader call group advance
the refinement relation to the same successor. -/
theorem SourceParserPrefixAgrees.varDecl
    {fileId : String} {source next : SourceState}
    {site terminator : LocatedByteSpan} {names : List LocatedName}
    {initial final : ParserObservedState}
    {entries : List (LocatedToken × TokenCall)}
    (agreement : SourceParserPrefixAgrees source initial)
    (trace : SpelledCallTrace fileId initial
      ("$v" :: names.map LocatedName.name ++ ["$."]) entries final)
    (charsets : ∀ name ∈ names, NameCharset mathBytesValid name)
    (applied : applyStatement source (.varDecl site names terminator) =
      .ok (next, [])) :
    SourceParserPrefixAgrees next final := by
  rcases initial with ⟨db, mode⟩
  cases agreement.mode_eq
  obtain ⟨position, finalEq⟩ := trace.varStatement_final charsets
  cases payloadApplied : applyLocalPayload?
      (.declareVariables (names.map LocatedName.name)) source with
  | none =>
      simp only [applyStatement, payloadApplied] at applied
      exact nomatch applied
  | some after =>
      simp only [applyStatement, payloadApplied] at applied
      cases applied
      rw [finalEq]
      exact
        { mode_eq := rfl
          database :=
            SourceGSLTRuntimeCoEvolution.RuntimeDBAgrees.applyPayload
              agreement.database payloadApplied agreement.interrupt_eq position
          interrupt_eq :=
            (runtimeApplyPayload_interrupt position
              (.declareVariables (names.map LocatedName.name)) db).trans
              agreement.interrupt_eq }

/-! ## `$d` incremental pair construction -/

/-- Remaining pair pushes performed by the shipped `$d` loop, written as a
list fold so it can be compared directly with `allDistinctPairs`. -/
def pushRemainingDJPairs (array : Array String) (start : Nat)
    (current : String) (state : ParserState) : ParserState :=
  (array.toList.drop start).foldl
    (fun next earlier =>
      next.withDB (fun db => db.withDJ (fun pairs =>
        pairs.push (canonicalDJPair earlier current)))) state

/-- With a fresh current name, the shipped index loop is exactly the
corresponding fold of canonical pairs over the unprocessed array suffix. -/
theorem djvars_loop_aux_eq_pushRemainingDJPairs
    (array : Array String) (state : ParserState) (position : Pos)
    (current : String) (start : Nat)
    (fresh : current ∉ array.toList) :
    ParserState.djvars_loop_aux array state position current start =
      { pushRemainingDJPairs array start current state with
        tokp := .djvars (array.push current) } := by
  refine Nat.rec (motive := fun remaining =>
      ∀ start (state : ParserState), array.size - start = remaining →
        ParserState.djvars_loop_aux array state position current start =
          { pushRemainingDJPairs array start current state with
            tokp := .djvars (array.push current) }) ?base ?step
      (array.size - start) start state rfl
  · intro index state sizeEq
    have outOfBounds : ¬ index < array.size := by
      intro inBounds
      have positive : 0 < array.size - index := Nat.sub_pos_of_lt inBounds
      simp [sizeEq] at positive
    have dropEq : array.toList.drop index = [] := by
      exact List.drop_eq_nil_of_le
        (by simpa using Nat.le_of_not_gt outOfBounds)
    simp [ParserState.djvars_loop_aux, outOfBounds,
      pushRemainingDJPairs, dropEq]
  · intro remaining inductionHypothesis index state sizeEq
    have inBounds : index < array.size := by
      by_contra outOfBounds
      have zero : array.size - index = 0 :=
        Nat.sub_eq_zero_of_le (Nat.le_of_not_gt outOfBounds)
      simp [zero] at sizeEq
    have nextSize : array.size - (index + 1) = remaining := by
      simp only [Nat.add_one, Nat.sub_succ, sizeEq, Nat.pred_succ]
    let earlier : String := array[index]
    have earlierMem : earlier ∈ array.toList := by
      change array[index] ∈ array.toList
      exact Array.getElem_mem_toList (xs := array) (i := index)
        (h := inBounds)
    have distinct : earlier ≠ current := by
      intro equality
      apply fresh
      simpa [equality] using earlierMem
    have listIndexBound : index < array.toList.length := by
      simpa using inBounds
    have dropEq :
        array.toList.drop index =
          earlier :: array.toList.drop (index + 1) := by
      simpa [earlier] using
        (List.cons_getElem_drop_succ
          (l := array.toList) (n := index) (h := listIndexBound)).symm
    dsimp only [earlier] at distinct dropEq ⊢
    unfold ParserState.djvars_loop_aux
    simp only [inBounds, ↓reduceDIte]
    simp only [distinct, beq_iff_eq, ↓reduceIte]
    rw [inductionHypothesis (index + 1) _ nextSize]
    simp [pushRemainingDJPairs, dropEq, canonicalDJPair]

/-- Projecting the parser-state fold to its database is exactly the shipped
`withDJ` fold for the newly generated pairs. -/
theorem pushRemainingDJPairs_db_toArray (prior : List String)
    (current : String) (state : ParserState) :
    (pushRemainingDJPairs prior.toArray 0 current state).db =
      prior.foldl
        (fun db earlier => db.withDJ (fun pairs =>
          pairs.push (canonicalDJPair earlier current))) state.db := by
  change
    (prior.foldl
      (fun next earlier =>
        next.withDB (fun db => db.withDJ (fun pairs =>
          pairs.push (canonicalDJPair earlier current)))) state).db = _
  induction prior generalizing state with
  | nil => rfl
  | cons earlier rest inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis]
      rfl

/-- A fresh `$d` name runs the reader's whole pair loop exactly. -/
theorem djvars_loop_eq_pushRemainingDJPairs
    (prior : List String) (state : ParserState) (position : Pos)
    (current : String) (fresh : current ∉ prior)
    (scopeGate : state.db.djvarsScopeViolation? current = none) :
    ParserState.djvars_loop prior.toArray state position current =
      { pushRemainingDJPairs prior.toArray 0 current state with
        tokp := .djvars (prior ++ [current]).toArray } := by
  unfold ParserState.djvars_loop
  simp only [scopeGate]
  rw [djvars_loop_aux_eq_pushRemainingDJPairs
    prior.toArray state position current 0 (by simpa using fresh)]
  have arrayEq : prior.toArray.push current =
      (prior ++ [current]).toArray := by
    apply Array.ext'
    simp
  rw [arrayEq]

/-- One retained `$d` name adds precisely its canonical pairs against all
earlier names and extends the reader's name accumulator. -/
theorem retainedCall_djSymbol
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB}
    {prior : List String} {name : LocatedName}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before =
      ⟨db, .djvars prior.toArray⟩)
    (spelling : tokenText entry.1.bytes = name.name)
    (charset : NameCharset mathBytesValid name)
    (fresh : name.name ∉ prior)
    (after_errorFree : call.after.db.error? = none) :
    parserObservedState call.after =
      ⟨prior.foldl
          (fun current earlier => current.withDJ (fun pairs =>
            pairs.push (canonicalDJPair earlier name.name))) db,
        .djvars (prior ++ [name.name]).toArray⟩ := by
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
      have notEndBytes :
          entry.1.bytes ≠ "$.".toAscii.data.toList := by
        rw [entryBytes]
        change head :: tail ≠ [36, 46]
        exact nonDollarHead_ne_commandPair headNeDollar
      have notComment :
          call.origin.token.eqArray "$(".toAscii = false := by
        simpa [shippedToken] using
          retainedCall_eqArray_false significant notCommentBytes
      have notInclude :
          call.origin.token.eqArray "$[".toAscii = false := by
        simpa [shippedToken] using
          retainedCall_eqArray_false significant notIncludeBytes
      have notEnd :
          call.origin.token.eqArray "$.".toAscii = false := by
        simpa [shippedToken] using
          retainedCall_eqArray_false significant notEndBytes
      have lexed : Metamath.Verify.toMath call.origin.token =
          (true, name.name) := by
        simpa [shippedToken] using
          retainedCall_toMath significant spelling
            ⟨head :: tail, valid, name_eq⟩
      obtain ⟨beforeDb, beforeMode⟩ :=
        call_before_fields_of_observed significant before_eq
      have liveSuccess :
          (call.before.feedToken call.origin.parserOffset
            call.origin.token).db.error? = none := by
        rw [← call.after_eq]
        exact after_errorFree
      cases scopeGate : db.djvarsScopeViolation? name.name with
      | some error =>
          simp [ParserState.feedToken, beforeDb, beforeMode, notComment,
            notInclude, notEnd, ParserState.withMath, lexed,
            ParserState.djvars_loop, scopeGate,
            ParserState.mkErrorFromEvidence,
            ParserState.withDB, DB.mkErrorFromEvidence,
            DB.mkErrorWithEvidence] at liveSuccess
      | none =>
          rw [call.after_eq]
          have loopEq := djvars_loop_eq_pushRemainingDJPairs prior
            call.before (call.before.mkPos call.origin.parserOffset)
              name.name fresh (by simpa [beforeDb] using scopeGate)
          simp [ParserState.feedToken, beforeDb, beforeMode, notComment,
            notInclude, notEnd, ParserState.withMath, lexed, loopEq,
            parserObservedState, observedSemanticState, parserSemanticState,
            logicalTokenMode, pushRemainingDJPairs_db_toArray]

/-- The actual retained `$d` terminator both certifies the book's minimum
arity and returns to a statement boundary without changing the database. -/
theorem retainedCall_djTerminator
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB}
    {prior : List String}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before =
      ⟨db, .djvars prior.toArray⟩)
    (spelling : tokenText entry.1.bytes = "$." )
    (after_errorFree : call.after.db.error? = none) :
    2 ≤ prior.length ∧
      parserObservedState call.after = ⟨db, .start⟩ := by
  have entryBytes : entry.1.bytes = statementEndBytes :=
    retainedBytes_eq_of_spelling spelling (by rfl)
  have notComment : call.origin.token.eqArray "$(".toAscii = false := by
    simpa [shippedToken] using
      retainedCall_eqArray_false significant (by rw [entryBytes]; decide)
  have notInclude : call.origin.token.eqArray "$[".toAscii = false := by
    simpa [shippedToken] using
      retainedCall_eqArray_false significant (by rw [entryBytes]; decide)
  have isEnd : call.origin.token.eqArray "$.".toAscii = true := by
    simpa [shippedToken] using
      retainedCall_eqArray_true significant (by rw [entryBytes]; rfl)
  obtain ⟨beforeDb, beforeMode⟩ :=
    call_before_fields_of_observed significant before_eq
  have liveSuccess :
      (call.before.feedToken call.origin.parserOffset
        call.origin.token).db.error? = none := by
    rw [← call.after_eq]
    exact after_errorFree
  have arity := Metamath.ParserOps.feedToken_djvars_terminator_size_ge_two
    call.before call.origin.parserOffset call.origin.token prior.toArray
      beforeMode (by simpa using notComment) (by simpa using notInclude)
      isEnd liveSuccess
  have arity' : 2 ≤ prior.length := by simpa using arity
  refine ⟨arity', ?_⟩
  rw [call.after_eq]
  have notTooShort : ¬ prior.length ≤ 1 := by omega
  simp [ParserState.feedToken, beforeDb, beforeMode, notComment,
    notInclude, isEnd, notTooShort, parserObservedState,
    observedSemanticState, parserSemanticState, logicalTokenMode]

/-- Append one canonical source pair to the shipped distinct-variable array. -/
def pushDJPair (db : DB) (pair : String × String) : DB :=
  db.withDJ (fun pairs => pairs.push pair)

/-- Folding the canonical pairs produced by mapping an earlier-name list is
definitionally the same update as folding over the names themselves. -/
theorem foldl_canonicalDJPairs (prior : List String) (current : String)
    (db : DB) :
    (prior.map (fun earlier => canonicalDJPair earlier current)).foldl
        pushDJPair db =
      prior.foldl
        (fun next earlier =>
          pushDJPair next (canonicalDJPair earlier current)) db := by
  induction prior generalizing db with
  | nil => rfl
  | cons earlier rest inductionHypothesis =>
      simp only [List.map_cons, List.foldl_cons]
      exact inductionHypothesis _

/-- Starting with an already accumulated prefix of names, the retained reader
processes the remaining `$d` names and terminator as exactly the corresponding
suffix of `allDistinctPairsFrom`.  Successful termination also exposes the
book grammar's minimum arity. -/
theorem SpelledCallTrace.djNamesFrom_final
    {fileId : String} {db : DB} {prior : List String}
    {names : List LocatedName}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId ⟨db, .djvars prior.toArray⟩
      (names.map LocatedName.name ++ ["$."]) entries final)
    (charsets : ∀ name ∈ names, NameCharset mathBytesValid name)
    (nodup : (prior ++ names.map LocatedName.name).Nodup) :
    2 ≤ (prior ++ names.map LocatedName.name).length ∧
      final =
        ⟨(allDistinctPairsFrom prior (names.map LocatedName.name)).foldl
            pushDJPair db,
          .start⟩ := by
  induction names generalizing prior db entries final with
  | nil =>
      simp only [List.map_nil, List.append_nil, List.nil_append] at trace ⊢
      cases trace with
      | @cons _ _ texts tailEntries text entry spelling significant
          after_errorFree before_eq tail =>
          cases tail with
          | nil state =>
              obtain ⟨arity, finalEq⟩ :=
                retainedCall_djTerminator significant before_eq spelling
                  after_errorFree
              refine ⟨arity, ?_⟩
              change parserObservedState entry.2.after = ⟨db, .start⟩
              exact finalEq
  | cons name rest inductionHypothesis =>
      simp only [List.map_cons, List.cons_append] at trace nodup ⊢
      cases trace with
      | @cons _ _ texts tailEntries text entry spelling significant
          after_errorFree before_eq tail =>
          have nameCharset : NameCharset mathBytesValid name :=
            charsets name (by simp)
          have restCharsets :
              ∀ next ∈ rest, NameCharset mathBytesValid next := by
            intro next member
            exact charsets next (by simp [member])
          have fresh : name.name ∉ prior := by
            intro member
            have disjoint := List.disjoint_of_nodup_append nodup
            exact disjoint member (by simp)
          have tailNodup :
              ((prior ++ [name.name]) ++
                rest.map LocatedName.name).Nodup := by
            simpa [List.append_assoc] using nodup
          have headFinal := retainedCall_djSymbol significant before_eq
            spelling nameCharset fresh after_errorFree
          have headFinal' : parserObservedState entry.2.after =
              ⟨prior.foldl
                  (fun next earlier => pushDJPair next
                    (canonicalDJPair earlier name.name)) db,
                .djvars (prior ++ [name.name]).toArray⟩ := by
            simpa [pushDJPair] using headFinal
          have tail' := tail.reindexInitial headFinal'
          obtain ⟨arity, finalEq⟩ := inductionHypothesis
            (prior := prior ++ [name.name]) tail' restCharsets tailNodup
          refine ⟨by simpa [List.append_assoc] using arity, ?_⟩
          rw [finalEq]
          apply congrArg (fun updated : DB =>
            (⟨updated, .start⟩ : ParserObservedState))
          rw [allDistinctPairsFrom_cons, List.foldl_append,
            foldl_canonicalDJPairs]

/-- A complete retained `$d` statement executes exactly the source payload's
one-shot distinct-pair update.  Its successful terminator independently
certifies that the statement contains at least two names. -/
theorem SpelledCallTrace.djStatement_final
    {fileId : String} {db : DB} {names : List LocatedName}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId ⟨db, .start⟩
      ("$d" :: names.map LocatedName.name ++ ["$."]) entries final)
    (charsets : ∀ name ∈ names, NameCharset mathBytesValid name)
    (nodup : (names.map LocatedName.name).Nodup) :
    2 ≤ names.length ∧
      ∃ position : Pos,
        final =
          ⟨runtimeApplyPayload position
              (.declareDisjoint (names.map LocatedName.name)) db,
            .start⟩ := by
  cases trace with
  | @cons _ _ texts tailEntries text entry spelling significant
      after_errorFree before_eq tail =>
      let position := entry.2.before.mkPos entry.2.origin.parserOffset
      have afterKeyword := retainedCall_djKeyword significant before_eq
        spelling
      have tail' := tail.reindexInitial afterKeyword
      obtain ⟨arity, finalEq⟩ :=
        tail'.djNamesFrom_final charsets (by simpa using nodup)
      have runtimeEq :
          runtimeApplyPayload position
              (.declareDisjoint (names.map LocatedName.name)) db =
            (allDistinctPairsFrom []
                (names.map LocatedName.name)).foldl pushDJPair db := by
        rfl
      refine ⟨by simpa using arity, position, ?_⟩
      rw [runtimeEq]
      exact finalEq

/-- An accepted source `$d` statement and its exact retained reader call group
advance the refinement relation to the same successor database. -/
theorem SourceParserPrefixAgrees.djDecl
    {fileId : String} {source next : SourceState}
    {site terminator : LocatedByteSpan} {names : List LocatedName}
    {initial final : ParserObservedState}
    {entries : List (LocatedToken × TokenCall)}
    (agreement : SourceParserPrefixAgrees source initial)
    (trace : SpelledCallTrace fileId initial
      ("$d" :: names.map LocatedName.name ++ ["$."]) entries final)
    (charsets : ∀ name ∈ names, NameCharset mathBytesValid name)
    (applied : applyStatement source (.djDecl site names terminator) =
      .ok (next, [])) :
    SourceParserPrefixAgrees next final := by
  rcases initial with ⟨db, mode⟩
  cases agreement.mode_eq
  cases payloadApplied : applyLocalPayload?
      (.declareDisjoint (names.map LocatedName.name)) source with
  | none =>
      simp only [applyStatement, payloadApplied] at applied
      exact nomatch applied
  | some after =>
      simp only [applyStatement, payloadApplied] at applied
      cases applied
      obtain ⟨-, namesNodup⟩ :=
        declareDisjoint?_arity_and_nodup payloadApplied
      obtain ⟨-, position, finalEq⟩ :=
        trace.djStatement_final charsets namesNodup
      rw [finalEq]
      exact
        { mode_eq := rfl
          database :=
            SourceGSLTRuntimeCoEvolution.RuntimeDBAgrees.applyPayload
              agreement.database payloadApplied agreement.interrupt_eq position
          interrupt_eq :=
            (runtimeApplyPayload_interrupt position
              (.declareDisjoint (names.map LocatedName.name)) db).trans
              agreement.interrupt_eq }

/-! ## `$f`, `$e`, and `$a` formula terminators -/

/-- Prefixing a source-tagged body by its admitted typecode produces the
constant-headed formula consumed by the shipped reader. -/
theorem tagBody_typecode_cons
    {state : SourceState} {typecode : LocatedName}
    {body : List LocatedName} {bodySymbols : List Sym}
    (valid : sourceStateValid state = true)
    (formulaDeclared :
      formulaSymbolsRespectDeclarations state.declaredConstants
        state.declaredVariables ⟨typecode.name, bodySymbols⟩ = true)
    (taggedBody : tagBody state body = .ok bodySymbols) :
    tagBody state (typecode :: body) =
      .ok (.const typecode.name :: bodySymbols) := by
  unfold formulaSymbolsRespectDeclarations at formulaDeclared
  simp only [Bool.and_eq_true] at formulaDeclared
  have typecodeConstant : typecode.name ∈ state.declaredConstants := by
    simpa [List.contains_iff_mem] using formulaDeclared.1
  have typecodeNotVariable :=
    declaredConstant_not_variable_of_sourceStateValid valid typecodeConstant
  simp [tagBody, tagSymbol, List.contains_iff_mem, typecodeConstant,
    typecodeNotVariable, taggedBody]

/-- A one-token `$f` chronology enters floating-hypothesis formula
collection. -/
theorem SpelledCallTrace.floatKeyword_final
    {fileId : String} {db : DB} {label : String} {labelPos : Pos}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId ⟨db, .label labelPos label⟩
      ["$f"] entries final) :
    final = ⟨db, .math #[] ⟨.float, labelPos, label⟩⟩ := by
  cases trace with
  | @cons _ _ texts tailEntries text entry spelling significant
      after_errorFree before_eq tail =>
      cases tail with
      | nil state =>
          exact retainedCall_floatKeyword significant before_eq spelling

/-- A one-token `$e` chronology enters essential-hypothesis formula
collection. -/
theorem SpelledCallTrace.essentialKeyword_final
    {fileId : String} {db : DB} {label : String} {labelPos : Pos}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId ⟨db, .label labelPos label⟩
      ["$e"] entries final) :
    final = ⟨db, .math #[] ⟨.ess, labelPos, label⟩⟩ := by
  cases trace with
  | @cons _ _ texts tailEntries text entry spelling significant
      after_errorFree before_eq tail =>
      cases tail with
      | nil state =>
          exact retainedCall_essentialKeyword significant before_eq spelling

/-- A one-token `$a` chronology enters axiom-formula collection. -/
theorem SpelledCallTrace.axiomKeyword_final
    {fileId : String} {db : DB} {label : String} {labelPos : Pos}
    {entries : List (LocatedToken × TokenCall)}
    {final : ParserObservedState}
    (trace : SpelledCallTrace fileId ⟨db, .label labelPos label⟩
      ["$a"] entries final) :
    final = ⟨db, .math #[] ⟨.ax, labelPos, label⟩⟩ := by
  cases trace with
  | @cons _ _ texts tailEntries text entry spelling significant
      after_errorFree before_eq tail =>
      cases tail with
      | nil state =>
          exact retainedCall_axiomKeyword significant before_eq spelling

/-- Successful shipped `$f` finalization has exactly the advertised database
update and returns to a statement boundary. -/
theorem parserObservedState_feedTokens_float
    (state : ParserState) (formula : RuntimeFormula)
    (position : Pos) (label : String)
    (success :
      (state.feedTokens formula ⟨.float, position, label⟩).db.error? = none) :
    parserObservedState
        (state.feedTokens formula ⟨.float, position, label⟩) =
      ⟨state.db.insertHyp position label false formula, .start⟩ := by
  have first := Metamath.ParserOps.feedTokens_success_first_not_var state
    formula ⟨.float, position, label⟩ success
  have shape := Metamath.ParserOps.feedTokens_success_float_shape state
    formula position label success
  have database := Metamath.ParserOps.feedTokens_float_db state formula
    position label first shape success
  have mode := Metamath.ParserOps.feedTokens_nonthm_success_tokp_start state
    formula .float position label (by intro equality; cases equality) success
  change
    (⟨(state.feedTokens formula ⟨.float, position, label⟩).db,
      logicalTokenMode
        (state.feedTokens formula ⟨.float, position, label⟩).tokp⟩ :
      ParserObservedState) = _
  rw [database, mode]
  rfl

/-- Successful shipped `$e` finalization has exactly the advertised database
update and returns to a statement boundary. -/
theorem parserObservedState_feedTokens_essential
    (state : ParserState) (formula : RuntimeFormula)
    (position : Pos) (label : String)
    (success :
      (state.feedTokens formula ⟨.ess, position, label⟩).db.error? = none) :
    parserObservedState
        (state.feedTokens formula ⟨.ess, position, label⟩) =
      ⟨state.db.insertHyp position label true formula, .start⟩ := by
  have first := Metamath.ParserOps.feedTokens_success_first_not_var state
    formula ⟨.ess, position, label⟩ success
  have database := Metamath.ParserOps.feedTokens_ess_db state formula
    position label first success
  have mode := Metamath.ParserOps.feedTokens_nonthm_success_tokp_start state
    formula .ess position label (by intro equality; cases equality) success
  change
    (⟨(state.feedTokens formula ⟨.ess, position, label⟩).db,
      logicalTokenMode
        (state.feedTokens formula ⟨.ess, position, label⟩).tokp⟩ :
      ParserObservedState) = _
  rw [database, mode]
  rfl

/-- Successful shipped `$a` finalization has exactly the advertised database
update and returns to a statement boundary. -/
theorem parserObservedState_feedTokens_axiom
    (state : ParserState) (formula : RuntimeFormula)
    (position : Pos) (label : String)
    (success :
      (state.feedTokens formula ⟨.ax, position, label⟩).db.error? = none) :
    parserObservedState
        (state.feedTokens formula ⟨.ax, position, label⟩) =
      ⟨state.db.insertAxiom position label formula, .start⟩ := by
  have first := Metamath.ParserOps.feedTokens_success_first_not_var state
    formula ⟨.ax, position, label⟩ success
  have database := Metamath.ParserOps.feedTokens_ax_db state formula
    position label first success
  have mode := Metamath.ParserOps.feedTokens_nonthm_success_tokp_start state
    formula .ax position label (by intro equality; cases equality) success
  change
    (⟨(state.feedTokens formula ⟨.ax, position, label⟩).db,
      logicalTokenMode
        (state.feedTokens formula ⟨.ax, position, label⟩).tokp⟩ :
      ParserObservedState) = _
  rw [database, mode]
  rfl

/-- For a non-theorem math accumulator, the retained `$.` call dispatches to
the shipped `feedTokens` operation. -/
theorem retainedCall_nonTheoremTerminator_feedTokens
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB}
    {formula : RuntimeFormula} {kind : TokensKind}
    {labelPos : Pos} {label : String}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before =
      ⟨db, .math formula ⟨kind, labelPos, label⟩⟩)
    (spelling : tokenText entry.1.bytes = "$." )
    (nonTheorem : kind ≠ .thm) :
    parserObservedState call.after =
      parserObservedState
        (call.before.feedTokens formula ⟨kind, labelPos, label⟩) := by
  have entryBytes : entry.1.bytes = statementEndBytes :=
    retainedBytes_eq_of_spelling spelling (by rfl)
  have notComment : call.origin.token.eqArray "$(".toAscii = false := by
    simpa [shippedToken] using
      retainedCall_eqArray_false significant (by rw [entryBytes]; decide)
  have notInclude : call.origin.token.eqArray "$[".toAscii = false := by
    simpa [shippedToken] using
      retainedCall_eqArray_false significant (by rw [entryBytes]; decide)
  have kindDelimiter : kind.delim = "$.".toAscii := by
    cases kind <;> simp_all [TokensKind.delim]
  have delimiter : call.origin.token.eqArray kind.delim = true := by
    simpa [kindDelimiter, shippedToken] using
      retainedCall_eqArray_true significant (by rw [entryBytes]; rfl)
  obtain ⟨beforeDb, beforeMode⟩ :=
    call_before_fields_of_observed significant before_eq
  rw [call.after_eq]
  simp [ParserState.feedToken, beforeMode, notComment, notInclude,
    delimiter]

theorem retainedCall_floatTerminator
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB}
    {formula : RuntimeFormula} {labelPos : Pos} {label : String}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before =
      ⟨db, .math formula ⟨.float, labelPos, label⟩⟩)
    (spelling : tokenText entry.1.bytes = "$." )
    (after_errorFree : call.after.db.error? = none) :
    parserObservedState call.after =
      ⟨db.insertHyp labelPos label false formula, .start⟩ := by
  have dispatched := retainedCall_nonTheoremTerminator_feedTokens
    significant before_eq spelling (by intro equality; cases equality)
  have feedSuccess :
      (call.before.feedTokens formula
        ⟨.float, labelPos, label⟩).db.error? = none := by
    have databaseEq := congrArg ParserObservedState.db dispatched
    change call.after.db =
      (call.before.feedTokens formula
        ⟨.float, labelPos, label⟩).db at databaseEq
    rw [← databaseEq]
    exact after_errorFree
  exact dispatched.trans
    (parserObservedState_feedTokens_float call.before formula labelPos label
      feedSuccess |>.trans (by
        obtain ⟨beforeDb, -⟩ :=
          call_before_fields_of_observed significant before_eq
        rw [beforeDb]))

theorem retainedCall_essentialTerminator
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB}
    {formula : RuntimeFormula} {labelPos : Pos} {label : String}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before =
      ⟨db, .math formula ⟨.ess, labelPos, label⟩⟩)
    (spelling : tokenText entry.1.bytes = "$." )
    (after_errorFree : call.after.db.error? = none) :
    parserObservedState call.after =
      ⟨db.insertHyp labelPos label true formula, .start⟩ := by
  have dispatched := retainedCall_nonTheoremTerminator_feedTokens
    significant before_eq spelling (by intro equality; cases equality)
  have feedSuccess :
      (call.before.feedTokens formula
        ⟨.ess, labelPos, label⟩).db.error? = none := by
    have databaseEq := congrArg ParserObservedState.db dispatched
    change call.after.db =
      (call.before.feedTokens formula
        ⟨.ess, labelPos, label⟩).db at databaseEq
    rw [← databaseEq]
    exact after_errorFree
  have feedFinal := parserObservedState_feedTokens_essential call.before
    formula labelPos label feedSuccess
  obtain ⟨beforeDb, -⟩ :=
    call_before_fields_of_observed significant before_eq
  rw [beforeDb] at feedFinal
  exact dispatched.trans feedFinal

theorem retainedCall_axiomTerminator
    {fileId : String} {call : TokenCall}
    {entry : LocatedToken × TokenCall} {db : DB}
    {formula : RuntimeFormula} {labelPos : Pos} {label : String}
    (significant : significantLocatedEntry? fileId call = some entry)
    (before_eq : parserObservedState call.before =
      ⟨db, .math formula ⟨.ax, labelPos, label⟩⟩)
    (spelling : tokenText entry.1.bytes = "$." )
    (after_errorFree : call.after.db.error? = none) :
    parserObservedState call.after =
      ⟨db.insertAxiom labelPos label formula, .start⟩ := by
  have dispatched := retainedCall_nonTheoremTerminator_feedTokens
    significant before_eq spelling (by intro equality; cases equality)
  have feedSuccess :
      (call.before.feedTokens formula
        ⟨.ax, labelPos, label⟩).db.error? = none := by
    have databaseEq := congrArg ParserObservedState.db dispatched
    change call.after.db =
      (call.before.feedTokens formula
        ⟨.ax, labelPos, label⟩).db at databaseEq
    rw [← databaseEq]
    exact after_errorFree
  have feedFinal := parserObservedState_feedTokens_axiom call.before formula
    labelPos label feedSuccess
  obtain ⟨beforeDb, -⟩ :=
    call_before_fields_of_observed significant before_eq
  rw [beforeDb] at feedFinal
  exact dispatched.trans feedFinal

/-! ## Executable integration canaries -/

private def emptyDisjointSource : String :=
  "$d $."

private def singletonDisjointSource : String :=
  "$v x $. $d x $."

private def binaryDisjointSource : String :=
  "$v x y $. $d x y $."

#guard (checkBytes emptyDisjointSource.toUTF8 .soundDefault).parseErrorCode? =
  some .disjointStatementTooShort

#guard (checkBytes singletonDisjointSource.toUTF8
    .soundDefault).parseErrorCode? =
  some .disjointStatementTooShort

#guard (checkBytes binaryDisjointSource.toUTF8 .soundDefault).error?.isNone

end Mettapedia.Languages.Metamath.SourceGSLTParserPrefixBisimulation
