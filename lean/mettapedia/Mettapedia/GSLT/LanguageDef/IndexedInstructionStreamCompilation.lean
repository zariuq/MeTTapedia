import Mettapedia.GSLT.Core.Composition

/-!
# Generated indexed-instruction stream compilation

Many authored byte languages encode finite-table references with continuation
digits, a terminating digit, and a few disjoint control bytes.  A generated
machine may classify those bytes once, carry the open numeric accumulator
across source chunks, and execute compact `use`/`save`/`unknown` instructions.

The decoder plan below is entirely data: byte ranges, radices, biases, and
control bytes.  Validation is fail-closed.  Arithmetic is checked against the
exact unsigned 64-bit carrier before either a continuation or terminal update
is accepted.  The central chunking theorem proves that streaming across source
token boundaries is identical to decoding the flattened byte stream.
-/

namespace Mettapedia.GSLT.LanguageDef.IndexedInstructionStreamCompilation

inductive Instruction where
  | use (index : UInt64)
  | save
  | unknown
  deriving DecidableEq, Repr

inductive DecodeError where
  | invalidPlan
  | invalidByte (byte : UInt8)
  | overflow
  | saveInsideIndex
  | saveWithoutUse
  | unknownInsideIndex
  | openIndexAtEnd
  deriving DecidableEq, Repr

/-- Whether one completed `use` licenses exactly one postfix save or any
number of adjacent saves.  This is generated language policy, not VM logic. -/
inductive SavePlacement where
  | immediatelyAfterUse
  | repeatableAfterUse
  deriving DecidableEq, Repr

/-- Generated description of one disjoint indexed-instruction alphabet. -/
structure Plan where
  terminalLow : UInt8
  terminalHigh : UInt8
  continuationLow : UInt8
  continuationHigh : UInt8
  saveByte : UInt8
  unknownByte : UInt8
  terminalRadix : UInt32
  terminalDigitBias : UInt32
  continuationRadix : UInt32
  continuationDigitBias : UInt32
  savePlacement : SavePlacement := .immediatelyAfterUse
  deriving DecidableEq, Repr

def inRange (byte low high : UInt8) : Bool := low <= byte && byte <= high

/-- The four byte classes are nonempty and pairwise disjoint where required;
both numeric updates have a positive radix. -/
def Plan.valid (plan : Plan) : Bool :=
  decide (plan.terminalLow <= plan.terminalHigh) &&
    decide (plan.continuationLow <= plan.continuationHigh) &&
    !(inRange plan.terminalLow plan.continuationLow plan.continuationHigh) &&
    !(inRange plan.terminalHigh plan.continuationLow plan.continuationHigh) &&
    !(inRange plan.continuationLow plan.terminalLow plan.terminalHigh) &&
    !(inRange plan.continuationHigh plan.terminalLow plan.terminalHigh) &&
    !(inRange plan.saveByte plan.terminalLow plan.terminalHigh) &&
    !(inRange plan.saveByte plan.continuationLow plan.continuationHigh) &&
    !(inRange plan.unknownByte plan.terminalLow plan.terminalHigh) &&
    !(inRange plan.unknownByte plan.continuationLow plan.continuationHigh) &&
    decide (plan.saveByte != plan.unknownByte) &&
    decide (0 < plan.terminalRadix) &&
    decide (0 < plan.continuationRadix)

inductive DecoderPhase where
  | betweenUses
  | openIndex (accumulator : UInt64)
  | justCompletedUse
  deriving DecidableEq, Repr

structure DecoderState where
  phase : DecoderPhase := .betweenUses
  deriving DecidableEq, Repr

def initialState : DecoderState := {}

def DecoderState.accumulator (state : DecoderState) : UInt64 :=
  match state.phase with
  | .openIndex accumulator => accumulator
  | .betweenUses | .justCompletedUse => 0

/-- The largest natural number represented by the generated C carrier. -/
def uint64MaxNat : Nat := 18446744073709551615

/-- Checked unsigned multiply-add.  The successful result is the ordinary
mathematical value because the guard excludes modular wraparound. -/
def checkedMulAdd (radix : UInt32) (accumulator : UInt64)
    (digit : UInt64) : Option UInt64 :=
  let value := radix.toNat * accumulator.toNat + digit.toNat
  if radix = 0 || uint64MaxNat < value then none
  else some (UInt64.ofNat value)

/-- Feed one byte.  `none` means a continuation consumed the byte without
emitting an instruction. -/
def feed (plan : Plan) (state : DecoderState) (byte : UInt8) :
    Except DecodeError (Option Instruction × DecoderState) :=
  if inRange byte plan.terminalLow plan.terminalHigh then
    let digit := UInt64.ofNat
      ((byte - plan.terminalLow).toNat + plan.terminalDigitBias.toNat)
    match checkedMulAdd plan.terminalRadix state.accumulator digit with
    | none => .error .overflow
    | some index =>
        .ok (some (.use index), { phase := .justCompletedUse })
  else if inRange byte plan.continuationLow plan.continuationHigh then
    let digit := UInt64.ofNat
      ((byte - plan.continuationLow).toNat +
        plan.continuationDigitBias.toNat)
    match checkedMulAdd plan.continuationRadix state.accumulator digit with
    | none => .error .overflow
    | some accumulator => .ok (none, { phase := .openIndex accumulator })
  else if byte = plan.saveByte then
    match state.phase with
    | .openIndex _ => .error .saveInsideIndex
    | .betweenUses => .error .saveWithoutUse
    | .justCompletedUse =>
        let nextPhase := match plan.savePlacement with
          | .immediatelyAfterUse => .betweenUses
          | .repeatableAfterUse => .justCompletedUse
        .ok (some .save, { phase := nextPhase })
  else if byte = plan.unknownByte then
    match state.phase with
    | .openIndex _ => .error .unknownInsideIndex
    | .betweenUses | .justCompletedUse =>
        .ok (some .unknown, initialState)
  else
    .error (.invalidByte byte)

/-- Streaming execution from an explicit accumulator state. -/
def runBytesFrom (plan : Plan) :
    DecoderState -> List UInt8 ->
      Except DecodeError (List Instruction × DecoderState)
  | state, [] => .ok ([], state)
  | state, byte :: bytes =>
      match feed plan state byte with
      | .error failure => .error failure
      | .ok (event, nextState) =>
          match runBytesFrom plan nextState bytes with
          | .error failure => .error failure
          | .ok (tail, finalState) =>
              .ok (event.toList ++ tail, finalState)

/-- Decoding concatenated byte lists is exactly sequential state threading. -/
theorem runBytesFrom_append
    (plan : Plan) (state : DecoderState) (left right : List UInt8) :
    runBytesFrom plan state (left ++ right) =
      match runBytesFrom plan state left with
      | .error failure => .error failure
      | .ok (leftInstructions, nextState) =>
          match runBytesFrom plan nextState right with
          | .error failure => .error failure
          | .ok (rightInstructions, finalState) =>
              .ok (leftInstructions ++ rightInstructions, finalState) := by
  induction left generalizing state with
  | nil =>
      simp only [List.nil_append, runBytesFrom]
      cases resultEq : runBytesFrom plan state right with
      | error failure => rfl
      | ok result =>
          obtain ⟨instructions, finalState⟩ := result
          rfl
  | cons byte bytes inductionHypothesis =>
      simp only [List.cons_append, runBytesFrom]
      cases feedEq : feed plan state byte with
      | error failure => rfl
      | ok emitted =>
          obtain ⟨event, nextState⟩ := emitted
          simp only
          rw [inductionHypothesis]
          cases leftEq : runBytesFrom plan nextState bytes with
          | error failure => rfl
          | ok leftResult =>
              obtain ⟨leftInstructions, afterLeft⟩ := leftResult
              cases rightEq : runBytesFrom plan afterLeft right with
              | error failure => simp only [rightEq]
              | ok rightResult =>
                  obtain ⟨rightInstructions, finalState⟩ := rightResult
                  simp only [rightEq, List.append_assoc]

/-- Streaming execution over lexical chunks; the accumulator deliberately
crosses chunk boundaries. -/
def runChunksFrom (plan : Plan) :
    DecoderState -> List (List UInt8) ->
      Except DecodeError (List Instruction × DecoderState)
  | state, [] => .ok ([], state)
  | state, chunk :: chunks =>
      match runBytesFrom plan state chunk with
      | .error failure => .error failure
      | .ok (head, nextState) =>
          match runChunksFrom plan nextState chunks with
          | .error failure => .error failure
          | .ok (tail, finalState) => .ok (head ++ tail, finalState)

/-- Chunked streaming is observationally identical to flattening the source
before decoding. -/
theorem runChunksFrom_eq_flatten
    (plan : Plan) (state : DecoderState) (chunks : List (List UInt8)) :
    runChunksFrom plan state chunks =
      runBytesFrom plan state chunks.flatten := by
  induction chunks generalizing state with
  | nil => rfl
  | cons chunk chunks inductionHypothesis =>
      simp only [runChunksFrom, List.flatten_cons]
      rw [runBytesFrom_append]
      cases headEq : runBytesFrom plan state chunk with
      | error failure => rfl
      | ok headResult =>
          obtain ⟨head, nextState⟩ := headResult
          simp only
          rw [inductionHypothesis]

/-- Complete compilation validates the alphabet and rejects an open numeric
index at end of input. -/
def compile? (plan : Plan) (chunks : List (List UInt8)) :
    Except DecodeError (List Instruction) := do
  if plan.valid != true then throw .invalidPlan
  let (instructions, finalState) <- runChunksFrom plan initialState chunks
  match finalState.phase with
  | .openIndex _ => throw .openIndexAtEnd
  | .betweenUses | .justCompletedUse => pure instructions

/-- A successfully compiled instruction list is retained with the exact
equation produced by its local recognizer. -/
structure AdmittedProgram where
  plan : Plan
  chunks : List (List UInt8)
  instructions : List Instruction
  compile_eq : compile? plan chunks = .ok instructions
  deriving DecidableEq, Repr

def admit? (plan : Plan) (chunks : List (List UInt8)) :
    Option AdmittedProgram :=
  match accepted : compile? plan chunks with
  | .error _ => none
  | .ok instructions => some ⟨plan, chunks, instructions, accepted⟩

/-- The compiled instruction carrier is a reusable realization of the exact
stream decoder observation. -/
def indexedInstructionRealization :
    Mettapedia.GSLT.SimpleRealization
      AdmittedProgram (List Instruction)
      (Except DecodeError (List Instruction)) where
  compile := fun _ admitted => admitted.instructions
  observeSource := fun _ admitted => compile? admitted.plan admitted.chunks
  observeArtifact := fun _ instructions => .ok instructions
  adequate := by
    intro _ admitted
    exact admitted.compile_eq.symm

def sourceByteClassifications (admitted : AdmittedProgram) : Nat :=
  admitted.chunks.flatten.length

def compiledByteClassifications (_admitted : AdmittedProgram) : Nat := 0

theorem compiledByteClassifications_le_source
    (admitted : AdmittedProgram) :
    compiledByteClassifications admitted <=
      sourceByteClassifications admitted := by
  simp [compiledByteClassifications]

theorem compiledByteClassifications_lt_source_of_nonempty
    (admitted : AdmittedProgram) (nonempty : admitted.chunks.flatten ≠ []) :
    compiledByteClassifications admitted <
      sourceByteClassifications admitted := by
  have positive : 0 < admitted.chunks.flatten.length :=
    List.length_pos_iff.mpr nonempty
  simpa [compiledByteClassifications, sourceByteClassifications] using positive

/-! ## Structurally independent generated alphabets -/

private def proofDagPlan : Plan :=
  { terminalLow := 65
    terminalHigh := 84
    continuationLow := 85
    continuationHigh := 89
    saveByte := 90
    unknownByte := 63
    terminalRadix := 20
    terminalDigitBias := 0
    continuationRadix := 5
    continuationDigitBias := 1
    savePlacement := .immediatelyAfterUse }

/-- One continuation digit may cross a chunk boundary before termination. -/
example : compile? proofDagPlan [[85], [65]] = .ok [.use 20] := by
  decide

/-- Save and unknown are ordinary generic instruction classes. -/
example : compile? proofDagPlan [[65, 90, 63]] =
    .ok [.use 0, .save, .unknown] := by
  decide

example : compile? proofDagPlan [[65, 85, 90]] =
    .error .saveInsideIndex := by
  decide

example : compile? proofDagPlan [[65, 90, 90]] =
    .error .saveWithoutUse := by
  decide

example : compile? proofDagPlan [[85, 63]] =
    .error .unknownInsideIndex := by
  decide

private def parserIndexPlan : Plan :=
  { terminalLow := 0
    terminalHigh := 9
    continuationLow := 10
    continuationHigh := 19
    saveByte := 20
    unknownByte := 21
    terminalRadix := 10
    terminalDigitBias := 0
    continuationRadix := 10
    continuationDigitBias := 0
    savePlacement := .immediatelyAfterUse }

/-- A differently shaped parser-table alphabet uses the same decoder. -/
example : compile? parserIndexPlan [[11, 2]] = .ok [.use 12] := by
  decide

/-- A control byte cannot interrupt an open numeric index. -/
example : compile? parserIndexPlan [[11, 20]] =
    .error .saveInsideIndex := by
  decide

/-- An alphabet with overlapping numeric classes fails admission. -/
example :
    ({ parserIndexPlan with continuationLow := 9 }.valid) = false := by
  decide

/-- A complete stream cannot end inside an index. -/
example : compile? parserIndexPlan [[11]] = .error .openIndexAtEnd := by
  decide

/-- Openness is structural even when the continuation digit itself is zero. -/
example : compile? parserIndexPlan [[10]] = .error .openIndexAtEnd := by
  decide

end Mettapedia.GSLT.LanguageDef.IndexedInstructionStreamCompilation
