import Mathlib.Tactic
import Mettapedia.Sequences.OEIS.Basic

/-!
# The Kolakoski sequence

This module constructs the sequence whose alternating runs have lengths equal
to the sequence itself.  The sequence was discussed by Rufus Oldenburger in
1939 and is named after William George Kolakoski; the OEIS entry A000002 was
contributed by N. J. A. Sloane.
-/

namespace Mettapedia.Sequences.OEIS.Kolakoski

/-- The symbol in the zero-based run numbered `run`: one, two, one, two, ... -/
def runSymbol (run : Nat) : Nat := if run % 2 = 0 then 1 else 2

@[simp] theorem runSymbol_zero : runSymbol 0 = 1 := by
  simp [runSymbol]

@[simp] theorem runSymbol_one : runSymbol 1 = 2 := by
  simp [runSymbol]

theorem runSymbol_binary (run : Nat) :
    runSymbol run = 1 ∨ runSymbol run = 2 := by
  unfold runSymbol
  split <;> simp_all

/-- A finite expansion into alternating runs with lengths supplied by `a`. -/
def runPrefix (a : Nat → Nat) (runs : Nat) : List Nat :=
  (List.range runs).flatMap fun run => List.replicate (a run) (runSymbol run)

/--
A sequence is a Kolakoski fixed point when it is binary and every finite
run-length expansion agrees with the corresponding prefix of the sequence.
-/
def IsRunLengthFixedPoint (a : Nat → Nat) : Prop :=
  (∀ n, a n = 1 ∨ a n = 2) ∧
  ∀ runs index (inBounds : index < (runPrefix a runs).length),
    (runPrefix a runs)[index] = a index

/-- A finite generator state whose next unread position is in bounds. -/
structure BuildState (readIndex : Nat) where
  word : List Nat
  readable : readIndex < word.length
  binary : ∀ value, value ∈ word → value = 1 ∨ value = 2

/-- Append the run described at the current readable position. -/
def BuildState.advance {readIndex : Nat}
    (state : BuildState readIndex) : BuildState (readIndex + 1) := by
  let count := state.word.get ⟨readIndex, state.readable⟩
  let nextWord := state.word ++ List.replicate count (runSymbol readIndex)
  have countBinary : count = 1 ∨ count = 2 :=
    state.binary count (List.get_mem state.word ⟨readIndex, state.readable⟩)
  have countPositive : 1 ≤ count := by omega
  refine
    { word := nextWord
      readable := ?_
      binary := ?_ }
  · simp only [nextWord, List.length_append, List.length_replicate]
    have readable := state.readable
    omega
  · intro value membership
    simp only [nextWord, List.mem_append, List.mem_replicate] at membership
    rcases membership with oldMembership | ⟨_, rfl⟩
    · exact state.binary value oldMembership
    · exact runSymbol_binary readIndex

/-- Successive finite prefixes, beginning with the first two complete runs. -/
def build : (steps : Nat) → BuildState (steps + 2)
  | 0 =>
      { word := [1, 2, 2]
        readable := by decide
        binary := by simp }
  | steps + 1 => (build steps).advance

def word (steps : Nat) : List Nat := (build steps).word

/-- The canonical sequence read at the stage where its position becomes active. -/
def value : Nat → Nat
  | 0 => 1
  | 1 => 2
  | index + 2 => (build index).word.get ⟨index + 2, (build index).readable⟩

@[simp] theorem value_zero : value 0 = 1 := rfl

@[simp] theorem value_one : value 1 = 2 := rfl

theorem word_succ (steps : Nat) :
    word (steps + 1) = word steps ++
      List.replicate (value (steps + 2)) (runSymbol (steps + 2)) := by
  rfl

theorem word_prefix_succ (steps : Nat) : word steps <+: word (steps + 1) := by
  rw [word_succ]
  exact List.prefix_append _ _

theorem word_prefix_of_le {first last : Nat} (order : first ≤ last) :
    word first <+: word last := by
  induction last with
  | zero =>
      have : first = 0 := by omega
      subst first
      simp
  | succ last inductionHypothesis =>
      by_cases atEnd : first = last + 1
      · subst first
        simp
      · exact (inductionHypothesis (by omega)).trans (word_prefix_succ last)

theorem word_get_eq_value (steps index : Nat)
    (inBounds : index < (word steps).length) :
    (word steps)[index] = value index := by
  cases index with
  | zero =>
      have prefixProof := word_prefix_of_le (Nat.zero_le steps)
      have firstValue := prefixProof.getElem (by decide : 0 < (word 0).length)
      simpa [word, build, value] using firstValue.symm
  | succ index =>
      cases index with
      | zero =>
          have prefixProof := word_prefix_of_le (Nat.zero_le steps)
          have secondValue := prefixProof.getElem (by decide : 1 < (word 0).length)
          simpa [word, build, value] using secondValue.symm
      | succ index =>
          let sourceStep := index
          by_cases sourceBefore : sourceStep ≤ steps
          · have prefixProof := word_prefix_of_le sourceBefore
            have equality := prefixProof.getElem (build sourceStep).readable
            simpa [sourceStep, word, value] using equality.symm
          · have stepsBefore : steps < sourceStep := by omega
            have prefixProof := word_prefix_of_le (Nat.le_of_lt stepsBefore)
            have equality := prefixProof.getElem inBounds
            simpa [sourceStep, word, value] using equality

theorem runPrefix_succ (a : Nat → Nat) (runs : Nat) :
    runPrefix a (runs + 1) = runPrefix a runs ++
      List.replicate (a runs) (runSymbol runs) := by
  simp [runPrefix, List.range_succ, List.flatMap_append]

theorem runPrefix_value_eq_word (steps : Nat) :
    runPrefix value (steps + 2) = word steps := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      rw [show steps + 1 + 2 = (steps + 2) + 1 by omega]
      rw [runPrefix_succ, inductionHypothesis, word_succ]

theorem value_binary (index : Nat) : value index = 1 ∨ value index = 2 := by
  cases index with
  | zero => simp
  | succ index =>
      cases index with
      | zero => simp
      | succ index =>
          exact (build index).binary _
            (List.get_mem (build index).word ⟨index + 2, (build index).readable⟩)

/-- The constructed sequence is extensionally its own alternating run-length encoding. -/
theorem value_isRunLengthFixedPoint : IsRunLengthFixedPoint value := by
  constructor
  · exact value_binary
  · intro runs index inBounds
    by_cases small : runs < 2
    · rcases (show runs = 0 ∨ runs = 1 by omega) with rfl | rfl
      · simp [runPrefix] at inBounds
      · have indexZero : index = 0 := by
          simp [runPrefix, value, runSymbol] at inBounds
          omega
        subst index
        rfl
    · let steps := runs - 2
      have runsShape : runs = steps + 2 := by
        dsimp [steps]
        omega
      have wordBounds : index < (word steps).length := by
        rw [← runPrefix_value_eq_word]
        simpa [runsShape] using inBounds
      have wordValue := word_get_eq_value steps index wordBounds
      simpa only [runsShape, runPrefix_value_eq_word] using wordValue

/-- Number of symbols preceding the zero-based run `run`. -/
def runStart (run : Nat) : Nat := (runPrefix value run).length

@[simp] theorem runStart_zero : runStart 0 = 0 := by
  simp [runStart, runPrefix]

theorem runStart_succ (run : Nat) :
    runStart (run + 1) = runStart run + value run := by
  simp [runStart, runPrefix_succ]

theorem runStart_lower_bound (run : Nat) : run ≤ runStart run := by
  induction run with
  | zero => simp
  | succ run inductionHypothesis =>
      rw [show run + 1 = run + 1 by rfl, runStart_succ]
      have positive : 1 ≤ value run := by
        rcases value_binary run with result | result <;> omega
      omega

/-- Every position inside a declared run has that run's alternating symbol. -/
theorem value_on_run (run offset : Nat) (inside : offset < value run) :
    value (runStart run + offset) = runSymbol run := by
  have inPrefix : runStart run + offset < (runPrefix value (run + 1)).length := by
    rw [runPrefix_succ]
    simp only [List.length_append, List.length_replicate]
    simp only [runStart]
    omega
  have fixedPoint := value_isRunLengthFixedPoint.2 (run + 1)
    (runStart run + offset) inPrefix
  have segmentValue :
      (runPrefix value (run + 1))[runStart run + offset] = runSymbol run := by
    let earlier := runPrefix value run
    let block := List.replicate (value run) (runSymbol run)
    have expansion : runPrefix value (run + 1) = earlier ++ block := by
      simpa [earlier, block] using runPrefix_succ value run
    have appendBound : earlier.length + offset < (earlier ++ block).length := by
      simp only [List.length_append, block, List.length_replicate]
      omega
    have appendValue :
        (earlier ++ block)[earlier.length + offset]'appendBound = runSymbol run := by
      simp [block]
    simpa only [expansion, runStart, earlier] using appendValue
  exact fixedPoint.symm.trans segmentValue

/-- The run and within-run offset of a positive sequence position. -/
structure RunCursor (position : Nat) where
  run : Nat
  offset : Nat
  runPositive : 1 ≤ run
  offsetBound : offset < value run
  positionEquation : position = runStart run + offset

/-- Advance one sequence position, either within a run or to the next run. -/
def RunCursor.advance {position : Nat}
    (cursor : RunCursor position) : RunCursor (position + 1) := by
  have positionEquation := cursor.positionEquation
  if continues : cursor.offset + 1 < value cursor.run then
    exact
      { run := cursor.run
        offset := cursor.offset + 1
        runPositive := cursor.runPositive
        offsetBound := continues
        positionEquation := by omega }
  else
    have offsetBound := cursor.offsetBound
    have filled : cursor.offset + 1 = value cursor.run := by
      omega
    exact
      { run := cursor.run + 1
        offset := 0
        runPositive := by omega
        offsetBound := by
          rcases value_binary (cursor.run + 1) with result | result <;> omega
        positionEquation := by
          rw [runStart_succ]
          omega }

/-- Cursor for the next symbol after zero-based output position `step`. -/
def cursor : (step : Nat) → RunCursor (step + 1)
  | 0 =>
      { run := 1
        offset := 0
        runPositive := by omega
        offsetBound := by simp [value_one]
        positionEquation := by simp [runStart, runPrefix, value, runSymbol] }
  | step + 1 => (cursor step).advance

theorem cursor_run_le_position (step : Nat) :
    (cursor step).run ≤ step + 1 := by
  have startBound := runStart_lower_bound (cursor step).run
  have position := (cursor step).positionEquation
  omega

theorem advance_run_le_succ {position : Nat} (current : RunCursor position) :
    current.advance.run ≤ current.run + 1 := by
  unfold RunCursor.advance
  split <;> simp

theorem cursor_run_le_current {step : Nat} (positive : 1 ≤ step) :
    (cursor step).run ≤ step := by
  induction step with
  | zero => omega
  | succ step inductionHypothesis =>
      by_cases stepZero : step = 0
      · subst step
        norm_num [cursor, RunCursor.advance, value_one]
      · have previous := inductionHypothesis (by omega)
        have advance := advance_run_le_succ (cursor step)
        simpa [cursor] using le_trans advance (by omega : (cursor step).run + 1 ≤ step + 1)

theorem value_at_cursor (step : Nat) :
    value (step + 1) = runSymbol (cursor step).run := by
  have positionValue := congrArg value (cursor step).positionEquation
  exact positionValue.trans (value_on_run _ _ (cursor step).offsetBound)

/-- Zero-based bit representation of the binary sequence. -/
def bit (index : Nat) : Nat := value index - 1

theorem bit_binary (index : Nat) : bit index = 0 ∨ bit index = 1 := by
  rcases value_binary index with result | result <;> simp [bit, result]

theorem bit_add_one (index : Nat) : bit index + 1 = value index := by
  rcases value_binary index with result | result <;> simp [bit, result]

/-- One exactly when the next sequence position starts a new run. -/
def boundaryBit (step : Nat) : Nat :=
  if (cursor step).offset = 0 then 1 else 0

theorem boundaryBit_binary (step : Nat) :
    boundaryBit step = 0 ∨ boundaryBit step = 1 := by
  unfold boundaryBit
  split <;> simp

/-- Packed cursor used by the reported list-state program. -/
def packedCursor (step : Nat) : Nat :=
  2 * (step + 1 - (cursor step).run) + boundaryBit step

theorem packedCursor_div_two (step : Nat) :
    packedCursor step / 2 = step + 1 - (cursor step).run := by
  rcases boundaryBit_binary step with boundary | boundary <;>
    simp only [packedCursor, boundary] <;> omega

theorem runSymbol_eq_mod_add_one (run : Nat) :
    runSymbol run = run % 2 + 1 := by
  have remainderBound := Nat.mod_lt run (by omega : 0 < 2)
  unfold runSymbol
  split <;> omega

theorem bit_on_run (run offset : Nat) (inside : offset < value run) :
    bit (runStart run + offset) = run % 2 := by
  rw [bit, value_on_run run offset inside, runSymbol_eq_mod_add_one]
  omega

theorem bit_at_cursor (step : Nat) :
    bit (step + 1) = (cursor step).run % 2 := by
  rw [bit, value_at_cursor, runSymbol_eq_mod_add_one]
  omega

/-- The packed parity bit advances the alternating run symbol exactly. -/
theorem bit_succ (step : Nat) :
    (boundaryBit step + bit step) % 2 = bit (step + 1) := by
  cases step with
  | zero => norm_num [boundaryBit, cursor, bit, value]
  | succ step =>
      let current := cursor (step + 1)
      have runPositive := current.runPositive
      have positionEquation := current.positionEquation
      have nextBit : bit (step + 1 + 1) = current.run % 2 := by
        simpa [current, add_assoc] using bit_at_cursor (step + 1)
      by_cases atBoundary : current.offset = 0
      · have predecessorShape : current.run - 1 + 1 = current.run :=
          Nat.sub_add_cancel runPositive
        have predecessorPositive : 1 ≤ value (current.run - 1) := by
          rcases value_binary (current.run - 1) with result | result <;> omega
        have currentIndex : step + 1 =
            runStart (current.run - 1) + (value (current.run - 1) - 1) := by
          rw [← predecessorShape, runStart_succ] at positionEquation
          omega
        have withinPredecessor :
            value (current.run - 1) - 1 < value (current.run - 1) := by
          omega
        have currentBit : bit (step + 1) = (current.run - 1) % 2 := by
          have indexEquality := congrArg bit currentIndex
          exact indexEquality.trans
            (bit_on_run _ _ withinPredecessor)
        have predecessorRemainder := Nat.mod_lt (current.run - 1) (by omega : 0 < 2)
        have currentRemainder := Nat.mod_lt current.run (by omega : 0 < 2)
        have parityStep : (1 + (current.run - 1) % 2) % 2 = current.run % 2 := by
          omega
        simpa [boundaryBit, current, atBoundary, currentBit, nextBit,
          add_assoc] using parityStep
      · have offsetPositive : 1 ≤ current.offset := by omega
        have offsetBound := current.offsetBound
        have currentIndex : step + 1 =
            runStart current.run + (current.offset - 1) := by
          omega
        have withinCurrent : current.offset - 1 < value current.run := by
          omega
        have currentBit : bit (step + 1) = current.run % 2 := by
          have indexEquality := congrArg bit currentIndex
          exact indexEquality.trans (bit_on_run _ _ withinCurrent)
        simp [boundaryBit, current, atBoundary, currentBit, nextBit, add_assoc]

/--
The value selected from the packed history at one machine step.  The initial
state contains only the pointer and the first bit, so its zero-pop lookup reads
the pointer itself; every later step reads the bit at the active run.
-/
def cursorIncrement (step : Nat) : Nat :=
  if step = 0 then 1 else bit (cursor step).run

theorem cursorIncrement_binary (step : Nat) :
    cursorIncrement step = 0 ∨ cursorIncrement step = 1 := by
  by_cases stepZero : step = 0
  · simp [cursorIncrement, stepZero]
  · simp only [cursorIncrement, stepZero, if_false]
    exact bit_binary (cursor step).run

/-- The packed cursor update is exactly the value selected from its history. -/
theorem packedCursor_succ (step : Nat) :
    packedCursor (step + 1) =
      packedCursor step + cursorIncrement step := by
  by_cases stepZero : step = 0
  · subst step
    decide
  simp only [cursorIncrement, stepZero, if_false]
  let current := cursor step
  have runBound : current.run ≤ step := by
    simpa [current] using cursor_run_le_current (step := step) (by omega)
  have offsetBound := current.offsetBound
  have valueBinary := value_binary current.run
  change
    2 * ((step + 1) + 1 - current.advance.run) +
        (if current.advance.offset = 0 then 1 else 0) =
      2 * (step + 1 - current.run) +
        (if current.offset = 0 then 1 else 0) +
        (value current.run - 1)
  by_cases continues : current.offset + 1 < value current.run
  · have advanceRun : current.advance.run = current.run := by
      simp [RunCursor.advance, continues]
    have advanceOffset : current.advance.offset = current.offset + 1 := by
      simp [RunCursor.advance, continues]
    rw [advanceRun, advanceOffset]
    rcases valueBinary with valueOne | valueTwo
    · omega
    · have offsetZero : current.offset = 0 := by omega
      simp [offsetZero, valueTwo]
      omega
  · have advanceRun : current.advance.run = current.run + 1 := by
      simp [RunCursor.advance, continues]
    have advanceOffset : current.advance.offset = 0 := by
      simp [RunCursor.advance, continues]
    rw [advanceRun, advanceOffset]
    have filled : current.offset + 1 = value current.run := by omega
    rcases valueBinary with valueOne | valueTwo
    · have offsetZero : current.offset = 0 := by omega
      simp [offsetZero, valueOne]
    · have offsetOne : current.offset = 1 := by omega
      simp [offsetOne, valueTwo]

/-- The low bit of the packed state is the next sequence bit. -/
theorem packedCursor_add_bit_mod_two (step : Nat) :
    (packedCursor step + bit step) % 2 = bit (step + 1) := by
  have transition := bit_succ step
  rcases boundaryBit_binary step with boundary | boundary <;>
    simp only [packedCursor, boundary] at transition ⊢ <;> omega

#print axioms value_on_run
#print axioms value_at_cursor
#print axioms bit_succ
#print axioms packedCursor_succ

/-- Source coordinates for OEIS A000002 in the pinned snapshot. -/
def sourceA000002 : EntrySource where
  oeisId := "A000002"
  snapshotRevision := "a6e0f22854cc1c307da428e9d6295093781df7fa"
  entrySha256 := "aec5dbb47113a73fc27ffd20bc7da1e29e5e2383b502d756de3ea0f5e6f83986"
  offset := 1

/-- OEIS A000002, with the public one-based index translated to `value`. -/
def specA000002 : SequenceSpec where
  offset := 1
  Domain := fun index => 1 ≤ index
  value := fun index => Int.ofNat (value (index.toNat - 1))

def formalizationA000002 : Formalization where
  source := sourceA000002
  spec := specA000002
  offsetMatches := rfl

#print axioms value_isRunLengthFixedPoint

end Mettapedia.Sequences.OEIS.Kolakoski
