import Mettapedia.GSLT.LanguageDef.C1AdditionCorrectness
import Mettapedia.GSLT.LanguageDef.WaltersZantemaDAMultiplication

/-!
# Universal loop facts for the C1 digit-multiplication program

The target program is the fixed grade-school loop from
`WaltersZantemaDAToC1`.  Its bounded digit table is extracted from the supplied
closed DA presentation.  The results below keep the table-row receipts and
source-rule origins in the target execution trace.
-/

namespace Mettapedia.GSLT.LanguageDef.C1MultiplicationCorrectness

set_option maxHeartbeats 1000000

open Mettapedia.GSLT.LanguageDef.C1DigitMachine
open Mettapedia.GSLT.LanguageDef.C1AdditionCorrectness
open Mettapedia.GSLT.LanguageDef.WaltersZantemaDAToC1

def multiplicationSchema (outputLimit : Nat) : Schema := {
  radix := 2
  radixAtLeastTwo := by decide
  bufferLimit := 3
  registerLimit := 10
  outputLimit
}

/-- State at the head of the inner loop (program counter 8). -/
def innerConfig (table : FiniteTable) (left right output : List Nat)
    (outer leftDigit inner rightDigit outputIndex accumulated carry digit fuel : Nat)
    (receipt : Receipt) : Config :=
  .running (multiplicationProgram table) 8 [left, right, output]
    [outer, left.length, right.length, leftDigit, inner, rightDigit,
      outputIndex, accumulated, carry, digit]
    fuel receipt

/-- State at the head of the outer loop (program counter 3). -/
def outerConfig (table : FiniteTable) (left right output : List Nat)
    (outer leftDigit inner rightDigit outputIndex accumulated carry digit fuel : Nat)
    (receipt : Receipt) : Config :=
  .running (multiplicationProgram table) 3 [left, right, output]
    [outer, left.length, right.length, leftDigit, inner, rightDigit,
      outputIndex, accumulated, carry, digit]
    fuel receipt

def activeInnerEvents (rowIndex : Nat) (origins : List String) : Receipt := [
  .execute 8 "right-active?",
  .execute 9 "read-right",
  .execute 10 "read-accumulated",
  .execute 11 "rules-4+6+8+10",
  .tableRow 11 rowIndex origins,
  .execute 12 "write-product-digit",
  .execute 13 "next-right-digit",
  .execute 14 "next-output-digit"]

def carryInnerEvents (rowIndex : Nat) (origins : List String) : Receipt := [
  .execute 8 "right-active?",
  .execute 15 "carry-active?",
  .execute 16 "right-zero",
  .execute 17 "read-carry-target",
  .execute 11 "rules-4+6+8+10",
  .tableRow 11 rowIndex origins,
  .execute 12 "write-product-digit",
  .execute 13 "next-right-digit",
  .execute 14 "next-output-digit"]

def finishInnerEvents : Receipt := [
  .execute 8 "right-active?",
  .execute 15 "carry-active?",
  .execute 18 "next-left-digit"]

def startOuterEvents : Receipt := [
  .execute 3 "left-active?",
  .execute 4 "read-left",
  .execute 5 "inner-index-zero",
  .execute 6 "output-index",
  .execute 7 "carry-zero"]

def terminalOuterEvents : Receipt := [
  .execute 3 "left-active?",
  .execute 19 "return"]

def multiplicationInitializationEvents : Receipt := [
  .execute 0 "left-length",
  .execute 1 "right-length",
  .execute 2 "outer-index-zero"]

theorem runSteps_succ_of_step {schema : Schema} {source target : Config}
    (steps : Nat) (step : step? schema source = some target) :
    runSteps schema (steps + 1) source = runSteps schema steps target := by
  simp [runSteps, step]

/-! Keep instruction fetch symbolic in machine proofs.  These equations avoid
expanding the complete twenty-cell program at every step. -/

@[simp] theorem multiplicationProgram_at_0 (table : FiniteTable) :
    at? (multiplicationProgram table) 0 =
      some ⟨"left-length", .length 0 1 1⟩ := rfl
@[simp] theorem multiplicationProgram_at_1 (table : FiniteTable) :
    at? (multiplicationProgram table) 1 =
      some ⟨"right-length", .length 1 2 2⟩ := rfl
@[simp] theorem multiplicationProgram_at_2 (table : FiniteTable) :
    at? (multiplicationProgram table) 2 =
      some ⟨"outer-index-zero", .set 0 0 3⟩ := rfl
@[simp] theorem multiplicationProgram_at_3 (table : FiniteTable) :
    at? (multiplicationProgram table) 3 =
      some ⟨"left-active?", .branchLt 0 1 4 19⟩ := rfl
@[simp] theorem multiplicationProgram_at_4 (table : FiniteTable) :
    at? (multiplicationProgram table) 4 =
      some ⟨"read-left", .readOrZero 0 0 3 5⟩ := rfl
@[simp] theorem multiplicationProgram_at_5 (table : FiniteTable) :
    at? (multiplicationProgram table) 5 =
      some ⟨"inner-index-zero", .set 4 0 6⟩ := rfl
@[simp] theorem multiplicationProgram_at_6 (table : FiniteTable) :
    at? (multiplicationProgram table) 6 =
      some ⟨"output-index", .copy 0 6 7⟩ := rfl
@[simp] theorem multiplicationProgram_at_7 (table : FiniteTable) :
    at? (multiplicationProgram table) 7 =
      some ⟨"carry-zero", .set 8 0 8⟩ := rfl
@[simp] theorem multiplicationProgram_at_8 (table : FiniteTable) :
    at? (multiplicationProgram table) 8 =
      some ⟨"right-active?", .branchLt 4 2 9 15⟩ := rfl
@[simp] theorem multiplicationProgram_at_9 (table : FiniteTable) :
    at? (multiplicationProgram table) 9 =
      some ⟨"read-right", .readOrZero 1 4 5 10⟩ := rfl
@[simp] theorem multiplicationProgram_at_10 (table : FiniteTable) :
    at? (multiplicationProgram table) 10 =
      some ⟨"read-accumulated", .readOrZero 2 6 7 11⟩ := rfl
@[simp] theorem multiplicationProgram_at_11 (table : FiniteTable) :
    at? (multiplicationProgram table) 11 =
      some ⟨"rules-4+6+8+10", .lookup [3, 5, 7, 8] [9, 8] table 12⟩ := rfl
@[simp] theorem multiplicationProgram_at_12 (table : FiniteTable) :
    at? (multiplicationProgram table) 12 =
      some ⟨"write-product-digit", .write 2 6 9 13⟩ := rfl
@[simp] theorem multiplicationProgram_at_13 (table : FiniteTable) :
    at? (multiplicationProgram table) 13 =
      some ⟨"next-right-digit", .increment 4 14⟩ := rfl
@[simp] theorem multiplicationProgram_at_14 (table : FiniteTable) :
    at? (multiplicationProgram table) 14 =
      some ⟨"next-output-digit", .increment 6 8⟩ := rfl
@[simp] theorem multiplicationProgram_at_15 (table : FiniteTable) :
    at? (multiplicationProgram table) 15 =
      some ⟨"carry-active?", .branchEq 8 0 18 16⟩ := rfl
@[simp] theorem multiplicationProgram_at_16 (table : FiniteTable) :
    at? (multiplicationProgram table) 16 =
      some ⟨"right-zero", .set 5 0 17⟩ := rfl
@[simp] theorem multiplicationProgram_at_17 (table : FiniteTable) :
    at? (multiplicationProgram table) 17 =
      some ⟨"read-carry-target", .readOrZero 2 6 7 11⟩ := rfl
@[simp] theorem multiplicationProgram_at_18 (table : FiniteTable) :
    at? (multiplicationProgram table) 18 =
      some ⟨"next-left-digit", .increment 0 3⟩ := rfl
@[simp] theorem multiplicationProgram_at_19 (table : FiniteTable) :
    at? (multiplicationProgram table) 19 =
      some ⟨"return", .returnBuffer 2⟩ := rfl

/-- The actual multiplication table structurally extracted from the supplied
radix-two DA presentation. -/
def radixTwoMultiplicationTable : FiniteTable :=
  ((inspect? (WaltersZantemaDA.language WaltersZantemaDA.radixTwo)).bind
    fun profile => do
      let additionTable <- additionTableFromProfile? profile
      multiplicationTableFromProfile? profile additionTable).getD []

/-- An independently written finite statement of the table that must be
extracted from DA Rules 4, 6, 8, and 10.  Origin strings are observations, not
selectors. -/
def radixTwoExpectedMultiplicationTable : FiniteTable := [
  ⟨[0, 0, 0, 0], [0, 0],
    ["8:wz-da:6[radix=2,0]", "15:wz-da:10[radix=2,0,0]",
      "3:wz-da:4[radix=2,0,0]", "3:wz-da:4[radix=2,0,0]"]⟩,
  ⟨[0, 0, 0, 1], [1, 0],
    ["8:wz-da:6[radix=2,0]", "15:wz-da:10[radix=2,0,0]",
      "3:wz-da:4[radix=2,0,0]", "4:wz-da:4[radix=2,0,1]"]⟩,
  ⟨[0, 0, 1, 0], [1, 0],
    ["8:wz-da:6[radix=2,0]", "15:wz-da:10[radix=2,0,0]",
      "4:wz-da:4[radix=2,0,1]", "5:wz-da:4[radix=2,1,0]"]⟩,
  ⟨[0, 0, 1, 1], [0, 1],
    ["8:wz-da:6[radix=2,0]", "15:wz-da:10[radix=2,0,0]",
      "4:wz-da:4[radix=2,0,1]", "6:wz-da:4[radix=2,1,1]",
      "3:wz-da:4[radix=2,0,0]", "11:wz-da:8[radix=2,0]"]⟩,
  ⟨[0, 1, 0, 0], [0, 0],
    ["8:wz-da:6[radix=2,0]", "16:wz-da:10[radix=2,0,1]",
      "3:wz-da:4[radix=2,0,0]", "3:wz-da:4[radix=2,0,0]"]⟩,
  ⟨[0, 1, 0, 1], [1, 0],
    ["8:wz-da:6[radix=2,0]", "16:wz-da:10[radix=2,0,1]",
      "3:wz-da:4[radix=2,0,0]", "4:wz-da:4[radix=2,0,1]"]⟩,
  ⟨[0, 1, 1, 0], [1, 0],
    ["8:wz-da:6[radix=2,0]", "16:wz-da:10[radix=2,0,1]",
      "4:wz-da:4[radix=2,0,1]", "5:wz-da:4[radix=2,1,0]"]⟩,
  ⟨[0, 1, 1, 1], [0, 1],
    ["8:wz-da:6[radix=2,0]", "16:wz-da:10[radix=2,0,1]",
      "4:wz-da:4[radix=2,0,1]", "6:wz-da:4[radix=2,1,1]",
      "3:wz-da:4[radix=2,0,0]", "11:wz-da:8[radix=2,0]"]⟩,
  ⟨[1, 0, 0, 0], [0, 0],
    ["9:wz-da:6[radix=2,1]", "17:wz-da:10[radix=2,1,0]",
      "3:wz-da:4[radix=2,0,0]", "3:wz-da:4[radix=2,0,0]"]⟩,
  ⟨[1, 0, 0, 1], [1, 0],
    ["9:wz-da:6[radix=2,1]", "17:wz-da:10[radix=2,1,0]",
      "3:wz-da:4[radix=2,0,0]", "4:wz-da:4[radix=2,0,1]"]⟩,
  ⟨[1, 0, 1, 0], [1, 0],
    ["9:wz-da:6[radix=2,1]", "17:wz-da:10[radix=2,1,0]",
      "4:wz-da:4[radix=2,0,1]", "5:wz-da:4[radix=2,1,0]"]⟩,
  ⟨[1, 0, 1, 1], [0, 1],
    ["9:wz-da:6[radix=2,1]", "17:wz-da:10[radix=2,1,0]",
      "4:wz-da:4[radix=2,0,1]", "6:wz-da:4[radix=2,1,1]",
      "3:wz-da:4[radix=2,0,0]", "11:wz-da:8[radix=2,0]"]⟩,
  ⟨[1, 1, 0, 0], [1, 0],
    ["9:wz-da:6[radix=2,1]", "18:wz-da:10[radix=2,1,1]",
      "5:wz-da:4[radix=2,1,0]", "5:wz-da:4[radix=2,1,0]"]⟩,
  ⟨[1, 1, 0, 1], [0, 1],
    ["9:wz-da:6[radix=2,1]", "18:wz-da:10[radix=2,1,1]",
      "5:wz-da:4[radix=2,1,0]", "6:wz-da:4[radix=2,1,1]",
      "3:wz-da:4[radix=2,0,0]", "11:wz-da:8[radix=2,0]"]⟩,
  ⟨[1, 1, 1, 0], [0, 1],
    ["9:wz-da:6[radix=2,1]", "18:wz-da:10[radix=2,1,1]",
      "6:wz-da:4[radix=2,1,1]", "3:wz-da:4[radix=2,0,0]",
      "11:wz-da:8[radix=2,0]", "3:wz-da:4[radix=2,0,0]",
      "5:wz-da:4[radix=2,1,0]"]⟩,
  ⟨[1, 1, 1, 1], [1, 1],
    ["9:wz-da:6[radix=2,1]", "18:wz-da:10[radix=2,1,1]",
      "6:wz-da:4[radix=2,1,1]", "3:wz-da:4[radix=2,0,0]",
      "11:wz-da:8[radix=2,0]", "4:wz-da:4[radix=2,0,1]",
      "5:wz-da:4[radix=2,1,0]"]⟩]

theorem radixTwoMultiplicationTable_eq_expected :
    radixTwoMultiplicationTable = radixTwoExpectedMultiplicationTable := by
  decide +kernel

theorem radixTwo_compiles_to_multiplication_table :
    compileMultiplication?
        (WaltersZantemaDA.language WaltersZantemaDA.radixTwo) =
      some (multiplicationProgram radixTwoMultiplicationTable) := by
  decide +kernel

/-- Exact semantic requirements on a bounded digit-accumulation table. -/
structure BinaryMultiplicationTable (table : FiniteTable) : Prop where
  sound : ∀ {first second accumulated carry digit nextCarry rowIndex : Nat}
      {origins : List String},
    lookupTable? [first, second, accumulated, carry] table =
        some (rowIndex,
          ⟨[first, second, accumulated, carry], [digit, nextCarry], origins⟩) →
    first < 2 → second < 2 → accumulated < 2 → carry < 2 →
    digit < 2 ∧ nextCarry < 2 ∧
      first * second + accumulated + carry = digit + 2 * nextCarry
  complete : ∀ (first second accumulated carry : Nat),
    first < 2 → second < 2 → accumulated < 2 → carry < 2 →
    ∃ rowIndex digit nextCarry origins,
      lookupTable? [first, second, accumulated, carry] table =
        some (rowIndex,
          ⟨[first, second, accumulated, carry], [digit, nextCarry], origins⟩)

theorem radixTwoMultiplicationTable_binary :
    BinaryMultiplicationTable radixTwoMultiplicationTable := by
  rw [radixTwoMultiplicationTable_eq_expected]
  constructor
  · intro first second accumulated carry digit nextCarry rowIndex origins
      lookup firstValid secondValid accumulatedValid carryValid
    interval_cases first <;> interval_cases second <;>
      interval_cases accumulated <;> interval_cases carry <;>
      simp [radixTwoExpectedMultiplicationTable, lookupTable?,
        lookupTableFrom?] at lookup <;> omega
  · intro first second accumulated carry firstValid secondValid
      accumulatedValid carryValid
    interval_cases first <;> interval_cases second <;>
      interval_cases accumulated <;> interval_cases carry <;>
      simp [radixTwoExpectedMultiplicationTable, lookupTable?, lookupTableFrom?]

/-- The write operation used by the inner-loop invariant.  It is the exact
non-faulting branch of the C1 `write` instruction. -/
def writeDigit? (digits : List Nat) (index digit : Nat) : Option (List Nat) :=
  if digits.length < index then none
  else if index = digits.length then some (digits ++ [digit])
  else replaceAt? digits index digit

theorem at?_length (values : List α) : at? values values.length = none := by
  rw [at?_eq_head?_drop]
  simp

theorem at?_append_cons_length (leading tail : List α) (value : α) :
    at? (leading ++ value :: tail) leading.length = some value := by
  rw [at?_eq_head?_drop]
  simp

theorem replaceAt?_append_cons_length (leading tail : List α)
    (oldValue newValue : α) :
    replaceAt? (leading ++ oldValue :: tail) leading.length newValue =
      some (leading ++ newValue :: tail) := by
  induction leading with
  | nil => rfl
  | cons head leading inductionHypothesis =>
      simp [replaceAt?, inductionHypothesis]

theorem writeDigit?_append_cons (leading tail : List Nat)
    (oldDigit newDigit : Nat) :
    writeDigit? (leading ++ oldDigit :: tail) leading.length newDigit =
      some (leading ++ newDigit :: tail) := by
  simp [writeDigit?, replaceAt?_append_cons_length]

theorem writeDigit?_append_end (leading : List Nat) (digit : Nat) :
    writeDigit? leading leading.length digit = some (leading ++ [digit]) := by
  simp [writeDigit?]

theorem writeDigit?_some_index_le {digits written : List Nat}
    {index digit : Nat} (write : writeDigit? digits index digit = some written) :
    index ≤ digits.length := by
  by_contra notLe
  have sparse : digits.length < index := Nat.lt_of_not_ge notLe
  simp [writeDigit?, sparse] at write

theorem digitsInRange_append {left right : List Nat}
    (leftRange : WaltersZantemaDA.DigitsInRange WaltersZantemaDA.radixTwo left)
    (rightRange : WaltersZantemaDA.DigitsInRange WaltersZantemaDA.radixTwo right) :
    WaltersZantemaDA.DigitsInRange WaltersZantemaDA.radixTwo (left ++ right) := by
  intro digit member
  rcases List.mem_append.mp member with member | member
  · exact leftRange digit member
  · exact rightRange digit member

theorem digitsInRange_firstInvalidDigit?_none {digits : List Nat}
    (range : WaltersZantemaDA.DigitsInRange WaltersZantemaDA.radixTwo digits) :
    firstInvalidDigit? 2 digits = none := by
  induction digits with
  | nil => rfl
  | cons digit digits inductionHypothesis =>
      have digitValid : digit < 2 := range digit (by simp)
      have tailRange :
          WaltersZantemaDA.DigitsInRange WaltersZantemaDA.radixTwo digits := by
        intro tailDigit member
        exact range tailDigit (List.mem_cons_of_mem digit member)
      simp [firstInvalidDigit?, digitValid, inductionHypothesis tailRange]

theorem firstInvalidDigit?_none_digitsInRange {digits : List Nat}
    (valid : firstInvalidDigit? 2 digits = none) :
    WaltersZantemaDA.DigitsInRange WaltersZantemaDA.radixTwo digits := by
  induction digits with
  | nil => simp [WaltersZantemaDA.DigitsInRange]
  | cons digit digits inductionHypothesis =>
      by_cases digitValid : digit < 2
      · have tailValid : firstInvalidDigit? 2 digits = none := by
          simpa [firstInvalidDigit?, digitValid] using valid
        have tailRange := inductionHypothesis tailValid
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · simpa [WaltersZantemaDA.radixTwo] using digitValid
        · exact tailRange value member
      · simp [firstInvalidDigit?, digitValid] at valid

theorem digitsInRange_take {digits : List Nat} (count : Nat)
    (range : WaltersZantemaDA.DigitsInRange WaltersZantemaDA.radixTwo digits) :
    WaltersZantemaDA.DigitsInRange WaltersZantemaDA.radixTwo
      (digits.take count) := by
  intro digit member
  exact range digit (List.mem_of_mem_take member)

theorem digitsInRange_drop {digits : List Nat} (count : Nat)
    (range : WaltersZantemaDA.DigitsInRange WaltersZantemaDA.radixTwo digits) :
    WaltersZantemaDA.DigitsInRange WaltersZantemaDA.radixTwo
      (digits.drop count) := by
  intro digit member
  exact range digit (List.mem_of_mem_drop member)

/-- A complete inner-loop trace for one source digit.  It records the exact
target events as well as the arithmetic fact justified by each target write. -/
inductive InnerTrace (table : FiniteTable) (first : Nat) :
    List Nat → List Nat → Nat → Nat → List Nat → Receipt → Nat → Prop where
  | done {output : List Nat} {position : Nat} :
      InnerTrace table first [] output position 0 output finishInnerEvents 3
  | active
      {second accumulated carry digit nextCarry rowIndex position : Nat}
      {right output written result : List Nat} {origins : List String}
      {events : Receipt} {steps : Nat}
      (outputRead : (at? output position).getD 0 = accumulated)
      (lookup : lookupTable? [first, second, accumulated, carry] table =
        some (rowIndex,
          ⟨[first, second, accumulated, carry], [digit, nextCarry], origins⟩))
      (secondValid : second < 2) (accumulatedValid : accumulated < 2)
      (digitValid : digit < 2)
      (write : writeDigit? output position digit = some written)
      (writeDenotes :
        WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo written +
            2 ^ position * accumulated =
          WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo output +
            2 ^ position * digit)
      (writtenValid : firstInvalidDigit? 2 written = none)
      (lengthMono : output.length ≤ written.length)
      (positionWritten : position < written.length)
      (rest : InnerTrace table first right written (position + 1) nextCarry
        result events steps) :
      InnerTrace table first (second :: right) output position carry result
        (activeInnerEvents rowIndex origins ++ events) (7 + steps)
  | carry
      {accumulated carry digit nextCarry rowIndex position : Nat}
      {output written result : List Nat} {origins : List String}
      {events : Receipt} {steps : Nat}
      (carryActive : carry ≠ 0)
      (outputRead : (at? output position).getD 0 = accumulated)
      (lookup : lookupTable? [first, 0, accumulated, carry] table =
        some (rowIndex,
          ⟨[first, 0, accumulated, carry], [digit, nextCarry], origins⟩))
      (accumulatedValid : accumulated < 2) (digitValid : digit < 2)
      (write : writeDigit? output position digit = some written)
      (writeDenotes :
        WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo written +
            2 ^ position * accumulated =
          WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo output +
            2 ^ position * digit)
      (writtenValid : firstInvalidDigit? 2 written = none)
      (lengthMono : output.length ≤ written.length)
      (positionWritten : position < written.length)
      (rest : InnerTrace table first [] written (position + 1) nextCarry
        result events steps) :
      InnerTrace table first [] output position carry result
        (carryInnerEvents rowIndex origins ++ events) (8 + steps)

theorem InnerTrace.output_length_le {table : FiniteTable} {first : Nat}
    {right output result : List Nat} {position carry : Nat}
    {events : Receipt} {steps : Nat}
    (trace : InnerTrace table first right output position carry result events steps) :
    output.length ≤ result.length := by
  induction trace with
  | done => exact Nat.le_refl _
  | active outputRead lookup secondValid accumulatedValid digitValid write
      writeDenotes writtenValid lengthMono positionWritten rest
      inductionHypothesis =>
      exact Nat.le_trans lengthMono inductionHypothesis
  | carry carryActive outputRead lookup accumulatedValid digitValid write
      writeDenotes writtenValid lengthMono positionWritten rest
      inductionHypothesis =>
      exact Nat.le_trans lengthMono inductionHypothesis

theorem InnerTrace.position_lt_result_of_right {table : FiniteTable}
    {first second position carry : Nat} {right output result : List Nat}
    {events : Receipt} {steps : Nat}
    (trace : InnerTrace table first (second :: right) output position carry
      result events steps) :
    position < result.length := by
  cases trace with
  | active outputRead lookup secondValid accumulatedValid digitValid write
      writeDenotes writtenValid lengthMono positionWritten rest =>
      exact lt_of_lt_of_le positionWritten (InnerTrace.output_length_le rest)

theorem InnerTrace.resultValid {table : FiniteTable} {first position carry : Nat}
    {right output result : List Nat} {events : Receipt} {steps : Nat}
    (trace : InnerTrace table first right output position carry result events steps)
    (outputValid : firstInvalidDigit? 2 output = none) :
    firstInvalidDigit? 2 result = none := by
  induction trace with
  | done => exact outputValid
  | active outputRead lookup secondValid accumulatedValid digitValid write
      writeDenotes writtenValid lengthMono positionWritten rest
      inductionHypothesis =>
      exact inductionHypothesis writtenValid
  | carry carryActive outputRead lookup accumulatedValid digitValid write
      writeDenotes writtenValid lengthMono positionWritten rest
      inductionHypothesis =>
      exact inductionHypothesis writtenValid

theorem InnerTrace.denotes {table : FiniteTable} {first position carry : Nat}
    {right output result : List Nat} {events : Receipt} {steps : Nat}
    (tableCorrect : BinaryMultiplicationTable table)
    (firstValid : first < 2)
    (trace : InnerTrace table first right output position carry result events steps)
    (carryValid : carry < 2) :
    WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo result =
      WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo output +
        2 ^ position *
          (first * WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo right +
            carry) := by
  induction trace with
  | done => simp [WaltersZantemaDA.decodeDigits]
  | active outputRead lookup secondValid accumulatedValid digitValid write
      writeDenotes writtenValid lengthMono positionWritten rest
      inductionHypothesis =>
      rename_i second accumulated currentCarry digit nextCarry rowIndex
        currentPosition rightTail currentOutput written result origins
        restEvents restSteps
      obtain ⟨_, nextCarryValid, arithmetic⟩ :=
        tableCorrect.sound lookup firstValid secondValid accumulatedValid carryValid
      have restDenotes := inductionHypothesis nextCarryValid
      have scaledArithmetic := congrArg
        (fun (value : Nat) => 2 ^ currentPosition * value)
        arithmetic
      have writeDenotes' :
          Nat.ofDigits 2 written + 2 ^ currentPosition * accumulated =
            Nat.ofDigits 2 currentOutput + 2 ^ currentPosition * digit := by
        simpa [WaltersZantemaDA.decodeDigits, WaltersZantemaDA.radixTwo] using
          writeDenotes
      have augmented :
          WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo result +
              2 ^ currentPosition * accumulated =
            (WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo currentOutput +
              2 ^ currentPosition *
                (first * WaltersZantemaDA.decodeDigits
                  WaltersZantemaDA.radixTwo (second :: rightTail) + currentCarry)) +
              2 ^ currentPosition * accumulated := by
        rw [restDenotes]
        simp only [WaltersZantemaDA.decodeDigits,
          WaltersZantemaDA.radixTwo, Nat.ofDigits_cons, pow_succ']
        calc
          Nat.ofDigits 2 written +
                2 * 2 ^ currentPosition * (first * Nat.ofDigits 2 rightTail + nextCarry) +
                2 ^ currentPosition * accumulated =
              (Nat.ofDigits 2 written + 2 ^ currentPosition * accumulated) +
                2 ^ currentPosition *
                  (2 * (first * Nat.ofDigits 2 rightTail + nextCarry)) := by ring
          _ = (Nat.ofDigits 2 currentOutput + 2 ^ currentPosition * digit) +
                2 ^ currentPosition *
                  (2 * (first * Nat.ofDigits 2 rightTail + nextCarry)) := by
              rw [writeDenotes']
          _ = Nat.ofDigits 2 currentOutput +
                2 ^ currentPosition * (digit + 2 * nextCarry) +
                2 ^ currentPosition * (2 * first * Nat.ofDigits 2 rightTail) := by ring
          _ = Nat.ofDigits 2 currentOutput +
                2 ^ currentPosition * (first * second + accumulated + currentCarry) +
                2 ^ currentPosition * (2 * first * Nat.ofDigits 2 rightTail) := by
              rw [← scaledArithmetic]
          _ = (Nat.ofDigits 2 currentOutput +
                2 ^ currentPosition *
                  (first * (second + 2 * Nat.ofDigits 2 rightTail) + currentCarry)) +
                2 ^ currentPosition * accumulated := by ring
      exact Nat.add_right_cancel augmented
  | carry carryActive outputRead lookup accumulatedValid digitValid write
      writeDenotes writtenValid lengthMono positionWritten rest
      inductionHypothesis =>
      rename_i accumulated currentCarry digit nextCarry rowIndex currentPosition
        currentOutput written result origins restEvents restSteps
      obtain ⟨_, nextCarryValid, arithmetic⟩ :=
        tableCorrect.sound lookup firstValid (by omega) accumulatedValid carryValid
      have restDenotes := inductionHypothesis nextCarryValid
      have scaledArithmetic := congrArg
        (fun (value : Nat) => 2 ^ currentPosition * value)
        arithmetic
      have writeDenotes' :
          Nat.ofDigits 2 written + 2 ^ currentPosition * accumulated =
            Nat.ofDigits 2 currentOutput + 2 ^ currentPosition * digit := by
        simpa [WaltersZantemaDA.decodeDigits, WaltersZantemaDA.radixTwo] using
          writeDenotes
      have augmented :
          WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo result +
              2 ^ currentPosition * accumulated =
            (WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo currentOutput +
              2 ^ currentPosition * currentCarry) +
              2 ^ currentPosition * accumulated := by
        rw [restDenotes]
        simp only [WaltersZantemaDA.decodeDigits,
          WaltersZantemaDA.radixTwo, Nat.ofDigits_nil, Nat.mul_zero,
          Nat.zero_add, pow_succ']
        calc
          Nat.ofDigits 2 written + 2 * 2 ^ currentPosition * nextCarry +
                2 ^ currentPosition * accumulated =
              (Nat.ofDigits 2 written + 2 ^ currentPosition * accumulated) +
                2 ^ currentPosition * (2 * nextCarry) := by ring
          _ = (Nat.ofDigits 2 currentOutput + 2 ^ currentPosition * digit) +
                2 ^ currentPosition * (2 * nextCarry) := by rw [writeDenotes']
          _ = Nat.ofDigits 2 currentOutput +
                2 ^ currentPosition * (digit + 2 * nextCarry) := by ring
          _ = Nat.ofDigits 2 currentOutput +
                2 ^ currentPosition * (first * 0 + accumulated + currentCarry) := by
              rw [← scaledArithmetic]
          _ = (Nat.ofDigits 2 currentOutput + 2 ^ currentPosition * currentCarry) +
                2 ^ currentPosition * accumulated := by ring
      simpa [WaltersZantemaDA.decodeDigits, WaltersZantemaDA.radixTwo] using
        Nat.add_right_cancel augmented

theorem exists_carry_trace_from_split {table : FiniteTable} {first : Nat}
    (tableCorrect : BinaryMultiplicationTable table) (firstValid : first < 2)
    (leading trailing : List Nat)
    (leadingRange : WaltersZantemaDA.DigitsInRange
      WaltersZantemaDA.radixTwo leading)
    (trailingRange : WaltersZantemaDA.DigitsInRange
      WaltersZantemaDA.radixTwo trailing)
    {carry : Nat} (carryValid : carry < 2) :
    ∃ result events steps,
      InnerTrace table first [] (leading ++ trailing) leading.length carry
        result events steps := by
  induction trailing generalizing leading carry with
  | nil =>
      by_cases carryZero : carry = 0
      · subst carry
        exact ⟨leading, finishInnerEvents, 3, by simpa using
          (InnerTrace.done (table := table) (first := first)
            (output := leading) (position := leading.length))⟩
      · obtain ⟨rowIndex, digit, nextCarry, origins, lookup⟩ :=
          tableCorrect.complete first 0 0 carry firstValid (by omega)
            (by omega) carryValid
        obtain ⟨digitValid, nextCarryValid, arithmetic⟩ :=
          tableCorrect.sound lookup firstValid (by omega) (by omega) carryValid
        have nextCarryZero : nextCarry = 0 := by omega
        subst nextCarry
        have writtenRange : WaltersZantemaDA.DigitsInRange
            WaltersZantemaDA.radixTwo (leading ++ [digit]) := by
          apply digitsInRange_append leadingRange
          intro value member
          simp only [List.mem_singleton] at member
          subst value
          exact digitValid
        have writeDenotes :
            WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo
                (leading ++ [digit]) + 2 ^ leading.length * 0 =
              WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo leading +
                2 ^ leading.length * digit := by
          simp [WaltersZantemaDA.decodeDigits, WaltersZantemaDA.radixTwo,
            Nat.ofDigits_append]
        have trace : InnerTrace table first [] leading leading.length carry
            (leading ++ [digit])
            (carryInnerEvents rowIndex origins ++ finishInnerEvents) (8 + 3) :=
          .carry carryZero (by simp [at?_length]) lookup (by omega)
            digitValid (writeDigit?_append_end leading digit) writeDenotes
            (digitsInRange_firstInvalidDigit?_none writtenRange) (by simp)
            (by simp) (.done)
        refine ⟨leading ++ [digit],
          carryInnerEvents rowIndex origins ++ finishInnerEvents, 8 + 3, ?_⟩
        simpa using trace
  | cons accumulated trailing inductionHypothesis =>
      by_cases carryZero : carry = 0
      · subst carry
        exact ⟨leading ++ accumulated :: trailing, finishInnerEvents, 3,
          .done⟩
      · have accumulatedValid : accumulated < 2 :=
          trailingRange accumulated (by simp)
        have tailRange : WaltersZantemaDA.DigitsInRange
            WaltersZantemaDA.radixTwo trailing := by
          intro value member
          exact trailingRange value (List.mem_cons_of_mem accumulated member)
        obtain ⟨rowIndex, digit, nextCarry, origins, lookup⟩ :=
          tableCorrect.complete first 0 accumulated carry firstValid (by omega)
            accumulatedValid carryValid
        obtain ⟨digitValid, nextCarryValid, arithmetic⟩ :=
          tableCorrect.sound lookup firstValid (by omega) accumulatedValid carryValid
        have nextLeadingRange : WaltersZantemaDA.DigitsInRange
            WaltersZantemaDA.radixTwo (leading ++ [digit]) := by
          apply digitsInRange_append leadingRange
          intro value member
          simp only [List.mem_singleton] at member
          subst value
          exact digitValid
        obtain ⟨result, events, steps, rest⟩ :=
          inductionHypothesis (leading ++ [digit]) nextLeadingRange tailRange
            nextCarryValid
        have rest' : InnerTrace table first []
            (leading ++ digit :: trailing) (leading.length + 1) nextCarry
            result events steps := by
          simpa [List.append_assoc] using rest
        have writeDenotes :
            WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo
                (leading ++ digit :: trailing) +
                2 ^ leading.length * accumulated =
              WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo
                  (leading ++ accumulated :: trailing) +
                2 ^ leading.length * digit := by
          simp only [WaltersZantemaDA.decodeDigits, WaltersZantemaDA.radixTwo,
            Nat.ofDigits_append, Nat.ofDigits_cons]
          ring
        have writtenRange := digitsInRange_append nextLeadingRange tailRange
        refine ⟨result, carryInnerEvents rowIndex origins ++ events,
          8 + steps, ?_⟩
        exact .carry carryZero
          (by simp [at?_append_cons_length]) lookup accumulatedValid digitValid
          (writeDigit?_append_cons leading trailing accumulated digit)
          writeDenotes (by
            apply digitsInRange_firstInvalidDigit?_none
            simpa [List.append_assoc] using writtenRange)
          (by simp) (by simp) rest'

theorem exists_inner_trace_from_split {table : FiniteTable} {first : Nat}
    (tableCorrect : BinaryMultiplicationTable table) (firstValid : first < 2)
    (right leading trailing : List Nat)
    (rightRange : WaltersZantemaDA.DigitsInRange
      WaltersZantemaDA.radixTwo right)
    (leadingRange : WaltersZantemaDA.DigitsInRange
      WaltersZantemaDA.radixTwo leading)
    (trailingRange : WaltersZantemaDA.DigitsInRange
      WaltersZantemaDA.radixTwo trailing)
    {carry : Nat} (carryValid : carry < 2) :
    ∃ result events steps,
      InnerTrace table first right (leading ++ trailing) leading.length carry
        result events steps := by
  induction right generalizing leading trailing carry with
  | nil =>
      exact exists_carry_trace_from_split tableCorrect firstValid leading trailing
        leadingRange trailingRange carryValid
  | cons second right inductionHypothesis =>
      have secondValid : second < 2 := rightRange second (by simp)
      have rightTailRange : WaltersZantemaDA.DigitsInRange
          WaltersZantemaDA.radixTwo right := by
        intro value member
        exact rightRange value (List.mem_cons_of_mem second member)
      cases trailing with
      | nil =>
          obtain ⟨rowIndex, digit, nextCarry, origins, lookup⟩ :=
            tableCorrect.complete first second 0 carry firstValid secondValid
              (by omega) carryValid
          obtain ⟨digitValid, nextCarryValid, arithmetic⟩ :=
            tableCorrect.sound lookup firstValid secondValid (by omega) carryValid
          have nextLeadingRange : WaltersZantemaDA.DigitsInRange
              WaltersZantemaDA.radixTwo (leading ++ [digit]) := by
            apply digitsInRange_append leadingRange
            intro value member
            simp only [List.mem_singleton] at member
            subst value
            exact digitValid
          have emptyRange : WaltersZantemaDA.DigitsInRange
              WaltersZantemaDA.radixTwo ([] : List Nat) := by
            simp [WaltersZantemaDA.DigitsInRange]
          obtain ⟨result, events, steps, rest⟩ :=
            inductionHypothesis (leading ++ [digit]) [] rightTailRange
              nextLeadingRange emptyRange nextCarryValid
          have rest' : InnerTrace table first right (leading ++ [digit])
              (leading.length + 1) nextCarry result events steps := by
            simpa [List.append_assoc] using rest
          have writeDenotes :
              WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo
                  (leading ++ [digit]) + 2 ^ leading.length * 0 =
                WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo leading +
                  2 ^ leading.length * digit := by
            simp [WaltersZantemaDA.decodeDigits, WaltersZantemaDA.radixTwo,
              Nat.ofDigits_append]
          have trace : InnerTrace table first (second :: right) leading
              leading.length carry result
              (activeInnerEvents rowIndex origins ++ events) (7 + steps) :=
            .active (by simp [at?_length]) lookup secondValid (by omega)
              digitValid (writeDigit?_append_end leading digit) writeDenotes
              (digitsInRange_firstInvalidDigit?_none nextLeadingRange)
              (by simp) (by simp) rest'
          exact ⟨result, activeInnerEvents rowIndex origins ++ events,
            7 + steps, by simpa using trace⟩
      | cons accumulated trailing =>
          have accumulatedValid : accumulated < 2 :=
            trailingRange accumulated (by simp)
          have trailingTailRange : WaltersZantemaDA.DigitsInRange
              WaltersZantemaDA.radixTwo trailing := by
            intro value member
            exact trailingRange value (List.mem_cons_of_mem accumulated member)
          obtain ⟨rowIndex, digit, nextCarry, origins, lookup⟩ :=
            tableCorrect.complete first second accumulated carry firstValid
              secondValid accumulatedValid carryValid
          obtain ⟨digitValid, nextCarryValid, arithmetic⟩ :=
            tableCorrect.sound lookup firstValid secondValid accumulatedValid
              carryValid
          have nextLeadingRange : WaltersZantemaDA.DigitsInRange
              WaltersZantemaDA.radixTwo (leading ++ [digit]) := by
            apply digitsInRange_append leadingRange
            intro value member
            simp only [List.mem_singleton] at member
            subst value
            exact digitValid
          obtain ⟨result, events, steps, rest⟩ :=
            inductionHypothesis (leading ++ [digit]) trailing rightTailRange
              nextLeadingRange trailingTailRange nextCarryValid
          have rest' : InnerTrace table first right
              (leading ++ digit :: trailing) (leading.length + 1) nextCarry
              result events steps := by
            simpa [List.append_assoc] using rest
          have writeDenotes :
              WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo
                  (leading ++ digit :: trailing) +
                  2 ^ leading.length * accumulated =
                WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo
                    (leading ++ accumulated :: trailing) +
                  2 ^ leading.length * digit := by
            simp only [WaltersZantemaDA.decodeDigits, WaltersZantemaDA.radixTwo,
              Nat.ofDigits_append, Nat.ofDigits_cons]
            ring
          have writtenRange :=
            digitsInRange_append nextLeadingRange trailingTailRange
          have trace : InnerTrace table first (second :: right)
              (leading ++ accumulated :: trailing) leading.length carry result
              (activeInnerEvents rowIndex origins ++ events) (7 + steps) :=
            .active (by simp [at?_append_cons_length]) lookup secondValid
              accumulatedValid digitValid
              (writeDigit?_append_cons leading trailing accumulated digit)
              writeDenotes (by
                apply digitsInRange_firstInvalidDigit?_none
                simpa [List.append_assoc] using writtenRange)
              (by simp) (by simp) rest'
          exact ⟨result, activeInnerEvents rowIndex origins ++ events,
            7 + steps, trace⟩

theorem inner_branch_active_step
    (table : FiniteTable) (left right output : List Nat)
    (outer first inner rightDigit outputIndex accumulated carry digit fuel
      outputLimit : Nat) (active : inner < right.length) (receipt : Receipt) :
    step? (multiplicationSchema outputLimit)
        (innerConfig table left right output outer first inner rightDigit
          outputIndex accumulated carry digit (fuel + 1) receipt) =
      some (.running (multiplicationProgram table) 9 [left, right, output]
        [outer, left.length, right.length, first, inner, rightDigit,
          outputIndex, accumulated, carry, digit]
        fuel (receipt ++ [.execute 8 "right-active?"])) := by
  simp [step?, innerConfig, multiplicationSchema, executeInstruction,
    boundedRegister?, appendExecute, active, at?]

theorem inner_read_right_step
    (table : FiniteTable) (left right output : List Nat)
    (outer first inner second oldRightDigit outputIndex accumulated carry digit
      fuel outputLimit : Nat)
    (rightAt : at? right inner = some second) (secondValid : second < 2)
    (receipt : Receipt) :
    step? (multiplicationSchema outputLimit)
        (.running (multiplicationProgram table) 9 [left, right, output]
          [outer, left.length, right.length, first, inner, oldRightDigit,
            outputIndex, accumulated, carry, digit]
          (fuel + 1) receipt) =
      some (.running (multiplicationProgram table) 10 [left, right, output]
        [outer, left.length, right.length, first, inner, second,
          outputIndex, accumulated, carry, digit]
        fuel (receipt ++ [.execute 9 "read-right"])) := by
  simp [step?, multiplicationSchema, executeInstruction, boundedBuffer?,
    boundedRegister?, replaceBoundedRegister?, continueWithRegisters,
    appendExecute, rightAt, replaceAt?, at?]
  all_goals omega

theorem inner_read_accumulated_step
    (table : FiniteTable) (left right output : List Nat)
    (outer first inner second outputIndex oldAccumulated accumulated carry digit
      fuel outputLimit : Nat)
    (outputRead : (at? output outputIndex).getD 0 = accumulated)
    (accumulatedValid : accumulated < 2) (receipt : Receipt) :
    step? (multiplicationSchema outputLimit)
        (.running (multiplicationProgram table) 10 [left, right, output]
          [outer, left.length, right.length, first, inner, second,
            outputIndex, oldAccumulated, carry, digit]
          (fuel + 1) receipt) =
      some (.running (multiplicationProgram table) 11 [left, right, output]
        [outer, left.length, right.length, first, inner, second,
          outputIndex, accumulated, carry, digit]
        fuel (receipt ++ [.execute 10 "read-accumulated"])) := by
  simp [step?, multiplicationSchema, executeInstruction, boundedBuffer?,
    boundedRegister?, replaceBoundedRegister?, continueWithRegisters,
    appendExecute, outputRead, replaceAt?, at?]
  all_goals omega

theorem inner_lookup_step
    (table : FiniteTable) (left right output : List Nat)
    (outer first inner second outputIndex accumulated carry oldDigit digit nextCarry
      fuel outputLimit rowIndex : Nat) (origins : List String)
    (lookup : lookupTable? [first, second, accumulated, carry] table =
      some (rowIndex,
        ⟨[first, second, accumulated, carry], [digit, nextCarry], origins⟩))
    (receipt : Receipt) :
    step? (multiplicationSchema outputLimit)
        (.running (multiplicationProgram table) 11 [left, right, output]
          [outer, left.length, right.length, first, inner, second,
            outputIndex, accumulated, carry, oldDigit]
          (fuel + 1) receipt) =
      some (.running (multiplicationProgram table) 12 [left, right, output]
        [outer, left.length, right.length, first, inner, second,
          outputIndex, accumulated, nextCarry, digit]
        fuel (receipt ++ [.execute 11 "rules-4+6+8+10",
          .tableRow 11 rowIndex origins])) := by
  simp [step?, multiplicationSchema, executeInstruction, boundedRegister?,
    replaceBoundedRegister?, firstMissingRegister?, readRegisters?,
    writeRegisters?, continueWithRegisters, appendExecute, lookup,
    replaceAt?, at?]

theorem inner_write_step
    (table : FiniteTable) (left right output written : List Nat)
    (outer first inner second outputIndex accumulated nextCarry digit fuel
      outputLimit : Nat)
    (digitValid : digit < 2) (notSparse : outputIndex ≤ output.length)
    (write : writeDigit? output outputIndex digit = some written)
    (outputRoom : written.length ≤ outputLimit) (receipt : Receipt) :
    step? (multiplicationSchema outputLimit)
        (.running (multiplicationProgram table) 12 [left, right, output]
          [outer, left.length, right.length, first, inner, second,
            outputIndex, accumulated, nextCarry, digit]
          (fuel + 1) receipt) =
      some (.running (multiplicationProgram table) 13 [left, right, written]
        [outer, left.length, right.length, first, inner, second,
          outputIndex, accumulated, nextCarry, digit]
        fuel (receipt ++ [.execute 12 "write-product-digit"])) := by
  have notSparse' : ¬ output.length < outputIndex := not_lt_of_ge notSparse
  by_cases atEnd : outputIndex = output.length
  · subst outputIndex
    have writtenEq : written = output ++ [digit] := by
      simpa [writeDigit?] using write.symm
    subst written
    have digitOk : ¬ 2 ≤ digit := Nat.not_le.mpr digitValid
    have outputHasRoom : ¬ outputLimit ≤ output.length := by
      simp at outputRoom
      omega
    simp [step?, multiplicationSchema, executeInstruction, boundedBuffer?,
      boundedRegister?, replaceBoundedBuffer?, continueWithBuffers,
      appendExecute, digitOk, outputHasRoom, replaceAt?, at?]
  · have replace : replaceAt? output outputIndex digit = some written := by
      simpa [writeDigit?, notSparse', atEnd] using write
    have digitOk : ¬ 2 ≤ digit := Nat.not_le.mpr digitValid
    have room : ¬ outputLimit < written.length := not_lt_of_ge outputRoom
    simp [step?, multiplicationSchema, executeInstruction, boundedBuffer?,
      boundedRegister?, replaceBoundedBuffer?, continueWithBuffers,
      appendExecute, replace, digitOk, room, notSparse', atEnd,
      replaceAt?, at?]

theorem inner_increment_right_step
    (table : FiniteTable) (left right output : List Nat)
    (outer first inner second outputIndex accumulated nextCarry digit fuel
      outputLimit : Nat) (receipt : Receipt) :
    step? (multiplicationSchema outputLimit)
        (.running (multiplicationProgram table) 13 [left, right, output]
          [outer, left.length, right.length, first, inner, second,
            outputIndex, accumulated, nextCarry, digit]
          (fuel + 1) receipt) =
      some (.running (multiplicationProgram table) 14 [left, right, output]
        [outer, left.length, right.length, first, inner + 1, second,
          outputIndex, accumulated, nextCarry, digit]
        fuel (receipt ++ [.execute 13 "next-right-digit"])) := by
  simp [step?, multiplicationSchema, executeInstruction, boundedRegister?,
    replaceBoundedRegister?, continueWithRegisters, appendExecute,
    replaceAt?, at?]

theorem inner_increment_output_step
    (table : FiniteTable) (left right output : List Nat)
    (outer first inner second outputIndex accumulated nextCarry digit fuel
      outputLimit : Nat) (receipt : Receipt) :
    step? (multiplicationSchema outputLimit)
        (.running (multiplicationProgram table) 14 [left, right, output]
          [outer, left.length, right.length, first, inner, second,
            outputIndex, accumulated, nextCarry, digit]
          (fuel + 1) receipt) =
      some (innerConfig table left right output outer first inner second
        (outputIndex + 1) accumulated nextCarry digit fuel
        (receipt ++ [.execute 14 "next-output-digit"])) := by
  simp [step?, innerConfig, multiplicationSchema, executeInstruction,
    boundedRegister?, replaceBoundedRegister?, continueWithRegisters,
    appendExecute, replaceAt?, at?]

theorem inner_branch_done_step
    (table : FiniteTable) (left right output : List Nat)
    (outer first inner rightDigit outputIndex accumulated carry digit fuel
      outputLimit : Nat) (rightDone : right.length ≤ inner) (receipt : Receipt) :
    step? (multiplicationSchema outputLimit)
        (innerConfig table left right output outer first inner rightDigit
          outputIndex accumulated carry digit (fuel + 1) receipt) =
      some (.running (multiplicationProgram table) 15 [left, right, output]
        [outer, left.length, right.length, first, inner, rightDigit,
          outputIndex, accumulated, carry, digit]
        fuel (receipt ++ [.execute 8 "right-active?"])) := by
  have rightAbsent : ¬ inner < right.length := not_lt_of_ge rightDone
  simp [step?, innerConfig, multiplicationSchema, executeInstruction,
    boundedRegister?, appendExecute, rightAbsent, at?]

theorem inner_branch_carry_step
    (table : FiniteTable) (left right output : List Nat)
    (outer first inner rightDigit outputIndex accumulated carry digit fuel
      outputLimit : Nat) (carryActive : carry ≠ 0) (receipt : Receipt) :
    step? (multiplicationSchema outputLimit)
        (.running (multiplicationProgram table) 15 [left, right, output]
          [outer, left.length, right.length, first, inner, rightDigit,
            outputIndex, accumulated, carry, digit]
          (fuel + 1) receipt) =
      some (.running (multiplicationProgram table) 16 [left, right, output]
        [outer, left.length, right.length, first, inner, rightDigit,
          outputIndex, accumulated, carry, digit]
        fuel (receipt ++ [.execute 15 "carry-active?"])) := by
  simp [step?, multiplicationSchema, executeInstruction, boundedRegister?,
    appendExecute, carryActive, at?]

theorem inner_set_right_zero_step
    (table : FiniteTable) (left right output : List Nat)
    (outer first inner rightDigit outputIndex accumulated carry digit fuel
      outputLimit : Nat) (receipt : Receipt) :
    step? (multiplicationSchema outputLimit)
        (.running (multiplicationProgram table) 16 [left, right, output]
          [outer, left.length, right.length, first, inner, rightDigit,
            outputIndex, accumulated, carry, digit]
          (fuel + 1) receipt) =
      some (.running (multiplicationProgram table) 17 [left, right, output]
        [outer, left.length, right.length, first, inner, 0,
          outputIndex, accumulated, carry, digit]
        fuel (receipt ++ [.execute 16 "right-zero"])) := by
  simp [step?, multiplicationSchema, executeInstruction,
    replaceBoundedRegister?, continueWithRegisters, appendExecute,
    replaceAt?]

theorem inner_read_carry_target_step
    (table : FiniteTable) (left right output : List Nat)
    (outer first inner outputIndex oldAccumulated accumulated carry digit fuel
      outputLimit : Nat)
    (outputRead : (at? output outputIndex).getD 0 = accumulated)
    (accumulatedValid : accumulated < 2) (receipt : Receipt) :
    step? (multiplicationSchema outputLimit)
        (.running (multiplicationProgram table) 17 [left, right, output]
          [outer, left.length, right.length, first, inner, 0,
            outputIndex, oldAccumulated, carry, digit]
          (fuel + 1) receipt) =
      some (.running (multiplicationProgram table) 11 [left, right, output]
        [outer, left.length, right.length, first, inner, 0,
          outputIndex, accumulated, carry, digit]
        fuel (receipt ++ [.execute 17 "read-carry-target"])) := by
  simp [step?, multiplicationSchema, executeInstruction, boundedBuffer?,
    boundedRegister?, replaceBoundedRegister?, continueWithRegisters,
    appendExecute, outputRead, replaceAt?, at?]
  all_goals omega

theorem active_inner_iteration
    (table : FiniteTable) (left right output written : List Nat)
    (outer first inner second outputIndex oldAccumulated accumulated carry digit nextCarry
      fuel outputLimit rowIndex : Nat)
    (origins : List String)
    (rightAt : at? right inner = some second)
    (outputRead : (at? output outputIndex).getD 0 = accumulated)
    (lookup : lookupTable? [first, second, accumulated, carry] table =
      some (rowIndex,
        ⟨[first, second, accumulated, carry], [digit, nextCarry], origins⟩))
    (secondValid : second < 2) (accumulatedValid : accumulated < 2)
    (digitValid : digit < 2)
    (notSparse : outputIndex ≤ output.length)
    (write : writeDigit? output outputIndex digit = some written)
    (outputRoom : written.length ≤ outputLimit)
    (oldRightDigit oldDigit : Nat) (receipt : Receipt) :
    runSteps (multiplicationSchema outputLimit) 7
        (innerConfig table left right output outer first inner oldRightDigit
          outputIndex oldAccumulated carry oldDigit (fuel + 7) receipt) =
      innerConfig table left right written outer first (inner + 1) second
        (outputIndex + 1) accumulated nextCarry digit fuel
        (receipt ++ activeInnerEvents rowIndex origins) := by
  have rightPresent : inner < right.length := at?_some_lt rightAt
  have step8 := inner_branch_active_step table left right output outer first inner
    oldRightDigit outputIndex oldAccumulated carry oldDigit (fuel + 6) outputLimit
    rightPresent receipt
  have step9 := inner_read_right_step table left right output outer first inner
    second oldRightDigit outputIndex oldAccumulated carry oldDigit (fuel + 5)
    outputLimit rightAt secondValid
    (receipt ++ [.execute 8 "right-active?"])
  have step10 := inner_read_accumulated_step table left right output outer first
    inner second outputIndex oldAccumulated accumulated carry oldDigit (fuel + 4)
    outputLimit outputRead accumulatedValid
    ((receipt ++ [.execute 8 "right-active?"]) ++
      [.execute 9 "read-right"])
  have step11 := inner_lookup_step table left right output outer first inner
    second outputIndex accumulated carry oldDigit digit nextCarry (fuel + 3)
    outputLimit rowIndex origins lookup
    (((receipt ++ [.execute 8 "right-active?"]) ++
      [.execute 9 "read-right"]) ++ [.execute 10 "read-accumulated"])
  have step12 := inner_write_step table left right output written outer first
    inner second outputIndex accumulated nextCarry digit (fuel + 2) outputLimit
    digitValid notSparse write outputRoom
    ((((receipt ++ [.execute 8 "right-active?"]) ++
      [.execute 9 "read-right"]) ++ [.execute 10 "read-accumulated"]) ++
      [.execute 11 "rules-4+6+8+10", .tableRow 11 rowIndex origins])
  have step13 := inner_increment_right_step table left right written outer first
    inner second outputIndex accumulated nextCarry digit (fuel + 1) outputLimit
    (((((receipt ++ [.execute 8 "right-active?"]) ++
      [.execute 9 "read-right"]) ++ [.execute 10 "read-accumulated"]) ++
      [.execute 11 "rules-4+6+8+10", .tableRow 11 rowIndex origins]) ++
      [.execute 12 "write-product-digit"])
  have step14 := inner_increment_output_step table left right written outer first
    (inner + 1) second outputIndex accumulated nextCarry digit fuel outputLimit
    ((((((receipt ++ [.execute 8 "right-active?"]) ++
      [.execute 9 "read-right"]) ++ [.execute 10 "read-accumulated"]) ++
      [.execute 11 "rules-4+6+8+10", .tableRow 11 rowIndex origins]) ++
      [.execute 12 "write-product-digit"]) ++
      [.execute 13 "next-right-digit"])
  rw [show 7 = 6 + 1 by omega, runSteps_succ_of_step 6 step8]
  rw [show 6 = 5 + 1 by omega, runSteps_succ_of_step 5 step9]
  rw [show 5 = 4 + 1 by omega, runSteps_succ_of_step 4 step10]
  rw [show 4 = 3 + 1 by omega, runSteps_succ_of_step 3 step11]
  rw [show 3 = 2 + 1 by omega, runSteps_succ_of_step 2 step12]
  rw [show 2 = 1 + 1 by omega, runSteps_succ_of_step 1 step13]
  rw [show 1 = 0 + 1 by omega, runSteps_succ_of_step 0 step14]
  simp [runSteps, activeInnerEvents, List.append_assoc]

theorem carry_inner_iteration
    (table : FiniteTable) (left right output written : List Nat)
    (outer first inner outputIndex oldAccumulated accumulated carry digit nextCarry fuel
      outputLimit rowIndex : Nat)
    (origins : List String)
    (rightDone : right.length ≤ inner) (carryActive : carry ≠ 0)
    (outputRead : (at? output outputIndex).getD 0 = accumulated)
    (lookup : lookupTable? [first, 0, accumulated, carry] table =
      some (rowIndex,
        ⟨[first, 0, accumulated, carry], [digit, nextCarry], origins⟩))
    (accumulatedValid : accumulated < 2) (digitValid : digit < 2)
    (notSparse : outputIndex ≤ output.length)
    (write : writeDigit? output outputIndex digit = some written)
    (outputRoom : written.length ≤ outputLimit)
    (oldRightDigit oldDigit : Nat) (receipt : Receipt) :
    runSteps (multiplicationSchema outputLimit) 8
        (innerConfig table left right output outer first inner oldRightDigit
          outputIndex oldAccumulated carry oldDigit (fuel + 8) receipt) =
      innerConfig table left right written outer first (inner + 1) 0
        (outputIndex + 1) accumulated nextCarry digit fuel
        (receipt ++ carryInnerEvents rowIndex origins) := by
  have step8 := inner_branch_done_step table left right output outer first inner
    oldRightDigit outputIndex oldAccumulated carry oldDigit (fuel + 7) outputLimit
    rightDone receipt
  have step15 := inner_branch_carry_step table left right output outer first inner
    oldRightDigit outputIndex oldAccumulated carry oldDigit (fuel + 6) outputLimit
    carryActive (receipt ++ [.execute 8 "right-active?"])
  have step16 := inner_set_right_zero_step table left right output outer first
    inner oldRightDigit outputIndex oldAccumulated carry oldDigit (fuel + 5)
    outputLimit ((receipt ++ [.execute 8 "right-active?"]) ++
      [.execute 15 "carry-active?"])
  have step17 := inner_read_carry_target_step table left right output outer first
    inner outputIndex oldAccumulated accumulated carry oldDigit (fuel + 4)
    outputLimit outputRead accumulatedValid
    (((receipt ++ [.execute 8 "right-active?"]) ++
      [.execute 15 "carry-active?"]) ++ [.execute 16 "right-zero"])
  have step11 := inner_lookup_step table left right output outer first inner 0
    outputIndex accumulated carry oldDigit digit nextCarry (fuel + 3)
    outputLimit rowIndex origins lookup
    ((((receipt ++ [.execute 8 "right-active?"]) ++
      [.execute 15 "carry-active?"]) ++ [.execute 16 "right-zero"]) ++
      [.execute 17 "read-carry-target"])
  have step12 := inner_write_step table left right output written outer first
    inner 0 outputIndex accumulated nextCarry digit (fuel + 2) outputLimit
    digitValid notSparse write outputRoom
    (((((receipt ++ [.execute 8 "right-active?"]) ++
      [.execute 15 "carry-active?"]) ++ [.execute 16 "right-zero"]) ++
      [.execute 17 "read-carry-target"]) ++
      [.execute 11 "rules-4+6+8+10", .tableRow 11 rowIndex origins])
  have step13 := inner_increment_right_step table left right written outer first
    inner 0 outputIndex accumulated nextCarry digit (fuel + 1) outputLimit
    ((((((receipt ++ [.execute 8 "right-active?"]) ++
      [.execute 15 "carry-active?"]) ++ [.execute 16 "right-zero"]) ++
      [.execute 17 "read-carry-target"]) ++
      [.execute 11 "rules-4+6+8+10", .tableRow 11 rowIndex origins]) ++
      [.execute 12 "write-product-digit"])
  have step14 := inner_increment_output_step table left right written outer first
    (inner + 1) 0 outputIndex accumulated nextCarry digit fuel outputLimit
    (((((((receipt ++ [.execute 8 "right-active?"]) ++
      [.execute 15 "carry-active?"]) ++ [.execute 16 "right-zero"]) ++
      [.execute 17 "read-carry-target"]) ++
      [.execute 11 "rules-4+6+8+10", .tableRow 11 rowIndex origins]) ++
      [.execute 12 "write-product-digit"]) ++
      [.execute 13 "next-right-digit"])
  rw [show 8 = 7 + 1 by omega, runSteps_succ_of_step 7 step8]
  rw [show 7 = 6 + 1 by omega, runSteps_succ_of_step 6 step15]
  rw [show 6 = 5 + 1 by omega, runSteps_succ_of_step 5 step16]
  rw [show 5 = 4 + 1 by omega, runSteps_succ_of_step 4 step17]
  rw [show 4 = 3 + 1 by omega, runSteps_succ_of_step 3 step11]
  rw [show 3 = 2 + 1 by omega, runSteps_succ_of_step 2 step12]
  rw [show 2 = 1 + 1 by omega, runSteps_succ_of_step 1 step13]
  rw [show 1 = 0 + 1 by omega, runSteps_succ_of_step 0 step14]
  simp [runSteps, carryInnerEvents, List.append_assoc]

theorem inner_branch_no_carry_step
    (table : FiniteTable) (left right output : List Nat)
    (outer first inner rightDigit outputIndex accumulated digit fuel outputLimit : Nat)
    (receipt : Receipt) :
    step? (multiplicationSchema outputLimit)
        (.running (multiplicationProgram table) 15 [left, right, output]
          [outer, left.length, right.length, first, inner, rightDigit,
            outputIndex, accumulated, 0, digit]
          (fuel + 1) receipt) =
      some (.running (multiplicationProgram table) 18 [left, right, output]
        [outer, left.length, right.length, first, inner, rightDigit,
          outputIndex, accumulated, 0, digit]
        fuel (receipt ++ [.execute 15 "carry-active?"])) := by
  simp [step?, multiplicationSchema, executeInstruction, boundedRegister?,
    appendExecute, at?]

theorem outer_increment_step
    (table : FiniteTable) (left right output : List Nat)
    (outer first inner rightDigit outputIndex accumulated carry digit fuel
      outputLimit : Nat) (receipt : Receipt) :
    step? (multiplicationSchema outputLimit)
        (.running (multiplicationProgram table) 18 [left, right, output]
          [outer, left.length, right.length, first, inner, rightDigit,
            outputIndex, accumulated, carry, digit]
          (fuel + 1) receipt) =
      some (outerConfig table left right output (outer + 1) first inner
        rightDigit outputIndex accumulated carry digit fuel
        (receipt ++ [.execute 18 "next-left-digit"])) := by
  simp [step?, outerConfig, multiplicationSchema, executeInstruction,
    boundedRegister?, replaceBoundedRegister?, continueWithRegisters,
    appendExecute, replaceAt?, at?]

theorem finish_inner_iteration
    (table : FiniteTable) (left right output : List Nat)
    (outer first inner rightDigit outputIndex accumulated digit fuel outputLimit : Nat)
    (rightDone : right.length ≤ inner) (receipt : Receipt) :
    runSteps (multiplicationSchema outputLimit) 3
        (innerConfig table left right output outer first inner rightDigit
          outputIndex accumulated 0 digit (fuel + 3) receipt) =
      outerConfig table left right output (outer + 1) first inner rightDigit
        outputIndex accumulated 0 digit fuel
        (receipt ++ finishInnerEvents) := by
  have step8 := inner_branch_done_step table left right output outer first inner
    rightDigit outputIndex accumulated 0 digit (fuel + 2) outputLimit
    rightDone receipt
  have step15 := inner_branch_no_carry_step table left right output outer first
    inner rightDigit outputIndex accumulated digit (fuel + 1) outputLimit
    (receipt ++ [.execute 8 "right-active?"])
  have step18 := outer_increment_step table left right output outer first inner
    rightDigit outputIndex accumulated 0 digit fuel outputLimit
    ((receipt ++ [.execute 8 "right-active?"]) ++
      [.execute 15 "carry-active?"])
  rw [show 3 = 2 + 1 by omega, runSteps_succ_of_step 2 step8]
  rw [show 2 = 1 + 1 by omega, runSteps_succ_of_step 1 step15]
  rw [show 1 = 0 + 1 by omega, runSteps_succ_of_step 0 step18]
  simp [runSteps, finishInnerEvents, List.append_assoc]

theorem outer_branch_active_step
    (table : FiniteTable) (left right output : List Nat)
    (outer leftDigit inner rightDigit outputIndex accumulated carry digit fuel
      outputLimit : Nat) (active : outer < left.length) (receipt : Receipt) :
    step? (multiplicationSchema outputLimit)
        (outerConfig table left right output outer leftDigit inner rightDigit
          outputIndex accumulated carry digit (fuel + 1) receipt) =
      some (.running (multiplicationProgram table) 4 [left, right, output]
        [outer, left.length, right.length, leftDigit, inner, rightDigit,
          outputIndex, accumulated, carry, digit]
        fuel (receipt ++ [.execute 3 "left-active?"])) := by
  simp [step?, outerConfig, multiplicationSchema, executeInstruction,
    boundedRegister?, appendExecute, active, at?]

theorem outer_read_left_step
    (table : FiniteTable) (left right output : List Nat)
    (outer first leftDigit inner rightDigit outputIndex accumulated carry digit
      fuel outputLimit : Nat)
    (leftAt : at? left outer = some first) (firstValid : first < 2)
    (receipt : Receipt) :
    step? (multiplicationSchema outputLimit)
        (.running (multiplicationProgram table) 4 [left, right, output]
          [outer, left.length, right.length, leftDigit, inner, rightDigit,
            outputIndex, accumulated, carry, digit]
          (fuel + 1) receipt) =
      some (.running (multiplicationProgram table) 5 [left, right, output]
        [outer, left.length, right.length, first, inner, rightDigit,
          outputIndex, accumulated, carry, digit]
        fuel (receipt ++ [.execute 4 "read-left"])) := by
  simp [step?, multiplicationSchema, executeInstruction, boundedBuffer?,
    boundedRegister?, replaceBoundedRegister?, continueWithRegisters,
    appendExecute, leftAt, replaceAt?, at?]
  all_goals omega

theorem outer_set_inner_step
    (table : FiniteTable) (left right output : List Nat)
    (outer first inner rightDigit outputIndex accumulated carry digit fuel
      outputLimit : Nat) (receipt : Receipt) :
    step? (multiplicationSchema outputLimit)
        (.running (multiplicationProgram table) 5 [left, right, output]
          [outer, left.length, right.length, first, inner, rightDigit,
            outputIndex, accumulated, carry, digit]
          (fuel + 1) receipt) =
      some (.running (multiplicationProgram table) 6 [left, right, output]
        [outer, left.length, right.length, first, 0, rightDigit,
          outputIndex, accumulated, carry, digit]
        fuel (receipt ++ [.execute 5 "inner-index-zero"])) := by
  simp [step?, multiplicationSchema, executeInstruction,
    replaceBoundedRegister?, continueWithRegisters, appendExecute,
    replaceAt?]

theorem outer_copy_index_step
    (table : FiniteTable) (left right output : List Nat)
    (outer first rightDigit outputIndex accumulated carry digit fuel outputLimit : Nat)
    (receipt : Receipt) :
    step? (multiplicationSchema outputLimit)
        (.running (multiplicationProgram table) 6 [left, right, output]
          [outer, left.length, right.length, first, 0, rightDigit,
            outputIndex, accumulated, carry, digit]
          (fuel + 1) receipt) =
      some (.running (multiplicationProgram table) 7 [left, right, output]
        [outer, left.length, right.length, first, 0, rightDigit,
          outer, accumulated, carry, digit]
        fuel (receipt ++ [.execute 6 "output-index"])) := by
  simp [step?, multiplicationSchema, executeInstruction, boundedRegister?,
    replaceBoundedRegister?, continueWithRegisters, appendExecute,
    replaceAt?, at?]

theorem outer_clear_carry_step
    (table : FiniteTable) (left right output : List Nat)
    (outer first rightDigit accumulated carry digit fuel outputLimit : Nat)
    (receipt : Receipt) :
    step? (multiplicationSchema outputLimit)
        (.running (multiplicationProgram table) 7 [left, right, output]
          [outer, left.length, right.length, first, 0, rightDigit,
            outer, accumulated, carry, digit]
          (fuel + 1) receipt) =
      some (innerConfig table left right output outer first 0 rightDigit outer
        accumulated 0 digit fuel (receipt ++ [.execute 7 "carry-zero"])) := by
  simp [step?, innerConfig, multiplicationSchema, executeInstruction,
    replaceBoundedRegister?, continueWithRegisters, appendExecute,
    replaceAt?]

theorem start_outer_iteration
    (table : FiniteTable) (left right output : List Nat)
    (outer first oldLeftDigit inner rightDigit outputIndex accumulated carry digit
      fuel outputLimit : Nat)
    (leftAt : at? left outer = some first) (firstValid : first < 2)
    (receipt : Receipt) :
    runSteps (multiplicationSchema outputLimit) 5
        (outerConfig table left right output outer oldLeftDigit inner rightDigit
          outputIndex accumulated carry digit (fuel + 5) receipt) =
      innerConfig table left right output outer first 0 rightDigit outer
        accumulated 0 digit fuel (receipt ++ startOuterEvents) := by
  have active : outer < left.length := at?_some_lt leftAt
  have step3 := outer_branch_active_step table left right output outer
    oldLeftDigit inner rightDigit outputIndex accumulated carry digit
    (fuel + 4) outputLimit active receipt
  have step4 := outer_read_left_step table left right output outer first
    oldLeftDigit inner rightDigit outputIndex accumulated carry digit
    (fuel + 3) outputLimit leftAt firstValid
    (receipt ++ [.execute 3 "left-active?"])
  have step5 := outer_set_inner_step table left right output outer first inner
    rightDigit outputIndex accumulated carry digit (fuel + 2) outputLimit
    ((receipt ++ [.execute 3 "left-active?"]) ++ [.execute 4 "read-left"])
  have step6 := outer_copy_index_step table left right output outer first
    rightDigit outputIndex accumulated carry digit (fuel + 1) outputLimit
    (((receipt ++ [.execute 3 "left-active?"]) ++ [.execute 4 "read-left"]) ++
      [.execute 5 "inner-index-zero"])
  have step7 := outer_clear_carry_step table left right output outer first
    rightDigit accumulated carry digit fuel outputLimit
    ((((receipt ++ [.execute 3 "left-active?"]) ++ [.execute 4 "read-left"]) ++
      [.execute 5 "inner-index-zero"]) ++ [.execute 6 "output-index"])
  rw [show 5 = 4 + 1 by omega, runSteps_succ_of_step 4 step3]
  rw [show 4 = 3 + 1 by omega, runSteps_succ_of_step 3 step4]
  rw [show 3 = 2 + 1 by omega, runSteps_succ_of_step 2 step5]
  rw [show 2 = 1 + 1 by omega, runSteps_succ_of_step 1 step6]
  rw [show 1 = 0 + 1 by omega, runSteps_succ_of_step 0 step7]
  simp [runSteps, startOuterEvents, List.append_assoc]

theorem outer_branch_done_step
    (table : FiniteTable) (left right output : List Nat)
    (outer leftDigit inner rightDigit outputIndex accumulated carry digit fuel
      outputLimit : Nat) (leftDone : left.length ≤ outer) (receipt : Receipt) :
    step? (multiplicationSchema outputLimit)
        (outerConfig table left right output outer leftDigit inner rightDigit
          outputIndex accumulated carry digit (fuel + 1) receipt) =
      some (.running (multiplicationProgram table) 19 [left, right, output]
        [outer, left.length, right.length, leftDigit, inner, rightDigit,
          outputIndex, accumulated, carry, digit]
        fuel (receipt ++ [.execute 3 "left-active?"])) := by
  have leftAbsent : ¬ outer < left.length := not_lt_of_ge leftDone
  simp [step?, outerConfig, multiplicationSchema, executeInstruction,
    boundedRegister?, appendExecute, leftAbsent, at?]

theorem return_output_step
    (table : FiniteTable) (left right output : List Nat)
    (outer leftDigit inner rightDigit outputIndex accumulated carry digit fuel
      outputLimit : Nat)
    (outputValid : firstInvalidDigit? 2 output = none) (receipt : Receipt) :
    step? (multiplicationSchema outputLimit)
        (.running (multiplicationProgram table) 19 [left, right, output]
          [outer, left.length, right.length, leftDigit, inner, rightDigit,
            outputIndex, accumulated, carry, digit]
          (fuel + 1) receipt) =
      some (.halted (.value output) (receipt ++ [.execute 19 "return"])) := by
  simp [step?, multiplicationSchema, executeInstruction, boundedBuffer?,
    appendExecute, outputValid, at?]

theorem terminal_outer_iteration
    (table : FiniteTable) (left right output : List Nat)
    (outer leftDigit inner rightDigit outputIndex accumulated carry digit fuel
      outputLimit : Nat)
    (leftDone : left.length ≤ outer)
    (outputValid : firstInvalidDigit? 2 output = none) (receipt : Receipt) :
    runSteps (multiplicationSchema outputLimit) 2
        (outerConfig table left right output outer leftDigit inner rightDigit
          outputIndex accumulated carry digit (fuel + 2) receipt) =
      .halted (.value output) (receipt ++ terminalOuterEvents) := by
  have step3 := outer_branch_done_step table left right output outer leftDigit
    inner rightDigit outputIndex accumulated carry digit (fuel + 1)
    outputLimit leftDone receipt
  have step19 := return_output_step table left right output outer leftDigit
    inner rightDigit outputIndex accumulated carry digit fuel outputLimit
    outputValid (receipt ++ [.execute 3 "left-active?"])
  rw [show 2 = 1 + 1 by omega, runSteps_succ_of_step 1 step3]
  rw [show 1 = 0 + 1 by omega, runSteps_succ_of_step 0 step19]
  simp [runSteps, terminalOuterEvents, List.append_assoc]

theorem initialize_multiplication (table : FiniteTable) (left right : List Nat)
    (fuel outputLimit : Nat) :
    runSteps (multiplicationSchema outputLimit) 3
        (initialMultiplicationConfig (multiplicationProgram table) left right
          (fuel + 3)) =
      outerConfig table left right [] 0 0 0 0 0 0 0 0 fuel
        multiplicationInitializationEvents := by
  simp [runSteps, step?, initialMultiplicationConfig, outerConfig,
    multiplicationSchema, executeInstruction,
    continueWithRegisters, appendExecute, boundedBuffer?,
    replaceBoundedRegister?, replaceAt?, at?, multiplicationInitializationEvents]

/-- Every certified inner trace is executed by the actual target program with
its exact instruction count and receipt.  The final scratch registers are
existential because the next outer iteration overwrites them before observing
them. -/
theorem inner_executes_trace
    {table : FiniteTable} {first position carry inner : Nat}
    {rightRemaining output result : List Nat}
    {events : Receipt} {steps : Nat}
    (trace : InnerTrace table first rightRemaining output position carry
      result events steps)
    (left right : List Nat) (outer oldRightDigit oldAccumulated oldDigit fuel
      outputLimit : Nat) (receipt : Receipt)
    (rightDrop : right.drop inner = rightRemaining)
    (outputBound : result.length ≤ outputLimit) :
    ∃ finalInner finalRightDigit finalOutputIndex finalAccumulated finalDigit,
      runSteps (multiplicationSchema outputLimit) steps
          (innerConfig table left right output outer first inner oldRightDigit
            position oldAccumulated carry oldDigit (fuel + steps) receipt) =
        outerConfig table left right result (outer + 1) first finalInner
          finalRightDigit finalOutputIndex finalAccumulated 0 finalDigit fuel
          (receipt ++ events) := by
  induction trace generalizing inner oldRightDigit oldAccumulated oldDigit fuel
      receipt with
  | done =>
      rename_i currentOutput currentPosition
      have rightDone : right.length ≤ inner :=
        length_le_of_drop_eq_nil rightDrop
      refine ⟨inner, oldRightDigit, currentPosition, oldAccumulated, oldDigit, ?_⟩
      simpa using finish_inner_iteration table left right currentOutput outer first inner
        oldRightDigit currentPosition oldAccumulated oldDigit fuel outputLimit
        rightDone receipt
  | active outputRead lookup secondValid accumulatedValid digitValid write
      writeDenotes writtenValid lengthMono positionWritten rest
      inductionHypothesis =>
      rename_i second accumulated currentCarry digit nextCarry rowIndex
        currentPosition rightTail currentOutput written result origins
        restEvents restSteps
      have rightAt : at? right inner = some second := by
        rw [at?_eq_head?_drop, rightDrop]
        rfl
      have nextRightDrop : right.drop (inner + 1) = rightTail := by
        rw [drop_succ_eq_tail_drop, rightDrop]
        rfl
      have notSparse : currentPosition ≤ currentOutput.length :=
        writeDigit?_some_index_le write
      have writtenBound : written.length ≤ outputLimit :=
        Nat.le_trans rest.output_length_le outputBound
      rw [runSteps_add (multiplicationSchema outputLimit) 7 restSteps]
      have fuelEq : fuel + (7 + restSteps) = (fuel + restSteps) + 7 := by omega
      rw [fuelEq, active_inner_iteration table left right currentOutput written
        outer first inner second currentPosition oldAccumulated accumulated
        currentCarry digit
        nextCarry (fuel + restSteps) outputLimit rowIndex origins rightAt
        outputRead lookup secondValid accumulatedValid digitValid notSparse write
        writtenBound oldRightDigit oldDigit receipt]
      obtain ⟨finalInner, finalRightDigit, finalOutputIndex, finalAccumulated,
          finalDigit, execution⟩ :=
        inductionHypothesis (inner := inner + 1) second accumulated digit fuel
          (receipt ++ activeInnerEvents rowIndex origins)
          nextRightDrop outputBound
      refine ⟨finalInner, finalRightDigit, finalOutputIndex, finalAccumulated,
        finalDigit, ?_⟩
      simpa [List.append_assoc] using execution

  | carry carryActive outputRead lookup accumulatedValid digitValid write
      writeDenotes writtenValid lengthMono positionWritten rest
      inductionHypothesis =>
      rename_i accumulated currentCarry digit nextCarry rowIndex currentPosition
        currentOutput written result origins restEvents restSteps
      have rightDone : right.length ≤ inner :=
        length_le_of_drop_eq_nil rightDrop
      have nextRightDrop : right.drop (inner + 1) = [] := by
        rw [drop_succ_eq_tail_drop, rightDrop]
        rfl
      have notSparse : currentPosition ≤ currentOutput.length :=
        writeDigit?_some_index_le write
      have writtenBound : written.length ≤ outputLimit :=
        Nat.le_trans rest.output_length_le outputBound
      rw [runSteps_add (multiplicationSchema outputLimit) 8 restSteps]
      have fuelEq : fuel + (8 + restSteps) = (fuel + restSteps) + 8 := by omega
      rw [fuelEq, carry_inner_iteration table left right currentOutput written
        outer first inner currentPosition oldAccumulated accumulated currentCarry
        digit nextCarry
        (fuel + restSteps) outputLimit rowIndex origins rightDone carryActive
        outputRead lookup accumulatedValid digitValid notSparse write writtenBound
        oldRightDigit oldDigit receipt]
      obtain ⟨finalInner, finalRightDigit, finalOutputIndex, finalAccumulated,
          finalDigit, execution⟩ :=
        inductionHypothesis (inner := inner + 1) 0 accumulated digit fuel
          (receipt ++ carryInnerEvents rowIndex origins) nextRightDrop outputBound
      refine ⟨finalInner, finalRightDigit, finalOutputIndex, finalAccumulated,
        finalDigit, ?_⟩
      simpa [List.append_assoc] using execution

/-- A complete outer-loop trace.  Each source digit contributes one certified
inner trace, so source-table provenance remains present in the final receipt. -/
inductive MultiplicationTrace (table : FiniteTable) (right : List Nat) :
    List Nat → List Nat → Nat → List Nat → Receipt → Nat → Prop where
  | done {output : List Nat} {outer : Nat} :
      MultiplicationTrace table right [] output outer output
        terminalOuterEvents 2
  | next
      {first outer : Nat} {left output intermediate result : List Nat}
      {innerEvents restEvents : Receipt} {innerSteps restSteps : Nat}
      (firstValid : first < 2)
      (inner : InnerTrace table first right output outer 0 intermediate
        innerEvents innerSteps)
      (rest : MultiplicationTrace table right left intermediate (outer + 1)
        result restEvents restSteps) :
      MultiplicationTrace table right (first :: left) output outer result
        (startOuterEvents ++ innerEvents ++ restEvents)
        (5 + innerSteps + restSteps)

theorem MultiplicationTrace.output_length_le {table : FiniteTable}
    {right left output result : List Nat} {outer : Nat}
    {events : Receipt} {steps : Nat}
    (trace : MultiplicationTrace table right left output outer result events steps) :
    output.length ≤ result.length := by
  induction trace with
  | done => exact Nat.le_refl _
  | next firstValid inner rest inductionHypothesis =>
      exact Nat.le_trans inner.output_length_le inductionHypothesis

theorem MultiplicationTrace.resultValid {table : FiniteTable}
    {right left output result : List Nat} {outer : Nat}
    {events : Receipt} {steps : Nat}
    (trace : MultiplicationTrace table right left output outer result events steps)
    (outputValid : firstInvalidDigit? 2 output = none) :
    firstInvalidDigit? 2 result = none := by
  induction trace with
  | done => exact outputValid
  | next firstValid inner rest inductionHypothesis =>
      exact inductionHypothesis (inner.resultValid outputValid)

theorem MultiplicationTrace.denotes {table : FiniteTable}
    {right left output result : List Nat} {outer : Nat}
    {events : Receipt} {steps : Nat}
    (tableCorrect : BinaryMultiplicationTable table)
    (trace : MultiplicationTrace table right left output outer result events steps) :
    WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo result =
      WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo output +
        2 ^ outer *
          (WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo left *
            WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo right) := by
  induction trace with
  | done => simp [WaltersZantemaDA.decodeDigits]
  | next firstValid inner rest inductionHypothesis =>
      rename_i first currentOuter leftTail currentOutput intermediate result
        innerEvents restEvents innerSteps restSteps
      have innerDenotes := inner.denotes tableCorrect firstValid (by omega)
      simp only [WaltersZantemaDA.decodeDigits, WaltersZantemaDA.radixTwo,
        Nat.ofDigits_cons, pow_succ'] at ⊢ inductionHypothesis innerDenotes
      rw [inductionHypothesis, innerDenotes]
      ring

theorem exists_multiplication_trace {table : FiniteTable}
    (tableCorrect : BinaryMultiplicationTable table)
    (left right output : List Nat) (outer : Nat)
    (leftRange : WaltersZantemaDA.DigitsInRange
      WaltersZantemaDA.radixTwo left)
    (rightRange : WaltersZantemaDA.DigitsInRange
      WaltersZantemaDA.radixTwo right)
    (outputRange : WaltersZantemaDA.DigitsInRange
      WaltersZantemaDA.radixTwo output)
    (positionReady : right ≠ [] → outer ≤ output.length) :
    ∃ result events steps,
      MultiplicationTrace table right left output outer result events steps := by
  induction left generalizing output outer with
  | nil => exact ⟨output, terminalOuterEvents, 2, .done⟩
  | cons first left inductionHypothesis =>
      have firstValid : first < 2 := leftRange first (by simp)
      have leftTailRange : WaltersZantemaDA.DigitsInRange
          WaltersZantemaDA.radixTwo left := by
        intro value member
        exact leftRange value (List.mem_cons_of_mem first member)
      have outputValid := digitsInRange_firstInvalidDigit?_none outputRange
      cases right with
      | nil =>
          have inner : InnerTrace table first [] output outer 0 output
              finishInnerEvents 3 := .done
          obtain ⟨result, restEvents, restSteps, rest⟩ :=
            inductionHypothesis output (outer + 1) leftTailRange
              outputRange (by simp)
          exact ⟨result,
            startOuterEvents ++ finishInnerEvents ++ restEvents,
            5 + 3 + restSteps, .next firstValid inner rest⟩
      | cons second rightTail =>
          have ready : outer ≤ output.length := positionReady (by simp)
          let leading := output.take outer
          let trailing := output.drop outer
          have leadingRange : WaltersZantemaDA.DigitsInRange
              WaltersZantemaDA.radixTwo leading :=
            digitsInRange_take outer outputRange
          have trailingRange : WaltersZantemaDA.DigitsInRange
              WaltersZantemaDA.radixTwo trailing :=
            digitsInRange_drop outer outputRange
          have leadingLength : leading.length = outer := by
            simp [leading, List.length_take, Nat.min_eq_left ready]
          obtain ⟨intermediate, innerEvents, innerSteps, innerRaw⟩ :=
            exists_inner_trace_from_split tableCorrect firstValid
              (second :: rightTail) leading trailing rightRange leadingRange
              trailingRange (carry := 0) (by omega)
          have inner : InnerTrace table first (second :: rightTail) output outer 0
              intermediate innerEvents innerSteps := by
            simpa [leading, trailing, leadingLength] using innerRaw
          have intermediateValid := inner.resultValid outputValid
          have intermediateRange :=
            firstInvalidDigit?_none_digitsInRange intermediateValid
          have nextReady : outer + 1 ≤ intermediate.length :=
            inner.position_lt_result_of_right
          obtain ⟨result, restEvents, restSteps, rest⟩ :=
            inductionHypothesis intermediate (outer + 1) leftTailRange
              intermediateRange (by
                intro notEmpty
                exact nextReady)
          exact ⟨result, startOuterEvents ++ innerEvents ++ restEvents,
            5 + innerSteps + restSteps, .next firstValid inner rest⟩

theorem outer_executes_trace
    {table : FiniteTable} {right leftRemaining output result : List Nat}
    {outer : Nat} {events : Receipt} {steps : Nat}
    (trace : MultiplicationTrace table right leftRemaining output outer result
      events steps)
    (left : List Nat)
    (oldLeftDigit oldInner oldRightDigit oldOutputIndex oldAccumulated oldCarry
      oldDigit fuel outputLimit : Nat) (receipt : Receipt)
    (leftDrop : left.drop outer = leftRemaining)
    (outputValid : firstInvalidDigit? 2 output = none)
    (outputBound : result.length ≤ outputLimit) :
    runSteps (multiplicationSchema outputLimit) steps
        (outerConfig table left right output outer oldLeftDigit oldInner
          oldRightDigit oldOutputIndex oldAccumulated oldCarry oldDigit
          (fuel + steps) receipt) =
      .halted (.value result) (receipt ++ events) := by
  induction trace generalizing oldLeftDigit oldInner oldRightDigit oldOutputIndex
      oldAccumulated oldCarry oldDigit fuel receipt with
  | done =>
      rename_i currentOutput currentOuter
      have leftDone : left.length ≤ currentOuter :=
        length_le_of_drop_eq_nil leftDrop
      simpa using terminal_outer_iteration table left right currentOutput currentOuter
        oldLeftDigit oldInner oldRightDigit oldOutputIndex oldAccumulated
        oldCarry oldDigit fuel outputLimit leftDone outputValid receipt
  | next firstValid inner rest inductionHypothesis =>
      rename_i first currentOuter leftTail currentOutput intermediate result
        innerEvents restEvents innerSteps restSteps
      have leftAt : at? left currentOuter = some first := by
        rw [at?_eq_head?_drop, leftDrop]
        rfl
      have nextLeftDrop : left.drop (currentOuter + 1) = leftTail := by
        rw [drop_succ_eq_tail_drop, leftDrop]
        rfl
      have intermediateValid := inner.resultValid outputValid
      have intermediateBound : intermediate.length ≤ outputLimit :=
        Nat.le_trans rest.output_length_le outputBound
      have stepsEq : 5 + innerSteps + restSteps =
          5 + (innerSteps + restSteps) := by omega
      rw [stepsEq, runSteps_add (multiplicationSchema outputLimit) 5
        (innerSteps + restSteps)]
      have fuelStart :
          fuel + (5 + (innerSteps + restSteps)) =
            (fuel + innerSteps + restSteps) + 5 := by omega
      rw [fuelStart, start_outer_iteration table left right currentOutput
        currentOuter first oldLeftDigit oldInner oldRightDigit oldOutputIndex
        oldAccumulated oldCarry oldDigit (fuel + innerSteps + restSteps)
        outputLimit leftAt firstValid receipt]
      have innerFuelEq : fuel + innerSteps + restSteps =
          (fuel + restSteps) + innerSteps := by omega
      rw [innerFuelEq]
      rw [runSteps_add (multiplicationSchema outputLimit) innerSteps restSteps]
      obtain ⟨finalInner, finalRightDigit, finalOutputIndex, finalAccumulated,
          finalDigit, innerExecution⟩ :=
        inner_executes_trace (inner := 0) inner left right currentOuter oldRightDigit
          oldAccumulated oldDigit (fuel + restSteps) outputLimit
          (receipt ++ startOuterEvents) (by rfl) intermediateBound
      rw [innerExecution]
      have restExecution := inductionHypothesis first finalInner
        finalRightDigit finalOutputIndex finalAccumulated 0 finalDigit fuel
        (receipt ++ startOuterEvents ++ innerEvents) nextLeftDrop
        intermediateValid outputBound
      simpa [List.append_assoc] using restExecution

/-- Initialization followed by any certified multiplication trace is executed
by the actual twenty-instruction target program, with the complete receipt. -/
theorem initial_executes_trace
    {table : FiniteTable} {left right result : List Nat}
    {events : Receipt} {steps : Nat}
    (trace : MultiplicationTrace table right left [] 0 result events steps)
    (outputLimit fuel : Nat)
    (outputBound : result.length ≤ outputLimit) :
    runSteps (multiplicationSchema outputLimit) (3 + steps)
        (initialMultiplicationConfig (multiplicationProgram table) left right
          (fuel + 3 + steps)) =
      .halted (.value result) (multiplicationInitializationEvents ++ events) := by
  rw [runSteps_add (multiplicationSchema outputLimit) 3 steps]
  have fuelEq : fuel + 3 + steps = (fuel + steps) + 3 := by omega
  rw [fuelEq, initialize_multiplication table left right (fuel + steps) outputLimit]
  simpa using outer_executes_trace trace left 0 0 0 0 0 0 0 fuel outputLimit
    multiplicationInitializationEvents (by simp) (by simp [firstInvalidDigit?])
    outputBound

/-- Universal source-to-target multiplication preservation for the actual
table extracted from the supplied closed DA presentation. -/
theorem radixTwo_compiled_multiplication_preserves (first second : Nat) :
    ∃ digits events steps,
      WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo digits =
          first * second ∧
      runSteps (multiplicationSchema digits.length) (3 + steps)
          (initialMultiplicationConfig
            (multiplicationProgram radixTwoMultiplicationTable)
            (WaltersZantemaDA.encodeDigits WaltersZantemaDA.radixTwo first)
            (WaltersZantemaDA.encodeDigits WaltersZantemaDA.radixTwo second)
            (3 + steps)) =
        .halted (.value digits) (multiplicationInitializationEvents ++ events) := by
  have leftRange :=
    (WaltersZantemaDA.encodeDigits_canonical WaltersZantemaDA.radixTwo first).1
  have rightRange :=
    (WaltersZantemaDA.encodeDigits_canonical WaltersZantemaDA.radixTwo second).1
  obtain ⟨digits, events, steps, trace⟩ :=
    exists_multiplication_trace radixTwoMultiplicationTable_binary
      (WaltersZantemaDA.encodeDigits WaltersZantemaDA.radixTwo first)
      (WaltersZantemaDA.encodeDigits WaltersZantemaDA.radixTwo second)
      [] 0 leftRange rightRange (by
        intro digit member
        cases member) (fun _ => Nat.zero_le _)
  refine ⟨digits, events, steps, ?_, ?_⟩
  · have denotation := trace.denotes radixTwoMultiplicationTable_binary
    have emptyDecode : WaltersZantemaDA.decodeDigits
        WaltersZantemaDA.radixTwo [] = 0 := rfl
    simpa only [emptyDecode, WaltersZantemaDA.decodeDigits_encodeDigits,
      Nat.pow_zero, one_mul, zero_add] using denotation
  · exact initial_executes_trace trace digits.length 0 (Nat.le_refl _)

/-- Any value claimed for the exact trace-driven run is forced to be the
source-authorized product; the machine cannot invent a different result. -/
theorem radixTwo_compiled_multiplication_no_invention
    (first second : Nat) {digits observed : List Nat}
    {events observedReceipt : Receipt} {steps : Nat}
    (trace : MultiplicationTrace radixTwoMultiplicationTable
      (WaltersZantemaDA.encodeDigits WaltersZantemaDA.radixTwo second)
      (WaltersZantemaDA.encodeDigits WaltersZantemaDA.radixTwo first)
      [] 0 digits events steps)
    (execution :
      runSteps (multiplicationSchema digits.length) (3 + steps)
          (initialMultiplicationConfig
            (multiplicationProgram radixTwoMultiplicationTable)
            (WaltersZantemaDA.encodeDigits WaltersZantemaDA.radixTwo first)
            (WaltersZantemaDA.encodeDigits WaltersZantemaDA.radixTwo second)
            (3 + steps)) =
        .halted (.value observed) observedReceipt) :
    observed = digits ∧
      WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo observed =
        first * second := by
  have expected := initial_executes_trace trace digits.length 0 (Nat.le_refl _)
  have equalHalted := execution.symm.trans expected
  injection equalHalted with observedEq receiptEq
  have observedEq' : observed = digits := by
    injection observedEq
  subst observed
  constructor
  · rfl
  · have denotation := trace.denotes radixTwoMultiplicationTable_binary
    have emptyDecode : WaltersZantemaDA.decodeDigits
        WaltersZantemaDA.radixTwo [] = 0 := rfl
    simpa only [emptyDecode, WaltersZantemaDA.decodeDigits_encodeDigits,
      Nat.pow_zero, one_mul, zero_add] using denotation

/-- The source DA multiplication graph and the certified execution graph of
the compiled C1 program are the same relation on natural numbers.  The target
side retains the complete event trace and source-rule origins. -/
theorem radixTwo_source_iff_compiled_multiplication
    (first second result : Nat) :
    WaltersZantemaDA.MultiStep WaltersZantemaDA.radixTwo
        (.mul
          (WaltersZantemaDA.encodeTerm WaltersZantemaDA.radixTwo first)
          (WaltersZantemaDA.encodeTerm WaltersZantemaDA.radixTwo second))
        (WaltersZantemaDA.encodeTerm WaltersZantemaDA.radixTwo result) ↔
      ∃ digits events steps,
        MultiplicationTrace radixTwoMultiplicationTable
          (WaltersZantemaDA.encodeDigits WaltersZantemaDA.radixTwo second)
          (WaltersZantemaDA.encodeDigits WaltersZantemaDA.radixTwo first)
          [] 0 digits events steps ∧
        WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo digits = result ∧
        runSteps (multiplicationSchema digits.length) (3 + steps)
            (initialMultiplicationConfig
              (multiplicationProgram radixTwoMultiplicationTable)
              (WaltersZantemaDA.encodeDigits WaltersZantemaDA.radixTwo first)
              (WaltersZantemaDA.encodeDigits WaltersZantemaDA.radixTwo second)
              (3 + steps)) =
          .halted (.value digits)
            (multiplicationInitializationEvents ++ events) := by
  constructor
  · intro source
    have resultEquation :=
      (WaltersZantemaDA.encoded_multiplication_graph
        WaltersZantemaDA.radixTwo first second result).1 source
    have leftRange :=
      (WaltersZantemaDA.encodeDigits_canonical WaltersZantemaDA.radixTwo first).1
    have rightRange :=
      (WaltersZantemaDA.encodeDigits_canonical WaltersZantemaDA.radixTwo second).1
    obtain ⟨digits, events, steps, trace⟩ :=
      exists_multiplication_trace radixTwoMultiplicationTable_binary
        (WaltersZantemaDA.encodeDigits WaltersZantemaDA.radixTwo first)
        (WaltersZantemaDA.encodeDigits WaltersZantemaDA.radixTwo second)
        [] 0 leftRange rightRange (by
          intro digit member
          cases member) (fun _ => Nat.zero_le _)
    refine ⟨digits, events, steps, trace, ?_, ?_⟩
    · have denotation := trace.denotes radixTwoMultiplicationTable_binary
      have emptyDecode : WaltersZantemaDA.decodeDigits
          WaltersZantemaDA.radixTwo [] = 0 := rfl
      simpa only [resultEquation, emptyDecode,
        WaltersZantemaDA.decodeDigits_encodeDigits, Nat.pow_zero, one_mul,
        zero_add] using denotation
    · exact initial_executes_trace trace digits.length 0 (Nat.le_refl _)
  · rintro ⟨digits, events, steps, trace, decoded, execution⟩
    apply (WaltersZantemaDA.encoded_multiplication_graph
      WaltersZantemaDA.radixTwo first second result).2
    have denotation := trace.denotes radixTwoMultiplicationTable_binary
    have emptyDecode : WaltersZantemaDA.decodeDigits
        WaltersZantemaDA.radixTwo [] = 0 := rfl
    rw [decoded] at denotation
    simpa only [emptyDecode, WaltersZantemaDA.decodeDigits_encodeDigits,
      Nat.pow_zero, one_mul, zero_add] using denotation

#print axioms radixTwoMultiplicationTable_binary
#print axioms initial_executes_trace
#print axioms radixTwo_compiled_multiplication_preserves
#print axioms radixTwo_compiled_multiplication_no_invention
#print axioms radixTwo_source_iff_compiled_multiplication

end Mettapedia.GSLT.LanguageDef.C1MultiplicationCorrectness
