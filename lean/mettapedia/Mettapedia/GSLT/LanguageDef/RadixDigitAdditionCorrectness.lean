import Mettapedia.GSLT.LanguageDef.WaltersZantemaDAToRadixDigitMachine
import Mettapedia.GSLT.LanguageDef.WaltersZantemaDAAddition

/-!
# Universal loop facts for the radix-digit addition program

These lemmas expose the loop invariant of the target radix-digit program. They are
stated over an arbitrary finite lookup table; source-language correctness is
connected separately through the table extracted from the DA rules.
-/

namespace Mettapedia.GSLT.LanguageDef.RadixDigitAdditionCorrectness

open Mettapedia.GSLT.LanguageDef.RadixDigitMachine
open Mettapedia.GSLT.LanguageDef.WaltersZantemaDAToRadixDigitMachine

def additionSchema (outputLimit : Nat) : Schema := {
  radix := 2
  radixAtLeastTwo := by decide
  bufferLimit := 3
  registerLimit := 8
  outputLimit
}

def loopConfig (table : FiniteTable) (left right output : List Nat)
    (index leftDigit rightDigit carry outputDigit fuel : Nat)
    (receipt : Receipt) : Config :=
  .running (additionProgram table) 4 [left, right, output]
    [index, left.length, right.length, leftDigit, rightDigit, carry,
      outputDigit]
    fuel receipt

theorem at?_some_lt {values : List α} {index : Nat} {value : α}
    (found : at? values index = some value) : index < values.length := by
  induction values generalizing index with
  | nil => simp [at?] at found
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => simp
      | succ index =>
          simp only [at?] at found
          have smaller := inductionHypothesis found
          simp only [List.length_cons]
          omega

theorem both_active_iteration
    (table : FiniteTable) (left right output : List Nat)
    (index first second carry digit nextCarry fuel outputLimit rowIndex : Nat)
    (oldLeftDigit oldRightDigit oldOutputDigit : Nat)
    (origins : List String)
    (leftAt : at? left index = some first)
    (rightAt : at? right index = some second)
    (lookup : lookupTable? [first, second, carry] table =
      some (rowIndex, ⟨[first, second, carry], [digit, nextCarry], origins⟩))
    (firstValid : first < 2) (secondValid : second < 2)
    (digitValid : digit < 2)
    (outputAtEnd : index = output.length)
    (outputRoom : output.length < outputLimit)
    (receipt : Receipt) :
    runSteps (additionSchema outputLimit) 8
        (loopConfig table left right output index oldLeftDigit oldRightDigit
          carry oldOutputDigit
          (fuel + 8) receipt) =
      loopConfig table left right (output ++ [digit]) (index + 1)
        first second nextCarry digit fuel
        (receipt ++ [
          .execute 4 "left-present?",
          .execute 5 "read-left",
          .execute 7 "right-present?",
          .execute 8 "read-right",
          .execute 10 "left-active?",
          .execute 13 "rules-4+8",
          .tableRow 13 rowIndex origins,
          .execute 14 "write-digit",
          .execute 15 "next-digit"]) := by
  subst index
  have leftPresent : output.length < left.length := by
    exact at?_some_lt leftAt
  have rightPresent : output.length < right.length := by
    exact at?_some_lt rightAt
  have digitOk : ¬ 2 ≤ digit := Nat.not_le.mpr digitValid
  have room : ¬ outputLimit ≤ output.length := Nat.not_le.mpr outputRoom
  simp [runSteps, step?, loopConfig, additionProgram, additionSchema,
    executeInstruction, continueWithRegisters, continueWithBuffers,
    appendExecute, boundedBuffer?, boundedRegister?,
    replaceBoundedRegister?, replaceBoundedBuffer?, firstMissingRegister?,
    readRegisters?, writeRegisters?, lookup,
    leftPresent, rightPresent, leftAt, rightAt, firstValid, secondValid,
    digitOk, room, replaceAt?, at?, List.append_assoc]

theorem left_active_iteration
    (table : FiniteTable) (left right output : List Nat)
    (index first carry digit nextCarry fuel outputLimit rowIndex : Nat)
    (oldLeftDigit oldRightDigit oldOutputDigit : Nat)
    (origins : List String)
    (leftAt : at? left index = some first)
    (rightDone : right.length ≤ index)
    (lookup : lookupTable? [first, 0, carry] table =
      some (rowIndex, ⟨[first, 0, carry], [digit, nextCarry], origins⟩))
    (firstValid : first < 2) (digitValid : digit < 2)
    (outputAtEnd : index = output.length)
    (outputRoom : output.length < outputLimit)
    (receipt : Receipt) :
    runSteps (additionSchema outputLimit) 8
        (loopConfig table left right output index oldLeftDigit oldRightDigit
          carry oldOutputDigit (fuel + 8) receipt) =
      loopConfig table left right (output ++ [digit]) (index + 1)
        first 0 nextCarry digit fuel
        (receipt ++ [
          .execute 4 "left-present?",
          .execute 5 "read-left",
          .execute 7 "right-present?",
          .execute 9 "right-zero",
          .execute 10 "left-active?",
          .execute 13 "rules-4+8",
          .tableRow 13 rowIndex origins,
          .execute 14 "write-digit",
          .execute 15 "next-digit"]) := by
  subst index
  have leftPresent : output.length < left.length := at?_some_lt leftAt
  have rightAbsent : ¬ output.length < right.length := not_lt_of_ge rightDone
  have digitOk : ¬ 2 ≤ digit := Nat.not_le.mpr digitValid
  have room : ¬ outputLimit ≤ output.length := Nat.not_le.mpr outputRoom
  simp [runSteps, step?, loopConfig, additionProgram, additionSchema,
    executeInstruction, continueWithRegisters, continueWithBuffers,
    appendExecute, boundedBuffer?, boundedRegister?,
    replaceBoundedRegister?, replaceBoundedBuffer?, firstMissingRegister?,
    readRegisters?, writeRegisters?, lookup, leftPresent, rightAbsent,
    leftAt, firstValid, digitOk, room, replaceAt?, at?, List.append_assoc]

theorem right_active_iteration
    (table : FiniteTable) (left right output : List Nat)
    (index second carry digit nextCarry fuel outputLimit rowIndex : Nat)
    (oldLeftDigit oldRightDigit oldOutputDigit : Nat)
    (origins : List String)
    (leftDone : left.length ≤ index)
    (rightAt : at? right index = some second)
    (lookup : lookupTable? [0, second, carry] table =
      some (rowIndex, ⟨[0, second, carry], [digit, nextCarry], origins⟩))
    (secondValid : second < 2) (digitValid : digit < 2)
    (outputAtEnd : index = output.length)
    (outputRoom : output.length < outputLimit)
    (receipt : Receipt) :
    runSteps (additionSchema outputLimit) 9
        (loopConfig table left right output index oldLeftDigit oldRightDigit
          carry oldOutputDigit (fuel + 9) receipt) =
      loopConfig table left right (output ++ [digit]) (index + 1)
        0 second nextCarry digit fuel
        (receipt ++ [
          .execute 4 "left-present?",
          .execute 6 "left-zero",
          .execute 7 "right-present?",
          .execute 8 "read-right",
          .execute 10 "left-active?",
          .execute 11 "right-active?",
          .execute 13 "rules-4+8",
          .tableRow 13 rowIndex origins,
          .execute 14 "write-digit",
          .execute 15 "next-digit"]) := by
  subst index
  have leftAbsent : ¬ output.length < left.length := not_lt_of_ge leftDone
  have rightPresent : output.length < right.length := at?_some_lt rightAt
  have digitOk : ¬ 2 ≤ digit := Nat.not_le.mpr digitValid
  have room : ¬ outputLimit ≤ output.length := Nat.not_le.mpr outputRoom
  simp [runSteps, step?, loopConfig, additionProgram, additionSchema,
    executeInstruction, continueWithRegisters, continueWithBuffers,
    appendExecute, boundedBuffer?, boundedRegister?,
    replaceBoundedRegister?, replaceBoundedBuffer?, firstMissingRegister?,
    readRegisters?, writeRegisters?, lookup, leftAbsent, rightPresent,
    rightAt, secondValid, digitOk, room, replaceAt?, at?, List.append_assoc]

theorem carry_only_iteration
    (table : FiniteTable) (left right output : List Nat)
    (index carry digit nextCarry fuel outputLimit rowIndex : Nat)
    (oldLeftDigit oldRightDigit oldOutputDigit : Nat)
    (origins : List String)
    (leftDone : left.length ≤ index) (rightDone : right.length ≤ index)
    (carryActive : carry ≠ 0)
    (lookup : lookupTable? [0, 0, carry] table =
      some (rowIndex, ⟨[0, 0, carry], [digit, nextCarry], origins⟩))
    (digitValid : digit < 2)
    (outputAtEnd : index = output.length)
    (outputRoom : output.length < outputLimit)
    (receipt : Receipt) :
    runSteps (additionSchema outputLimit) 10
        (loopConfig table left right output index oldLeftDigit oldRightDigit
          carry oldOutputDigit (fuel + 10) receipt) =
      loopConfig table left right (output ++ [digit]) (index + 1)
        0 0 nextCarry digit fuel
        (receipt ++ [
          .execute 4 "left-present?",
          .execute 6 "left-zero",
          .execute 7 "right-present?",
          .execute 9 "right-zero",
          .execute 10 "left-active?",
          .execute 11 "right-active?",
          .execute 12 "carry-active?",
          .execute 13 "rules-4+8",
          .tableRow 13 rowIndex origins,
          .execute 14 "write-digit",
          .execute 15 "next-digit"]) := by
  subst index
  have leftAbsent : ¬ output.length < left.length := not_lt_of_ge leftDone
  have rightAbsent : ¬ output.length < right.length := not_lt_of_ge rightDone
  have digitOk : ¬ 2 ≤ digit := Nat.not_le.mpr digitValid
  have room : ¬ outputLimit ≤ output.length := Nat.not_le.mpr outputRoom
  simp [runSteps, step?, loopConfig, additionProgram, additionSchema,
    executeInstruction, continueWithRegisters, continueWithBuffers,
    appendExecute, boundedBuffer?, boundedRegister?,
    replaceBoundedRegister?, replaceBoundedBuffer?, firstMissingRegister?,
    readRegisters?, writeRegisters?, lookup, leftAbsent, rightAbsent,
    carryActive, digitOk, room, replaceAt?, at?, List.append_assoc]

theorem terminal_iteration
    (table : FiniteTable) (left right output : List Nat)
    (index fuel outputLimit oldLeftDigit oldRightDigit oldOutputDigit : Nat)
    (leftDone : left.length ≤ index) (rightDone : right.length ≤ index)
    (outputAtEnd : index = output.length)
    (outputValid : firstInvalidDigit? 2 output = none)
    (receipt : Receipt) :
    runSteps (additionSchema outputLimit) 8
        (loopConfig table left right output index oldLeftDigit oldRightDigit
          0 oldOutputDigit (fuel + 8) receipt) =
      .halted (.value output)
        (receipt ++ [
          .execute 4 "left-present?",
          .execute 6 "left-zero",
          .execute 7 "right-present?",
          .execute 9 "right-zero",
          .execute 10 "left-active?",
          .execute 11 "right-active?",
          .execute 12 "carry-active?",
          .execute 16 "return"]) := by
  subst index
  have leftAbsent : ¬ output.length < left.length := not_lt_of_ge leftDone
  have rightAbsent : ¬ output.length < right.length := not_lt_of_ge rightDone
  simp [runSteps, step?, loopConfig, additionProgram, additionSchema,
    executeInstruction, continueWithRegisters, appendExecute,
    boundedBuffer?, boundedRegister?,
    replaceBoundedRegister?, leftAbsent, rightAbsent, outputValid,
    replaceAt?, at?, List.append_assoc]

def bothEvents (rowIndex : Nat) (origins : List String) : Receipt := [
  .execute 4 "left-present?",
  .execute 5 "read-left",
  .execute 7 "right-present?",
  .execute 8 "read-right",
  .execute 10 "left-active?",
  .execute 13 "rules-4+8",
  .tableRow 13 rowIndex origins,
  .execute 14 "write-digit",
  .execute 15 "next-digit"]

def leftEvents (rowIndex : Nat) (origins : List String) : Receipt := [
  .execute 4 "left-present?",
  .execute 5 "read-left",
  .execute 7 "right-present?",
  .execute 9 "right-zero",
  .execute 10 "left-active?",
  .execute 13 "rules-4+8",
  .tableRow 13 rowIndex origins,
  .execute 14 "write-digit",
  .execute 15 "next-digit"]

def rightEvents (rowIndex : Nat) (origins : List String) : Receipt := [
  .execute 4 "left-present?",
  .execute 6 "left-zero",
  .execute 7 "right-present?",
  .execute 8 "read-right",
  .execute 10 "left-active?",
  .execute 11 "right-active?",
  .execute 13 "rules-4+8",
  .tableRow 13 rowIndex origins,
  .execute 14 "write-digit",
  .execute 15 "next-digit"]

def carryEvents (rowIndex : Nat) (origins : List String) : Receipt := [
  .execute 4 "left-present?",
  .execute 6 "left-zero",
  .execute 7 "right-present?",
  .execute 9 "right-zero",
  .execute 10 "left-active?",
  .execute 11 "right-active?",
  .execute 12 "carry-active?",
  .execute 13 "rules-4+8",
  .tableRow 13 rowIndex origins,
  .execute 14 "write-digit",
  .execute 15 "next-digit"]

def terminalEvents : Receipt := [
  .execute 4 "left-present?",
  .execute 6 "left-zero",
  .execute 7 "right-present?",
  .execute 9 "right-zero",
  .execute 10 "left-active?",
  .execute 11 "right-active?",
  .execute 12 "carry-active?",
  .execute 16 "return"]

/-- A complete finite addition trace through a supplied target table.  Its
indices record the exact RadixDigit instruction budget and receipt suffix. -/
inductive AdditionTrace (table : FiniteTable) :
    List Nat → List Nat → Nat → List Nat → Receipt → Nat → Prop where
  | done : AdditionTrace table [] [] 0 [] terminalEvents 8
  | both
      {first second carry digit nextCarry rowIndex : Nat}
      {left right digits : List Nat} {origins : List String}
      {events : Receipt} {steps : Nat}
      (lookup : lookupTable? [first, second, carry] table =
        some (rowIndex, ⟨[first, second, carry], [digit, nextCarry], origins⟩))
      (firstValid : first < 2) (secondValid : second < 2)
      (digitValid : digit < 2)
      (rest : AdditionTrace table left right nextCarry digits events steps) :
      AdditionTrace table (first :: left) (second :: right) carry
        (digit :: digits) (bothEvents rowIndex origins ++ events) (8 + steps)
  | left
      {first carry digit nextCarry rowIndex : Nat}
      {left digits : List Nat} {origins : List String}
      {events : Receipt} {steps : Nat}
      (lookup : lookupTable? [first, 0, carry] table =
        some (rowIndex, ⟨[first, 0, carry], [digit, nextCarry], origins⟩))
      (firstValid : first < 2) (digitValid : digit < 2)
      (rest : AdditionTrace table left [] nextCarry digits events steps) :
      AdditionTrace table (first :: left) [] carry
        (digit :: digits) (leftEvents rowIndex origins ++ events) (8 + steps)
  | right
      {second carry digit nextCarry rowIndex : Nat}
      {right digits : List Nat} {origins : List String}
      {events : Receipt} {steps : Nat}
      (lookup : lookupTable? [0, second, carry] table =
        some (rowIndex, ⟨[0, second, carry], [digit, nextCarry], origins⟩))
      (secondValid : second < 2) (digitValid : digit < 2)
      (rest : AdditionTrace table [] right nextCarry digits events steps) :
      AdditionTrace table [] (second :: right) carry
        (digit :: digits) (rightEvents rowIndex origins ++ events) (9 + steps)
  | carry
      {carry digit nextCarry rowIndex : Nat}
      {digits : List Nat} {origins : List String}
      {events : Receipt} {steps : Nat}
      (carryActive : carry ≠ 0)
      (lookup : lookupTable? [0, 0, carry] table =
        some (rowIndex, ⟨[0, 0, carry], [digit, nextCarry], origins⟩))
      (digitValid : digit < 2)
      (rest : AdditionTrace table [] [] nextCarry digits events steps) :
      AdditionTrace table [] [] carry
        (digit :: digits) (carryEvents rowIndex origins ++ events) (10 + steps)

/-- Exact semantic requirements on a finite binary addition table. -/
structure BinaryAdditionTable (table : FiniteTable) : Prop where
  sound : ∀ {first second carry digit nextCarry rowIndex : Nat}
      {origins : List String},
    lookupTable? [first, second, carry] table =
        some (rowIndex, ⟨[first, second, carry], [digit, nextCarry], origins⟩) →
    first < 2 → second < 2 → carry < 2 →
    digit < 2 ∧ nextCarry < 2 ∧
      first + second + carry = digit + 2 * nextCarry
  complete : ∀ (first second carry : Nat),
    first < 2 → second < 2 → carry < 2 →
    ∃ rowIndex digit nextCarry origins,
      lookupTable? [first, second, carry] table =
        some (rowIndex, ⟨[first, second, carry], [digit, nextCarry], origins⟩)

/-- The actual table structurally extracted from the supplied radix-two DA
presentation. -/
def radixTwoAdditionTable : FiniteTable :=
  ((inspect? (WaltersZantemaDA.language WaltersZantemaDA.radixTwo)).bind
    additionTableFromProfile?).getD []

def radixTwoExpectedAdditionTable : FiniteTable := [
  ⟨[0, 0, 0], [0, 0], ["3:wz-da:4[radix=2,0,0]"]⟩,
  ⟨[0, 0, 1], [1, 0],
    ["3:wz-da:4[radix=2,0,0]", "11:wz-da:8[radix=2,0]"]⟩,
  ⟨[0, 1, 0], [1, 0], ["4:wz-da:4[radix=2,0,1]"]⟩,
  ⟨[0, 1, 1], [0, 1],
    ["4:wz-da:4[radix=2,0,1]", "12:wz-da:8[radix=2,1]"]⟩,
  ⟨[1, 0, 0], [1, 0], ["5:wz-da:4[radix=2,1,0]"]⟩,
  ⟨[1, 0, 1], [0, 1],
    ["5:wz-da:4[radix=2,1,0]", "12:wz-da:8[radix=2,1]"]⟩,
  ⟨[1, 1, 0], [0, 1], ["6:wz-da:4[radix=2,1,1]"]⟩,
  ⟨[1, 1, 1], [1, 1],
    ["6:wz-da:4[radix=2,1,1]", "11:wz-da:8[radix=2,0]"]⟩]

theorem radixTwoAdditionTable_eq_expected :
    radixTwoAdditionTable = radixTwoExpectedAdditionTable := by
  decide +kernel

theorem radixTwo_compiles_to_addition_table :
    compileAddition? (WaltersZantemaDA.language WaltersZantemaDA.radixTwo) =
      some (additionProgram radixTwoAdditionTable) := by
  decide +kernel

theorem radixTwoAdditionTable_binary :
    BinaryAdditionTable radixTwoAdditionTable := by
  rw [radixTwoAdditionTable_eq_expected]
  constructor
  · intro first second carry digit nextCarry rowIndex origins lookup
      firstValid secondValid carryValid
    interval_cases first <;> interval_cases second <;> interval_cases carry <;>
      simp [radixTwoExpectedAdditionTable, lookupTable?, lookupTableFrom?] at lookup <;>
      omega
  · intro first second carry firstValid secondValid carryValid
    interval_cases first <;> interval_cases second <;> interval_cases carry <;>
      simp [radixTwoExpectedAdditionTable, lookupTable?, lookupTableFrom?]

theorem at?_eq_head?_drop (values : List α) (index : Nat) :
    at? values index = (values.drop index).head? := by
  induction values generalizing index with
  | nil => simp [at?]
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index => simpa [at?] using inductionHypothesis index

theorem drop_succ_eq_tail_drop (values : List α) (index : Nat) :
    values.drop (index + 1) = (values.drop index).tail := by
  induction values generalizing index with
  | nil => simp
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index => exact inductionHypothesis index

theorem length_le_of_drop_eq_nil {values : List α} {index : Nat}
    (empty : values.drop index = []) : values.length ≤ index := by
  have lengthZero : values.length - index = 0 := by
    rw [← List.length_drop, empty]
    rfl
  exact Nat.sub_eq_zero_iff_le.mp lengthZero

theorem firstInvalidDigit?_append (radix : Nat) (left right : List Nat) :
    firstInvalidDigit? radix (left ++ right) =
      match firstInvalidDigit? radix left with
      | some digit => some digit
      | none => firstInvalidDigit? radix right := by
  induction left with
  | nil => rfl
  | cons digit digits inductionHypothesis =>
      simp only [List.cons_append, firstInvalidDigit?]
      split <;> simp_all

theorem AdditionTrace.denotes {table : FiniteTable}
    (tableCorrect : BinaryAdditionTable table)
    {left right digits : List Nat} {carry : Nat}
    {events : Receipt} {steps : Nat}
    (trace : AdditionTrace table left right carry digits events steps)
    (carryValid : carry < 2) :
    WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo digits =
      WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo left +
        WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo right + carry := by
  induction trace with
  | done => simp [WaltersZantemaDA.decodeDigits, WaltersZantemaDA.radixTwo]
  | both lookup firstValid secondValid digitValid rest inductionHypothesis =>
      obtain ⟨_, nextCarryValid, arithmetic⟩ :=
        tableCorrect.sound lookup firstValid secondValid carryValid
      have restDenotes := inductionHypothesis nextCarryValid
      simp only [WaltersZantemaDA.decodeDigits, WaltersZantemaDA.radixTwo,
        Nat.ofDigits_cons] at ⊢ restDenotes
      omega
  | left lookup firstValid digitValid rest inductionHypothesis =>
      obtain ⟨_, nextCarryValid, arithmetic⟩ :=
        tableCorrect.sound lookup firstValid (by omega) carryValid
      have restDenotes := inductionHypothesis nextCarryValid
      simp only [WaltersZantemaDA.decodeDigits, WaltersZantemaDA.radixTwo,
        Nat.ofDigits_cons,
        Nat.ofDigits_nil] at ⊢ restDenotes
      omega
  | right lookup secondValid digitValid rest inductionHypothesis =>
      obtain ⟨_, nextCarryValid, arithmetic⟩ :=
        tableCorrect.sound lookup (by omega) secondValid carryValid
      have restDenotes := inductionHypothesis nextCarryValid
      simp only [WaltersZantemaDA.decodeDigits, WaltersZantemaDA.radixTwo,
        Nat.ofDigits_cons,
        Nat.ofDigits_nil] at ⊢ restDenotes
      omega
  | carry carryActive lookup digitValid rest inductionHypothesis =>
      obtain ⟨_, nextCarryValid, arithmetic⟩ :=
        tableCorrect.sound lookup (by omega) (by omega) carryValid
      have restDenotes := inductionHypothesis nextCarryValid
      simp only [WaltersZantemaDA.decodeDigits, WaltersZantemaDA.radixTwo,
        Nat.ofDigits_cons,
        Nat.ofDigits_nil] at ⊢ restDenotes
      omega

theorem exists_addition_trace {table : FiniteTable}
    (tableCorrect : BinaryAdditionTable table)
    {left right : List Nat}
    (leftRange : WaltersZantemaDA.DigitsInRange WaltersZantemaDA.radixTwo left)
    (rightRange : WaltersZantemaDA.DigitsInRange WaltersZantemaDA.radixTwo right)
    {carry : Nat} (carryValid : carry < 2) :
    ∃ digits events steps, AdditionTrace table left right carry digits events steps := by
  induction left generalizing right carry with
  | nil =>
      induction right generalizing carry with
      | nil =>
          by_cases carryZero : carry = 0
          · subst carry
            exact ⟨[], terminalEvents, 8, .done⟩
          · obtain ⟨rowIndex, digit, nextCarry, origins, lookup⟩ :=
              tableCorrect.complete 0 0 carry (by omega) (by omega) carryValid
            obtain ⟨digitValid, nextCarryValid, arithmetic⟩ :=
              tableCorrect.sound lookup (by omega) (by omega) carryValid
            have nextCarryZero : nextCarry = 0 := by omega
            subst nextCarry
            exact ⟨[digit], carryEvents rowIndex origins ++ terminalEvents,
              10 + 8, .carry carryZero lookup digitValid .done⟩
      | cons second right inductionHypothesis =>
          have secondValid : second < 2 := rightRange second (by simp)
          have rightTailRange :
              WaltersZantemaDA.DigitsInRange WaltersZantemaDA.radixTwo right := by
            intro digit member
            exact rightRange digit (List.mem_cons_of_mem second member)
          obtain ⟨rowIndex, digit, nextCarry, origins, lookup⟩ :=
            tableCorrect.complete 0 second carry (by omega) secondValid carryValid
          obtain ⟨digitValid, nextCarryValid, _⟩ :=
            tableCorrect.sound lookup (by omega) secondValid carryValid
          obtain ⟨digits, events, steps, rest⟩ :=
            inductionHypothesis rightTailRange nextCarryValid
          exact ⟨digit :: digits, rightEvents rowIndex origins ++ events,
            9 + steps, .right lookup secondValid digitValid rest⟩
  | cons first left inductionHypothesis =>
      have firstValid : first < 2 := leftRange first (by simp)
      have leftTailRange :
          WaltersZantemaDA.DigitsInRange WaltersZantemaDA.radixTwo left := by
        intro digit member
        exact leftRange digit (List.mem_cons_of_mem first member)
      cases right with
      | nil =>
          obtain ⟨rowIndex, digit, nextCarry, origins, lookup⟩ :=
            tableCorrect.complete first 0 carry firstValid (by omega) carryValid
          obtain ⟨digitValid, nextCarryValid, _⟩ :=
            tableCorrect.sound lookup firstValid (by omega) carryValid
          have emptyRange :
              WaltersZantemaDA.DigitsInRange WaltersZantemaDA.radixTwo
                ([] : List Nat) := by
            simp [WaltersZantemaDA.DigitsInRange]
          obtain ⟨digits, events, steps, rest⟩ :=
            inductionHypothesis leftTailRange emptyRange nextCarryValid
          exact ⟨digit :: digits, leftEvents rowIndex origins ++ events,
            8 + steps, .left lookup firstValid digitValid rest⟩
      | cons second right =>
          have secondValid : second < 2 := rightRange second (by simp)
          have rightTailRange :
              WaltersZantemaDA.DigitsInRange WaltersZantemaDA.radixTwo right := by
            intro digit member
            exact rightRange digit (List.mem_cons_of_mem second member)
          obtain ⟨rowIndex, digit, nextCarry, origins, lookup⟩ :=
            tableCorrect.complete first second carry firstValid secondValid carryValid
          obtain ⟨digitValid, nextCarryValid, _⟩ :=
            tableCorrect.sound lookup firstValid secondValid carryValid
          obtain ⟨digits, events, steps, rest⟩ :=
            inductionHypothesis leftTailRange rightTailRange nextCarryValid
          exact ⟨digit :: digits, bothEvents rowIndex origins ++ events,
            8 + steps, .both lookup firstValid secondValid digitValid rest⟩

/-- Every finite table trace is executed by the actual RadixDigit addition loop with
the exact instruction count, value, and receipt suffix carried by the trace. -/
theorem loop_executes_trace
    {table : FiniteTable} {leftRemaining rightRemaining digits : List Nat}
    {carry : Nat} {events : Receipt} {steps : Nat}
    (trace : AdditionTrace table leftRemaining rightRemaining carry
      digits events steps)
    (left right output : List Nat) (index : Nat)
    (oldLeftDigit oldRightDigit oldOutputDigit fuel outputLimit : Nat)
    (receipt : Receipt)
    (leftDrop : left.drop index = leftRemaining)
    (rightDrop : right.drop index = rightRemaining)
    (outputAtEnd : index = output.length)
    (outputValid : firstInvalidDigit? 2 output = none)
    (outputBound : output.length + digits.length ≤ outputLimit) :
    runSteps (additionSchema outputLimit) steps
        (loopConfig table left right output index oldLeftDigit oldRightDigit
          carry oldOutputDigit (fuel + steps) receipt) =
      .halted (.value (output ++ digits)) (receipt ++ events) := by
  induction trace generalizing left right output index oldLeftDigit
      oldRightDigit oldOutputDigit fuel receipt with
  | done =>
      have leftDone : left.length ≤ index := length_le_of_drop_eq_nil leftDrop
      have rightDone : right.length ≤ index := length_le_of_drop_eq_nil rightDrop
      simpa [terminalEvents] using
        terminal_iteration table left right output index fuel outputLimit
          oldLeftDigit oldRightDigit oldOutputDigit leftDone rightDone
          outputAtEnd outputValid receipt
  | both lookup firstValid secondValid digitValid rest inductionHypothesis =>
      rename_i first second carry digit nextCarry rowIndex leftRest rightRest
        restDigits origins restEvents restSteps
      have leftAt : at? left index = some first := by
        rw [at?_eq_head?_drop, leftDrop]
        rfl
      have rightAt : at? right index = some second := by
        rw [at?_eq_head?_drop, rightDrop]
        rfl
      have nextLeftDrop : left.drop (index + 1) = leftRest := by
        rw [drop_succ_eq_tail_drop, leftDrop]
        rfl
      have nextRightDrop : right.drop (index + 1) = rightRest := by
        rw [drop_succ_eq_tail_drop, rightDrop]
        rfl
      have nextOutputAtEnd : index + 1 = (output ++ [digit]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have outputRoom : output.length < outputLimit := by
        simp only [List.length_cons] at outputBound
        omega
      have nextOutputValid :
          firstInvalidDigit? 2 (output ++ [digit]) = none := by
        rw [firstInvalidDigit?_append, outputValid]
        simp [firstInvalidDigit?, digitValid]
      have nextOutputBound :
          (output ++ [digit]).length + restDigits.length ≤ outputLimit := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        simp only [List.length_cons] at outputBound
        omega
      rw [runSteps_add (additionSchema outputLimit) 8 restSteps]
      have fuelEq : fuel + (8 + restSteps) = (fuel + restSteps) + 8 := by omega
      rw [fuelEq, both_active_iteration table left right output index first second
        carry digit nextCarry (fuel + restSteps) outputLimit rowIndex oldLeftDigit
        oldRightDigit oldOutputDigit origins leftAt rightAt lookup firstValid
        secondValid digitValid outputAtEnd outputRoom receipt]
      simpa [bothEvents, List.append_assoc] using
        inductionHypothesis left right (output ++ [digit]) (index + 1)
          first second digit fuel (receipt ++ bothEvents rowIndex origins)
          nextLeftDrop nextRightDrop nextOutputAtEnd nextOutputValid
          nextOutputBound
  | left lookup firstValid digitValid rest inductionHypothesis =>
      rename_i first carry digit nextCarry rowIndex leftRest restDigits origins
        restEvents restSteps
      have leftAt : at? left index = some first := by
        rw [at?_eq_head?_drop, leftDrop]
        rfl
      have rightDone : right.length ≤ index :=
        length_le_of_drop_eq_nil rightDrop
      have nextLeftDrop : left.drop (index + 1) = leftRest := by
        rw [drop_succ_eq_tail_drop, leftDrop]
        rfl
      have nextRightDrop : right.drop (index + 1) = [] := by
        rw [drop_succ_eq_tail_drop, rightDrop]
        rfl
      have nextOutputAtEnd : index + 1 = (output ++ [digit]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have outputRoom : output.length < outputLimit := by
        simp only [List.length_cons] at outputBound
        omega
      have nextOutputValid :
          firstInvalidDigit? 2 (output ++ [digit]) = none := by
        rw [firstInvalidDigit?_append, outputValid]
        simp [firstInvalidDigit?, digitValid]
      have nextOutputBound :
          (output ++ [digit]).length + restDigits.length ≤ outputLimit := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        simp only [List.length_cons] at outputBound
        omega
      rw [runSteps_add (additionSchema outputLimit) 8 restSteps]
      have fuelEq : fuel + (8 + restSteps) = (fuel + restSteps) + 8 := by omega
      rw [fuelEq, left_active_iteration table left right output index first carry
        digit nextCarry (fuel + restSteps) outputLimit rowIndex oldLeftDigit
        oldRightDigit oldOutputDigit origins leftAt rightDone lookup firstValid
        digitValid outputAtEnd outputRoom receipt]
      simpa [leftEvents, List.append_assoc] using
        inductionHypothesis left right (output ++ [digit]) (index + 1)
          first 0 digit fuel (receipt ++ leftEvents rowIndex origins)
          nextLeftDrop nextRightDrop nextOutputAtEnd nextOutputValid
          nextOutputBound
  | right lookup secondValid digitValid rest inductionHypothesis =>
      rename_i second carry digit nextCarry rowIndex rightRest restDigits origins
        restEvents restSteps
      have leftDone : left.length ≤ index :=
        length_le_of_drop_eq_nil leftDrop
      have rightAt : at? right index = some second := by
        rw [at?_eq_head?_drop, rightDrop]
        rfl
      have nextLeftDrop : left.drop (index + 1) = [] := by
        rw [drop_succ_eq_tail_drop, leftDrop]
        rfl
      have nextRightDrop : right.drop (index + 1) = rightRest := by
        rw [drop_succ_eq_tail_drop, rightDrop]
        rfl
      have nextOutputAtEnd : index + 1 = (output ++ [digit]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have outputRoom : output.length < outputLimit := by
        simp only [List.length_cons] at outputBound
        omega
      have nextOutputValid :
          firstInvalidDigit? 2 (output ++ [digit]) = none := by
        rw [firstInvalidDigit?_append, outputValid]
        simp [firstInvalidDigit?, digitValid]
      have nextOutputBound :
          (output ++ [digit]).length + restDigits.length ≤ outputLimit := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        simp only [List.length_cons] at outputBound
        omega
      rw [runSteps_add (additionSchema outputLimit) 9 restSteps]
      have fuelEq : fuel + (9 + restSteps) = (fuel + restSteps) + 9 := by omega
      rw [fuelEq, right_active_iteration table left right output index second
        carry digit nextCarry (fuel + restSteps) outputLimit rowIndex oldLeftDigit
        oldRightDigit oldOutputDigit origins leftDone rightAt lookup secondValid
        digitValid outputAtEnd outputRoom receipt]
      simpa [rightEvents, List.append_assoc] using
        inductionHypothesis left right (output ++ [digit]) (index + 1)
          0 second digit fuel (receipt ++ rightEvents rowIndex origins)
          nextLeftDrop nextRightDrop nextOutputAtEnd nextOutputValid
          nextOutputBound
  | carry carryActive lookup digitValid rest inductionHypothesis =>
      rename_i carry digit nextCarry rowIndex restDigits origins restEvents
        restSteps
      have leftDone : left.length ≤ index :=
        length_le_of_drop_eq_nil leftDrop
      have rightDone : right.length ≤ index :=
        length_le_of_drop_eq_nil rightDrop
      have nextLeftDrop : left.drop (index + 1) = [] := by
        rw [drop_succ_eq_tail_drop, leftDrop]
        rfl
      have nextRightDrop : right.drop (index + 1) = [] := by
        rw [drop_succ_eq_tail_drop, rightDrop]
        rfl
      have nextOutputAtEnd : index + 1 = (output ++ [digit]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have outputRoom : output.length < outputLimit := by
        simp only [List.length_cons] at outputBound
        omega
      have nextOutputValid :
          firstInvalidDigit? 2 (output ++ [digit]) = none := by
        rw [firstInvalidDigit?_append, outputValid]
        simp [firstInvalidDigit?, digitValid]
      have nextOutputBound :
          (output ++ [digit]).length + restDigits.length ≤ outputLimit := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        simp only [List.length_cons] at outputBound
        omega
      rw [runSteps_add (additionSchema outputLimit) 10 restSteps]
      have fuelEq : fuel + (10 + restSteps) = (fuel + restSteps) + 10 := by omega
      rw [fuelEq, carry_only_iteration table left right output index carry digit
        nextCarry (fuel + restSteps) outputLimit rowIndex oldLeftDigit oldRightDigit
        oldOutputDigit origins leftDone rightDone carryActive lookup digitValid
        outputAtEnd outputRoom receipt]
      simpa [carryEvents, List.append_assoc] using
        inductionHypothesis left right (output ++ [digit]) (index + 1)
          0 0 digit fuel (receipt ++ carryEvents rowIndex origins)
          nextLeftDrop nextRightDrop nextOutputAtEnd nextOutputValid
          nextOutputBound

def initializationEvents : Receipt := [
  .execute 0 "left-length",
  .execute 1 "right-length",
  .execute 2 "index-zero",
  .execute 3 "carry-zero"]

theorem initialize_addition (table : FiniteTable) (left right : List Nat)
    (fuel outputLimit : Nat) :
    runSteps (additionSchema outputLimit) 4
        (initialAdditionConfig (additionProgram table) left right (fuel + 4)) =
      loopConfig table left right [] 0 0 0 0 0 fuel initializationEvents := by
  simp [runSteps, step?, initialAdditionConfig, loopConfig, additionProgram,
    additionSchema, executeInstruction, continueWithRegisters, appendExecute,
    boundedBuffer?, replaceBoundedRegister?, replaceAt?, at?,
    initializationEvents]

theorem initial_executes_trace
    {table : FiniteTable} {left right digits : List Nat}
    {events : Receipt} {steps : Nat}
    (trace : AdditionTrace table left right 0 digits events steps)
    (outputLimit fuel : Nat)
    (outputBound : digits.length ≤ outputLimit) :
    runSteps (additionSchema outputLimit) (4 + steps)
        (initialAdditionConfig (additionProgram table) left right
          (fuel + 4 + steps)) =
      .halted (.value digits) (initializationEvents ++ events) := by
  rw [runSteps_add (additionSchema outputLimit) 4 steps]
  have fuelEq : fuel + 4 + steps = (fuel + steps) + 4 := by omega
  rw [fuelEq, initialize_addition table left right (fuel + steps) outputLimit]
  simpa using loop_executes_trace trace left right [] 0 0 0 0 fuel outputLimit
    initializationEvents (by simp) (by simp) (by simp)
    (by simp [firstInvalidDigit?]) (by simpa using outputBound)

/-- Universal source-to-target addition preservation for the actual table
extracted from the supplied closed DA presentation. -/
theorem radixTwo_compiled_addition_preserves (first second : Nat) :
    ∃ digits events steps,
      WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo digits =
          first + second ∧
      runSteps (additionSchema digits.length) (4 + steps)
          (initialAdditionConfig (additionProgram radixTwoAdditionTable)
            (WaltersZantemaDA.encodeDigits WaltersZantemaDA.radixTwo first)
            (WaltersZantemaDA.encodeDigits WaltersZantemaDA.radixTwo second)
            (4 + steps)) =
        .halted (.value digits) (initializationEvents ++ events) := by
  have leftRange :=
    (WaltersZantemaDA.encodeDigits_canonical WaltersZantemaDA.radixTwo first).1
  have rightRange :=
    (WaltersZantemaDA.encodeDigits_canonical WaltersZantemaDA.radixTwo second).1
  obtain ⟨digits, events, steps, trace⟩ :=
    exists_addition_trace radixTwoAdditionTable_binary leftRange rightRange
      (carry := 0) (by omega)
  refine ⟨digits, events, steps, ?_, ?_⟩
  · have denotation := trace.denotes radixTwoAdditionTable_binary (by omega)
    simpa [WaltersZantemaDA.decodeDigits_encodeDigits] using denotation
  · simpa [Nat.add_comm] using initial_executes_trace trace digits.length 0
      (by omega)

/-- Any value claimed for the exact trace-driven run is forced to be the
source-authorized sum; the machine cannot invent a different result. -/
theorem radixTwo_compiled_addition_no_invention
    (first second : Nat) {digits observed : List Nat}
    {events observedReceipt : Receipt} {steps : Nat}
    (trace : AdditionTrace radixTwoAdditionTable
      (WaltersZantemaDA.encodeDigits WaltersZantemaDA.radixTwo first)
      (WaltersZantemaDA.encodeDigits WaltersZantemaDA.radixTwo second)
      0 digits events steps)
    (execution :
      runSteps (additionSchema digits.length) (4 + steps)
          (initialAdditionConfig (additionProgram radixTwoAdditionTable)
            (WaltersZantemaDA.encodeDigits WaltersZantemaDA.radixTwo first)
            (WaltersZantemaDA.encodeDigits WaltersZantemaDA.radixTwo second)
            (4 + steps)) =
        .halted (.value observed) observedReceipt) :
    observed = digits ∧
      WaltersZantemaDA.decodeDigits WaltersZantemaDA.radixTwo observed =
        first + second := by
  have expected := initial_executes_trace trace digits.length 0
    (by omega)
  have equalHalted := execution.symm.trans (by simpa [Nat.add_comm] using expected)
  injection equalHalted with observedEq receiptEq
  have observedEq' : observed = digits := by
    injection observedEq
  subst observed
  constructor
  · rfl
  · have denotation := trace.denotes radixTwoAdditionTable_binary (by omega)
    simpa [WaltersZantemaDA.decodeDigits_encodeDigits] using denotation

#print axioms both_active_iteration
#print axioms terminal_iteration
#print axioms loop_executes_trace
#print axioms radixTwo_compiled_addition_preserves
#print axioms radixTwo_compiled_addition_no_invention

end Mettapedia.GSLT.LanguageDef.RadixDigitAdditionCorrectness
