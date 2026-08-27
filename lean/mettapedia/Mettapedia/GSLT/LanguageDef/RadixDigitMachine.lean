import Mettapedia.GSLT.Core.GSLT

/-!
# Radix-digit buffer operational machine

`RadixDigitMachine` is the smallest target machine needed by the
digit-recursive Walters--Zantema arithmetic compiler. Its semantics is authored
over mathematical buffers, registers, and
instruction graphs.  It does not mention C layouts, emitted source, native
arithmetic providers, or a particular source language.

Programs are carried by running configurations.  Every executed instruction
records its program counter and authored origin, so later compilation theorems
can retain source-rule provenance without making rule names operational.
-/

namespace Mettapedia.GSLT.LanguageDef.RadixDigitMachine

/-- Static limits and the digit radix advertised by a radix-digit realization. -/
structure Schema where
  radix : Nat
  radixAtLeastTwo : 2 <= radix
  bufferLimit : Nat
  registerLimit : Nat
  outputLimit : Nat
deriving Repr

inductive LanguageFault where
  | invalidDigit (digit : Nat)
  | sparseWrite (buffer index : Nat)
  | missingTableRow (inputs : List Nat)
deriving Repr, DecidableEq

inductive EngineFault where
  | missingProgramCounter (pc : Nat)
  | missingBuffer (buffer : Nat)
  | missingRegister (register : Nat)
  | inconsistentBufferWrite (buffer index : Nat)
  | malformedTableRow
deriving Repr, DecidableEq

inductive ResourceFault where
  | outputLimit (buffer : Nat)
  | fuelExhausted
deriving Repr, DecidableEq

inductive Outcome where
  | value (digits : List Nat)
  | languageFault (detail : LanguageFault)
  | engineFault (detail : EngineFault)
  | resourceFault (detail : ResourceFault)
deriving Repr, DecidableEq

/-- RadixDigit instructions are intentionally presentation-neutral.  A compiler may
attach any source-rule identity to a `Cell`; the identity is recorded but never
changes instruction behavior. -/
structure TableRow where
  inputs : List Nat
  outputs : List Nat
  origins : List String
deriving Repr, DecidableEq

abbrev FiniteTable := List TableRow

inductive Instruction where
  | set (register value next : Nat)
  | copy (source destination next : Nat)
  | increment (register next : Nat)
  | length (buffer destination next : Nat)
  | readOrZero (buffer indexRegister destination next : Nat)
  | write (buffer indexRegister digitRegister next : Nat)
  | lookup (inputRegisters outputRegisters : List Nat)
      (table : FiniteTable) (next : Nat)
  | branchLt (left right ifTrue ifFalse : Nat)
  | branchEq (register value ifTrue ifFalse : Nat)
  | jump (next : Nat)
  | returnBuffer (buffer : Nat)
  | failLanguage (detail : LanguageFault)
  | failEngine (detail : EngineFault)
  | failResource (detail : ResourceFault)
deriving Repr, DecidableEq

structure Cell where
  origin : String
  instruction : Instruction
deriving Repr, DecidableEq

abbrev Program := List Cell
abbrev Buffers := List (List Nat)
abbrev Registers := List Nat

inductive Event where
  | execute (pc : Nat) (origin : String)
  | tableRow (pc row : Nat) (origins : List String)
  | languageFault (pc : Nat) (detail : LanguageFault)
  | engineFault (pc : Nat) (detail : EngineFault)
  | resourceFault (pc : Nat) (detail : ResourceFault)
deriving Repr, DecidableEq

abbrev Receipt := List Event

inductive Config where
  | running
      (program : Program)
      (pc : Nat)
      (buffers : Buffers)
      (registers : Registers)
      (fuel : Nat)
      (receipt : Receipt)
  | halted (outcome : Outcome) (receipt : Receipt)
deriving Repr, DecidableEq

def at? : List alpha -> Nat -> Option alpha
  | [], _ => none
  | head :: _, 0 => some head
  | _ :: tail, index + 1 => at? tail index

def replaceAt? : List alpha -> Nat -> alpha -> Option (List alpha)
  | [], _, _ => none
  | _ :: tail, 0, value => some (value :: tail)
  | head :: tail, index + 1, value =>
      (replaceAt? tail index value).map (head :: .)

def boundedBuffer? (schema : Schema) (buffers : Buffers) (buffer : Nat) :
    Option (List Nat) :=
  if buffer < schema.bufferLimit then at? buffers buffer else none

def boundedRegister? (schema : Schema) (registers : Registers)
    (register : Nat) : Option Nat :=
  if register < schema.registerLimit then at? registers register else none

def replaceBoundedRegister? (schema : Schema) (registers : Registers)
    (register value : Nat) : Option Registers :=
  if register < schema.registerLimit then
    replaceAt? registers register value
  else
    none

def replaceBoundedBuffer? (schema : Schema) (buffers : Buffers)
    (buffer : Nat) (digits : List Nat) : Option Buffers :=
  if buffer < schema.bufferLimit then
    replaceAt? buffers buffer digits
  else
    none

def readRegisters? (schema : Schema) (registers : Registers) :
    List Nat -> Option (List Nat)
  | [] => some []
  | register :: rest => do
      let value <- boundedRegister? schema registers register
      let values <- readRegisters? schema registers rest
      pure (value :: values)

def writeRegisters? (schema : Schema) :
    Registers -> List Nat -> List Nat -> Option Registers
  | registers, [], [] => some registers
  | registers, register :: registerRest, value :: valueRest => do
      let registers' <- replaceBoundedRegister? schema registers register value
      writeRegisters? schema registers' registerRest valueRest
  | _, _, _ => none

def firstMissingRegister? (schema : Schema) (registers : Registers) :
    List Nat -> Option Nat
  | [] => none
  | register :: rest =>
      match boundedRegister? schema registers register with
      | none => some register
      | some _ => firstMissingRegister? schema registers rest

def lookupTableFrom? (inputs : List Nat) :
    Nat -> FiniteTable -> Option (Nat × TableRow)
  | _, [] => none
  | index, row :: rows =>
      if row.inputs = inputs then some (index, row)
      else lookupTableFrom? inputs (index + 1) rows

def lookupTable? (inputs : List Nat) (table : FiniteTable) :
    Option (Nat × TableRow) :=
  lookupTableFrom? inputs 0 table

def firstInvalidDigit? (radix : Nat) : List Nat -> Option Nat
  | [] => none
  | digit :: digits =>
      if digit < radix then firstInvalidDigit? radix digits else some digit

def appendExecute (receipt : Receipt) (pc : Nat) (origin : String) : Receipt :=
  receipt ++ [.execute pc origin]

def haltLanguage (receipt : Receipt) (pc : Nat)
    (detail : LanguageFault) : Config :=
  .halted (.languageFault detail) (receipt ++ [.languageFault pc detail])

def haltEngine (receipt : Receipt) (pc : Nat)
    (detail : EngineFault) : Config :=
  .halted (.engineFault detail) (receipt ++ [.engineFault pc detail])

def haltResource (receipt : Receipt) (pc : Nat)
    (detail : ResourceFault) : Config :=
  .halted (.resourceFault detail) (receipt ++ [.resourceFault pc detail])

def missingBuffer (receipt : Receipt) (pc buffer : Nat) : Config :=
  haltEngine receipt pc (.missingBuffer buffer)

def missingRegister (receipt : Receipt) (pc register : Nat) : Config :=
  haltEngine receipt pc (.missingRegister register)

/-- Continue after an instruction has replaced registers.  This is public so
relation-catalog realizations can state their correspondence without duplicating
the machine's continuation equation. -/
def continueWithRegisters (program : Program) (next : Nat)
    (buffers : Buffers) (registers : Registers) (fuel : Nat)
    (receipt : Receipt) : Config :=
  .running program next buffers registers fuel receipt

/-- Continue after an instruction has replaced buffers. -/
def continueWithBuffers (program : Program) (next : Nat)
    (buffers : Buffers) (registers : Registers) (fuel : Nat)
    (receipt : Receipt) : Config :=
  .running program next buffers registers fuel receipt

/-- Execute one fetched instruction.  `fuel` is already the remaining fuel and
`receipt` already contains the instruction event. -/
def executeInstruction (schema : Schema) (program : Program) (pc : Nat)
    (buffers : Buffers) (registers : Registers) (fuel : Nat)
    (receipt : Receipt) : Instruction -> Config
  | .set register value next =>
      match replaceBoundedRegister? schema registers register value with
      | some registers' =>
          continueWithRegisters program next buffers registers' fuel receipt
      | none => missingRegister receipt pc register
  | .copy source destination next =>
      match boundedRegister? schema registers source with
      | none => missingRegister receipt pc source
      | some value =>
          match replaceBoundedRegister? schema registers destination value with
          | some registers' =>
              continueWithRegisters program next buffers registers' fuel receipt
          | none => missingRegister receipt pc destination
  | .increment register next =>
      match boundedRegister? schema registers register with
      | none => missingRegister receipt pc register
      | some value =>
          match replaceBoundedRegister? schema registers register (value + 1) with
          | some registers' =>
              continueWithRegisters program next buffers registers' fuel receipt
          | none => missingRegister receipt pc register
  | .length buffer destination next =>
      match boundedBuffer? schema buffers buffer with
      | none => missingBuffer receipt pc buffer
      | some digits =>
          match replaceBoundedRegister? schema registers destination digits.length with
          | some registers' =>
              continueWithRegisters program next buffers registers' fuel receipt
          | none => missingRegister receipt pc destination
  | .readOrZero buffer indexRegister destination next =>
      match boundedBuffer? schema buffers buffer with
      | none => missingBuffer receipt pc buffer
      | some digits =>
          match boundedRegister? schema registers indexRegister with
          | none => missingRegister receipt pc indexRegister
          | some index =>
              let digit := (at? digits index).getD 0
              if _ : digit < schema.radix then
                match replaceBoundedRegister? schema registers destination digit with
                | some registers' =>
                    continueWithRegisters program next buffers registers' fuel receipt
                | none => missingRegister receipt pc destination
              else
                haltLanguage receipt pc (.invalidDigit digit)
  | .write buffer indexRegister digitRegister next =>
      match boundedBuffer? schema buffers buffer with
      | none => missingBuffer receipt pc buffer
      | some digits =>
          match boundedRegister? schema registers indexRegister with
          | none => missingRegister receipt pc indexRegister
          | some index =>
              match boundedRegister? schema registers digitRegister with
              | none => missingRegister receipt pc digitRegister
              | some digit =>
                  if _ : schema.radix <= digit then
                    haltLanguage receipt pc (.invalidDigit digit)
                  else if _ : digits.length < index then
                    haltLanguage receipt pc (.sparseWrite buffer index)
                  else
                    let written :=
                      if index = digits.length then
                        some (digits ++ [digit])
                      else
                        replaceAt? digits index digit
                    match written with
                    | none =>
                        haltEngine receipt pc (.inconsistentBufferWrite buffer index)
                    | some digits' =>
                        if _ : schema.outputLimit < digits'.length then
                          haltResource receipt pc (.outputLimit buffer)
                        else
                          match replaceBoundedBuffer? schema buffers buffer digits' with
                          | some buffers' =>
                              continueWithBuffers program next buffers' registers fuel receipt
                          | none => missingBuffer receipt pc buffer
  | .lookup inputRegisters outputRegisters table next =>
      match firstMissingRegister? schema registers inputRegisters with
      | some register => missingRegister receipt pc register
      | none =>
          match readRegisters? schema registers inputRegisters with
          | none => haltEngine receipt pc .malformedTableRow
          | some inputs =>
              match lookupTable? inputs table with
              | none => haltLanguage receipt pc (.missingTableRow inputs)
              | some (rowIndex, row) =>
                  let receipt' := receipt ++ [.tableRow pc rowIndex row.origins]
                  if row.outputs.length != outputRegisters.length then
                    haltEngine receipt' pc .malformedTableRow
                  else
                    match firstMissingRegister? schema registers outputRegisters with
                    | some register => missingRegister receipt' pc register
                    | none =>
                        match writeRegisters? schema registers outputRegisters row.outputs with
                        | none => haltEngine receipt' pc .malformedTableRow
                        | some registers' =>
                            continueWithRegisters program next buffers registers'
                              fuel receipt'
  | .branchLt left right ifTrue ifFalse =>
      match boundedRegister? schema registers left with
      | none => missingRegister receipt pc left
      | some leftValue =>
          match boundedRegister? schema registers right with
          | none => missingRegister receipt pc right
          | some rightValue =>
              .running program (if leftValue < rightValue then ifTrue else ifFalse)
                buffers registers fuel receipt
  | .branchEq register value ifTrue ifFalse =>
      match boundedRegister? schema registers register with
      | none => missingRegister receipt pc register
      | some stored =>
          .running program (if stored = value then ifTrue else ifFalse)
            buffers registers fuel receipt
  | .jump next => .running program next buffers registers fuel receipt
  | .returnBuffer buffer =>
      match boundedBuffer? schema buffers buffer with
      | none => missingBuffer receipt pc buffer
      | some digits =>
          match firstInvalidDigit? schema.radix digits with
          | some digit => haltLanguage receipt pc (.invalidDigit digit)
          | none => .halted (.value digits) receipt
  | .failLanguage detail => haltLanguage receipt pc detail
  | .failEngine detail => haltEngine receipt pc detail
  | .failResource detail => haltResource receipt pc detail

/-- The complete deterministic one-step semantics.  Fuel exhaustion and invalid
program counters are observable machine faults, not failure of the meta-level
function. -/
def step? (schema : Schema) : Config -> Option Config
  | .halted _ _ => none
  | .running _ pc _ _ 0 receipt =>
      some (haltResource receipt pc .fuelExhausted)
  | .running program pc buffers registers (fuel + 1) receipt =>
      match at? program pc with
      | none =>
          some (haltEngine receipt pc (.missingProgramCounter pc))
      | some cell =>
          let receipt' := appendExecute receipt pc cell.origin
          some (executeInstruction schema program pc buffers registers fuel
            receipt' cell.instruction)

def runSteps (schema : Schema) : Nat -> Config -> Config
  | 0, config => config
  | steps + 1, config =>
      match step? schema config with
      | none => config
      | some next => runSteps schema steps next

theorem runSteps_eq_self_of_step_none (schema : Schema) (steps : Nat)
    (config : Config) (normal : step? schema config = none) :
    runSteps schema steps config = config := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      simp [runSteps, normal]

/-- Running two finite instruction budgets in sequence is the same as running
their sum.  This is the composition law used by compiler loop invariants. -/
theorem runSteps_add (schema : Schema) (first second : Nat) (config : Config) :
    runSteps schema (first + second) config =
      runSteps schema second (runSteps schema first config) := by
  induction first generalizing config with
  | zero => simp [runSteps]
  | succ first inductionHypothesis =>
      simp only [Nat.succ_add, runSteps]
      cases nextStep : step? schema config with
      | none =>
          exact (runSteps_eq_self_of_step_none schema second config nextStep).symm
      | some next => exact inductionHypothesis next

/-- The authored RadixDigit operational GSLT.  Equality is the only equation; all
machine behavior is supplied by `step?`. -/
def radixDigitGSLT (schema : Schema) : Mettapedia.GSLT.GSLT where
  Term := Config
  equations := {
    r := Eq
    iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  }
  rewrites := fun source target => step? schema source = some target
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

theorem step_iff (schema : Schema) (source target : Config) :
    (radixDigitGSLT schema).Step source target <-> step? schema source = some target :=
  Iff.rfl

theorem step_deterministic (schema : Schema) {source first second : Config}
    (firstStep : (radixDigitGSLT schema).Step source first)
    (secondStep : (radixDigitGSLT schema).Step source second) :
    first = second := by
  exact Option.some.inj (firstStep.symm.trans secondStep)

theorem normal_iff_step_none (schema : Schema) (source : Config) :
    (radixDigitGSLT schema).IsNormalForm source <-> step? schema source = none := by
  constructor
  · intro normal
    cases result : step? schema source with
    | none => rfl
    | some target =>
        exact False.elim (normal ⟨target, result⟩)
  · intro noStep redex
    obtain ⟨target, step⟩ := redex
    change step? schema source = some target at step
    rw [noStep] at step
    contradiction

theorem halted_is_normal (schema : Schema) (outcome : Outcome)
    (receipt : Receipt) :
    (radixDigitGSLT schema).IsNormalForm (.halted outcome receipt) := by
  intro redex
  obtain ⟨target, step⟩ := redex
  change step? schema (.halted outcome receipt) = some target at step
  simp [step?] at step

def radixTwo : Schema where
  radix := 2
  radixAtLeastTwo := by decide
  bufferLimit := 3
  registerLimit := 8
  outputLimit := 16

def lengthReturnProgram : Program := [
  ⟨"length", .length 0 0 1⟩,
  ⟨"return", .returnBuffer 0⟩
]

def lengthReturnInitial : Config :=
  .running lengthReturnProgram 0 [[1, 0, 1]] [0] 2 []

theorem length_then_return_positive :
    runSteps radixTwo 2 lengthReturnInitial =
      .halted (.value [1, 0, 1]) [
        .execute 0 "length",
        .execute 1 "return"] := by
  rfl

def appendOneProgram : Program := [
  ⟨"append", .write 0 0 1 1⟩
]

theorem bounded_write_positive :
    step? radixTwo (.running appendOneProgram 0 [[]] [0, 1] 1 []) =
      some (.running appendOneProgram 1 [[1]] [0, 1] 0 [
        .execute 0 "append"]) := by
  rfl

theorem sparse_write_negative :
    step? radixTwo (.running appendOneProgram 0 [[]] [1, 1] 1 []) =
      some (.halted (.languageFault (.sparseWrite 0 1)) [
        .execute 0 "append",
        .languageFault 0 (.sparseWrite 0 1)]) := by
  rfl

def returnProgram : Program := [
  ⟨"return", .returnBuffer 0⟩
]

theorem invalid_digit_negative :
    step? radixTwo (.running returnProgram 0 [[2]] [] 1 []) =
      some (.halted (.languageFault (.invalidDigit 2)) [
        .execute 0 "return",
        .languageFault 0 (.invalidDigit 2)]) := by
  rfl

def carryTable : FiniteTable := [
  ⟨[1, 1, 0], [0, 1], ["rule-4", "rule-8"]⟩
]

def carryLookupProgram : Program := [
  ⟨"rule-4+rule-8", .lookup [0, 1, 2] [3, 4] carryTable 1⟩
]

theorem finite_lookup_positive :
    step? radixTwo
        (.running carryLookupProgram 0 [] [1, 1, 0, 9, 9] 1 []) =
      some (.running carryLookupProgram 1 [] [1, 1, 0, 0, 1] 0 [
        .execute 0 "rule-4+rule-8",
        .tableRow 0 0 ["rule-4", "rule-8"]]) := by
  rfl

theorem missing_lookup_row_negative :
    step? radixTwo
        (.running carryLookupProgram 0 [] [0, 1, 0, 9, 9] 1 []) =
      some (.halted (.languageFault (.missingTableRow [0, 1, 0])) [
        .execute 0 "rule-4+rule-8",
        .languageFault 0 (.missingTableRow [0, 1, 0])]) := by
  rfl

def loopProgram : Program := [
  ⟨"loop", .jump 0⟩
]

theorem bounded_loop_exhausts_fuel :
    runSteps radixTwo 3 (.running loopProgram 0 [] [] 2 []) =
      .halted (.resourceFault .fuelExhausted) [
        .execute 0 "loop",
        .execute 0 "loop",
        .resourceFault 0 .fuelExhausted] := by
  rfl

end Mettapedia.GSLT.LanguageDef.RadixDigitMachine
