import Mettapedia.GSLT.LanguageDef.C1DigitLanguageDef

/-!
# Primitive relation catalog for the C1 digit machine

The reified C1 LanguageDef delegates bounded instruction work to
`C1ExecuteInstruction`.  This module gives that relation an explicit,
executable mathematical graph and proves that it agrees with the independently
authored closed C1 machine, including lookup-row and fault receipts.
-/

namespace Mettapedia.GSLT.LanguageDef.C1DigitRelationCatalog

open Mettapedia.GSLT.LanguageDef.C1DigitMachine

inductive PrimitiveResult where
  | next (buffers : Buffers) (registers : Registers) (pc : Nat)
      (receipt : Receipt)
  | value (digits : List Nat) (receipt : Receipt)
  | languageFault (detail : LanguageFault) (receipt : Receipt)
  | engineFault (detail : EngineFault) (receipt : Receipt)
  | resourceFault (detail : ResourceFault) (receipt : Receipt)
deriving Repr, DecidableEq

def PrimitiveResult.toConfig (program : Program) (fuel : Nat) :
    PrimitiveResult -> Config
  | .next buffers registers pc receipt =>
      .running program pc buffers registers fuel receipt
  | .value digits receipt => .halted (.value digits) receipt
  | .languageFault detail receipt => .halted (.languageFault detail) receipt
  | .engineFault detail receipt => .halted (.engineFault detail) receipt
  | .resourceFault detail receipt => .halted (.resourceFault detail) receipt

theorem PrimitiveResult.toConfig_injective (program : Program) (fuel : Nat) :
    Function.Injective (PrimitiveResult.toConfig program fuel) := by
  intro first second equal
  cases first <;> cases second <;>
    simp_all [PrimitiveResult.toConfig]

def languageFault (receipt : Receipt) (pc : Nat)
    (detail : LanguageFault) : PrimitiveResult :=
  .languageFault detail (receipt ++ [.languageFault pc detail])

def engineFault (receipt : Receipt) (pc : Nat)
    (detail : EngineFault) : PrimitiveResult :=
  .engineFault detail (receipt ++ [.engineFault pc detail])

def resourceFault (receipt : Receipt) (pc : Nat)
    (detail : ResourceFault) : PrimitiveResult :=
  .resourceFault detail (receipt ++ [.resourceFault pc detail])

def missingBuffer (receipt : Receipt) (pc buffer : Nat) : PrimitiveResult :=
  engineFault receipt pc (.missingBuffer buffer)

def missingRegister (receipt : Receipt) (pc register : Nat) : PrimitiveResult :=
  engineFault receipt pc (.missingRegister register)

/-- The complete executable graph of `C1ExecuteInstruction`. -/
def executePrimitive (schema : Schema) (pc : Nat)
    (buffers : Buffers) (registers : Registers) (receipt : Receipt) :
    Instruction -> PrimitiveResult
  | .set register value next =>
      match replaceBoundedRegister? schema registers register value with
      | some registers' => .next buffers registers' next receipt
      | none => missingRegister receipt pc register
  | .copy source destination next =>
      match boundedRegister? schema registers source with
      | none => missingRegister receipt pc source
      | some value =>
          match replaceBoundedRegister? schema registers destination value with
          | some registers' => .next buffers registers' next receipt
          | none => missingRegister receipt pc destination
  | .increment register next =>
      match boundedRegister? schema registers register with
      | none => missingRegister receipt pc register
      | some value =>
          match replaceBoundedRegister? schema registers register (value + 1) with
          | some registers' => .next buffers registers' next receipt
          | none => missingRegister receipt pc register
  | .length buffer destination next =>
      match boundedBuffer? schema buffers buffer with
      | none => missingBuffer receipt pc buffer
      | some digits =>
          match replaceBoundedRegister? schema registers destination digits.length with
          | some registers' => .next buffers registers' next receipt
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
                | some registers' => .next buffers registers' next receipt
                | none => missingRegister receipt pc destination
              else
                languageFault receipt pc (.invalidDigit digit)
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
                    languageFault receipt pc (.invalidDigit digit)
                  else if _ : digits.length < index then
                    languageFault receipt pc (.sparseWrite buffer index)
                  else
                    let written :=
                      if index = digits.length then
                        some (digits ++ [digit])
                      else
                        replaceAt? digits index digit
                    match written with
                    | none =>
                        engineFault receipt pc (.inconsistentBufferWrite buffer index)
                    | some digits' =>
                        if _ : schema.outputLimit < digits'.length then
                          resourceFault receipt pc (.outputLimit buffer)
                        else
                          match replaceBoundedBuffer? schema buffers buffer digits' with
                          | some buffers' => .next buffers' registers next receipt
                          | none => missingBuffer receipt pc buffer
  | .lookup inputRegisters outputRegisters table next =>
      match firstMissingRegister? schema registers inputRegisters with
      | some register => missingRegister receipt pc register
      | none =>
          match readRegisters? schema registers inputRegisters with
          | none => engineFault receipt pc .malformedTableRow
          | some inputs =>
              match lookupTable? inputs table with
              | none => languageFault receipt pc (.missingTableRow inputs)
              | some (rowIndex, row) =>
                  let receipt' := receipt ++ [.tableRow pc rowIndex row.origins]
                  if row.outputs.length != outputRegisters.length then
                    engineFault receipt' pc .malformedTableRow
                  else
                    match firstMissingRegister? schema registers outputRegisters with
                    | some register => missingRegister receipt' pc register
                    | none =>
                        match writeRegisters? schema registers outputRegisters row.outputs with
                        | none => engineFault receipt' pc .malformedTableRow
                        | some registers' => .next buffers registers' next receipt'
  | .branchLt left right ifTrue ifFalse =>
      match boundedRegister? schema registers left with
      | none => missingRegister receipt pc left
      | some leftValue =>
          match boundedRegister? schema registers right with
          | none => missingRegister receipt pc right
          | some rightValue =>
              .next buffers registers
                (if leftValue < rightValue then ifTrue else ifFalse) receipt
  | .branchEq register value ifTrue ifFalse =>
      match boundedRegister? schema registers register with
      | none => missingRegister receipt pc register
      | some stored =>
          .next buffers registers (if stored = value then ifTrue else ifFalse)
            receipt
  | .jump next => .next buffers registers next receipt
  | .returnBuffer buffer =>
      match boundedBuffer? schema buffers buffer with
      | none => missingBuffer receipt pc buffer
      | some digits =>
          match firstInvalidDigit? schema.radix digits with
          | some digit => languageFault receipt pc (.invalidDigit digit)
          | none => .value digits receipt
  | .failLanguage detail => languageFault receipt pc detail
  | .failEngine detail => engineFault receipt pc detail
  | .failResource detail => resourceFault receipt pc detail

structure Catalog where
  consumeFuel : Nat -> Nat -> Prop
  fetch : Program -> Nat -> Instruction -> Prop
  execute : Nat -> Instruction -> Buffers -> Registers -> Receipt ->
    PrimitiveResult -> Prop
  missingProgramCounter : Program -> Nat -> EngineFault -> Prop
  fuelExhausted : ResourceFault -> Prop

def catalog (schema : Schema) : Catalog where
  consumeFuel := fun fuel nextFuel => fuel = nextFuel + 1
  fetch := fun program pc instruction =>
    ∃ origin, at? program pc = some ⟨origin, instruction⟩
  execute := fun pc instruction buffers registers receipt result =>
    executePrimitive schema pc buffers registers receipt instruction = result
  missingProgramCounter := fun program pc fault =>
    at? program pc = none ∧ fault = .missingProgramCounter pc
  fuelExhausted := fun fault => fault = .fuelExhausted

theorem executePrimitive_agrees
    (schema : Schema) (program : Program) (pc : Nat)
    (buffers : Buffers) (registers : Registers) (fuel : Nat)
    (receipt : Receipt) (instruction : Instruction) :
    (executePrimitive schema pc buffers registers receipt instruction).toConfig
        program fuel =
      executeInstruction schema program pc buffers registers fuel receipt
        instruction := by
  cases instruction <;>
    simp [executePrimitive, PrimitiveResult.toConfig,
      C1DigitMachine.executeInstruction, languageFault, engineFault,
      resourceFault, missingBuffer, missingRegister,
      C1DigitMachine.missingBuffer, C1DigitMachine.missingRegister,
      C1DigitMachine.continueWithRegisters,
      C1DigitMachine.continueWithBuffers,
      C1DigitMachine.haltLanguage, C1DigitMachine.haltEngine,
      C1DigitMachine.haltResource] <;> aesop

theorem catalog_execute_iff_closed
    (schema : Schema) (program : Program) (pc : Nat)
    (buffers : Buffers) (registers : Registers) (fuel : Nat)
    (receipt : Receipt) (instruction : Instruction)
    (result : PrimitiveResult) :
    (catalog schema).execute pc instruction buffers registers receipt result <->
      executeInstruction schema program pc buffers registers fuel receipt
          instruction = result.toConfig program fuel := by
  rw [show (catalog schema).execute pc instruction buffers registers receipt result =
      (executePrimitive schema pc buffers registers receipt instruction = result) by rfl]
  constructor
  · intro equal
    subst result
    exact executePrimitive_agrees schema program pc buffers registers fuel
      receipt instruction |>.symm
  · intro equal
    have agreement := executePrimitive_agrees schema program pc buffers registers
      fuel receipt instruction
    exact PrimitiveResult.toConfig_injective program fuel
      (agreement.trans equal)

theorem lookup_receipt_positive :
    executePrimitive radixTwo 0 [] [1, 1, 0, 9, 9]
        [.execute 0 "rule-4+rule-8"]
        (.lookup [0, 1, 2] [3, 4] carryTable 1) =
      .next [] [1, 1, 0, 0, 1] 1 [
        .execute 0 "rule-4+rule-8",
        .tableRow 0 0 ["rule-4", "rule-8"]] := by
  rfl

theorem missing_lookup_row_negative :
    executePrimitive radixTwo 0 [] [0, 1, 0, 9, 9]
        [.execute 0 "rule-4+rule-8"]
        (.lookup [0, 1, 2] [3, 4] carryTable 1) =
      .languageFault (.missingTableRow [0, 1, 0]) [
        .execute 0 "rule-4+rule-8",
        .languageFault 0 (.missingTableRow [0, 1, 0])] := by
  rfl

#print axioms executePrimitive_agrees
#print axioms catalog_execute_iff_closed

end Mettapedia.GSLT.LanguageDef.C1DigitRelationCatalog
