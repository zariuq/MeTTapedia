import Mettapedia.GSLT.LanguageDef.M0GCIndexedBodyAddressByteMachineRealization
import Mathlib.Tactic

/-!
# On-demand M0GC body-record loads in the checked byte-machine

After a table index has been qualified and resolved to a physical address,
M0GC needs only the selected record.  This module lowers the three canonical
record shapes into small fixed byte-machine programs:

* a 20-byte `TermNode`,
* a 32-byte `ProofNode`, and
* a four-byte scalar used by child, argument, and premise-reference tables.

Each independent source operation uses checked address additions and typed
little-endian loads.  Each target program exposes every field load; no
instruction means "decode term" or "decode proof".  Exact source/target
agreement includes all intermediate overflow and short-read faults.

Maturity boundary: this is a connected intermediate proof of concept, not an
endgame record loop or production checker.  Address qualification remains the
separate proved resolver and will be fused compositionally later.  This module
does prove that its term and proof loads agree with the canonical flat-body
readers, plus raw scalar-read agreement.  It does not yet compose indexed
address qualification with these loads into one program, validate record
contents or cross-table references, compute the body checksum, replay a proof,
emit C, or implement the official MM0/MMB format.  Register assignments are
proof-oriented and not a claim of final allocation quality.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCBodyRecordByteMachineRealization

open Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory
open Mettapedia.GSLT.LanguageDef.M0GCCheckedByteMachineIR
open Mettapedia.GSLT.LanguageDef.M0GCFlatBodyLoaderCorrespondence
open Mettapedia.GSLT.LanguageDef.M0GCFlatHeaderLoaderCorrespondence

attribute [local simp] bind Except.bind pure Except.pure

/-! ## Term records -/

namespace Term

/-- Independent checked load of one term record at an already-qualified
physical address. -/
def readDetailed (memory : ByteMemory) (address : UInt64) :
    Except Fault TermNode := do
  let symbol <- loadWord16Detailed memory address
  let arityAddress <- addAddressDetailed address 2
  let arity <- loadWord16Detailed memory arityAddress
  let childStartAddress <- addAddressDetailed arityAddress 2
  let childStart <- loadWord32Detailed memory childStartAddress
  let reservedAddress <- addAddressDetailed childStartAddress 4
  let reserved <- loadWord32Detailed memory reservedAddress
  let hashAddress <- addAddressDetailed reservedAddress 4
  let termHash <- loadWord64Detailed memory hashAddress
  pure { symbol, arity, childStart, reserved, termHash }

def shape : RegisterShape where
  byteCount := 0
  word16Count := 2
  word32Count := 2
  word64Count := 1
  addressCount := 2
  flagCount := 0

def symbol : Word16Register shape := ⟨0, by decide⟩
def arity : Word16Register shape := ⟨1, by decide⟩
def childStart : Word32Register shape := ⟨0, by decide⟩
def reserved : Word32Register shape := ⟨1, by decide⟩
def termHash : Word64Register shape := ⟨0, by decide⟩
def cursor : AddressRegister shape := ⟨0, by decide⟩
def delta : AddressRegister shape := ⟨1, by decide⟩

attribute [local simp] shape symbol arity childStart reserved termHash cursor
  delta

def program : Program shape where
  code := #[
    .loadWord16LE symbol cursor,
    .constAddress delta 2,
    .addAddressChecked cursor cursor delta,
    .loadWord16LE arity cursor,
    .addAddressChecked cursor cursor delta,
    .loadWord32LE childStart cursor,
    .constAddress delta 4,
    .addAddressChecked cursor cursor delta,
    .loadWord32LE reserved cursor,
    .addAddressChecked cursor cursor delta,
    .loadWord64LE termHash cursor,
    .halt true]

def initialRegisters (address : UInt64) : RegisterFile shape :=
  (RegisterFile.zero shape).writeAddress cursor address

def execute (memory : ByteMemory) (address : UInt64) : MachineState shape :=
  runSteps program 12 (.running 0 (initialRegisters address) memory)

def nodeOfRegisters (registers : RegisterFile shape) : TermNode :=
  { symbol := registers.words16 symbol
    arity := registers.words16 arity
    childStart := registers.words32 childStart
    reserved := registers.words32 reserved
    termHash := registers.words64 termHash }

def observe : MachineState shape -> Option (Except Fault TermNode)
  | .running _ _ _ => none
  | .halted false _ _ => none
  | .halted true registers _ => some (.ok (nodeOfRegisters registers))
  | .faulted reason _ _ => some (.error reason)

theorem execute_agrees_readDetailed (memory : ByteMemory) (address : UInt64) :
    observe (execute memory address) = some (readDetailed memory address) := by
  cases hSymbol : memory.loadUInt16LE? address with
  | none =>
      simp [execute, initialRegisters, program, observe, readDetailed,
        loadWord16Detailed, runSteps, step, executeInstruction,
        hSymbol]
  | some symbolValue =>
      cases hArityAddress : checkedAdd address 2 with
      | none =>
          simp [execute, initialRegisters, program, observe, readDetailed,
            loadWord16Detailed, addAddressDetailed, runSteps, step,
            executeInstruction, continueAt, hSymbol, hArityAddress]
      | some arityAddressValue =>
          cases hArity : memory.loadUInt16LE? arityAddressValue with
          | none =>
              simp [execute, initialRegisters, program, observe, readDetailed,
                loadWord16Detailed, addAddressDetailed, runSteps, step,
                executeInstruction, continueAt, hSymbol, hArityAddress,
                hArity]
          | some arityValue =>
              cases hChildAddress : checkedAdd arityAddressValue 2 with
              | none =>
                  simp [execute, initialRegisters, program, observe,
                    readDetailed, loadWord16Detailed, addAddressDetailed,
                    runSteps, step, executeInstruction, continueAt, hSymbol,
                    hArityAddress, hArity, hChildAddress]
              | some childAddressValue =>
                  cases hChild : memory.loadUInt32LE? childAddressValue with
                  | none =>
                      simp [execute, initialRegisters, program, observe,
                        readDetailed, loadWord16Detailed, loadWord32Detailed,
                        addAddressDetailed, runSteps, step,
                        executeInstruction, continueAt, hSymbol,
                        hArityAddress, hArity, hChildAddress, hChild]
                  | some childValue =>
                      cases hReservedAddress :
                          checkedAdd childAddressValue 4 with
                      | none =>
                          simp [execute, initialRegisters, program, observe,
                            readDetailed, loadWord16Detailed,
                            loadWord32Detailed, addAddressDetailed, runSteps,
                            step, executeInstruction, continueAt, hSymbol,
                            hArityAddress, hArity, hChildAddress, hChild,
                            hReservedAddress]
                      | some reservedAddressValue =>
                          cases hReserved :
                              memory.loadUInt32LE? reservedAddressValue with
                          | none =>
                              simp [execute, initialRegisters, program,
                                observe, readDetailed, loadWord16Detailed,
                                loadWord32Detailed, addAddressDetailed,
                                runSteps, step, executeInstruction,
                                continueAt, hSymbol, hArityAddress, hArity,
                                hChildAddress, hChild, hReservedAddress,
                                hReserved]
                          | some reservedValue =>
                              cases hHashAddress :
                                  checkedAdd reservedAddressValue 4 with
                              | none =>
                                  simp [execute, initialRegisters, program,
                                    observe, readDetailed,
                                    loadWord16Detailed, loadWord32Detailed,
                                    addAddressDetailed, runSteps, step,
                                    executeInstruction, continueAt, hSymbol,
                                    hArityAddress, hArity, hChildAddress,
                                    hChild, hReservedAddress, hReserved,
                                    hHashAddress]
                              | some hashAddressValue =>
                                  cases hHash :
                                      memory.loadUInt64LE? hashAddressValue with
                                  | none =>
                                      simp [execute, initialRegisters,
                                        program, observe, readDetailed,
                                        loadWord16Detailed,
                                        loadWord32Detailed,
                                        loadWord64Detailed,
                                        addAddressDetailed, runSteps, step,
                                        executeInstruction, continueAt,
                                        hSymbol, hArityAddress, hArity,
                                        hChildAddress, hChild,
                                        hReservedAddress, hReserved,
                                        hHashAddress, hHash]
                                  | some hashValue =>
                                      simp [execute, initialRegisters,
                                        program, observe, nodeOfRegisters,
                                        readDetailed, loadWord16Detailed,
                                        loadWord32Detailed,
                                        loadWord64Detailed,
                                        addAddressDetailed, runSteps, step,
                                        executeInstruction, continueAt,
                                        hSymbol, hArityAddress, hArity,
                                        hChildAddress, hChild,
                                        hReservedAddress, hReserved,
                                        hHashAddress, hHash]

end Term

/-! ## Proof records -/

namespace Proof

/-- Independent checked load of one chronological proof record. -/
def readDetailed (memory : ByteMemory) (address : UInt64) :
    Except Fault ProofNode := do
  let opcode <- loadWord16Detailed memory address
  let ruleAddress <- addAddressDetailed address 2
  let rule <- loadWord16Detailed memory ruleAddress
  let argumentCountAddress <- addAddressDetailed ruleAddress 2
  let argumentCount <- loadWord16Detailed memory argumentCountAddress
  let premiseCountAddress <- addAddressDetailed argumentCountAddress 2
  let premiseCount <- loadWord16Detailed memory premiseCountAddress
  let argumentStartAddress <- addAddressDetailed premiseCountAddress 2
  let argumentStart <- loadWord32Detailed memory argumentStartAddress
  let premiseStartAddress <- addAddressDetailed argumentStartAddress 4
  let premiseStart <- loadWord32Detailed memory premiseStartAddress
  let resultTermAddress <- addAddressDetailed premiseStartAddress 4
  let resultTerm <- loadWord32Detailed memory resultTermAddress
  let reservedAddress <- addAddressDetailed resultTermAddress 4
  let reserved <- loadWord32Detailed memory reservedAddress
  let fingerprintAddress <- addAddressDetailed reservedAddress 4
  let ruleFingerprint <- loadWord64Detailed memory fingerprintAddress
  pure
    { opcode, rule, argumentCount, premiseCount, argumentStart, premiseStart,
      resultTerm, reserved, ruleFingerprint }

def shape : RegisterShape where
  byteCount := 0
  word16Count := 4
  word32Count := 4
  word64Count := 1
  addressCount := 2
  flagCount := 0

def opcode : Word16Register shape := ⟨0, by decide⟩
def rule : Word16Register shape := ⟨1, by decide⟩
def argumentCount : Word16Register shape := ⟨2, by decide⟩
def premiseCount : Word16Register shape := ⟨3, by decide⟩
def argumentStart : Word32Register shape := ⟨0, by decide⟩
def premiseStart : Word32Register shape := ⟨1, by decide⟩
def resultTerm : Word32Register shape := ⟨2, by decide⟩
def reserved : Word32Register shape := ⟨3, by decide⟩
def ruleFingerprint : Word64Register shape := ⟨0, by decide⟩
def cursor : AddressRegister shape := ⟨0, by decide⟩
def delta : AddressRegister shape := ⟨1, by decide⟩

attribute [local simp] shape opcode rule argumentCount premiseCount
  argumentStart premiseStart resultTerm reserved ruleFingerprint cursor delta

def program : Program shape where
  code := #[
    .loadWord16LE opcode cursor,
    .constAddress delta 2,
    .addAddressChecked cursor cursor delta,
    .loadWord16LE rule cursor,
    .addAddressChecked cursor cursor delta,
    .loadWord16LE argumentCount cursor,
    .addAddressChecked cursor cursor delta,
    .loadWord16LE premiseCount cursor,
    .addAddressChecked cursor cursor delta,
    .loadWord32LE argumentStart cursor,
    .constAddress delta 4,
    .addAddressChecked cursor cursor delta,
    .loadWord32LE premiseStart cursor,
    .addAddressChecked cursor cursor delta,
    .loadWord32LE resultTerm cursor,
    .addAddressChecked cursor cursor delta,
    .loadWord32LE reserved cursor,
    .addAddressChecked cursor cursor delta,
    .loadWord64LE ruleFingerprint cursor,
    .halt true]

def initialRegisters (address : UInt64) : RegisterFile shape :=
  (RegisterFile.zero shape).writeAddress cursor address

def execute (memory : ByteMemory) (address : UInt64) : MachineState shape :=
  runSteps program 20 (.running 0 (initialRegisters address) memory)

def nodeOfRegisters (registers : RegisterFile shape) : ProofNode :=
  { opcode := registers.words16 opcode
    rule := registers.words16 rule
    argumentCount := registers.words16 argumentCount
    premiseCount := registers.words16 premiseCount
    argumentStart := registers.words32 argumentStart
    premiseStart := registers.words32 premiseStart
    resultTerm := registers.words32 resultTerm
    reserved := registers.words32 reserved
    ruleFingerprint := registers.words64 ruleFingerprint }

def observe : MachineState shape -> Option (Except Fault ProofNode)
  | .running _ _ _ => none
  | .halted false _ _ => none
  | .halted true registers _ => some (.ok (nodeOfRegisters registers))
  | .faulted reason _ _ => some (.error reason)

theorem execute_agrees_readDetailed (memory : ByteMemory) (address : UInt64) :
    observe (execute memory address) = some (readDetailed memory address) := by
  cases hOpcode : memory.loadUInt16LE? address with
  | none =>
      simp [execute, initialRegisters, program, observe, readDetailed,
        loadWord16Detailed, runSteps, step, executeInstruction,
        hOpcode]
  | some opcodeValue =>
      cases hRuleAddress : checkedAdd address 2 with
      | none =>
          simp [execute, initialRegisters, program, observe, readDetailed,
            loadWord16Detailed, addAddressDetailed, runSteps, step,
            executeInstruction, continueAt, hOpcode, hRuleAddress]
      | some ruleAddressValue =>
          cases hRule : memory.loadUInt16LE? ruleAddressValue with
          | none =>
              simp [execute, initialRegisters, program, observe, readDetailed,
                loadWord16Detailed, addAddressDetailed, runSteps, step,
                executeInstruction, continueAt, hOpcode, hRuleAddress, hRule]
          | some ruleValue =>
              cases hArgumentCountAddress :
                  checkedAdd ruleAddressValue 2 with
              | none =>
                  simp [execute, initialRegisters, program, observe,
                    readDetailed, loadWord16Detailed, addAddressDetailed,
                    runSteps, step, executeInstruction, continueAt, hOpcode,
                    hRuleAddress, hRule, hArgumentCountAddress]
              | some argumentCountAddressValue =>
                  cases hArgumentCount :
                      memory.loadUInt16LE? argumentCountAddressValue with
                  | none =>
                      simp [execute, initialRegisters, program, observe,
                        readDetailed, loadWord16Detailed, addAddressDetailed,
                        runSteps, step, executeInstruction, continueAt,
                        hOpcode, hRuleAddress, hRule, hArgumentCountAddress,
                        hArgumentCount]
                  | some argumentCountValue =>
                      cases hPremiseCountAddress :
                          checkedAdd argumentCountAddressValue 2 with
                      | none =>
                          simp [execute, initialRegisters, program, observe,
                            readDetailed, loadWord16Detailed,
                            addAddressDetailed, runSteps, step,
                            executeInstruction, continueAt, hOpcode,
                            hRuleAddress, hRule, hArgumentCountAddress,
                            hArgumentCount, hPremiseCountAddress]
                      | some premiseCountAddressValue =>
                          cases hPremiseCount :
                              memory.loadUInt16LE? premiseCountAddressValue with
                          | none =>
                              simp [execute, initialRegisters, program,
                                observe, readDetailed, loadWord16Detailed,
                                addAddressDetailed, runSteps, step,
                                executeInstruction, continueAt, hOpcode,
                                hRuleAddress, hRule, hArgumentCountAddress,
                                hArgumentCount, hPremiseCountAddress,
                                hPremiseCount]
                          | some premiseCountValue =>
                              cases hArgumentStartAddress :
                                  checkedAdd premiseCountAddressValue 2 with
                              | none =>
                                  simp [execute, initialRegisters, program,
                                    observe, readDetailed,
                                    loadWord16Detailed, addAddressDetailed,
                                    runSteps, step, executeInstruction,
                                    continueAt, hOpcode, hRuleAddress, hRule,
                                    hArgumentCountAddress, hArgumentCount,
                                    hPremiseCountAddress, hPremiseCount,
                                    hArgumentStartAddress]
                              | some argumentStartAddressValue =>
                                  cases hArgumentStart : memory.loadUInt32LE?
                                      argumentStartAddressValue with
                                  | none =>
                                      simp [execute, initialRegisters,
                                        program, observe, readDetailed,
                                        loadWord16Detailed,
                                        loadWord32Detailed,
                                        addAddressDetailed, runSteps, step,
                                        executeInstruction, continueAt,
                                        hOpcode, hRuleAddress, hRule,
                                        hArgumentCountAddress, hArgumentCount,
                                        hPremiseCountAddress, hPremiseCount,
                                        hArgumentStartAddress, hArgumentStart]
                                  | some argumentStartValue =>
                                      cases hPremiseStartAddress : checkedAdd
                                          argumentStartAddressValue 4 with
                                      | none =>
                                          simp [execute, initialRegisters,
                                            program, observe, readDetailed,
                                            loadWord16Detailed,
                                            loadWord32Detailed,
                                            addAddressDetailed, runSteps, step,
                                            executeInstruction, continueAt,
                                            hOpcode, hRuleAddress, hRule,
                                            hArgumentCountAddress,
                                            hArgumentCount,
                                            hPremiseCountAddress,
                                            hPremiseCount,
                                            hArgumentStartAddress,
                                            hArgumentStart,
                                            hPremiseStartAddress]
                                      | some premiseStartAddressValue =>
                                          cases hPremiseStart :
                                              memory.loadUInt32LE?
                                                premiseStartAddressValue with
                                          | none =>
                                              simp [execute, initialRegisters,
                                                program, observe,
                                                readDetailed,
                                                loadWord16Detailed,
                                                loadWord32Detailed,
                                                addAddressDetailed, runSteps,
                                                step, executeInstruction,
                                                continueAt, hOpcode,
                                                hRuleAddress, hRule,
                                                hArgumentCountAddress,
                                                hArgumentCount,
                                                hPremiseCountAddress,
                                                hPremiseCount,
                                                hArgumentStartAddress,
                                                hArgumentStart,
                                                hPremiseStartAddress,
                                                hPremiseStart]
                                          | some premiseStartValue =>
                                              cases hResultTermAddress :
                                                  checkedAdd
                                                    premiseStartAddressValue 4 with
                                              | none =>
                                                  simp [execute,
                                                    initialRegisters, program,
                                                    observe, readDetailed,
                                                    loadWord16Detailed,
                                                    loadWord32Detailed,
                                                    addAddressDetailed,
                                                    runSteps, step,
                                                    executeInstruction,
                                                    continueAt, hOpcode,
                                                    hRuleAddress, hRule,
                                                    hArgumentCountAddress,
                                                    hArgumentCount,
                                                    hPremiseCountAddress,
                                                    hPremiseCount,
                                                    hArgumentStartAddress,
                                                    hArgumentStart,
                                                    hPremiseStartAddress,
                                                    hPremiseStart,
                                                    hResultTermAddress]
                                              | some resultTermAddressValue =>
                                                  cases hResultTerm :
                                                      memory.loadUInt32LE?
                                                        resultTermAddressValue with
                                                  | none =>
                                                      simp [execute,
                                                        initialRegisters,
                                                        program, observe,
                                                        readDetailed,
                                                        loadWord16Detailed,
                                                        loadWord32Detailed,
                                                        addAddressDetailed,
                                                        runSteps, step,
                                                        executeInstruction,
                                                        continueAt, hOpcode,
                                                        hRuleAddress, hRule,
                                                        hArgumentCountAddress,
                                                        hArgumentCount,
                                                        hPremiseCountAddress,
                                                        hPremiseCount,
                                                        hArgumentStartAddress,
                                                        hArgumentStart,
                                                        hPremiseStartAddress,
                                                        hPremiseStart,
                                                        hResultTermAddress,
                                                        hResultTerm]
                                                  | some resultTermValue =>
                                                      cases hReservedAddress :
                                                          checkedAdd
                                                            resultTermAddressValue
                                                            4 with
                                                      | none =>
                                                          simp [execute,
                                                            initialRegisters,
                                                            program, observe,
                                                            readDetailed,
                                                            loadWord16Detailed,
                                                            loadWord32Detailed,
                                                            addAddressDetailed,
                                                            runSteps, step,
                                                            executeInstruction,
                                                            continueAt,
                                                            hOpcode,
                                                            hRuleAddress,
                                                            hRule,
                                                            hArgumentCountAddress,
                                                            hArgumentCount,
                                                            hPremiseCountAddress,
                                                            hPremiseCount,
                                                            hArgumentStartAddress,
                                                            hArgumentStart,
                                                            hPremiseStartAddress,
                                                            hPremiseStart,
                                                            hResultTermAddress,
                                                            hResultTerm,
                                                            hReservedAddress]
                                                      | some reservedAddressValue =>
                                                          cases hReserved :
                                                              memory.loadUInt32LE?
                                                                reservedAddressValue with
                                                          | none =>
                                                              simp [execute,
                                                                initialRegisters,
                                                                program,
                                                                observe,
                                                                readDetailed,
                                                                loadWord16Detailed,
                                                                loadWord32Detailed,
                                                                addAddressDetailed,
                                                                runSteps, step,
                                                                executeInstruction,
                                                                continueAt,
                                                                hOpcode,
                                                                hRuleAddress,
                                                                hRule,
                                                                hArgumentCountAddress,
                                                                hArgumentCount,
                                                                hPremiseCountAddress,
                                                                hPremiseCount,
                                                                hArgumentStartAddress,
                                                                hArgumentStart,
                                                                hPremiseStartAddress,
                                                                hPremiseStart,
                                                                hResultTermAddress,
                                                                hResultTerm,
                                                                hReservedAddress,
                                                                hReserved]
                                                          | some reservedValue =>
                                                              cases hFingerprintAddress :
                                                                  checkedAdd
                                                                    reservedAddressValue
                                                                    4 with
                                                              | none =>
                                                                  simp [execute,
                                                                    initialRegisters,
                                                                    program,
                                                                    observe,
                                                                    readDetailed,
                                                                    loadWord16Detailed,
                                                                    loadWord32Detailed,
                                                                    addAddressDetailed,
                                                                    runSteps,
                                                                    step,
                                                                    executeInstruction,
                                                                    continueAt,
                                                                    hOpcode,
                                                                    hRuleAddress,
                                                                    hRule,
                                                                    hArgumentCountAddress,
                                                                    hArgumentCount,
                                                                    hPremiseCountAddress,
                                                                    hPremiseCount,
                                                                    hArgumentStartAddress,
                                                                    hArgumentStart,
                                                                    hPremiseStartAddress,
                                                                    hPremiseStart,
                                                                    hResultTermAddress,
                                                                    hResultTerm,
                                                                    hReservedAddress,
                                                                    hReserved,
                                                                    hFingerprintAddress]
                                                              | some fingerprintAddressValue =>
                                                                  cases hFingerprint :
                                                                      memory.loadUInt64LE?
                                                                        fingerprintAddressValue with
                                                                  | none =>
                                                                      simp [execute,
                                                                        initialRegisters,
                                                                        program,
                                                                        observe,
                                                                        readDetailed,
                                                                        loadWord16Detailed,
                                                                        loadWord32Detailed,
                                                                        loadWord64Detailed,
                                                                        addAddressDetailed,
                                                                        runSteps,
                                                                        step,
                                                                        executeInstruction,
                                                                        continueAt,
                                                                        hOpcode,
                                                                        hRuleAddress,
                                                                        hRule,
                                                                        hArgumentCountAddress,
                                                                        hArgumentCount,
                                                                        hPremiseCountAddress,
                                                                        hPremiseCount,
                                                                        hArgumentStartAddress,
                                                                        hArgumentStart,
                                                                        hPremiseStartAddress,
                                                                        hPremiseStart,
                                                                        hResultTermAddress,
                                                                        hResultTerm,
                                                                        hReservedAddress,
                                                                        hReserved,
                                                                        hFingerprintAddress,
                                                                        hFingerprint]
                                                                  | some fingerprintValue =>
                                                                      simp [execute,
                                                                        initialRegisters,
                                                                        program,
                                                                        observe,
                                                                        nodeOfRegisters,
                                                                        readDetailed,
                                                                        loadWord16Detailed,
                                                                        loadWord32Detailed,
                                                                        loadWord64Detailed,
                                                                        addAddressDetailed,
                                                                        runSteps,
                                                                        step,
                                                                        executeInstruction,
                                                                        continueAt,
                                                                        hOpcode,
                                                                        hRuleAddress,
                                                                        hRule,
                                                                        hArgumentCountAddress,
                                                                        hArgumentCount,
                                                                        hPremiseCountAddress,
                                                                        hPremiseCount,
                                                                        hArgumentStartAddress,
                                                                        hArgumentStart,
                                                                        hPremiseStartAddress,
                                                                        hPremiseStart,
                                                                        hResultTermAddress,
                                                                        hResultTerm,
                                                                        hReservedAddress,
                                                                        hReserved,
                                                                        hFingerprintAddress,
                                                                        hFingerprint]

end Proof

/-! ## Scalar-reference records -/

namespace Scalar

def readDetailed (memory : ByteMemory) (address : UInt64) :
    Except Fault UInt32 :=
  loadWord32Detailed memory address

def shape : RegisterShape where
  byteCount := 0
  word16Count := 0
  word32Count := 1
  word64Count := 0
  addressCount := 1
  flagCount := 0

def value : Word32Register shape := ⟨0, by decide⟩
def address : AddressRegister shape := ⟨0, by decide⟩

attribute [local simp] shape value address

def program : Program shape where
  code := #[.loadWord32LE value address, .halt true]

def initialRegisters (physicalAddress : UInt64) : RegisterFile shape :=
  (RegisterFile.zero shape).writeAddress address physicalAddress

def execute (memory : ByteMemory) (physicalAddress : UInt64) :
    MachineState shape :=
  runSteps program 2 (.running 0 (initialRegisters physicalAddress) memory)

def observe : MachineState shape -> Option (Except Fault UInt32)
  | .running _ _ _ => none
  | .halted false _ _ => none
  | .halted true registers _ => some (.ok (registers.words32 value))
  | .faulted reason _ _ => some (.error reason)

theorem execute_agrees_readDetailed (memory : ByteMemory)
    (physicalAddress : UInt64) :
    observe (execute memory physicalAddress) =
      some (readDetailed memory physicalAddress) := by
  cases hLoad : memory.loadUInt32LE? physicalAddress with
  | none =>
      simp [execute, initialRegisters, program, observe, readDetailed,
        loadWord32Detailed, runSteps, step, executeInstruction,
        hLoad]
  | some value =>
      simp [execute, initialRegisters, program, observe, readDetailed,
        loadWord32Detailed, runSteps, step, executeInstruction, continueAt,
        hLoad]

end Scalar

/-! ## Canonical flat-reader evidence -/

/-- Fixed-offset scalar reads constituting one canonical term record. -/
structure FlatTermReads (bytes : List UInt8) (offset : Nat)
    (node : TermNode) : Prop where
  symbol : readAt? readUInt16LE bytes offset = some node.symbol
  arity : readAt? readUInt16LE bytes (offset + 2) = some node.arity
  childStart :
    readAt? readUInt32LE bytes (offset + 4) = some node.childStart
  reserved : readAt? readUInt32LE bytes (offset + 8) = some node.reserved
  termHash : readAt? readUInt64LE bytes (offset + 12) = some node.termHash

/-- The explicit field view reconstructs the established canonical term
reader; it is not a second term format. -/
theorem FlatTermReads.refines_canonical
    {bytes : List UInt8} {offset : Nat} {node : TermNode}
    (reads : FlatTermReads bytes offset node) :
    readAt? readTermNode bytes offset = some node := by
  have symbolCursor := readAt?_refines_cursor
    readUInt16LE_consumesExactly bytes offset node.symbol reads.symbol
  have arityCursor := readAt?_refines_cursor
    readUInt16LE_consumesExactly bytes (offset + 2) node.arity reads.arity
  have childCursor := readAt?_refines_cursor
    readUInt32LE_consumesExactly bytes (offset + 4) node.childStart
      reads.childStart
  have reservedCursor := readAt?_refines_cursor
    readUInt32LE_consumesExactly bytes (offset + 8) node.reserved
      reads.reserved
  have hashCursor := readAt?_refines_cursor
    readUInt64LE_consumesExactly bytes (offset + 12) node.termHash
      reads.termHash
  unfold readAt?
  simp [readTermNode, symbolCursor, arityCursor, childCursor, reservedCursor,
    hashCursor, Nat.add_assoc]

namespace Term

/-- Over list-backed physical memory, a complete term range and its flat
field evidence make the checked source loader return that exact term. -/
theorem readDetailed_of_flatReads
    (base address : UInt64) (bytes : List UInt8) (offset : Nat)
    (node : TermNode)
    (whole :
      (ByteMemory.ofList base bytes).rangeOffset? address 20 = some offset)
    (reads : FlatTermReads bytes offset node) :
    readDetailed (ByteMemory.ofList base bytes) address = .ok node := by
  have symbolRange := ByteMemory.rangeOffset?_smaller_width whole
    (fieldWidth := 2) (by decide)
  obtain ⟨arityAddressValue, hArityAddress⟩ :=
    ByteMemory.exists_checkedAdd_of_rangeOffset whole
      (fieldWidth := 2) (by decide)
  have arityTail := ByteMemory.rangeOffset?_shifted whole hArityAddress
    (fieldWidth := 18) (by decide)
  have arityRange := ByteMemory.rangeOffset?_smaller_width arityTail
    (fieldWidth := 2) (by decide)
  obtain ⟨childAddressValue, hChildAddress⟩ :=
    ByteMemory.exists_checkedAdd_of_rangeOffset arityTail
      (fieldWidth := 2) (by decide)
  have childTail := ByteMemory.rangeOffset?_shifted arityTail hChildAddress
    (fieldWidth := 16) (by decide)
  have childRange := ByteMemory.rangeOffset?_smaller_width childTail
    (fieldWidth := 4) (by decide)
  obtain ⟨reservedAddressValue, hReservedAddress⟩ :=
    ByteMemory.exists_checkedAdd_of_rangeOffset childTail
      (fieldWidth := 4) (by decide)
  have reservedTail := ByteMemory.rangeOffset?_shifted childTail
    hReservedAddress (fieldWidth := 12) (by decide)
  have reservedRange := ByteMemory.rangeOffset?_smaller_width reservedTail
    (fieldWidth := 4) (by decide)
  obtain ⟨hashAddressValue, hHashAddress⟩ :=
    ByteMemory.exists_checkedAdd_of_rangeOffset reservedTail
      (fieldWidth := 4) (by decide)
  have hashRange := ByteMemory.rangeOffset?_shifted reservedTail hHashAddress
    (fieldWidth := 8) (by decide)
  have symbolLoad :
      (ByteMemory.ofList base bytes).loadUInt16LE? address =
        some node.symbol := by
    rw [ByteMemory.loadUInt16LE?_ofList_of_range base address bytes offset
      symbolRange]
    exact reads.symbol
  have arityLoad :
      (ByteMemory.ofList base bytes).loadUInt16LE? arityAddressValue =
        some node.arity := by
    rw [ByteMemory.loadUInt16LE?_ofList_of_range base arityAddressValue
      bytes (offset + 2) arityRange]
    exact reads.arity
  have childLoad :
      (ByteMemory.ofList base bytes).loadUInt32LE? childAddressValue =
        some node.childStart := by
    rw [ByteMemory.loadUInt32LE?_ofList_of_range base childAddressValue
      bytes (offset + 4) (by simpa [Nat.add_assoc] using childRange)]
    exact reads.childStart
  have reservedLoad :
      (ByteMemory.ofList base bytes).loadUInt32LE? reservedAddressValue =
        some node.reserved := by
    rw [ByteMemory.loadUInt32LE?_ofList_of_range base reservedAddressValue
      bytes (offset + 8) (by simpa [Nat.add_assoc] using reservedRange)]
    exact reads.reserved
  have hashLoad :
      (ByteMemory.ofList base bytes).loadUInt64LE? hashAddressValue =
        some node.termHash := by
    rw [ByteMemory.loadUInt64LE?_ofList_of_range base hashAddressValue
      bytes (offset + 12) (by simpa [Nat.add_assoc] using hashRange)]
    exact reads.termHash
  simp [readDetailed, loadWord16Detailed, loadWord32Detailed,
    loadWord64Detailed, addAddressDetailed, hArityAddress, hChildAddress,
    hReservedAddress, hHashAddress, symbolLoad, arityLoad, childLoad,
    reservedLoad, hashLoad]

/-- The target term loader and canonical list reader select the same node. -/
theorem machine_and_canonical_agree
    (base address : UInt64) (bytes : List UInt8) (offset : Nat)
    (node : TermNode)
    (whole :
      (ByteMemory.ofList base bytes).rangeOffset? address 20 = some offset)
    (reads : FlatTermReads bytes offset node) :
    observe (execute (ByteMemory.ofList base bytes) address) =
        some (.ok node) ∧
      readAt? readTermNode bytes offset = some node := by
  constructor
  · rw [execute_agrees_readDetailed,
      readDetailed_of_flatReads base address bytes offset node whole reads]
  · exact reads.refines_canonical

end Term

/-- Fixed-offset scalar reads constituting one canonical proof record. -/
structure FlatProofReads (bytes : List UInt8) (offset : Nat)
    (node : ProofNode) : Prop where
  opcode : readAt? readUInt16LE bytes offset = some node.opcode
  rule : readAt? readUInt16LE bytes (offset + 2) = some node.rule
  argumentCount :
    readAt? readUInt16LE bytes (offset + 4) = some node.argumentCount
  premiseCount :
    readAt? readUInt16LE bytes (offset + 6) = some node.premiseCount
  argumentStart :
    readAt? readUInt32LE bytes (offset + 8) = some node.argumentStart
  premiseStart :
    readAt? readUInt32LE bytes (offset + 12) = some node.premiseStart
  resultTerm :
    readAt? readUInt32LE bytes (offset + 16) = some node.resultTerm
  reserved :
    readAt? readUInt32LE bytes (offset + 20) = some node.reserved
  ruleFingerprint :
    readAt? readUInt64LE bytes (offset + 24) = some node.ruleFingerprint

/-- The explicit proof fields reconstruct the established canonical proof
reader. -/
theorem FlatProofReads.refines_canonical
    {bytes : List UInt8} {offset : Nat} {node : ProofNode}
    (reads : FlatProofReads bytes offset node) :
    readAt? readProofNode bytes offset = some node := by
  have opcodeCursor := readAt?_refines_cursor
    readUInt16LE_consumesExactly bytes offset node.opcode reads.opcode
  have ruleCursor := readAt?_refines_cursor
    readUInt16LE_consumesExactly bytes (offset + 2) node.rule reads.rule
  have argumentCountCursor := readAt?_refines_cursor
    readUInt16LE_consumesExactly bytes (offset + 4) node.argumentCount
      reads.argumentCount
  have premiseCountCursor := readAt?_refines_cursor
    readUInt16LE_consumesExactly bytes (offset + 6) node.premiseCount
      reads.premiseCount
  have argumentStartCursor := readAt?_refines_cursor
    readUInt32LE_consumesExactly bytes (offset + 8) node.argumentStart
      reads.argumentStart
  have premiseStartCursor := readAt?_refines_cursor
    readUInt32LE_consumesExactly bytes (offset + 12) node.premiseStart
      reads.premiseStart
  have resultTermCursor := readAt?_refines_cursor
    readUInt32LE_consumesExactly bytes (offset + 16) node.resultTerm
      reads.resultTerm
  have reservedCursor := readAt?_refines_cursor
    readUInt32LE_consumesExactly bytes (offset + 20) node.reserved
      reads.reserved
  have fingerprintCursor := readAt?_refines_cursor
    readUInt64LE_consumesExactly bytes (offset + 24) node.ruleFingerprint
      reads.ruleFingerprint
  unfold readAt?
  simp [readProofNode, opcodeCursor, ruleCursor, argumentCountCursor,
    premiseCountCursor, argumentStartCursor, premiseStartCursor,
    resultTermCursor, reservedCursor, fingerprintCursor, Nat.add_assoc]

namespace Proof

/-- Over list-backed physical memory, a complete proof range and its flat
field evidence make the checked source loader return that exact proof node. -/
theorem readDetailed_of_flatReads
    (base address : UInt64) (bytes : List UInt8) (offset : Nat)
    (node : ProofNode)
    (whole :
      (ByteMemory.ofList base bytes).rangeOffset? address 32 = some offset)
    (reads : FlatProofReads bytes offset node) :
    readDetailed (ByteMemory.ofList base bytes) address = .ok node := by
  have opcodeRange := ByteMemory.rangeOffset?_smaller_width whole
    (fieldWidth := 2) (by decide)
  obtain ⟨ruleAddressValue, hRuleAddress⟩ :=
    ByteMemory.exists_checkedAdd_of_rangeOffset whole
      (fieldWidth := 2) (by decide)
  have ruleTail := ByteMemory.rangeOffset?_shifted whole hRuleAddress
    (fieldWidth := 30) (by decide)
  have ruleRange := ByteMemory.rangeOffset?_smaller_width ruleTail
    (fieldWidth := 2) (by decide)
  obtain ⟨argumentCountAddressValue, hArgumentCountAddress⟩ :=
    ByteMemory.exists_checkedAdd_of_rangeOffset ruleTail
      (fieldWidth := 2) (by decide)
  have argumentCountTail := ByteMemory.rangeOffset?_shifted ruleTail
    hArgumentCountAddress (fieldWidth := 28) (by decide)
  have argumentCountRange := ByteMemory.rangeOffset?_smaller_width
    argumentCountTail (fieldWidth := 2) (by decide)
  obtain ⟨premiseCountAddressValue, hPremiseCountAddress⟩ :=
    ByteMemory.exists_checkedAdd_of_rangeOffset argumentCountTail
      (fieldWidth := 2) (by decide)
  have premiseCountTail := ByteMemory.rangeOffset?_shifted argumentCountTail
    hPremiseCountAddress (fieldWidth := 26) (by decide)
  have premiseCountRange := ByteMemory.rangeOffset?_smaller_width
    premiseCountTail (fieldWidth := 2) (by decide)
  obtain ⟨argumentStartAddressValue, hArgumentStartAddress⟩ :=
    ByteMemory.exists_checkedAdd_of_rangeOffset premiseCountTail
      (fieldWidth := 2) (by decide)
  have argumentStartTail := ByteMemory.rangeOffset?_shifted premiseCountTail
    hArgumentStartAddress (fieldWidth := 24) (by decide)
  have argumentStartRange := ByteMemory.rangeOffset?_smaller_width
    argumentStartTail (fieldWidth := 4) (by decide)
  obtain ⟨premiseStartAddressValue, hPremiseStartAddress⟩ :=
    ByteMemory.exists_checkedAdd_of_rangeOffset argumentStartTail
      (fieldWidth := 4) (by decide)
  have premiseStartTail := ByteMemory.rangeOffset?_shifted argumentStartTail
    hPremiseStartAddress (fieldWidth := 20) (by decide)
  have premiseStartRange := ByteMemory.rangeOffset?_smaller_width
    premiseStartTail (fieldWidth := 4) (by decide)
  obtain ⟨resultTermAddressValue, hResultTermAddress⟩ :=
    ByteMemory.exists_checkedAdd_of_rangeOffset premiseStartTail
      (fieldWidth := 4) (by decide)
  have resultTermTail := ByteMemory.rangeOffset?_shifted premiseStartTail
    hResultTermAddress (fieldWidth := 16) (by decide)
  have resultTermRange := ByteMemory.rangeOffset?_smaller_width
    resultTermTail (fieldWidth := 4) (by decide)
  obtain ⟨reservedAddressValue, hReservedAddress⟩ :=
    ByteMemory.exists_checkedAdd_of_rangeOffset resultTermTail
      (fieldWidth := 4) (by decide)
  have reservedTail := ByteMemory.rangeOffset?_shifted resultTermTail
    hReservedAddress (fieldWidth := 12) (by decide)
  have reservedRange := ByteMemory.rangeOffset?_smaller_width reservedTail
    (fieldWidth := 4) (by decide)
  obtain ⟨fingerprintAddressValue, hFingerprintAddress⟩ :=
    ByteMemory.exists_checkedAdd_of_rangeOffset reservedTail
      (fieldWidth := 4) (by decide)
  have fingerprintRange := ByteMemory.rangeOffset?_shifted reservedTail
    hFingerprintAddress (fieldWidth := 8) (by decide)
  have opcodeLoad :
      (ByteMemory.ofList base bytes).loadUInt16LE? address =
        some node.opcode := by
    rw [ByteMemory.loadUInt16LE?_ofList_of_range base address bytes offset
      opcodeRange]
    exact reads.opcode
  have ruleLoad :
      (ByteMemory.ofList base bytes).loadUInt16LE? ruleAddressValue =
        some node.rule := by
    rw [ByteMemory.loadUInt16LE?_ofList_of_range base ruleAddressValue bytes
      (offset + 2) ruleRange]
    exact reads.rule
  have argumentCountLoad :
      (ByteMemory.ofList base bytes).loadUInt16LE?
          argumentCountAddressValue = some node.argumentCount := by
    rw [ByteMemory.loadUInt16LE?_ofList_of_range base
      argumentCountAddressValue bytes (offset + 4)
      (by simpa [Nat.add_assoc] using argumentCountRange)]
    exact reads.argumentCount
  have premiseCountLoad :
      (ByteMemory.ofList base bytes).loadUInt16LE?
          premiseCountAddressValue = some node.premiseCount := by
    rw [ByteMemory.loadUInt16LE?_ofList_of_range base
      premiseCountAddressValue bytes (offset + 6)
      (by simpa [Nat.add_assoc] using premiseCountRange)]
    exact reads.premiseCount
  have argumentStartLoad :
      (ByteMemory.ofList base bytes).loadUInt32LE?
          argumentStartAddressValue = some node.argumentStart := by
    rw [ByteMemory.loadUInt32LE?_ofList_of_range base
      argumentStartAddressValue bytes (offset + 8)
      (by simpa [Nat.add_assoc] using argumentStartRange)]
    exact reads.argumentStart
  have premiseStartLoad :
      (ByteMemory.ofList base bytes).loadUInt32LE?
          premiseStartAddressValue = some node.premiseStart := by
    rw [ByteMemory.loadUInt32LE?_ofList_of_range base
      premiseStartAddressValue bytes (offset + 12)
      (by simpa [Nat.add_assoc] using premiseStartRange)]
    exact reads.premiseStart
  have resultTermLoad :
      (ByteMemory.ofList base bytes).loadUInt32LE?
          resultTermAddressValue = some node.resultTerm := by
    rw [ByteMemory.loadUInt32LE?_ofList_of_range base
      resultTermAddressValue bytes (offset + 16)
      (by simpa [Nat.add_assoc] using resultTermRange)]
    exact reads.resultTerm
  have reservedLoad :
      (ByteMemory.ofList base bytes).loadUInt32LE? reservedAddressValue =
        some node.reserved := by
    rw [ByteMemory.loadUInt32LE?_ofList_of_range base reservedAddressValue
      bytes (offset + 20)
      (by simpa [Nat.add_assoc] using reservedRange)]
    exact reads.reserved
  have fingerprintLoad :
      (ByteMemory.ofList base bytes).loadUInt64LE? fingerprintAddressValue =
        some node.ruleFingerprint := by
    rw [ByteMemory.loadUInt64LE?_ofList_of_range base fingerprintAddressValue
      bytes (offset + 24)
      (by simpa [Nat.add_assoc] using fingerprintRange)]
    exact reads.ruleFingerprint
  simp [readDetailed, loadWord16Detailed, loadWord32Detailed,
    loadWord64Detailed, addAddressDetailed, hRuleAddress,
    hArgumentCountAddress, hPremiseCountAddress, hArgumentStartAddress,
    hPremiseStartAddress, hResultTermAddress, hReservedAddress,
    hFingerprintAddress, opcodeLoad, ruleLoad, argumentCountLoad,
    premiseCountLoad, argumentStartLoad, premiseStartLoad, resultTermLoad,
    reservedLoad, fingerprintLoad]

/-- The target proof loader and canonical list reader select the same node. -/
theorem machine_and_canonical_agree
    (base address : UInt64) (bytes : List UInt8) (offset : Nat)
    (node : ProofNode)
    (whole :
      (ByteMemory.ofList base bytes).rangeOffset? address 32 = some offset)
    (reads : FlatProofReads bytes offset node) :
    observe (execute (ByteMemory.ofList base bytes) address) =
        some (.ok node) ∧
      readAt? readProofNode bytes offset = some node := by
  constructor
  · rw [execute_agrees_readDetailed,
      readDetailed_of_flatReads base address bytes offset node whole reads]
  · exact reads.refines_canonical

end Proof

namespace Scalar

/-- The scalar loader agrees with the established fixed-offset four-byte
reader whenever the physical four-byte range is qualified. -/
theorem machine_and_flat_agree
    (base address : UInt64) (bytes : List UInt8) (offset : Nat)
    (value : UInt32)
    (whole :
      (ByteMemory.ofList base bytes).rangeOffset? address 4 = some offset)
    (read : readAt? readUInt32LE bytes offset = some value) :
    observe (execute (ByteMemory.ofList base bytes) address) =
        some (.ok value) := by
  have loaded :
      (ByteMemory.ofList base bytes).loadUInt32LE? address = some value := by
    rw [ByteMemory.loadUInt32LE?_ofList_of_range base address bytes offset
      whole]
    exact read
  rw [execute_agrees_readDetailed]
  simp [readDetailed, loadWord32Detailed, loaded]

end Scalar

/-! ## Executable positive and negative controls -/

namespace Canary

def termMemory : ByteMemory :=
  ByteMemory.ofList 1104 (encodeTermNode canaryTerm)

def proofMemory : ByteMemory :=
  ByteMemory.ofList 1124 (encodeProofNode canaryProof)

theorem term_loads_canonical_node :
    Term.observe (Term.execute termMemory 1104) =
      some (.ok canaryTerm) := by
  rw [Term.execute_agrees_readDetailed]
  have hArityAddress : checkedAdd 1104 2 = some 1106 := by decide
  have hChildAddress : checkedAdd 1106 2 = some 1108 := by decide
  have hReservedAddress : checkedAdd 1108 4 = some 1112 := by decide
  have hHashAddress : checkedAdd 1112 4 = some 1116 := by decide
  have hSymbol : termMemory.loadUInt16LE? 1104 = some 0 := by decide
  have hArity : termMemory.loadUInt16LE? 1106 = some 0 := by decide
  have hChild : termMemory.loadUInt32LE? 1108 = some 0 := by decide
  have hReserved : termMemory.loadUInt32LE? 1112 = some 0 := by decide
  have hHash : termMemory.loadUInt64LE? 1116 = some 0 := by decide
  simp [Term.readDetailed, loadWord16Detailed, loadWord32Detailed,
    loadWord64Detailed, addAddressDetailed, canaryTerm, hArityAddress,
    hChildAddress, hReservedAddress, hHashAddress, hSymbol, hArity, hChild,
    hReserved, hHash]

theorem proof_loads_canonical_node :
    Proof.observe (Proof.execute proofMemory 1124) =
      some (.ok canaryProof) := by
  rw [Proof.execute_agrees_readDetailed]
  have hRuleAddress : checkedAdd 1124 2 = some 1126 := by decide
  have hArgumentCountAddress : checkedAdd 1126 2 = some 1128 := by decide
  have hPremiseCountAddress : checkedAdd 1128 2 = some 1130 := by decide
  have hArgumentStartAddress : checkedAdd 1130 2 = some 1132 := by decide
  have hPremiseStartAddress : checkedAdd 1132 4 = some 1136 := by decide
  have hResultTermAddress : checkedAdd 1136 4 = some 1140 := by decide
  have hReservedAddress : checkedAdd 1140 4 = some 1144 := by decide
  have hFingerprintAddress : checkedAdd 1144 4 = some 1148 := by decide
  have hOpcode : proofMemory.loadUInt16LE? 1124 = some 1 := by decide
  have hRule : proofMemory.loadUInt16LE? 1126 = some 0 := by decide
  have hArgumentCount : proofMemory.loadUInt16LE? 1128 = some 0 := by decide
  have hPremiseCount : proofMemory.loadUInt16LE? 1130 = some 0 := by decide
  have hArgumentStart : proofMemory.loadUInt32LE? 1132 = some 0 := by decide
  have hPremiseStart : proofMemory.loadUInt32LE? 1136 = some 0 := by decide
  have hResultTerm : proofMemory.loadUInt32LE? 1140 = some 0 := by decide
  have hReserved : proofMemory.loadUInt32LE? 1144 = some 0 := by decide
  have hFingerprint : proofMemory.loadUInt64LE? 1148 = some 0 := by decide
  simp [Proof.readDetailed, loadWord16Detailed, loadWord32Detailed,
    loadWord64Detailed, addAddressDetailed, canaryProof, hRuleAddress,
    hArgumentCountAddress, hPremiseCountAddress, hArgumentStartAddress,
    hPremiseStartAddress, hResultTermAddress, hReservedAddress,
    hFingerprintAddress, hOpcode, hRule, hArgumentCount, hPremiseCount,
    hArgumentStart, hPremiseStart, hResultTerm, hReserved, hFingerprint]

/-- Starting one byte late preserves checked execution and exposes a
short-record fault rather than accepting a shifted record. -/
theorem shifted_proof_faults :
    Proof.observe (Proof.execute proofMemory 1125) =
      some (.error .word64ReadOutOfBounds) := by
  rw [Proof.execute_agrees_readDetailed]
  have hRuleAddress : checkedAdd 1125 2 = some 1127 := by decide
  have hArgumentCountAddress : checkedAdd 1127 2 = some 1129 := by decide
  have hPremiseCountAddress : checkedAdd 1129 2 = some 1131 := by decide
  have hArgumentStartAddress : checkedAdd 1131 2 = some 1133 := by decide
  have hPremiseStartAddress : checkedAdd 1133 4 = some 1137 := by decide
  have hResultTermAddress : checkedAdd 1137 4 = some 1141 := by decide
  have hReservedAddress : checkedAdd 1141 4 = some 1145 := by decide
  have hFingerprintAddress : checkedAdd 1145 4 = some 1149 := by decide
  have hOpcode : proofMemory.loadUInt16LE? 1125 = some 0 := by decide
  have hRule : proofMemory.loadUInt16LE? 1127 = some 0 := by decide
  have hArgumentCount : proofMemory.loadUInt16LE? 1129 = some 0 := by decide
  have hPremiseCount : proofMemory.loadUInt16LE? 1131 = some 0 := by decide
  have hArgumentStart : proofMemory.loadUInt32LE? 1133 = some 0 := by decide
  have hPremiseStart : proofMemory.loadUInt32LE? 1137 = some 0 := by decide
  have hResultTerm : proofMemory.loadUInt32LE? 1141 = some 0 := by decide
  have hReserved : proofMemory.loadUInt32LE? 1145 = some 0 := by decide
  have hFingerprint : proofMemory.loadUInt64LE? 1149 = none := by decide
  simp [Proof.readDetailed, loadWord16Detailed, loadWord32Detailed,
    loadWord64Detailed, addAddressDetailed, hRuleAddress,
    hArgumentCountAddress, hPremiseCountAddress, hArgumentStartAddress,
    hPremiseStartAddress, hResultTermAddress, hReservedAddress,
    hFingerprintAddress, hOpcode, hRule, hArgumentCount, hPremiseCount,
    hArgumentStart, hPremiseStart, hResultTerm, hReserved, hFingerprint]

def scalarMemory : ByteMemory := ByteMemory.ofList 200 [1, 2, 3, 4]

theorem scalar_loads_little_endian :
    Scalar.observe (Scalar.execute scalarMemory 200) =
      some (.ok 0x04030201) := by
  rw [Scalar.execute_agrees_readDetailed]
  decide

theorem scalar_short_read_faults :
    Scalar.observe (Scalar.execute scalarMemory 201) =
      some (.error .word32ReadOutOfBounds) := by
  rw [Scalar.execute_agrees_readDetailed]
  decide

end Canary

#print axioms Term.execute_agrees_readDetailed
#print axioms Proof.execute_agrees_readDetailed
#print axioms Scalar.execute_agrees_readDetailed
#print axioms FlatTermReads.refines_canonical
#print axioms Term.machine_and_canonical_agree
#print axioms FlatProofReads.refines_canonical
#print axioms Proof.machine_and_canonical_agree
#print axioms Scalar.machine_and_flat_agree
#print axioms Canary.term_loads_canonical_node
#print axioms Canary.proof_loads_canonical_node
#print axioms Canary.shifted_proof_faults
#print axioms Canary.scalar_loads_little_endian
#print axioms Canary.scalar_short_read_faults

end Mettapedia.GSLT.LanguageDef.M0GCBodyRecordByteMachineRealization
