import Mettapedia.GSLT.LanguageDef.M0GCHeaderByteMachineRealization
import Mathlib.Tactic

/-!
# Zero-copy M0GC body views in the checked byte-machine

The five M0GC body tables already have canonical fixed-width encodings.  This
module therefore prepares checked physical views into the immutable submitted
allocation instead of copying the tables into a second decoded heap.

The target is a fixed 25-instruction program.  Starting from parsed header
counts, a physical allocation base, and its exclusive end, it zero-extends
each count, performs checked stride multiplication and checked address
addition, retains every table base, and accepts exactly when the computed body
end equals the supplied allocation end.  No instruction means "decode body"
or "trust table layout".

Maturity boundary: this is a connected intermediate proof of concept for
zero-copy table-view preparation.  It is not yet the per-record loader,
checksum loop, replay loop, endgame register allocation, StructuredC, portable
C, verified object code, or the official MM0/MMB format.  The wide register
assignment is proof-oriented; a later liveness proof may coalesce registers
without changing the prepared view.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCBodyViewByteMachineRealization

open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory
open Mettapedia.GSLT.LanguageDef.M0GCFlatBodyLoaderCorrespondence
open Mettapedia.GSLT.LanguageDef.M0GCCheckedByteMachineIR

/-! ## Independent source operation -/

/-- A zero-copy physical view of all five canonical body tables.  Counts are
retained beside bases so later indexed record loads can check both table and
record bounds. -/
structure BodyView where
  termBase : UInt64
  childBase : UInt64
  proofBase : UInt64
  argumentBase : UInt64
  premiseBase : UInt64
  bodyEnd : UInt64
  termCount : UInt32
  childCount : UInt32
  proofCount : UInt32
  argumentCount : UInt32
  premiseCount : UInt32
deriving DecidableEq, Repr

/-- Source-level table-view preparation with the same reject/fault
distinction as the target program.  An arithmetic overflow is a physical
address fault; a representable but non-exact allocation length is a logical
rejection. -/
def prepareDetailed (base allocationEnd : UInt64) (header : Header) :
    Except Fault (Option BodyView) := do
  let termBase <- addAddressDetailed base 104
  let termWidth <- mulAddressDetailed header.termCount.toUInt64 20
  let childBase <- addAddressDetailed termBase termWidth
  let childWidth <- mulAddressDetailed header.childCount.toUInt64 4
  let proofBase <- addAddressDetailed childBase childWidth
  let proofWidth <- mulAddressDetailed header.proofCount.toUInt64 32
  let argumentBase <- addAddressDetailed proofBase proofWidth
  let argumentWidth <- mulAddressDetailed header.argumentCount.toUInt64 4
  let premiseBase <- addAddressDetailed argumentBase argumentWidth
  let premiseWidth <- mulAddressDetailed header.premiseReferenceCount.toUInt64 4
  let bodyEnd <- addAddressDetailed premiseBase premiseWidth
  if bodyEnd = allocationEnd then
    pure (some
      { termBase
        childBase
        proofBase
        argumentBase
        premiseBase
        bodyEnd
        termCount := header.termCount
        childCount := header.childCount
        proofCount := header.proofCount
        argumentCount := header.argumentCount
        premiseCount := header.premiseReferenceCount })
  else
    pure none

/-! ## Fixed target program -/

def shape : RegisterShape where
  byteCount := 0
  word16Count := 0
  word32Count := 5
  word64Count := 0
  addressCount := 10
  flagCount := 1

def termCount : Word32Register shape := ⟨0, by decide⟩
def childCount : Word32Register shape := ⟨1, by decide⟩
def proofCount : Word32Register shape := ⟨2, by decide⟩
def argumentCount : Word32Register shape := ⟨3, by decide⟩
def premiseCount : Word32Register shape := ⟨4, by decide⟩

def baseAddress : AddressRegister shape := ⟨0, by decide⟩
def allocationEnd : AddressRegister shape := ⟨1, by decide⟩
def termBase : AddressRegister shape := ⟨2, by decide⟩
def childBase : AddressRegister shape := ⟨3, by decide⟩
def proofBase : AddressRegister shape := ⟨4, by decide⟩
def argumentBase : AddressRegister shape := ⟨5, by decide⟩
def premiseBase : AddressRegister shape := ⟨6, by decide⟩
def bodyEnd : AddressRegister shape := ⟨7, by decide⟩
def temporary : AddressRegister shape := ⟨8, by decide⟩
def stride : AddressRegister shape := ⟨9, by decide⟩

def exactEnd : FlagRegister shape := ⟨0, by decide⟩

attribute [local simp] shape termCount childCount proofCount argumentCount
  premiseCount baseAddress allocationEnd termBase childBase proofBase
  argumentBase premiseBase bodyEnd temporary stride exactEnd

attribute [local simp] bind Except.bind pure Except.pure

/-- Fixed zero-copy layout program.  Multiplication is an ordinary checked
address operation; there is no body-layout oracle in the instruction set. -/
def program : Program shape where
  code := #[
    .constAddress temporary 104,
    .addAddressChecked termBase baseAddress temporary,

    .word32ToAddress temporary termCount,
    .constAddress stride 20,
    .mulAddressChecked temporary temporary stride,
    .addAddressChecked childBase termBase temporary,

    .word32ToAddress temporary childCount,
    .constAddress stride 4,
    .mulAddressChecked temporary temporary stride,
    .addAddressChecked proofBase childBase temporary,

    .word32ToAddress temporary proofCount,
    .constAddress stride 32,
    .mulAddressChecked temporary temporary stride,
    .addAddressChecked argumentBase proofBase temporary,

    .word32ToAddress temporary argumentCount,
    .constAddress stride 4,
    .mulAddressChecked temporary temporary stride,
    .addAddressChecked premiseBase argumentBase temporary,

    .word32ToAddress temporary premiseCount,
    .constAddress stride 4,
    .mulAddressChecked temporary temporary stride,
    .addAddressChecked bodyEnd premiseBase temporary,

    .equalAddress exactEnd bodyEnd allocationEnd,
    .rejectUnless exactEnd,
    .halt true]

def initialRegisters (base endAddress : UInt64) (header : Header) :
    RegisterFile shape :=
  (((((((RegisterFile.zero shape).writeWord32 termCount header.termCount).writeWord32
      childCount header.childCount).writeWord32
      proofCount header.proofCount).writeWord32
      argumentCount header.argumentCount).writeWord32
      premiseCount header.premiseReferenceCount).writeAddress
      baseAddress base).writeAddress allocationEnd endAddress

def initialState (memory : ByteMemory) (endAddress : UInt64)
    (header : Header) : MachineState shape :=
  .running 0 (initialRegisters memory.base endAddress header) memory

def execute (memory : ByteMemory) (endAddress : UInt64)
    (header : Header) : MachineState shape :=
  runSteps program 25 (initialState memory endAddress header)

/-- Decode the retained table capability from a successful target register
file. -/
def viewOfRegisters (registers : RegisterFile shape) : BodyView :=
  { termBase := registers.addresses termBase
    childBase := registers.addresses childBase
    proofBase := registers.addresses proofBase
    argumentBase := registers.addresses argumentBase
    premiseBase := registers.addresses premiseBase
    bodyEnd := registers.addresses bodyEnd
    termCount := registers.words32 termCount
    childCount := registers.words32 childCount
    proofCount := registers.words32 proofCount
    argumentCount := registers.words32 argumentCount
    premiseCount := registers.words32 premiseCount }

/-- Semantic target observation retaining logical rejection, physical fault,
and the complete successful table view. -/
def observeView : MachineState shape ->
    Option (Except Fault (Option BodyView))
  | .running _ _ _ => none
  | .halted false _ _ => some (.ok none)
  | .halted true registers _ => some (.ok (some (viewOfRegisters registers)))
  | .faulted reason _ _ => some (.error reason)

/-! ## Generic source/target agreement -/

/-- The fixed target program implements the independently stated source
preparation for every header, base, exclusive end, and backing byte array. -/
theorem execute_agrees_prepareDetailed
    (memory : ByteMemory) (endAddress : UInt64) (header : Header) :
    observeView (execute memory endAddress header) =
      some (prepareDetailed memory.base endAddress header) := by
  unfold execute
  rw [show 25 = 2 + 23 by decide, runSteps_add]
  cases hTermBase : checkedAdd memory.base 104 with
  | none =>
      simp [initialState, initialRegisters, program, observeView,
        prepareDetailed, addAddressDetailed, runSteps, step,
        executeInstruction, continueAt, hTermBase]
  | some termBaseValue =>
      let registersTerm :=
        ((initialRegisters memory.base endAddress header).writeAddress
          temporary 104).writeAddress termBase termBaseValue
      have termStage :
          runSteps program 2 (initialState memory endAddress header) =
            .running 2 registersTerm memory := by
        simp [initialState, initialRegisters, registersTerm, program, runSteps,
          step, executeInstruction, continueAt, hTermBase]
      rw [termStage]
      rw [show 23 = 4 + 19 by decide, runSteps_add]
      cases hTermWidth : checkedMul header.termCount.toUInt64 20 with
      | none =>
          simp [registersTerm, initialRegisters, program, observeView,
            prepareDetailed, addAddressDetailed, mulAddressDetailed, runSteps, step,
            executeInstruction, continueAt, hTermBase, hTermWidth]
      | some termWidthValue =>
          cases hChildBase : checkedAdd termBaseValue termWidthValue with
          | none =>
              simp [registersTerm, initialRegisters, program, observeView,
                prepareDetailed, addAddressDetailed, mulAddressDetailed, runSteps, step,
                executeInstruction, continueAt, hTermBase, hTermWidth,
                hChildBase]
          | some childBaseValue =>
              let registersChild :=
                ((((registersTerm.writeAddress temporary
                  header.termCount.toUInt64).writeAddress stride 20).writeAddress
                  temporary termWidthValue).writeAddress childBase
                  childBaseValue)
              have childStage :
                  runSteps program 4 (.running 2 registersTerm memory) =
                    .running 6 registersChild memory := by
                simp [registersTerm, registersChild, initialRegisters, program,
                  runSteps, step, executeInstruction, continueAt, hTermWidth,
                  hChildBase]
              rw [childStage]
              rw [show 19 = 4 + 15 by decide, runSteps_add]
              cases hChildWidth : checkedMul header.childCount.toUInt64 4 with
              | none =>
                  simp [registersTerm, registersChild, initialRegisters,
                    program, observeView, prepareDetailed, addAddressDetailed,
                    mulAddressDetailed, runSteps, step, executeInstruction,
                    continueAt, hTermBase, hTermWidth, hChildBase,
                    hChildWidth]
              | some childWidthValue =>
                  cases hProofBase :
                      checkedAdd childBaseValue childWidthValue with
                  | none =>
                      simp [registersTerm, registersChild, initialRegisters,
                        program, observeView, prepareDetailed, addAddressDetailed,
                        mulAddressDetailed, runSteps, step, executeInstruction,
                        continueAt, hTermBase, hTermWidth, hChildBase,
                        hChildWidth, hProofBase]
                  | some proofBaseValue =>
                      let registersProof :=
                        ((((registersChild.writeAddress temporary
                          header.childCount.toUInt64).writeAddress stride 4).writeAddress
                          temporary childWidthValue).writeAddress proofBase
                          proofBaseValue)
                      have proofStage :
                          runSteps program 4
                              (.running 6 registersChild memory) =
                            .running 10 registersProof memory := by
                        simp [registersTerm, registersChild, registersProof,
                          initialRegisters, program, runSteps, step,
                          executeInstruction, continueAt, hChildWidth,
                          hProofBase]
                      rw [proofStage]
                      rw [show 15 = 4 + 11 by decide, runSteps_add]
                      cases hProofWidth :
                          checkedMul header.proofCount.toUInt64 32 with
                      | none =>
                          simp [registersTerm, registersChild, registersProof,
                            initialRegisters, program, observeView,
                            prepareDetailed, addAddressDetailed,
                            mulAddressDetailed, runSteps,
                            step, executeInstruction, continueAt, hTermBase,
                            hTermWidth, hChildBase, hChildWidth, hProofBase,
                            hProofWidth]
                      | some proofWidthValue =>
                          cases hArgumentBase :
                              checkedAdd proofBaseValue proofWidthValue with
                          | none =>
                              simp [registersTerm, registersChild,
                                registersProof, initialRegisters, program,
                                observeView, prepareDetailed,
                                addAddressDetailed, mulAddressDetailed, runSteps,
                                step, executeInstruction,
                                continueAt, hTermBase, hTermWidth, hChildBase,
                                hChildWidth, hProofBase, hProofWidth,
                                hArgumentBase]
                          | some argumentBaseValue =>
                              let registersArgument :=
                                ((((registersProof.writeAddress temporary
                                  header.proofCount.toUInt64).writeAddress
                                  stride 32).writeAddress temporary
                                  proofWidthValue).writeAddress argumentBase
                                  argumentBaseValue)
                              have argumentStage :
                                  runSteps program 4
                                      (.running 10 registersProof memory) =
                                    .running 14 registersArgument memory := by
                                simp [registersTerm, registersChild,
                                  registersProof, registersArgument,
                                  initialRegisters, program, runSteps, step,
                                  executeInstruction, continueAt, hProofWidth,
                                  hArgumentBase]
                              rw [argumentStage]
                              rw [show 11 = 4 + 7 by decide, runSteps_add]
                              cases hArgumentWidth : checkedMul
                                  header.argumentCount.toUInt64 4 with
                              | none =>
                                  simp [registersTerm, registersChild,
                                    registersProof, registersArgument,
                                    initialRegisters, program, observeView,
                                    prepareDetailed, addAddressDetailed,
                                    mulAddressDetailed,
                                    runSteps, step, executeInstruction,
                                    continueAt, hTermBase, hTermWidth,
                                    hChildBase, hChildWidth, hProofBase,
                                    hProofWidth, hArgumentBase, hArgumentWidth]
                              | some argumentWidthValue =>
                                  cases hPremiseBase : checkedAdd
                                      argumentBaseValue argumentWidthValue with
                                  | none =>
                                      simp [registersTerm, registersChild,
                                        registersProof, registersArgument,
                                        initialRegisters, program, observeView,
                                        prepareDetailed, addAddressDetailed,
                                        mulAddressDetailed,
                                        runSteps, step, executeInstruction,
                                        continueAt, hTermBase, hTermWidth,
                                        hChildBase, hChildWidth, hProofBase,
                                        hProofWidth, hArgumentBase,
                                        hArgumentWidth, hPremiseBase]
                                  | some premiseBaseValue =>
                                      let registersPremise :=
                                        ((((registersArgument.writeAddress
                                          temporary
                                          header.argumentCount.toUInt64).writeAddress
                                          stride 4).writeAddress temporary
                                          argumentWidthValue).writeAddress
                                          premiseBase premiseBaseValue)
                                      have premiseStage :
                                          runSteps program 4
                                              (.running 14 registersArgument
                                                memory) =
                                            .running 18 registersPremise
                                              memory := by
                                        simp [registersTerm, registersChild,
                                          registersProof, registersArgument,
                                          registersPremise, initialRegisters,
                                          program, runSteps, step,
                                          executeInstruction, continueAt,
                                          hArgumentWidth, hPremiseBase]
                                      rw [premiseStage]
                                      rw [show 7 = 4 + 3 by decide,
                                        runSteps_add]
                                      cases hPremiseWidth : checkedMul
                                          header.premiseReferenceCount.toUInt64
                                            4 with
                                      | none =>
                                          simp [registersTerm, registersChild,
                                            registersProof, registersArgument,
                                            registersPremise, initialRegisters,
                                            program, observeView,
                                            prepareDetailed,
                                            addAddressDetailed,
                                            mulAddressDetailed, runSteps, step,
                                            executeInstruction, continueAt,
                                            hTermBase, hTermWidth, hChildBase,
                                            hChildWidth, hProofBase,
                                            hProofWidth, hArgumentBase,
                                            hArgumentWidth, hPremiseBase,
                                            hPremiseWidth]
                                      | some premiseWidthValue =>
                                          cases hBodyEnd : checkedAdd
                                              premiseBaseValue
                                              premiseWidthValue with
                                          | none =>
                                              simp [registersTerm,
                                                registersChild, registersProof,
                                                registersArgument,
                                                registersPremise,
                                                initialRegisters, program,
                                                observeView, prepareDetailed,
                                                addAddressDetailed,
                                                mulAddressDetailed,
                                                runSteps, step,
                                                executeInstruction, continueAt,
                                                hTermBase, hTermWidth,
                                                hChildBase, hChildWidth,
                                                hProofBase, hProofWidth,
                                                hArgumentBase, hArgumentWidth,
                                                hPremiseBase, hPremiseWidth,
                                                hBodyEnd]
                                          | some bodyEndValue =>
                                              let registersEnd :=
                                                ((((registersPremise.writeAddress
                                                  temporary header.premiseReferenceCount.toUInt64).writeAddress
                                                  stride 4).writeAddress
                                                  temporary premiseWidthValue).writeAddress
                                                  bodyEnd bodyEndValue)
                                              have endStage :
                                                  runSteps program 4
                                                      (.running 18
                                                        registersPremise
                                                        memory) =
                                                    .running 22 registersEnd
                                                      memory := by
                                                simp [registersTerm,
                                                  registersChild,
                                                  registersProof,
                                                  registersArgument,
                                                  registersPremise,
                                                  registersEnd,
                                                  initialRegisters, program,
                                                  runSteps, step,
                                                  executeInstruction,
                                                  continueAt, hPremiseWidth,
                                                  hBodyEnd]
                                              rw [endStage]
                                              by_cases exact :
                                                  bodyEndValue = endAddress
                                              · simp [registersTerm,
                                                  registersChild,
                                                  registersProof,
                                                  registersArgument,
                                                  registersPremise,
                                                  registersEnd,
                                                  initialRegisters, program,
                                                  observeView, viewOfRegisters,
                                                  prepareDetailed,
                                                  addAddressDetailed,
                                                  mulAddressDetailed, runSteps,
                                                  step,
                                                  executeInstruction,
                                                  continueAt, hTermBase,
                                                  hTermWidth, hChildBase,
                                                  hChildWidth, hProofBase,
                                                  hProofWidth, hArgumentBase,
                                                  hArgumentWidth, hPremiseBase,
                                                  hPremiseWidth, hBodyEnd,
                                                  exact]
                                              · simp [registersTerm,
                                                  registersChild,
                                                  registersProof,
                                                  registersArgument,
                                                  registersPremise,
                                                  registersEnd,
                                                  initialRegisters, program,
                                                  observeView,
                                                  prepareDetailed,
                                                  addAddressDetailed,
                                                  mulAddressDetailed, runSteps,
                                                  step,
                                                  executeInstruction,
                                                  continueAt, hTermBase,
                                                  hTermWidth, hChildBase,
                                                  hChildWidth, hProofBase,
                                                  hProofWidth, hArgumentBase,
                                                  hArgumentWidth, hPremiseBase,
                                                  hPremiseWidth, hBodyEnd,
                                                  exact]

/-! ## Allocation-facing consequences -/

/-- The representable exclusive physical end of a well-formed allocation. -/
def physicalEnd (memory : ByteMemory) (wellFormed : memory.WellFormed) : UInt64 :=
  UInt64.ofNatLT (memory.base.toNat + memory.cells.size) wellFormed

@[simp] theorem physicalEnd_toNat (memory : ByteMemory)
    (wellFormed : memory.WellFormed) :
    (physicalEnd memory wellFormed).toNat =
      memory.base.toNat + memory.cells.size :=
  UInt64.toNat_ofNatLT

/-- Every header-derived body width fits the address word before the physical
base is added. -/
theorem header_bodyByteLength_lt_uint64 (header : Header) :
    bodyByteLength (BodyCounts.ofHeader header) < UInt64.size := by
  have termBound := header.termCount.toNat_lt_size
  have childBound := header.childCount.toNat_lt_size
  have proofBound := header.proofCount.toNat_lt_size
  have argumentBound := header.argumentCount.toNat_lt_size
  have premiseBound := header.premiseReferenceCount.toNat_lt_size
  simp only [BodyCounts.ofHeader, bodyByteLength, premiseTableOffset,
    argumentTableOffset, proofTableOffset, childTableOffset]
  norm_num [UInt32.size, UInt64.size] at termBound childBound proofBound argumentBound premiseBound ⊢
  omega

/-! ## Positive and negative executable controls -/

namespace Canary

def header : Header :=
  headerOf canaryCertificate (fnv1a64 (encodeBody canaryCertificate))

def memory : ByteMemory :=
  ByteMemory.ofList 1000 (encodeCertificate canaryCertificate)

@[simp] theorem memory_base : memory.base = 1000 := rfl

/-- The canonical canary contains a 104-byte header, one 20-byte term, and
one 32-byte proof.  Its three scalar-reference tables are empty. -/
theorem encodedCertificate_length :
    (encodeCertificate canaryCertificate).length = 156 := by
  have profileWidth : header.profileDigest.length = digestWidth := by
    simp [header, headerOf, canaryCertificate, digestWidth]
  have sourceWidth : header.sourceDigest.length = digestWidth := by
    simp [header, headerOf, canaryCertificate, digestWidth]
  change (encodeHeader header ++ encodeBody canaryCertificate).length = 156
  rw [List.length_append, encodeHeader_length header profileWidth sourceWidth]
  simp [encodeBody, canaryCertificate, encodeTermNode_length,
    encodeProofNode_length]

def endAddress : UInt64 :=
  UInt64.ofNat (1000 + (encodeCertificate canaryCertificate).length)

@[simp] theorem endAddress_eq : endAddress = 1156 := by
  simp [endAddress, encodedCertificate_length]

def expectedView : BodyView :=
  { termBase := 1104
    childBase := 1124
    proofBase := 1124
    argumentBase := 1156
    premiseBase := 1156
    bodyEnd := endAddress
    termCount := header.termCount
    childCount := header.childCount
    proofCount := header.proofCount
    argumentCount := header.argumentCount
    premiseCount := header.premiseReferenceCount }

theorem prepare_expected :
    prepareDetailed 1000 1156 header = .ok (some expectedView) := by
  have termBaseAddress : checkedAdd 1000 104 = some 1104 := by decide
  have termWidth : checkedMul 1 20 = some 20 := by decide
  have childBaseAddress : checkedAdd 1104 20 = some 1124 := by decide
  have childWidth : checkedMul 0 4 = some 0 := by decide
  have proofBaseAddress : checkedAdd 1124 0 = some 1124 := by decide
  have proofWidth : checkedMul 1 32 = some 32 := by decide
  have argumentBaseAddress : checkedAdd 1124 32 = some 1156 := by decide
  have premiseBaseAddress : checkedAdd 1156 0 = some 1156 := by decide
  simp [prepareDetailed, addAddressDetailed, mulAddressDetailed, header,
    headerOf,
    canaryCertificate, expectedView, endAddress_eq, termBaseAddress,
    termWidth, childBaseAddress, childWidth, proofBaseAddress, proofWidth,
    argumentBaseAddress, premiseBaseAddress]

theorem exact_body_view_values :
    observeView (execute memory endAddress header) =
      some (.ok (some expectedView)) := by
  rw [execute_agrees_prepareDetailed]
  simp only [memory_base, endAddress_eq]
  rw [prepare_expected]

theorem exact_body_view_accepts :
    ∃ view, observeView (execute memory endAddress header) =
      some (.ok (some view)) :=
  ⟨expectedView, exact_body_view_values⟩

def truncatedMemory : ByteMemory :=
  ByteMemory.ofList 1000 (encodeCertificate canaryCertificate).dropLast

def truncatedEnd : UInt64 :=
  UInt64.ofNat (1000 + (encodeCertificate canaryCertificate).dropLast.length)

@[simp] theorem truncatedMemory_base : truncatedMemory.base = 1000 := rfl

@[simp] theorem truncatedEnd_eq : truncatedEnd = 1155 := by
  have lengthValue :
      (encodeCertificate canaryCertificate).dropLast.length = 155 := by
    rw [List.length_dropLast, encodedCertificate_length]
  simp [truncatedEnd, lengthValue]

theorem truncated_body_rejected_without_fault :
    observeView (execute truncatedMemory truncatedEnd header) =
      some (.ok none) := by
  rw [execute_agrees_prepareDetailed]
  simp only [truncatedMemory_base, truncatedEnd_eq]
  decide

def trailingMemory : ByteMemory :=
  ByteMemory.ofList 1000 (encodeCertificate canaryCertificate ++ [0])

def trailingEnd : UInt64 :=
  UInt64.ofNat (1000 + (encodeCertificate canaryCertificate ++ [0]).length)

@[simp] theorem trailingMemory_base : trailingMemory.base = 1000 := rfl

@[simp] theorem trailingEnd_eq : trailingEnd = 1157 := by
  simp [trailingEnd, encodedCertificate_length]

theorem trailing_body_rejected_without_fault :
    observeView (execute trailingMemory trailingEnd header) =
      some (.ok none) := by
  rw [execute_agrees_prepareDetailed]
  simp only [trailingMemory_base, trailingEnd_eq]
  decide

end Canary

#print axioms execute_agrees_prepareDetailed
#print axioms physicalEnd_toNat
#print axioms header_bodyByteLength_lt_uint64
#print axioms Canary.exact_body_view_accepts
#print axioms Canary.exact_body_view_values
#print axioms Canary.truncated_body_rejected_without_fault
#print axioms Canary.trailing_body_rejected_without_fault

end Mettapedia.GSLT.LanguageDef.M0GCBodyViewByteMachineRealization
