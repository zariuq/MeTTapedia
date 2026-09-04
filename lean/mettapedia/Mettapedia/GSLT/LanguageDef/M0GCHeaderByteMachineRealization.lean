import Mettapedia.GSLT.LanguageDef.M0GCCheckedByteMachineIR

/-!
# M0GC fixed-header realization in the checked byte-machine

This module lowers the complete fixed-offset M0GC header reader to ordinary
checked byte-machine instructions.  The target program performs explicit
address formation, width-correct loads, magic and version comparisons, and
control transfer.  It contains no primitive header decoder.

Malformed magic or version is a logical rejection.  Address overflow and an
incomplete memory field are machine faults.  These outcomes remain distinct
even though the higher-level `Option Header` reader intentionally forgets the
difference.

Maturity boundary: this is a connected intermediate proof of concept for the
fixed 104-byte header only.  It is not the body decoder, table preparation,
logical replay, complete checker lowering, an endgame register allocation,
StructuredC, portable C, verified object code, or the official MM0/MMB
format.  The explicit register assignment is proof-oriented and may later be
refined to a smaller liveness-based allocation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCHeaderByteMachineRealization

open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCCheckedByteMachineIR

/-! ## Typed register assignment -/

def shape : RegisterShape where
  byteCount := 0
  word16Count := 3
  word32Count := 8
  word64Count := 9
  addressCount := 3
  flagCount := 1

def versionActual : Word16Register shape := ⟨0, by decide⟩
def versionExpected : Word16Register shape := ⟨1, by decide⟩
def flags : Word16Register shape := ⟨2, by decide⟩

def magicActual : Word32Register shape := ⟨0, by decide⟩
def magicExpected : Word32Register shape := ⟨1, by decide⟩
def termCount : Word32Register shape := ⟨2, by decide⟩
def childCount : Word32Register shape := ⟨3, by decide⟩
def proofCount : Word32Register shape := ⟨4, by decide⟩
def argumentCount : Word32Register shape := ⟨5, by decide⟩
def premiseCount : Word32Register shape := ⟨6, by decide⟩
def goalTerm : Word32Register shape := ⟨7, by decide⟩

def profileChunk0 : Word64Register shape := ⟨0, by decide⟩
def profileChunk1 : Word64Register shape := ⟨1, by decide⟩
def profileChunk2 : Word64Register shape := ⟨2, by decide⟩
def profileChunk3 : Word64Register shape := ⟨3, by decide⟩
def sourceChunk0 : Word64Register shape := ⟨4, by decide⟩
def sourceChunk1 : Word64Register shape := ⟨5, by decide⟩
def sourceChunk2 : Word64Register shape := ⟨6, by decide⟩
def sourceChunk3 : Word64Register shape := ⟨7, by decide⟩
def bodyChecksum : Word64Register shape := ⟨8, by decide⟩

def baseAddress : AddressRegister shape := ⟨0, by decide⟩
def fieldOffset : AddressRegister shape := ⟨1, by decide⟩
def fieldAddress : AddressRegister shape := ⟨2, by decide⟩
def equal : FlagRegister shape := ⟨0, by decide⟩

/-- Little-endian scalar spelling of the canonical four-byte magic. -/
def magicWord : UInt32 := 0x4347304d

theorem magicWord_encodes_magic :
    Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat.encodeUInt32LE
      magicWord = magic := by
  decide

/-! ## Source-level detailed header operation -/

def readWord16At (memory : ByteMemory) (offset : UInt64) :
    Except Fault UInt16 :=
  match Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory.checkedAdd
      memory.base offset with
  | none => .error .addressOverflow
  | some address =>
      match memory.loadUInt16LE? address with
      | none => .error .word16ReadOutOfBounds
      | some value => .ok value

def readWord32At (memory : ByteMemory) (offset : UInt64) :
    Except Fault UInt32 :=
  match Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory.checkedAdd
      memory.base offset with
  | none => .error .addressOverflow
  | some address =>
      match memory.loadUInt32LE? address with
      | none => .error .word32ReadOutOfBounds
      | some value => .ok value

def readWord64At (memory : ByteMemory) (offset : UInt64) :
    Except Fault UInt64 :=
  match Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory.checkedAdd
      memory.base offset with
  | none => .error .addressOverflow
  | some address =>
      match memory.loadUInt64LE? address with
      | none => .error .word64ReadOutOfBounds
      | some value => .ok value

/-- Explicit evidence for one checked two-byte physical field read. -/
structure Word16Read (memory : ByteMemory) (offset : UInt64)
    (value : UInt16) where
  address : UInt64
  addressExact :
    Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory.checkedAdd
      memory.base offset = some address
  valueExact : memory.loadUInt16LE? address = some value

/-- Explicit evidence for one checked four-byte physical field read. -/
structure Word32Read (memory : ByteMemory) (offset : UInt64)
    (value : UInt32) where
  address : UInt64
  addressExact :
    Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory.checkedAdd
      memory.base offset = some address
  valueExact : memory.loadUInt32LE? address = some value

/-- Explicit evidence for one checked eight-byte physical field read. -/
structure Word64Read (memory : ByteMemory) (offset : UInt64)
    (value : UInt64) where
  address : UInt64
  addressExact :
    Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory.checkedAdd
      memory.base offset = some address
  valueExact : memory.loadUInt64LE? address = some value

/-- The source header algorithm with the logical-reject/machine-fault
distinction retained.  Digest blocks are represented as four ordinary
little-endian 64-bit fields each. -/
def readHeaderDetailed (memory : ByteMemory) : Except Fault (Option Header) := do
  let decodedMagic ← readWord32At memory 0
  if decodedMagic = magicWord then do
    let decodedVersion ← readWord16At memory 4
    if decodedVersion = version then do
      let decodedFlags ← readWord16At memory 6
      let decodedTermCount ← readWord32At memory 8
      let decodedChildCount ← readWord32At memory 12
      let decodedProofCount ← readWord32At memory 16
      let decodedArgumentCount ← readWord32At memory 20
      let decodedPremiseCount ← readWord32At memory 24
      let decodedGoalTerm ← readWord32At memory 28
      let profile0 ← readWord64At memory 32
      let profile1 ← readWord64At memory 40
      let profile2 ← readWord64At memory 48
      let profile3 ← readWord64At memory 56
      let source0 ← readWord64At memory 64
      let source1 ← readWord64At memory 72
      let source2 ← readWord64At memory 80
      let source3 ← readWord64At memory 88
      let checksum ← readWord64At memory 96
      pure (some
        { flags := decodedFlags
          termCount := decodedTermCount
          childCount := decodedChildCount
          proofCount := decodedProofCount
          argumentCount := decodedArgumentCount
          premiseReferenceCount := decodedPremiseCount
          goalTerm := decodedGoalTerm
          profileDigest := encodeUInt64LE profile0 ++ encodeUInt64LE profile1 ++
            encodeUInt64LE profile2 ++ encodeUInt64LE profile3
          sourceDigest := encodeUInt64LE source0 ++ encodeUInt64LE source1 ++
            encodeUInt64LE source2 ++ encodeUInt64LE source3
          bodyChecksum := checksum })
    else
      pure none
  else
    pure none

/-- Successful physical evidence through the last digest chunk.  This prefix
is sufficient to reach the checksum-load instruction even when the checksum
field itself is truncated. -/
structure HeaderPrefixReads (memory : ByteMemory) (header : Header) where
  magicRead : Word32Read memory 0 magicWord
  versionRead : Word16Read memory 4 version
  flagsRead : Word16Read memory 6 header.flags
  termCountRead : Word32Read memory 8 header.termCount
  childCountRead : Word32Read memory 12 header.childCount
  proofCountRead : Word32Read memory 16 header.proofCount
  argumentCountRead : Word32Read memory 20 header.argumentCount
  premiseCountRead : Word32Read memory 24 header.premiseReferenceCount
  goalTermRead : Word32Read memory 28 header.goalTerm
  profile0 : UInt64
  profile1 : UInt64
  profile2 : UInt64
  profile3 : UInt64
  source0 : UInt64
  source1 : UInt64
  source2 : UInt64
  source3 : UInt64
  profile0Read : Word64Read memory 32 profile0
  profile1Read : Word64Read memory 40 profile1
  profile2Read : Word64Read memory 48 profile2
  profile3Read : Word64Read memory 56 profile3
  source0Read : Word64Read memory 64 source0
  source1Read : Word64Read memory 72 source1
  source2Read : Word64Read memory 80 source2
  source3Read : Word64Read memory 88 source3
  profileDigestExact : header.profileDigest =
    encodeUInt64LE profile0 ++ encodeUInt64LE profile1 ++
      encodeUInt64LE profile2 ++ encodeUInt64LE profile3
  sourceDigestExact : header.sourceDigest =
    encodeUInt64LE source0 ++ encodeUInt64LE source1 ++
      encodeUInt64LE source2 ++ encodeUInt64LE source3

/-- Successful source-side physical evidence for all fixed header fields. -/
structure HeaderReads (memory : ByteMemory) (header : Header)
    extends HeaderPrefixReads memory header where
  checksumRead : Word64Read memory 96 header.bodyChecksum

/-! ## Explicit target program -/

/-- A fixed instruction program independent of submitted byte contents and
physical base.  `baseAddress` is initialized from the allocation; all field
addresses are formed by checked target instructions. -/
def program : Program shape where
  code := #[
    .constAddress fieldOffset 0,
    .addAddressChecked fieldAddress baseAddress fieldOffset,
    .loadWord32LE magicActual fieldAddress,
    .constWord32 magicExpected magicWord,
    .equalWord32 equal magicActual magicExpected,
    .rejectUnless equal,

    .constAddress fieldOffset 4,
    .addAddressChecked fieldAddress baseAddress fieldOffset,
    .loadWord16LE versionActual fieldAddress,
    .constWord16 versionExpected version,
    .equalWord16 equal versionActual versionExpected,
    .rejectUnless equal,

    .constAddress fieldOffset 6,
    .addAddressChecked fieldAddress baseAddress fieldOffset,
    .loadWord16LE flags fieldAddress,

    .constAddress fieldOffset 8,
    .addAddressChecked fieldAddress baseAddress fieldOffset,
    .loadWord32LE termCount fieldAddress,
    .constAddress fieldOffset 12,
    .addAddressChecked fieldAddress baseAddress fieldOffset,
    .loadWord32LE childCount fieldAddress,
    .constAddress fieldOffset 16,
    .addAddressChecked fieldAddress baseAddress fieldOffset,
    .loadWord32LE proofCount fieldAddress,
    .constAddress fieldOffset 20,
    .addAddressChecked fieldAddress baseAddress fieldOffset,
    .loadWord32LE argumentCount fieldAddress,
    .constAddress fieldOffset 24,
    .addAddressChecked fieldAddress baseAddress fieldOffset,
    .loadWord32LE premiseCount fieldAddress,
    .constAddress fieldOffset 28,
    .addAddressChecked fieldAddress baseAddress fieldOffset,
    .loadWord32LE goalTerm fieldAddress,

    .constAddress fieldOffset 32,
    .addAddressChecked fieldAddress baseAddress fieldOffset,
    .loadWord64LE profileChunk0 fieldAddress,
    .constAddress fieldOffset 40,
    .addAddressChecked fieldAddress baseAddress fieldOffset,
    .loadWord64LE profileChunk1 fieldAddress,
    .constAddress fieldOffset 48,
    .addAddressChecked fieldAddress baseAddress fieldOffset,
    .loadWord64LE profileChunk2 fieldAddress,
    .constAddress fieldOffset 56,
    .addAddressChecked fieldAddress baseAddress fieldOffset,
    .loadWord64LE profileChunk3 fieldAddress,

    .constAddress fieldOffset 64,
    .addAddressChecked fieldAddress baseAddress fieldOffset,
    .loadWord64LE sourceChunk0 fieldAddress,
    .constAddress fieldOffset 72,
    .addAddressChecked fieldAddress baseAddress fieldOffset,
    .loadWord64LE sourceChunk1 fieldAddress,
    .constAddress fieldOffset 80,
    .addAddressChecked fieldAddress baseAddress fieldOffset,
    .loadWord64LE sourceChunk2 fieldAddress,
    .constAddress fieldOffset 88,
    .addAddressChecked fieldAddress baseAddress fieldOffset,
    .loadWord64LE sourceChunk3 fieldAddress,

    .constAddress fieldOffset 96,
    .addAddressChecked fieldAddress baseAddress fieldOffset,
    .loadWord64LE bodyChecksum fieldAddress,
    .halt true]

def initialState (memory : ByteMemory) : MachineState shape :=
  .running 0
    ((RegisterFile.zero shape).writeAddress baseAddress memory.base) memory

/-- The accepting path executes 61 instructions; early rejection and faults
stutter for the remaining fuel. -/
def execute (memory : ByteMemory) : MachineState shape :=
  runSteps program 61 (initialState memory)

def headerOfRegisters (registers : RegisterFile shape) : Header :=
  { flags := registers.words16 flags
    termCount := registers.words32 termCount
    childCount := registers.words32 childCount
    proofCount := registers.words32 proofCount
    argumentCount := registers.words32 argumentCount
    premiseReferenceCount := registers.words32 premiseCount
    goalTerm := registers.words32 goalTerm
    profileDigest := encodeUInt64LE (registers.words64 profileChunk0) ++
      encodeUInt64LE (registers.words64 profileChunk1) ++
      encodeUInt64LE (registers.words64 profileChunk2) ++
      encodeUInt64LE (registers.words64 profileChunk3)
    sourceDigest := encodeUInt64LE (registers.words64 sourceChunk0) ++
      encodeUInt64LE (registers.words64 sourceChunk1) ++
      encodeUInt64LE (registers.words64 sourceChunk2) ++
      encodeUInt64LE (registers.words64 sourceChunk3)
    bodyChecksum := registers.words64 bodyChecksum }

/-- Read the program's typed semantic result.  It intentionally preserves the
machine-fault versus logical-rejection distinction. -/
def observeHeader : MachineState shape →
    Option (Except Fault (Option Header))
  | .running _ _ _ => none
  | .halted false _ _ => some (.ok none)
  | .halted true registers _ => some (.ok (some (headerOfRegisters registers)))
  | .faulted reason _ _ => some (.error reason)

/-- The exact register file after all fields preceding the checksum have been
loaded.  Keeping this state named lets success and truncation proofs share
the same 57-step prefix rather than re-evaluating it independently. -/
def prefixRegisters {memory : ByteMemory} {header : Header}
    (reads : HeaderPrefixReads memory header) : RegisterFile shape :=
  let registers0 :=
    (RegisterFile.zero shape).writeAddress baseAddress memory.base
  let registersMagic :=
    (((((registers0.writeAddress fieldOffset 0).writeAddress fieldAddress
      reads.magicRead.address).writeWord32 magicActual magicWord).writeWord32
      magicExpected magicWord).writeFlag equal true)
  let registersVersion :=
    (((((registersMagic.writeAddress fieldOffset 4).writeAddress fieldAddress
      reads.versionRead.address).writeWord16 versionActual version).writeWord16
      versionExpected version).writeFlag equal true)
  let registersFlags :=
    ((registersVersion.writeAddress fieldOffset 6).writeAddress fieldAddress
      reads.flagsRead.address).writeWord16 flags header.flags
  let registersTerm :=
    ((registersFlags.writeAddress fieldOffset 8).writeAddress fieldAddress
      reads.termCountRead.address).writeWord32 termCount header.termCount
  let registersChild :=
    ((registersTerm.writeAddress fieldOffset 12).writeAddress fieldAddress
      reads.childCountRead.address).writeWord32 childCount header.childCount
  let registersProof :=
    ((registersChild.writeAddress fieldOffset 16).writeAddress fieldAddress
      reads.proofCountRead.address).writeWord32 proofCount header.proofCount
  let registersArgument :=
    ((registersProof.writeAddress fieldOffset 20).writeAddress fieldAddress
      reads.argumentCountRead.address).writeWord32 argumentCount
      header.argumentCount
  let registersPremise :=
    ((registersArgument.writeAddress fieldOffset 24).writeAddress fieldAddress
      reads.premiseCountRead.address).writeWord32 premiseCount
      header.premiseReferenceCount
  let registersScalars :=
    ((registersPremise.writeAddress fieldOffset 28).writeAddress fieldAddress
      reads.goalTermRead.address).writeWord32 goalTerm header.goalTerm
  let registersProfile0 :=
    ((registersScalars.writeAddress fieldOffset 32).writeAddress fieldAddress
      reads.profile0Read.address).writeWord64 profileChunk0 reads.profile0
  let registersProfile1 :=
    ((registersProfile0.writeAddress fieldOffset 40).writeAddress fieldAddress
      reads.profile1Read.address).writeWord64 profileChunk1 reads.profile1
  let registersProfile2 :=
    ((registersProfile1.writeAddress fieldOffset 48).writeAddress fieldAddress
      reads.profile2Read.address).writeWord64 profileChunk2 reads.profile2
  let registersProfile :=
    ((registersProfile2.writeAddress fieldOffset 56).writeAddress fieldAddress
      reads.profile3Read.address).writeWord64 profileChunk3 reads.profile3
  let registersSource0 :=
    ((registersProfile.writeAddress fieldOffset 64).writeAddress fieldAddress
      reads.source0Read.address).writeWord64 sourceChunk0 reads.source0
  let registersSource1 :=
    ((registersSource0.writeAddress fieldOffset 72).writeAddress fieldAddress
      reads.source1Read.address).writeWord64 sourceChunk1 reads.source1
  let registersSource2 :=
    ((registersSource1.writeAddress fieldOffset 80).writeAddress fieldAddress
      reads.source2Read.address).writeWord64 sourceChunk2 reads.source2
  ((registersSource2.writeAddress fieldOffset 88).writeAddress fieldAddress
    reads.source3Read.address).writeWord64 sourceChunk3 reads.source3

@[simp] theorem prefixRegisters_base {memory : ByteMemory} {header : Header}
    (reads : HeaderPrefixReads memory header) :
    (prefixRegisters reads).addresses baseAddress = memory.base := by
  simp [prefixRegisters, baseAddress, fieldOffset, fieldAddress]

/-! ## Source-to-target correspondence -/

/-- The machine reaches the checksum instruction after exactly 57 ordinary
steps whenever every preceding physical field read is witnessed. -/
theorem runPrefix_of_reads {memory : ByteMemory} {header : Header}
    (reads : HeaderPrefixReads memory header) :
    runSteps program 57 (initialState memory) =
      .running 57 (prefixRegisters reads) memory := by
  let registers0 :=
    (RegisterFile.zero shape).writeAddress baseAddress memory.base
  let registersMagic :=
    (((((registers0.writeAddress fieldOffset 0).writeAddress fieldAddress
      reads.magicRead.address).writeWord32 magicActual magicWord).writeWord32
      magicExpected magicWord).writeFlag equal true)
  let registersVersion :=
    (((((registersMagic.writeAddress fieldOffset 4).writeAddress fieldAddress
      reads.versionRead.address).writeWord16 versionActual version).writeWord16
      versionExpected version).writeFlag equal true)
  let registersFlags :=
    ((registersVersion.writeAddress fieldOffset 6).writeAddress fieldAddress
      reads.flagsRead.address).writeWord16 flags header.flags
  let registersTerm :=
    ((registersFlags.writeAddress fieldOffset 8).writeAddress fieldAddress
      reads.termCountRead.address).writeWord32 termCount header.termCount
  let registersChild :=
    ((registersTerm.writeAddress fieldOffset 12).writeAddress fieldAddress
      reads.childCountRead.address).writeWord32 childCount header.childCount
  let registersProof :=
    ((registersChild.writeAddress fieldOffset 16).writeAddress fieldAddress
      reads.proofCountRead.address).writeWord32 proofCount header.proofCount
  let registersArgument :=
    ((registersProof.writeAddress fieldOffset 20).writeAddress fieldAddress
      reads.argumentCountRead.address).writeWord32 argumentCount
      header.argumentCount
  let registersPremise :=
    ((registersArgument.writeAddress fieldOffset 24).writeAddress fieldAddress
      reads.premiseCountRead.address).writeWord32 premiseCount
      header.premiseReferenceCount
  let registersScalars :=
    ((registersPremise.writeAddress fieldOffset 28).writeAddress fieldAddress
      reads.goalTermRead.address).writeWord32 goalTerm header.goalTerm
  let registersProfile0 :=
    ((registersScalars.writeAddress fieldOffset 32).writeAddress fieldAddress
      reads.profile0Read.address).writeWord64 profileChunk0 reads.profile0
  let registersProfile1 :=
    ((registersProfile0.writeAddress fieldOffset 40).writeAddress fieldAddress
      reads.profile1Read.address).writeWord64 profileChunk1 reads.profile1
  let registersProfile2 :=
    ((registersProfile1.writeAddress fieldOffset 48).writeAddress fieldAddress
      reads.profile2Read.address).writeWord64 profileChunk2 reads.profile2
  let registersProfile :=
    ((registersProfile2.writeAddress fieldOffset 56).writeAddress fieldAddress
      reads.profile3Read.address).writeWord64 profileChunk3 reads.profile3
  let registersSource0 :=
    ((registersProfile.writeAddress fieldOffset 64).writeAddress fieldAddress
      reads.source0Read.address).writeWord64 sourceChunk0 reads.source0
  let registersSource1 :=
    ((registersSource0.writeAddress fieldOffset 72).writeAddress fieldAddress
      reads.source1Read.address).writeWord64 sourceChunk1 reads.source1
  let registersSource2 :=
    ((registersSource1.writeAddress fieldOffset 80).writeAddress fieldAddress
      reads.source2Read.address).writeWord64 sourceChunk2 reads.source2
  let registersSource :=
    ((registersSource2.writeAddress fieldOffset 88).writeAddress fieldAddress
      reads.source3Read.address).writeWord64 sourceChunk3 reads.source3
  have baseNeOffset : baseAddress ≠ fieldOffset := by decide
  have baseNeField : baseAddress ≠ fieldAddress := by decide
  have registers0Base : registers0.addresses baseAddress = memory.base := by
    simp [registers0]
  have registersMagicBase :
      registersMagic.addresses baseAddress = memory.base := by
    simp [registersMagic, registers0Base, baseNeOffset, baseNeField]
  have registersVersionBase :
      registersVersion.addresses baseAddress = memory.base := by
    simp [registersVersion, registersMagicBase, baseNeOffset, baseNeField]
  have registersScalarsBase :
      registersScalars.addresses baseAddress = memory.base := by
    simp [registersScalars, registersPremise, registersArgument,
      registersProof, registersChild, registersTerm, registersFlags,
      registersVersionBase, baseNeOffset, baseNeField]
  have registersProfileBase :
      registersProfile.addresses baseAddress = memory.base := by
    simp [registersProfile, registersProfile2, registersProfile1,
      registersProfile0, registersScalarsBase, baseNeOffset, baseNeField]
  have registersVersionBase0 :
      registersVersion.addresses (0 : Fin 3) = memory.base := by
    rw [show (0 : Fin 3) = baseAddress by rfl]
    exact registersVersionBase
  have registersScalarsBase0 :
      registersScalars.addresses (0 : Fin 3) = memory.base := by
    rw [show (0 : Fin 3) = baseAddress by rfl]
    exact registersScalarsBase
  have registersProfileBase0 :
      registersProfile.addresses (0 : Fin 3) = memory.base := by
    rw [show (0 : Fin 3) = baseAddress by rfl]
    exact registersProfileBase
  have magicStage :
      runSteps program 6 (initialState memory) =
        .running 6 registersMagic memory := by
    simp [initialState, program, runSteps, step, executeInstruction,
      continueAt, registers0, registersMagic,
      RegisterFile.writeAddress, RegisterFile.writeWord32,
      RegisterFile.writeFlag, shape, baseAddress, fieldOffset, fieldAddress,
      magicActual, magicExpected, equal, reads.magicRead.addressExact,
      reads.magicRead.valueExact]
  have versionStage :
      runSteps program 6 (.running 6 registersMagic memory) =
        .running 12 registersVersion memory := by
    simp [program, runSteps, step, executeInstruction, continueAt,
      registers0, registersMagic, registersVersion, RegisterFile.writeAddress,
      RegisterFile.writeWord16, RegisterFile.writeFlag, shape, baseAddress,
      fieldOffset, fieldAddress, versionActual, versionExpected, equal,
      reads.versionRead.addressExact, reads.versionRead.valueExact]
  have scalarStage :
      runSteps program 21 (.running 12 registersVersion memory) =
        .running 33 registersScalars memory := by
    simp [program, runSteps, step, executeInstruction, continueAt,
      registersFlags, registersTerm, registersChild, registersProof,
      registersArgument, registersPremise, registersScalars,
      RegisterFile.writeAddress, RegisterFile.writeWord16,
      RegisterFile.writeWord32, shape, baseAddress, fieldOffset, fieldAddress,
      flags, termCount, childCount, proofCount, argumentCount, premiseCount,
      goalTerm, registersVersionBase0, reads.flagsRead.addressExact,
      reads.flagsRead.valueExact, reads.termCountRead.addressExact,
      reads.termCountRead.valueExact, reads.childCountRead.addressExact,
      reads.childCountRead.valueExact, reads.proofCountRead.addressExact,
      reads.proofCountRead.valueExact, reads.argumentCountRead.addressExact,
      reads.argumentCountRead.valueExact, reads.premiseCountRead.addressExact,
      reads.premiseCountRead.valueExact, reads.goalTermRead.addressExact,
      reads.goalTermRead.valueExact]
  have profileStage :
      runSteps program 12 (.running 33 registersScalars memory) =
        .running 45 registersProfile memory := by
    simp [program, runSteps, step, executeInstruction, continueAt,
      registersProfile0, registersProfile1, registersProfile2,
      registersProfile, RegisterFile.writeAddress, RegisterFile.writeWord64,
      shape, baseAddress, fieldOffset, fieldAddress, profileChunk0,
      profileChunk1, profileChunk2, profileChunk3, registersScalarsBase0,
      reads.profile0Read.addressExact, reads.profile0Read.valueExact,
      reads.profile1Read.addressExact, reads.profile1Read.valueExact,
      reads.profile2Read.addressExact, reads.profile2Read.valueExact,
      reads.profile3Read.addressExact, reads.profile3Read.valueExact]
  have sourceStage :
      runSteps program 12 (.running 45 registersProfile memory) =
        .running 57 registersSource memory := by
    simp [program, runSteps, step, executeInstruction, continueAt,
      registersSource0, registersSource1, registersSource2, registersSource,
      RegisterFile.writeAddress, RegisterFile.writeWord64, shape,
      baseAddress, fieldOffset, fieldAddress, sourceChunk0, sourceChunk1,
      sourceChunk2, sourceChunk3, registersProfileBase0,
      reads.source0Read.addressExact, reads.source0Read.valueExact,
      reads.source1Read.addressExact, reads.source1Read.valueExact,
      reads.source2Read.addressExact, reads.source2Read.valueExact,
      reads.source3Read.addressExact, reads.source3Read.valueExact]
  rw [show 57 = 6 + 51 by decide, runSteps_add, magicStage]
  rw [show 51 = 6 + 45 by decide, runSteps_add, versionStage]
  rw [show 45 = 21 + 24 by decide, runSteps_add, scalarStage]
  rw [show 24 = 12 + 12 by decide, runSteps_add, profileStage, sourceStage]
  rfl

/-- A complete but incorrect magic word is a logical rejection, regardless
of whether later header fields are allocated. -/
theorem execute_rejects_wrong_magic {memory : ByteMemory} {actual : UInt32}
    (read : Word32Read memory 0 actual)
    (different : actual ≠ magicWord) :
    observeHeader (execute memory) = some (.ok none) := by
  let registers0 :=
    (RegisterFile.zero shape).writeAddress baseAddress memory.base
  let registersRejected :=
    (((((registers0.writeAddress fieldOffset 0).writeAddress fieldAddress
      read.address).writeWord32 magicActual actual).writeWord32
      magicExpected magicWord).writeFlag equal false)
  have rejectionStage :
      runSteps program 6 (initialState memory) =
        .halted false registersRejected memory := by
    simp [initialState, program, runSteps, step, executeInstruction,
      continueAt, registers0, registersRejected, RegisterFile.writeAddress,
      RegisterFile.writeWord32, RegisterFile.writeFlag, shape, baseAddress,
      fieldOffset, fieldAddress, magicActual, magicExpected, equal,
      read.addressExact, read.valueExact, different]
  unfold execute
  rw [show 61 = 6 + 55 by decide, runSteps_add, rejectionStage]
  rfl

/-- A correct magic word followed by a complete unsupported version is a
logical rejection before any later header field is consulted. -/
theorem execute_rejects_wrong_version {memory : ByteMemory} {actual : UInt16}
    (magicRead : Word32Read memory 0 magicWord)
    (versionRead : Word16Read memory 4 actual)
    (different : actual ≠ version) :
    observeHeader (execute memory) = some (.ok none) := by
  let registers0 :=
    (RegisterFile.zero shape).writeAddress baseAddress memory.base
  let registersMagic :=
    (((((registers0.writeAddress fieldOffset 0).writeAddress fieldAddress
      magicRead.address).writeWord32 magicActual magicWord).writeWord32
      magicExpected magicWord).writeFlag equal true)
  let registersRejected :=
    (((((registersMagic.writeAddress fieldOffset 4).writeAddress fieldAddress
      versionRead.address).writeWord16 versionActual actual).writeWord16
      versionExpected version).writeFlag equal false)
  have magicStage :
      runSteps program 6 (initialState memory) =
        .running 6 registersMagic memory := by
    simp [initialState, program, runSteps, step, executeInstruction,
      continueAt, registers0, registersMagic, RegisterFile.writeAddress,
      RegisterFile.writeWord32, RegisterFile.writeFlag, shape, baseAddress,
      fieldOffset, fieldAddress, magicActual, magicExpected, equal,
      magicRead.addressExact, magicRead.valueExact]
  have rejectionStage :
      runSteps program 6 (.running 6 registersMagic memory) =
        .halted false registersRejected memory := by
    simp [program, runSteps, step, executeInstruction, continueAt,
      registers0, registersMagic, registersRejected, RegisterFile.writeAddress,
      RegisterFile.writeWord16, RegisterFile.writeFlag, shape, baseAddress,
      fieldOffset, fieldAddress, versionActual, versionExpected, equal,
      versionRead.addressExact, versionRead.valueExact, different]
  unfold execute
  rw [show 61 = 6 + 55 by decide, runSteps_add, magicStage]
  rw [show 55 = 6 + 49 by decide, runSteps_add, rejectionStage]
  rfl

theorem readHeaderDetailed_of_reads {memory : ByteMemory} {header : Header}
    (reads : HeaderReads memory header) :
    readHeaderDetailed memory = .ok (some header) := by
  simp [readHeaderDetailed, bind, Except.bind, pure, Except.pure,
    readWord16At, readWord32At, readWord64At,
    reads.magicRead.addressExact, reads.magicRead.valueExact,
    reads.versionRead.addressExact, reads.versionRead.valueExact,
    reads.flagsRead.addressExact, reads.flagsRead.valueExact,
    reads.termCountRead.addressExact, reads.termCountRead.valueExact,
    reads.childCountRead.addressExact, reads.childCountRead.valueExact,
    reads.proofCountRead.addressExact, reads.proofCountRead.valueExact,
    reads.argumentCountRead.addressExact, reads.argumentCountRead.valueExact,
    reads.premiseCountRead.addressExact, reads.premiseCountRead.valueExact,
    reads.goalTermRead.addressExact, reads.goalTermRead.valueExact,
    reads.profile0Read.addressExact, reads.profile0Read.valueExact,
    reads.profile1Read.addressExact, reads.profile1Read.valueExact,
    reads.profile2Read.addressExact, reads.profile2Read.valueExact,
    reads.profile3Read.addressExact, reads.profile3Read.valueExact,
    reads.source0Read.addressExact, reads.source0Read.valueExact,
    reads.source1Read.addressExact, reads.source1Read.valueExact,
    reads.source2Read.addressExact, reads.source2Read.valueExact,
    reads.source3Read.addressExact, reads.source3Read.valueExact,
    reads.checksumRead.addressExact, reads.checksumRead.valueExact]
  cases header
  simp
  exact ⟨reads.profileDigestExact.symm, reads.sourceDigestExact.symm⟩

/-- Every independently witnessed successful physical header read follows an
accepting target path and reconstructs exactly the same header. -/
theorem execute_accepts_of_reads {memory : ByteMemory} {header : Header}
    (reads : HeaderReads memory header) :
    observeHeader (execute memory) = some (.ok (some header)) := by
  let registers0 :=
    (RegisterFile.zero shape).writeAddress baseAddress memory.base
  let registersMagic :=
    (((((registers0.writeAddress fieldOffset 0).writeAddress fieldAddress
      reads.magicRead.address).writeWord32 magicActual magicWord).writeWord32
      magicExpected magicWord).writeFlag equal true)
  let registersVersion :=
    (((((registersMagic.writeAddress fieldOffset 4).writeAddress fieldAddress
      reads.versionRead.address).writeWord16 versionActual version).writeWord16
      versionExpected version).writeFlag equal true)
  let registersFlags :=
    ((registersVersion.writeAddress fieldOffset 6).writeAddress fieldAddress
      reads.flagsRead.address).writeWord16 flags header.flags
  let registersTerm :=
    ((registersFlags.writeAddress fieldOffset 8).writeAddress fieldAddress
      reads.termCountRead.address).writeWord32 termCount header.termCount
  let registersChild :=
    ((registersTerm.writeAddress fieldOffset 12).writeAddress fieldAddress
      reads.childCountRead.address).writeWord32 childCount header.childCount
  let registersProof :=
    ((registersChild.writeAddress fieldOffset 16).writeAddress fieldAddress
      reads.proofCountRead.address).writeWord32 proofCount header.proofCount
  let registersArgument :=
    ((registersProof.writeAddress fieldOffset 20).writeAddress fieldAddress
      reads.argumentCountRead.address).writeWord32 argumentCount
      header.argumentCount
  let registersPremise :=
    ((registersArgument.writeAddress fieldOffset 24).writeAddress fieldAddress
      reads.premiseCountRead.address).writeWord32 premiseCount
      header.premiseReferenceCount
  let registersScalars :=
    ((registersPremise.writeAddress fieldOffset 28).writeAddress fieldAddress
      reads.goalTermRead.address).writeWord32 goalTerm header.goalTerm
  let registersProfile0 :=
    ((registersScalars.writeAddress fieldOffset 32).writeAddress fieldAddress
      reads.profile0Read.address).writeWord64 profileChunk0 reads.profile0
  let registersProfile1 :=
    ((registersProfile0.writeAddress fieldOffset 40).writeAddress fieldAddress
      reads.profile1Read.address).writeWord64 profileChunk1 reads.profile1
  let registersProfile2 :=
    ((registersProfile1.writeAddress fieldOffset 48).writeAddress fieldAddress
      reads.profile2Read.address).writeWord64 profileChunk2 reads.profile2
  let registersProfile :=
    ((registersProfile2.writeAddress fieldOffset 56).writeAddress fieldAddress
      reads.profile3Read.address).writeWord64 profileChunk3 reads.profile3
  let registersSource0 :=
    ((registersProfile.writeAddress fieldOffset 64).writeAddress fieldAddress
      reads.source0Read.address).writeWord64 sourceChunk0 reads.source0
  let registersSource1 :=
    ((registersSource0.writeAddress fieldOffset 72).writeAddress fieldAddress
      reads.source1Read.address).writeWord64 sourceChunk1 reads.source1
  let registersSource2 :=
    ((registersSource1.writeAddress fieldOffset 80).writeAddress fieldAddress
      reads.source2Read.address).writeWord64 sourceChunk2 reads.source2
  let registersSource :=
    ((registersSource2.writeAddress fieldOffset 88).writeAddress fieldAddress
      reads.source3Read.address).writeWord64 sourceChunk3 reads.source3
  let registersChecksum :=
    (((registersSource.writeAddress fieldOffset 96).writeAddress fieldAddress
      reads.checksumRead.address).writeWord64 bodyChecksum header.bodyChecksum)
  have baseNeOffset : baseAddress ≠ fieldOffset := by decide
  have baseNeField : baseAddress ≠ fieldAddress := by decide
  have registers0Base : registers0.addresses baseAddress = memory.base := by
    simp [registers0]
  have registersMagicBase :
      registersMagic.addresses baseAddress = memory.base := by
    simp [registersMagic, registers0Base, baseNeOffset, baseNeField]
  have registersVersionBase :
      registersVersion.addresses baseAddress = memory.base := by
    simp [registersVersion, registersMagicBase, baseNeOffset, baseNeField]
  have registersScalarsBase :
      registersScalars.addresses baseAddress = memory.base := by
    simp [registersScalars, registersPremise, registersArgument,
      registersProof, registersChild, registersTerm, registersFlags,
      registersVersionBase, baseNeOffset, baseNeField]
  have registersProfileBase :
      registersProfile.addresses baseAddress = memory.base := by
    simp [registersProfile, registersProfile2, registersProfile1,
      registersProfile0, registersScalarsBase, baseNeOffset, baseNeField]
  have registersSourceBase :
      registersSource.addresses baseAddress = memory.base := by
    simp [registersSource, registersSource2, registersSource1,
      registersSource0, registersProfileBase, baseNeOffset, baseNeField]
  have registersVersionBase0 :
      registersVersion.addresses (0 : Fin 3) = memory.base := by
    rw [show (0 : Fin 3) = baseAddress by rfl]
    exact registersVersionBase
  have registersScalarsBase0 :
      registersScalars.addresses (0 : Fin 3) = memory.base := by
    rw [show (0 : Fin 3) = baseAddress by rfl]
    exact registersScalarsBase
  have registersProfileBase0 :
      registersProfile.addresses (0 : Fin 3) = memory.base := by
    rw [show (0 : Fin 3) = baseAddress by rfl]
    exact registersProfileBase
  have registersSourceBase0 :
      registersSource.addresses (0 : Fin 3) = memory.base := by
    rw [show (0 : Fin 3) = baseAddress by rfl]
    exact registersSourceBase
  have magicStage :
      runSteps program 6 (initialState memory) =
        .running 6 registersMagic memory := by
    simp [initialState, program, runSteps, step, executeInstruction,
      continueAt, registers0, registersMagic,
      RegisterFile.writeAddress, RegisterFile.writeWord32,
      RegisterFile.writeFlag, shape, baseAddress, fieldOffset, fieldAddress,
      magicActual, magicExpected, equal, reads.magicRead.addressExact,
      reads.magicRead.valueExact]
  have versionStage :
      runSteps program 6 (.running 6 registersMagic memory) =
        .running 12 registersVersion memory := by
    simp [program, runSteps, step, executeInstruction, continueAt,
      registers0, registersMagic, registersVersion, RegisterFile.writeAddress,
      RegisterFile.writeWord16, RegisterFile.writeFlag, shape, baseAddress,
      fieldOffset, fieldAddress, versionActual, versionExpected, equal,
      reads.versionRead.addressExact, reads.versionRead.valueExact]
  have scalarStage :
      runSteps program 21 (.running 12 registersVersion memory) =
        .running 33 registersScalars memory := by
    simp [program, runSteps, step, executeInstruction, continueAt,
      registersFlags, registersTerm, registersChild,
      registersProof, registersArgument, registersPremise, registersScalars,
      RegisterFile.writeAddress,
      RegisterFile.writeWord16, RegisterFile.writeWord32, shape, baseAddress,
      fieldOffset, fieldAddress, flags, termCount, childCount, proofCount,
      argumentCount, premiseCount, goalTerm,
      registersVersionBase0,
      reads.flagsRead.addressExact, reads.flagsRead.valueExact,
      reads.termCountRead.addressExact, reads.termCountRead.valueExact,
      reads.childCountRead.addressExact, reads.childCountRead.valueExact,
      reads.proofCountRead.addressExact, reads.proofCountRead.valueExact,
      reads.argumentCountRead.addressExact, reads.argumentCountRead.valueExact,
      reads.premiseCountRead.addressExact, reads.premiseCountRead.valueExact,
      reads.goalTermRead.addressExact, reads.goalTermRead.valueExact]
  have profileStage :
      runSteps program 12 (.running 33 registersScalars memory) =
        .running 45 registersProfile memory := by
    simp [program, runSteps, step, executeInstruction, continueAt,
      registersProfile0, registersProfile1,
      registersProfile2, registersProfile, RegisterFile.writeAddress,
      RegisterFile.writeWord64, shape, baseAddress, fieldOffset, fieldAddress,
      profileChunk0, profileChunk1, profileChunk2, profileChunk3,
      registersScalarsBase0,
      reads.profile0Read.addressExact, reads.profile0Read.valueExact,
      reads.profile1Read.addressExact, reads.profile1Read.valueExact,
      reads.profile2Read.addressExact, reads.profile2Read.valueExact,
      reads.profile3Read.addressExact, reads.profile3Read.valueExact]
  have sourceStage :
      runSteps program 12 (.running 45 registersProfile memory) =
        .running 57 registersSource memory := by
    simp [program, runSteps, step, executeInstruction, continueAt,
      registersSource0, registersSource1,
      registersSource2, registersSource, RegisterFile.writeAddress,
      RegisterFile.writeWord64, shape, baseAddress, fieldOffset, fieldAddress,
      sourceChunk0, sourceChunk1, sourceChunk2, sourceChunk3,
      registersProfileBase0,
      reads.source0Read.addressExact, reads.source0Read.valueExact,
      reads.source1Read.addressExact, reads.source1Read.valueExact,
      reads.source2Read.addressExact, reads.source2Read.valueExact,
      reads.source3Read.addressExact, reads.source3Read.valueExact]
  have checksumStage :
      runSteps program 3 (.running 57 registersSource memory) =
        .running 60 registersChecksum memory := by
    simp [program, runSteps, step, executeInstruction, continueAt,
      registersChecksum, RegisterFile.writeAddress,
      RegisterFile.writeWord64, shape, baseAddress, fieldOffset, fieldAddress,
      bodyChecksum, registersSourceBase0, reads.checksumRead.addressExact,
      reads.checksumRead.valueExact]
  have haltStage :
      runSteps program 1 (.running 60 registersChecksum memory) =
        .halted true registersChecksum memory := by
    simp [program, runSteps, step, executeInstruction]
  unfold execute
  rw [show 61 = 6 + 55 by decide, runSteps_add, magicStage]
  rw [show 55 = 6 + 49 by decide, runSteps_add, versionStage]
  rw [show 49 = 21 + 28 by decide, runSteps_add, scalarStage]
  rw [show 28 = 12 + 16 by decide, runSteps_add, profileStage]
  rw [show 16 = 12 + 4 by decide, runSteps_add, sourceStage]
  rw [show 4 = 3 + 1 by decide, runSteps_add, checksumStage, haltStage]
  simp [observeHeader, headerOfRegisters, registersChecksum,
    registersSource, registersSource2, registersSource1, registersSource0,
    registersProfile, registersProfile2, registersProfile1, registersProfile0,
    registersScalars, registersPremise, registersArgument, registersProof,
    registersChild, registersTerm, registersFlags, registersVersion,
    registersMagic, registers0, RegisterFile.writeAddress,
    RegisterFile.writeWord16, RegisterFile.writeWord32,
    RegisterFile.writeWord64, RegisterFile.writeFlag, shape, baseAddress,
    fieldOffset, fieldAddress, flags, termCount, childCount, proofCount,
    argumentCount, premiseCount, goalTerm, profileChunk0, profileChunk1,
    profileChunk2, profileChunk3, sourceChunk0, sourceChunk1, sourceChunk2,
    sourceChunk3, bodyChecksum, magicActual, magicExpected, versionActual,
    versionExpected, equal]
  cases header
  simp
  exact ⟨reads.profileDigestExact.symm, reads.sourceDigestExact.symm⟩

theorem execute_refines_detailed_of_reads
    {memory : ByteMemory} {header : Header}
    (reads : HeaderReads memory header) :
    observeHeader (execute memory) = some (readHeaderDetailed memory) := by
  rw [readHeaderDetailed_of_reads reads]
  exact execute_accepts_of_reads reads

/-! ## Concrete positive and negative canaries -/

namespace Canary

def canonicalBytes : List UInt8 := encodeCertificate canaryCertificate

def canonicalHeader : Header :=
  headerOf canaryCertificate (fnv1a64 (encodeBody canaryCertificate))

def memory : ByteMemory := ByteMemory.ofList 1000 canonicalBytes

def canonicalFlatReads :
    M0GCFlatHeaderLoaderCorrespondence.FlatHeaderReads
      canonicalBytes canonicalHeader :=
  (M0GCFlatHeaderLoaderCorrespondence.readHeaderFlat?_eq_some_iff
    canonicalBytes canonicalHeader).mp (by
      simpa [canonicalBytes, canonicalHeader,
        M0GCFlatHeaderLoaderCorrespondence.canaryHeader] using
        M0GCFlatHeaderLoaderCorrespondence.canary_flat_header_accepts)

theorem canonicalBytes_has_header : 104 ≤ canonicalBytes.length := by
  have profileWidth : canonicalHeader.profileDigest.length = digestWidth := by
    simp [canonicalHeader, headerOf, canaryCertificate, digestWidth]
  have sourceWidth : canonicalHeader.sourceDigest.length = digestWidth := by
    simp [canonicalHeader, headerOf, canaryCertificate, digestWidth]
  have headerLength :=
    encodeHeader_length canonicalHeader profileWidth sourceWidth
  change 104 ≤ (encodeHeader canonicalHeader ++ encodeBody canaryCertificate).length
  simp [headerLength]

/-- Resolve one concrete canary field without evaluating the backing array.
The only byte-list fact used is that the canonical certificate contains its
complete 104-byte header. -/
theorem canonicalRange
    (address width addressEnd : UInt64) (offset : Nat)
    (addition :
      Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory.checkedAdd
        address width = some addressEnd)
    (addressNat : address.toNat = 1000 + offset)
    (endBound : addressEnd.toNat ≤ 1104) :
    memory.rangeOffset? address width = some offset := by
  have inside : (1000 : UInt64).toNat ≤ address.toNat ∧
      addressEnd.toNat ≤ (1000 : UInt64).toNat + canonicalBytes.length := by
    constructor <;> simp only [UInt64.toNat_ofNat]
    · omega
    · have lengthBound := canonicalBytes_has_header
      omega
  have resolved := ByteMemory.rangeOffset?_ofList_eq_some
    (base := (1000 : UInt64)) (bytes := canonicalBytes)
    addition inside
  simpa [memory, addressNat] using resolved

theorem range0 : memory.rangeOffset? 1000 4 = some 0 :=
  canonicalRange 1000 4 1004 0 (by decide) (by decide) (by decide)
theorem range4 : memory.rangeOffset? 1004 2 = some 4 :=
  canonicalRange 1004 2 1006 4 (by decide) (by decide) (by decide)
theorem range6 : memory.rangeOffset? 1006 2 = some 6 :=
  canonicalRange 1006 2 1008 6 (by decide) (by decide) (by decide)
theorem range8 : memory.rangeOffset? 1008 4 = some 8 :=
  canonicalRange 1008 4 1012 8 (by decide) (by decide) (by decide)
theorem range12 : memory.rangeOffset? 1012 4 = some 12 :=
  canonicalRange 1012 4 1016 12 (by decide) (by decide) (by decide)
theorem range16 : memory.rangeOffset? 1016 4 = some 16 :=
  canonicalRange 1016 4 1020 16 (by decide) (by decide) (by decide)
theorem range20 : memory.rangeOffset? 1020 4 = some 20 :=
  canonicalRange 1020 4 1024 20 (by decide) (by decide) (by decide)
theorem range24 : memory.rangeOffset? 1024 4 = some 24 :=
  canonicalRange 1024 4 1028 24 (by decide) (by decide) (by decide)
theorem range28 : memory.rangeOffset? 1028 4 = some 28 :=
  canonicalRange 1028 4 1032 28 (by decide) (by decide) (by decide)
theorem range32 : memory.rangeOffset? 1032 8 = some 32 :=
  canonicalRange 1032 8 1040 32 (by decide) (by decide) (by decide)
theorem range40 : memory.rangeOffset? 1040 8 = some 40 :=
  canonicalRange 1040 8 1048 40 (by decide) (by decide) (by decide)
theorem range48 : memory.rangeOffset? 1048 8 = some 48 :=
  canonicalRange 1048 8 1056 48 (by decide) (by decide) (by decide)
theorem range56 : memory.rangeOffset? 1056 8 = some 56 :=
  canonicalRange 1056 8 1064 56 (by decide) (by decide) (by decide)
theorem range64 : memory.rangeOffset? 1064 8 = some 64 :=
  canonicalRange 1064 8 1072 64 (by decide) (by decide) (by decide)
theorem range72 : memory.rangeOffset? 1072 8 = some 72 :=
  canonicalRange 1072 8 1080 72 (by decide) (by decide) (by decide)
theorem range80 : memory.rangeOffset? 1080 8 = some 80 :=
  canonicalRange 1080 8 1088 80 (by decide) (by decide) (by decide)
theorem range88 : memory.rangeOffset? 1088 8 = some 88 :=
  canonicalRange 1088 8 1096 88 (by decide) (by decide) (by decide)
theorem range96 : memory.rangeOffset? 1096 8 = some 96 :=
  canonicalRange 1096 8 1104 96 (by decide) (by decide) (by decide)

theorem magicFlat :
    M0GCFlatHeaderLoaderCorrespondence.readAt?
      Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat.readUInt32LE
      canonicalBytes 0 = some magicWord := by
  simp [canonicalBytes, encodeCertificate, encodeHeader, magicWord,
    M0GCFlatHeaderLoaderCorrespondence.readAt?, magic,
    Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat.readUInt32LE]

theorem profile0Flat :
    M0GCFlatHeaderLoaderCorrespondence.readAt? readUInt64LE
      canonicalBytes 32 = some 0 := by
  simp [canonicalBytes, encodeCertificate, encodeHeader, headerOf,
    canaryCertificate, digestWidth,
    magic, encodeUInt16LE, encodeUInt64LE,
    Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat.encodeUInt32LE,
    M0GCFlatHeaderLoaderCorrespondence.readAt?, readUInt64LE]

theorem profile1Flat :
    M0GCFlatHeaderLoaderCorrespondence.readAt? readUInt64LE
      canonicalBytes 40 = some 0 := by
  simp [canonicalBytes, encodeCertificate, encodeHeader, headerOf,
    canaryCertificate, digestWidth,
    magic, encodeUInt16LE, encodeUInt64LE,
    Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat.encodeUInt32LE,
    M0GCFlatHeaderLoaderCorrespondence.readAt?, readUInt64LE]

theorem profile2Flat :
    M0GCFlatHeaderLoaderCorrespondence.readAt? readUInt64LE
      canonicalBytes 48 = some 0 := by
  simp [canonicalBytes, encodeCertificate, encodeHeader, headerOf,
    canaryCertificate, digestWidth,
    magic, encodeUInt16LE, encodeUInt64LE,
    Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat.encodeUInt32LE,
    M0GCFlatHeaderLoaderCorrespondence.readAt?, readUInt64LE]

theorem profile3Flat :
    M0GCFlatHeaderLoaderCorrespondence.readAt? readUInt64LE
      canonicalBytes 56 = some 0 := by
  simp [canonicalBytes, encodeCertificate, encodeHeader, headerOf,
    canaryCertificate, digestWidth,
    magic, encodeUInt16LE, encodeUInt64LE,
    Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat.encodeUInt32LE,
    M0GCFlatHeaderLoaderCorrespondence.readAt?, readUInt64LE]

theorem source0Flat :
    M0GCFlatHeaderLoaderCorrespondence.readAt? readUInt64LE
      canonicalBytes 64 = some 0 := by
  simp [canonicalBytes, encodeCertificate, encodeHeader, headerOf,
    canaryCertificate, digestWidth,
    magic, encodeUInt16LE, encodeUInt64LE,
    Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat.encodeUInt32LE,
    M0GCFlatHeaderLoaderCorrespondence.readAt?, readUInt64LE]

theorem source1Flat :
    M0GCFlatHeaderLoaderCorrespondence.readAt? readUInt64LE
      canonicalBytes 72 = some 0 := by
  simp [canonicalBytes, encodeCertificate, encodeHeader, headerOf,
    canaryCertificate, digestWidth,
    magic, encodeUInt16LE, encodeUInt64LE,
    Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat.encodeUInt32LE,
    M0GCFlatHeaderLoaderCorrespondence.readAt?, readUInt64LE]

theorem source2Flat :
    M0GCFlatHeaderLoaderCorrespondence.readAt? readUInt64LE
      canonicalBytes 80 = some 0 := by
  simp [canonicalBytes, encodeCertificate, encodeHeader, headerOf,
    canaryCertificate, digestWidth,
    magic, encodeUInt16LE, encodeUInt64LE,
    Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat.encodeUInt32LE,
    M0GCFlatHeaderLoaderCorrespondence.readAt?, readUInt64LE]

theorem source3Flat :
    M0GCFlatHeaderLoaderCorrespondence.readAt? readUInt64LE
      canonicalBytes 88 = some 0 := by
  simp [canonicalBytes, encodeCertificate, encodeHeader, headerOf,
    canaryCertificate, digestWidth,
    magic, encodeUInt16LE, encodeUInt64LE,
    Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat.encodeUInt32LE,
    M0GCFlatHeaderLoaderCorrespondence.readAt?, readUInt64LE]

theorem load16_eq_flat (address : UInt64) (offset : Nat)
    (range : memory.rangeOffset? address 2 = some offset) :
    memory.loadUInt16LE? address =
      M0GCFlatHeaderLoaderCorrespondence.readAt? readUInt16LE
        canonicalBytes offset := by
  have compiledRange :
      (ByteMemory.ofList 1000 canonicalBytes).rangeOffset? address 2 =
        some offset := by
    simpa [memory] using range
  simpa [memory] using ByteMemory.loadUInt16LE?_ofList_of_range
    1000 address canonicalBytes offset compiledRange

theorem load32_eq_flat (address : UInt64) (offset : Nat)
    (range : memory.rangeOffset? address 4 = some offset) :
    memory.loadUInt32LE? address =
      M0GCFlatHeaderLoaderCorrespondence.readAt?
        Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat.readUInt32LE
        canonicalBytes offset := by
  have compiledRange :
      (ByteMemory.ofList 1000 canonicalBytes).rangeOffset? address 4 =
        some offset := by
    simpa [memory] using range
  simpa [memory] using ByteMemory.loadUInt32LE?_ofList_of_range
    1000 address canonicalBytes offset compiledRange

theorem load64_eq_flat (address : UInt64) (offset : Nat)
    (range : memory.rangeOffset? address 8 = some offset) :
    memory.loadUInt64LE? address =
      M0GCFlatHeaderLoaderCorrespondence.readAt? readUInt64LE
        canonicalBytes offset := by
  have compiledRange :
      (ByteMemory.ofList 1000 canonicalBytes).rangeOffset? address 8 =
        some offset := by
    simpa [memory] using range
  simpa [memory] using ByteMemory.loadUInt64LE?_ofList_of_range
    1000 address canonicalBytes offset compiledRange

/-- Concrete physical witnesses are intentionally separate from the machine
run.  The canary checks each field once, then exercises the generic lowering
theorem instead of asking the reducer to rediscover a 61-step proof. -/
def canonicalReads : HeaderReads memory canonicalHeader where
  magicRead :=
    { address := 1000
      addressExact := by decide
      valueExact := (load32_eq_flat 1000 0 range0).trans magicFlat }
  versionRead :=
    { address := 1004
      addressExact := by decide
      valueExact := (load16_eq_flat 1004 4 range4).trans
        canonicalFlatReads.versionRead }
  flagsRead :=
    { address := 1006
      addressExact := by decide
      valueExact := (load16_eq_flat 1006 6 range6).trans
        canonicalFlatReads.flagsRead }
  termCountRead :=
    { address := 1008
      addressExact := by decide
      valueExact := (load32_eq_flat 1008 8 range8).trans
        canonicalFlatReads.termCountRead }
  childCountRead :=
    { address := 1012
      addressExact := by decide
      valueExact := (load32_eq_flat 1012 12 range12).trans
        canonicalFlatReads.childCountRead }
  proofCountRead :=
    { address := 1016
      addressExact := by decide
      valueExact := (load32_eq_flat 1016 16 range16).trans
        canonicalFlatReads.proofCountRead }
  argumentCountRead :=
    { address := 1020
      addressExact := by decide
      valueExact := (load32_eq_flat 1020 20 range20).trans
        canonicalFlatReads.argumentCountRead }
  premiseCountRead :=
    { address := 1024
      addressExact := by decide
      valueExact := (load32_eq_flat 1024 24 range24).trans
        canonicalFlatReads.premiseCountRead }
  goalTermRead :=
    { address := 1028
      addressExact := by decide
      valueExact := (load32_eq_flat 1028 28 range28).trans
        canonicalFlatReads.goalTermRead }
  profile0 := 0
  profile1 := 0
  profile2 := 0
  profile3 := 0
  source0 := 0
  source1 := 0
  source2 := 0
  source3 := 0
  profile0Read :=
    { address := 1032
      addressExact := by decide
      valueExact := (load64_eq_flat 1032 32 range32).trans profile0Flat }
  profile1Read :=
    { address := 1040
      addressExact := by decide
      valueExact := (load64_eq_flat 1040 40 range40).trans profile1Flat }
  profile2Read :=
    { address := 1048
      addressExact := by decide
      valueExact := (load64_eq_flat 1048 48 range48).trans profile2Flat }
  profile3Read :=
    { address := 1056
      addressExact := by decide
      valueExact := (load64_eq_flat 1056 56 range56).trans profile3Flat }
  source0Read :=
    { address := 1064
      addressExact := by decide
      valueExact := (load64_eq_flat 1064 64 range64).trans source0Flat }
  source1Read :=
    { address := 1072
      addressExact := by decide
      valueExact := (load64_eq_flat 1072 72 range72).trans source1Flat }
  source2Read :=
    { address := 1080
      addressExact := by decide
      valueExact := (load64_eq_flat 1080 80 range80).trans source2Flat }
  source3Read :=
    { address := 1088
      addressExact := by decide
      valueExact := (load64_eq_flat 1088 88 range88).trans source3Flat }
  checksumRead :=
    { address := 1096
      addressExact := by decide
      valueExact := (load64_eq_flat 1096 96 range96).trans
        canonicalFlatReads.bodyChecksumRead }
  profileDigestExact := by decide
  sourceDigestExact := by decide

theorem canonical_accepts :
    observeHeader (execute memory) =
      some (.ok (some
        (headerOf canaryCertificate (fnv1a64 (encodeBody canaryCertificate))))) := by
  exact execute_accepts_of_reads canonicalReads

/-- The shortest allocation containing a complete but invalid magic field.
The absent tail makes this a precedence canary: logical rejection must occur
before the machine can fault on a later missing field. -/
def corruptMagicMemory : ByteMemory :=
  ByteMemory.ofList 1000 [0, 48, 71, 67]

def corruptMagicRead : Word32Read corruptMagicMemory 0 0x43473000 where
  address := 1000
  addressExact := by decide
  valueExact := by decide

theorem corrupt_magic_logically_rejected :
    observeHeader (execute corruptMagicMemory) = some (.ok none) := by
  exact execute_rejects_wrong_magic corruptMagicRead (by decide)

/-- A complete valid magic followed by a complete unsupported version, with
no irrelevant header tail. -/
def wrongVersionMemory : ByteMemory :=
  ByteMemory.ofList 1000 (magic ++ encodeUInt16LE 2)

def wrongVersionMagicRead : Word32Read wrongVersionMemory 0 magicWord where
  address := 1000
  addressExact := by decide
  valueExact := by decide

def wrongVersionRead : Word16Read wrongVersionMemory 4 2 where
  address := 1004
  addressExact := by decide
  valueExact := by decide

theorem wrong_version_logically_rejected :
    observeHeader (execute wrongVersionMemory) = some (.ok none) := by
  exact execute_rejects_wrong_version wrongVersionMagicRead wrongVersionRead
    (by decide)

def truncatedBytes : List UInt8 := canonicalBytes.take 100

theorem truncatedBytes_length : truncatedBytes.length = 100 := by
  have enough : 100 ≤ canonicalBytes.length := by
    have := canonicalBytes_has_header
    omega
  simp [truncatedBytes, List.length_take, Nat.min_eq_left enough]

def truncatedMemory : ByteMemory :=
  ByteMemory.ofList 1000 truncatedBytes

/-- Resolve any canary field wholly contained in the first 100 bytes. -/
theorem truncatedRange
    (address width addressEnd : UInt64) (offset : Nat)
    (addition :
      Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory.checkedAdd
        address width = some addressEnd)
    (addressNat : address.toNat = 1000 + offset)
    (endBound : addressEnd.toNat ≤ 1100) :
    truncatedMemory.rangeOffset? address width = some offset := by
  have inside : (1000 : UInt64).toNat ≤ address.toNat ∧
      addressEnd.toNat ≤ (1000 : UInt64).toNat + truncatedBytes.length := by
    constructor <;> simp only [UInt64.toNat_ofNat]
    · omega
    · rw [truncatedBytes_length]
      omega
  have resolved := ByteMemory.rangeOffset?_ofList_eq_some
    (base := (1000 : UInt64)) (bytes := truncatedBytes)
    addition inside
  simpa [truncatedMemory, addressNat] using resolved

theorem truncatedRange0 :
    truncatedMemory.rangeOffset? 1000 4 = some 0 :=
  truncatedRange 1000 4 1004 0 (by decide) (by decide) (by decide)
theorem truncatedRange4 :
    truncatedMemory.rangeOffset? 1004 2 = some 4 :=
  truncatedRange 1004 2 1006 4 (by decide) (by decide) (by decide)
theorem truncatedRange6 :
    truncatedMemory.rangeOffset? 1006 2 = some 6 :=
  truncatedRange 1006 2 1008 6 (by decide) (by decide) (by decide)
theorem truncatedRange8 :
    truncatedMemory.rangeOffset? 1008 4 = some 8 :=
  truncatedRange 1008 4 1012 8 (by decide) (by decide) (by decide)
theorem truncatedRange12 :
    truncatedMemory.rangeOffset? 1012 4 = some 12 :=
  truncatedRange 1012 4 1016 12 (by decide) (by decide) (by decide)
theorem truncatedRange16 :
    truncatedMemory.rangeOffset? 1016 4 = some 16 :=
  truncatedRange 1016 4 1020 16 (by decide) (by decide) (by decide)
theorem truncatedRange20 :
    truncatedMemory.rangeOffset? 1020 4 = some 20 :=
  truncatedRange 1020 4 1024 20 (by decide) (by decide) (by decide)
theorem truncatedRange24 :
    truncatedMemory.rangeOffset? 1024 4 = some 24 :=
  truncatedRange 1024 4 1028 24 (by decide) (by decide) (by decide)
theorem truncatedRange28 :
    truncatedMemory.rangeOffset? 1028 4 = some 28 :=
  truncatedRange 1028 4 1032 28 (by decide) (by decide) (by decide)
theorem truncatedRange32 :
    truncatedMemory.rangeOffset? 1032 8 = some 32 :=
  truncatedRange 1032 8 1040 32 (by decide) (by decide) (by decide)
theorem truncatedRange40 :
    truncatedMemory.rangeOffset? 1040 8 = some 40 :=
  truncatedRange 1040 8 1048 40 (by decide) (by decide) (by decide)
theorem truncatedRange48 :
    truncatedMemory.rangeOffset? 1048 8 = some 48 :=
  truncatedRange 1048 8 1056 48 (by decide) (by decide) (by decide)
theorem truncatedRange56 :
    truncatedMemory.rangeOffset? 1056 8 = some 56 :=
  truncatedRange 1056 8 1064 56 (by decide) (by decide) (by decide)
theorem truncatedRange64 :
    truncatedMemory.rangeOffset? 1064 8 = some 64 :=
  truncatedRange 1064 8 1072 64 (by decide) (by decide) (by decide)
theorem truncatedRange72 :
    truncatedMemory.rangeOffset? 1072 8 = some 72 :=
  truncatedRange 1072 8 1080 72 (by decide) (by decide) (by decide)
theorem truncatedRange80 :
    truncatedMemory.rangeOffset? 1080 8 = some 80 :=
  truncatedRange 1080 8 1088 80 (by decide) (by decide) (by decide)
theorem truncatedRange88 :
    truncatedMemory.rangeOffset? 1088 8 = some 88 :=
  truncatedRange 1088 8 1096 88 (by decide) (by decide) (by decide)

/-- Complete fields below the truncation boundary read identically from the
partial and complete canary allocations. -/
theorem truncatedLoad16_eq (address : UInt64) (offset : Nat)
    (shortRange : truncatedMemory.rangeOffset? address 2 = some offset)
    (fullRange : memory.rangeOffset? address 2 = some offset)
    (covered : offset + 2 ≤ 100) :
    truncatedMemory.loadUInt16LE? address = memory.loadUInt16LE? address := by
  unfold ByteMemory.loadUInt16LE?
  rw [shortRange, fullRange]
  simpa [truncatedMemory, truncatedBytes, memory,
    ByteMemory.toNeutralRegion_ofList,
    Mettapedia.GSLT.LanguageDef.M0GCBoundedByteMemory.ByteRegion.loadUInt16LE?]
    using
      Mettapedia.GSLT.LanguageDef.M0GCBoundedByteMemory.ByteRegion.readField?_ofList_take_eq
        readUInt16LE 2 canonicalBytes 100 offset covered (by
          have := canonicalBytes_has_header
          omega)

theorem truncatedLoad32_eq (address : UInt64) (offset : Nat)
    (shortRange : truncatedMemory.rangeOffset? address 4 = some offset)
    (fullRange : memory.rangeOffset? address 4 = some offset)
    (covered : offset + 4 ≤ 100) :
    truncatedMemory.loadUInt32LE? address = memory.loadUInt32LE? address := by
  unfold ByteMemory.loadUInt32LE?
  rw [shortRange, fullRange]
  simpa [truncatedMemory, truncatedBytes, memory,
    ByteMemory.toNeutralRegion_ofList,
    Mettapedia.GSLT.LanguageDef.M0GCBoundedByteMemory.ByteRegion.loadUInt32LE?]
    using
      Mettapedia.GSLT.LanguageDef.M0GCBoundedByteMemory.ByteRegion.readField?_ofList_take_eq
        Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat.readUInt32LE
        4 canonicalBytes 100 offset covered (by
          have := canonicalBytes_has_header
          omega)

theorem truncatedLoad64_eq (address : UInt64) (offset : Nat)
    (shortRange : truncatedMemory.rangeOffset? address 8 = some offset)
    (fullRange : memory.rangeOffset? address 8 = some offset)
    (covered : offset + 8 ≤ 100) :
    truncatedMemory.loadUInt64LE? address = memory.loadUInt64LE? address := by
  unfold ByteMemory.loadUInt64LE?
  rw [shortRange, fullRange]
  simpa [truncatedMemory, truncatedBytes, memory,
    ByteMemory.toNeutralRegion_ofList,
    Mettapedia.GSLT.LanguageDef.M0GCBoundedByteMemory.ByteRegion.loadUInt64LE?]
    using
      Mettapedia.GSLT.LanguageDef.M0GCBoundedByteMemory.ByteRegion.readField?_ofList_take_eq
        readUInt64LE 8 canonicalBytes 100 offset covered (by
          have := canonicalBytes_has_header
          omega)

/-- The partial allocation carries exactly the complete physical evidence
needed for the 57-instruction prefix.  Each value proof factors through the
generic truncation-locality theorem rather than re-running the decoder. -/
def truncatedPrefixReads : HeaderPrefixReads truncatedMemory canonicalHeader where
  magicRead :=
    { address := 1000
      addressExact := by decide
      valueExact := (truncatedLoad32_eq 1000 0 truncatedRange0 range0
        (by decide)).trans canonicalReads.magicRead.valueExact }
  versionRead :=
    { address := 1004
      addressExact := by decide
      valueExact := (truncatedLoad16_eq 1004 4 truncatedRange4 range4
        (by decide)).trans canonicalReads.versionRead.valueExact }
  flagsRead :=
    { address := 1006
      addressExact := by decide
      valueExact := (truncatedLoad16_eq 1006 6 truncatedRange6 range6
        (by decide)).trans canonicalReads.flagsRead.valueExact }
  termCountRead :=
    { address := 1008
      addressExact := by decide
      valueExact := (truncatedLoad32_eq 1008 8 truncatedRange8 range8
        (by decide)).trans canonicalReads.termCountRead.valueExact }
  childCountRead :=
    { address := 1012
      addressExact := by decide
      valueExact := (truncatedLoad32_eq 1012 12 truncatedRange12 range12
        (by decide)).trans canonicalReads.childCountRead.valueExact }
  proofCountRead :=
    { address := 1016
      addressExact := by decide
      valueExact := (truncatedLoad32_eq 1016 16 truncatedRange16 range16
        (by decide)).trans canonicalReads.proofCountRead.valueExact }
  argumentCountRead :=
    { address := 1020
      addressExact := by decide
      valueExact := (truncatedLoad32_eq 1020 20 truncatedRange20 range20
        (by decide)).trans canonicalReads.argumentCountRead.valueExact }
  premiseCountRead :=
    { address := 1024
      addressExact := by decide
      valueExact := (truncatedLoad32_eq 1024 24 truncatedRange24 range24
        (by decide)).trans canonicalReads.premiseCountRead.valueExact }
  goalTermRead :=
    { address := 1028
      addressExact := by decide
      valueExact := (truncatedLoad32_eq 1028 28 truncatedRange28 range28
        (by decide)).trans canonicalReads.goalTermRead.valueExact }
  profile0 := 0
  profile1 := 0
  profile2 := 0
  profile3 := 0
  source0 := 0
  source1 := 0
  source2 := 0
  source3 := 0
  profile0Read :=
    { address := 1032
      addressExact := by decide
      valueExact := (truncatedLoad64_eq 1032 32 truncatedRange32 range32
        (by decide)).trans canonicalReads.profile0Read.valueExact }
  profile1Read :=
    { address := 1040
      addressExact := by decide
      valueExact := (truncatedLoad64_eq 1040 40 truncatedRange40 range40
        (by decide)).trans canonicalReads.profile1Read.valueExact }
  profile2Read :=
    { address := 1048
      addressExact := by decide
      valueExact := (truncatedLoad64_eq 1048 48 truncatedRange48 range48
        (by decide)).trans canonicalReads.profile2Read.valueExact }
  profile3Read :=
    { address := 1056
      addressExact := by decide
      valueExact := (truncatedLoad64_eq 1056 56 truncatedRange56 range56
        (by decide)).trans canonicalReads.profile3Read.valueExact }
  source0Read :=
    { address := 1064
      addressExact := by decide
      valueExact := (truncatedLoad64_eq 1064 64 truncatedRange64 range64
        (by decide)).trans canonicalReads.source0Read.valueExact }
  source1Read :=
    { address := 1072
      addressExact := by decide
      valueExact := (truncatedLoad64_eq 1072 72 truncatedRange72 range72
        (by decide)).trans canonicalReads.source1Read.valueExact }
  source2Read :=
    { address := 1080
      addressExact := by decide
      valueExact := (truncatedLoad64_eq 1080 80 truncatedRange80 range80
        (by decide)).trans canonicalReads.source2Read.valueExact }
  source3Read :=
    { address := 1088
      addressExact := by decide
      valueExact := (truncatedLoad64_eq 1088 88 truncatedRange88 range88
        (by decide)).trans canonicalReads.source3Read.valueExact }
  profileDigestExact := canonicalReads.profileDigestExact
  sourceDigestExact := canonicalReads.sourceDigestExact

theorem truncatedChecksumRange_none :
    truncatedMemory.rangeOffset? 1096 8 = none := by
  unfold ByteMemory.rangeOffset?
  rw [show
    Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory.checkedAdd 1096 8 =
      some 1104 by decide]
  simp [truncatedMemory, ByteMemory.ofList, truncatedBytes_length]

theorem truncatedChecksumLoad_none :
    truncatedMemory.loadUInt64LE? 1096 = none := by
  simp [ByteMemory.loadUInt64LE?, truncatedChecksumRange_none]

theorem truncated_header_faults :
    observeHeader (execute truncatedMemory) =
      some (.error .word64ReadOutOfBounds) := by
  have prefixRun := runPrefix_of_reads truncatedPrefixReads
  let registersOffset :=
    (prefixRegisters truncatedPrefixReads).writeAddress fieldOffset 96
  let registersAddress :=
    registersOffset.writeAddress fieldAddress 1096
  have prefixBase0 :
      (prefixRegisters truncatedPrefixReads).addresses (0 : Fin 3) = 1000 := by
    rw [show (0 : Fin 3) = baseAddress by rfl, prefixRegisters_base]
    rfl
  have checksumAddress :
      Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory.checkedAdd 1000 96 =
        some 1096 := by
    decide
  have setupStage :
      runSteps program 2
          (.running 57 (prefixRegisters truncatedPrefixReads) truncatedMemory) =
        .running 59 registersAddress truncatedMemory := by
    simp [program, runSteps, step, executeInstruction, continueAt,
      registersOffset, registersAddress, RegisterFile.writeAddress, shape,
      baseAddress, fieldOffset, fieldAddress, prefixBase0, checksumAddress]
  have loadStage :
      runSteps program 1 (.running 59 registersAddress truncatedMemory) =
        .faulted .word64ReadOutOfBounds registersAddress truncatedMemory := by
    simp [program, runSteps, step, executeInstruction, registersAddress,
      registersOffset, RegisterFile.writeAddress, shape, fieldAddress,
      truncatedChecksumLoad_none]
  have tailStage :
      runSteps program 4
          (.running 57 (prefixRegisters truncatedPrefixReads) truncatedMemory) =
        .faulted .word64ReadOutOfBounds registersAddress truncatedMemory := by
    rw [show 4 = 2 + 2 by decide, runSteps_add, setupStage]
    rw [show 2 = 1 + 1 by decide, runSteps_add, loadStage]
    rfl
  unfold execute
  rw [show 61 = 57 + 4 by decide, runSteps_add, prefixRun]
  rw [tailStage]
  rfl

end Canary

#print axioms execute_refines_detailed_of_reads
#print axioms Canary.canonical_accepts
#print axioms Canary.corrupt_magic_logically_rejected
#print axioms Canary.truncated_header_faults

end Mettapedia.GSLT.LanguageDef.M0GCHeaderByteMachineRealization
