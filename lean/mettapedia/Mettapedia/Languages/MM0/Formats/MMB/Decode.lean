import Mettapedia.Languages.MM0.Formats.MMB.Machine

/-!
# Decoding MMB files

The byte layout of an MMB file, decoded into the tables and statements of the
proof machine. Numbers are little endian. A command is one byte whose low six
bits are the opcode and whose high two bits give the number of data bytes: none,
one, two or four. Every read is bounds checked; a malformed file decodes to
nothing.

An argument descriptor is a 64-bit word: bits 0–54 are the dependencies on
bound variables, bit 55 is reserved, bits 56–62 are the sort and bit 63 marks a
bound variable.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Formats.MMB.Decode

open Mettapedia.Languages.MM0.Kernel (SortInfo)

variable (bytes : ByteArray)

def u8 (at_ : Nat) : Option Nat := (bytes[at_]?).map (·.toNat)

def le : Nat → Nat → Option Nat
  | _, 0 => some 0
  | at_, count + 1 => do
      let low ← u8 bytes at_
      let high ← le (at_ + 1) count
      pure (low + 256 * high)

def u16 (at_ : Nat) : Option Nat := le bytes at_ 2
def u32 (at_ : Nat) : Option Nat := le bytes at_ 4
def u64 (at_ : Nat) : Option Nat := le bytes at_ 8

/-- A command: opcode, data and encoded size. -/
def command (at_ : Nat) : Option (Nat × Nat × Nat) := do
  let byte ← u8 bytes at_
  let opcode := byte % 64
  match byte / 64 with
  | 0 => pure (opcode, 0, 1)
  | 1 => pure (opcode, ← u8 bytes (at_ + 1), 2)
  | 2 => pure (opcode, ← u16 bytes (at_ + 1), 3)
  | _ => pure (opcode, ← u32 bytes (at_ + 1), 5)

def sortInfo (byte : Nat) : SortInfo :=
  { pure := byte % 2 == 1, strict := (byte / 2) % 2 == 1,
    provable := (byte / 4) % 2 == 1, free := (byte / 8) % 2 == 1 }

def argType (word : Nat) : ExprType :=
  { sort := (word / 2 ^ 56) % 128
    bound := word / 2 ^ 63 % 2 == 1
    deps := ((List.range 55).filter fun bit => (word / 2 ^ bit) % 2 == 1).toFinset }

def argAt (at_ : Nat) : Option ExprType := do
  let word ← u64 bytes at_
  if word / 2 ^ 55 % 2 ≠ 0 then none else pure (argType word)

def argTypes (at_ count : Nat) : Option (List ExprType) :=
  (List.range count).mapM fun index => argAt bytes (at_ + 8 * index)

/-- A unify stream, up to its `END`. The fuel bounds the number of commands. -/
def unifyStream : Nat → Nat → Option (List UnifyCmd)
  | 0, _ => none
  | fuel + 1, at_ => do
      let (opcode, data, size) ← command bytes at_
      match opcode with
      | 0x00 => if data = 0 then pure [] else none
      | 0x30 => pure (.term data :: (← unifyStream fuel (at_ + size)))
      | 0x31 => pure (.termSave data :: (← unifyStream fuel (at_ + size)))
      | 0x32 => pure (.ref data :: (← unifyStream fuel (at_ + size)))
      | 0x33 => pure (.dummy data :: (← unifyStream fuel (at_ + size)))
      | 0x36 => if data = 0 then
          pure (.hyp :: (← unifyStream fuel (at_ + size))) else none
      | _ => none

def proofCmd (opcode data : Nat) : Option ProofCmd :=
  if opcode ∈ [0x16, 0x17, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1E, 0x1F] ∧ data ≠ 0 then
    none else
  match opcode with
  | 0x10 => some (.term data)
  | 0x11 => some (.termSave data)
  | 0x12 => some (.ref data)
  | 0x13 => some (.dummy data)
  | 0x14 => some (.thm data)
  | 0x15 => some (.thmSave data)
  | 0x16 => some .hyp
  | 0x17 => some .conv
  | 0x18 => some .refl
  | 0x19 => some .symm
  | 0x1A => some .cong
  | 0x1B => some .unfold
  | 0x1C => some .convCut
  | 0x1E => some .convSave
  | 0x1F => some .save
  | _ => none

/-- A proof stream, up to its `END`, with the position after it. -/
def proofStream : Nat → Nat → Option (List ProofCmd × Nat)
  | 0, _ => none
  | fuel + 1, at_ => do
      let (opcode, data, size) ← command bytes at_
      if opcode = 0 then if data = 0 then pure ([], at_ + size) else none
      else
        let cmd ← proofCmd opcode data
        let (rest, next) ← proofStream fuel (at_ + size)
        pure (cmd :: rest, next)

def termEntry (fuel : Nat) (at_ : Nat) : Option (TermEntry × Bool) := do
  let count ← u16 bytes at_
  let sortByte ← u8 bytes (at_ + 2)
  let reserved ← u8 bytes (at_ + 3)
  let data ← u32 bytes (at_ + 4)
  if at_ % 8 ≠ 0 ∨ reserved ≠ 0 ∨ data % 8 ≠ 0 then none else
  let args ← argTypes bytes data count
  let ret ← argAt bytes (data + 8 * count)
  let isDef := sortByte / 128 == 1
  let value ← if isDef then (unifyStream bytes fuel (data + 8 * (count + 1))).map some else pure none
  pure (⟨sortByte % 128, args, ret, value⟩, isDef)

def thmEntry (fuel : Nat) (at_ : Nat) : Option ThmEntry := do
  let count ← u16 bytes at_
  let reserved ← u16 bytes (at_ + 2)
  let data ← u32 bytes (at_ + 4)
  if at_ % 8 ≠ 0 ∨ reserved ≠ 0 ∨ data % 8 ≠ 0 then none else
  let args ← argTypes bytes data count
  let unify ← unifyStream bytes fuel (data + 8 * count)
  pure ⟨args, unify⟩

/-- A decoded source statement, retaining its declaration visibility and
half-open byte interval. These fields are frontend metadata: `statement` is
the unchanged input of the reference proof machine. -/
structure DecodedStatement where
  statement : Statement
  isLocal : Bool
  start : Nat
  after : Nat
  opcode : Nat

/-- Forget source metadata without reordering or changing proof commands. -/
def proofStatements (source : List DecodedStatement) : List Statement :=
  source.map (·.statement)

/-- The statements of the proof stream. Whether a term statement carries a
proof stream is read from the term table. Local definitions and local theorems
retain their explicit source opcode; neither flag is inferred from a table. -/
def statements (isDef : List Bool) : Nat → Nat → Nat → Option (List DecodedStatement)
  | 0, _, _ => none
  | fuel + 1, at_, terms => do
      let (opcode, data, size) ← command bytes at_
      let next := at_ + data
      match opcode with
      | 0x00 => if data = 0 then pure [] else none
      | 0x04 =>
          if data = size then
            pure (⟨⟨.sort, []⟩, false, at_, next, opcode⟩ ::
              (← statements isDef fuel next terms))
          else none
      | 0x05 | 0x0D =>
          if isDef.getD terms false then do
            let (proof, after) ← proofStream bytes fuel (at_ + size)
            if after = next then
              pure (⟨⟨.term, proof⟩, opcode == 0x0D, at_, next, opcode⟩ ::
                (← statements isDef fuel next (terms + 1)))
            else none
          else if data = size then
            pure (⟨⟨.term, []⟩, opcode == 0x0D, at_, next, opcode⟩ ::
              (← statements isDef fuel next (terms + 1)))
          else none
      | 0x02 | 0x06 | 0x0E => do
          let (proof, after) ← proofStream bytes fuel (at_ + size)
          if after = next then
            let kind := if opcode = 0x02 then StatementKind.axiomDecl else .theoremDecl
            pure (⟨⟨kind, proof⟩, opcode == 0x0E, at_, next, opcode⟩ ::
              (← statements isDef fuel next terms))
          else none
      | _ => none

def sortAt (at_ : Nat) : Option SortInfo := do
  let byte ← u8 bytes at_
  if byte ≥ 16 then none else pure (sortInfo byte)

/-- The index extensions are opaque; their generic entry table must fit. -/
def indexValid (pProof pIndex : Nat) : Option Unit := do
  if pIndex = 0 then pure () else
  if pIndex % 8 ≠ 0 ∨ pIndex ≤ pProof ∨ bytes.size < pIndex + 8 then none else
  let count ← u64 bytes pIndex
  if bytes.size < pIndex + 8 + 16 * count then none else pure ()

/-- Position of the statement-stream terminator, before its encoded command. -/
def terminatorAt (pProof : Nat) (source : List DecodedStatement) : Nat :=
  match source.getLast? with
  | none => pProof
  | some last => last.after

/-- **Decode a file** using the required fields and alignment of binary
version 1. The optional index cannot authorize declarations or proofs. -/
def file : Option (Tables × List DecodedStatement) := do
  let fuel := bytes.size + 1
  let magic ← u32 bytes 0
  let version ← u8 bytes 4
  if magic ≠ 0x42304D4D ∨ version ≠ 1 then none else
  let numSorts ← u8 bytes 5
  let reserved ← u16 bytes 6
  let numTerms ← u32 bytes 8
  let numThms ← u32 bytes 12
  let pTerms ← u32 bytes 16
  let pThms ← u32 bytes 20
  let pProof ← u32 bytes 24
  let reserved2 ← u32 bytes 28
  let pIndex ← u64 bytes 32
  if numSorts > 128 ∨ reserved ≠ 0 ∨ reserved2 ≠ 0 ∨
      pTerms % 8 ≠ 0 ∨ pThms % 8 ≠ 0 ∨
      pTerms < 40 + numSorts ∨ pThms < pTerms + 8 * numTerms ∨
      pProof < pThms + 8 * numThms ∨ bytes.size ≤ pProof then none else
  let _ ← indexValid bytes pProof pIndex
  let sorts ← (List.range numSorts).mapM fun index => sortAt bytes (40 + index)
  let terms ← (List.range numTerms).mapM fun index => termEntry bytes fuel (pTerms + 8 * index)
  let thms ← (List.range numThms).mapM fun index => thmEntry bytes fuel (pThms + 8 * index)
  let source ← statements bytes (terms.map (·.2)) fuel pProof 0
  let (_, _, terminatorSize) ← command bytes (terminatorAt pProof source)
  if pIndex ≠ 0 ∧ pIndex < terminatorAt pProof source + terminatorSize then none else
  pure (⟨sorts, terms.map (·.1), thms⟩, source)

end Mettapedia.Languages.MM0.Formats.MMB.Decode
