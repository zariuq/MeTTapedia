import Mettapedia.Machines.TIsa.RelativeBranch
import Init.Data.RArray

/-!
# Native byte-image layout and relative-branch checking

These checks consume the actual byte image, not just emitter metadata. They
establish wrapper identity, contiguous recorded spans and exact branch fields.
Instruction semantics, instruction-boundary decoding and the absence of stack
accesses in ordinary body instructions remain separate refinement obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.NativeImage

abbrev Byte := BitVec 8

structure View where
  size : Nat
  read : Nat → Option Byte

def View.ofArray (bytes : Array Byte) : View := ⟨bytes.size, fun index => bytes[index]?⟩

def hexDigit? (byte : UInt8) : Option Nat :=
  let value := byte.toNat
  if 48 ≤ value ∧ value < 58 then some (value - 48)
  else if 97 ≤ value ∧ value < 103 then some (value - 87) else none

def hexByte? (text : String) (offset : Nat) : Option Byte := do
  let high ← text.toByteArray[2 * offset]?
  let low ← text.toByteArray[2 * offset + 1]?
  pure (BitVec.ofNat 8 (16 * (← hexDigit? high) + (← hexDigit? low)))

def hexView (text : String) : View := ⟨text.utf8ByteSize / 2, hexByte? text⟩

def readFour? (image : View) (offset : Nat) : Option (List Byte) := do
  let a ← image.read offset
  let b ← image.read (offset + 1)
  let c ← image.read (offset + 2)
  let d ← image.read (offset + 3)
  pure [a, b, c, d]

structure Patch where
  opcodeOffset : Nat
  fieldOffset : Nat
  nextIp : Nat
  target : Nat
  opcode : Byte
  conditional : Bool
  relative : Int
  patched : Bool
  deriving DecidableEq, Repr

def Patch.prefixCheck (patch : Patch) (image : View) : Bool :=
  if patch.conditional then
    decide (128 ≤ patch.opcode.toNat ∧ patch.opcode.toNat < 144) &&
      image.read patch.opcodeOffset == some 15 && image.read (patch.opcodeOffset + 1) == some patch.opcode &&
      patch.fieldOffset == patch.opcodeOffset + 2
  else patch.opcode == 233 && image.read patch.opcodeOffset == some 233 &&
    patch.fieldOffset == patch.opcodeOffset + 1

def Patch.check (patch : Patch) (image : View) (bodyOffset epilogueOffset : Nat) : Bool :=
  match readFour? image patch.fieldOffset with
  | none => false
  | some bytes => patch.patched && patch.prefixCheck image && patch.nextIp == patch.fieldOffset + 4 &&
      decide (bodyOffset ≤ patch.opcodeOffset ∧ patch.nextIp ≤ epilogueOffset ∧
        bodyOffset ≤ patch.target ∧ patch.target ≤ epilogueOffset) &&
      decide ((RelativeBranch.decode32 bytes).toInt = patch.relative) &&
      decide (RelativeBranch.decodedTarget patch.fieldOffset bytes = (patch.target : Int))

theorem Patch.checked_target (patch : Patch) (image : View) (bodyOffset epilogueOffset : Nat)
    (checked : patch.check image bodyOffset epilogueOffset = true) :
    ∃ bytes, readFour? image patch.fieldOffset = some bytes ∧
      RelativeBranch.decodedTarget patch.fieldOffset bytes = (patch.target : Int) := by
  cases read : readFour? image patch.fieldOffset with
  | none => simp [check, read] at checked
  | some bytes =>
      refine ⟨bytes, rfl, ?_⟩
      simp only [check, read, Bool.and_eq_true, decide_eq_true_eq] at checked
      exact checked.2

structure Span where
  offset : Nat
  length : Nat
  kind : String
  deriving DecidableEq, Repr

/-- A finite helper output before whole-image linking and relocation. -/
structure TemplateSample where
  inputs : List Nat
  bytes : List Nat
  spans : List Span
  scratchMask : Nat
  deriving DecidableEq, Repr

def TemplateSample.body (sample : TemplateSample) (kind : String) : Option (List Nat) := do
  let span ← sample.spans.find? (fun span => span.kind == kind)
  if span.offset + span.length ≤ sample.bytes.length then
    some ((sample.bytes.drop span.offset).take span.length)
  else none

def spanEnd? : Nat → List Span → Option Nat
  | cursor, [] => some cursor
  | cursor, span :: later =>
      if span.offset = cursor ∧ 0 < span.length then spanEnd? (cursor + span.length) later else none

structure Image where
  name : String
  id : Nat
  size : Nat
  data : Lean.RArray Nat
  bodyOffset : Nat
  epilogueOffset : Nat
  spans : List Span
  branches : List Patch

def prologue : List Byte := [83, 65, 84, 65, 85, 65, 86, 65, 87]
def epilogue : List Byte := [65, 95, 65, 94, 65, 93, 65, 92, 91, 195]

def Image.view (image : Image) : View := ⟨image.size, fun index =>
  if index < image.size then
    let value : Nat := Lean.RArray.get image.data index
    if Nat.ble value 255 then some (BitVec.ofNat 8 value) else none
  else none⟩

def readRange? (view : View) (offset count : Nat) : Option (List Byte) :=
  (List.range count).mapM fun index => view.read (offset + index)

def Image.layoutCheckOn (image : Image) (view : View) : Bool :=
  image.bodyOffset == 9 && image.epilogueOffset + 10 == view.size &&
  readRange? view 0 9 == some prologue && readRange? view image.epilogueOffset 10 == some epilogue &&
  spanEnd? 0 image.spans == some view.size &&
  image.branches.all (fun branch => branch.check view image.bodyOffset image.epilogueOffset)

def Image.layoutCheck (image : Image) : Bool := image.layoutCheckOn image.view

theorem Image.checked_branch (image : Image) (checked : image.layoutCheck = true)
    (branch : Patch) (member : branch ∈ image.branches) :
    branch.check image.view image.bodyOffset image.epilogueOffset = true := by
  have all : image.branches.all (fun branch => branch.check image.view image.bodyOffset image.epilogueOffset) = true :=
    ((Bool.and_eq_true _ _).mp checked).2
  exact List.all_eq_true.mp all branch member

theorem Image.branch_target_exact (image : Image) (checked : image.layoutCheck = true)
    (branch : Patch) (member : branch ∈ image.branches) :
    ∃ bytes, readFour? image.view branch.fieldOffset = some bytes ∧
      RelativeBranch.decodedTarget branch.fieldOffset bytes = (branch.target : Int) :=
  branch.checked_target image.view image.bodyOffset image.epilogueOffset (image.checked_branch checked branch member)

namespace Controls

private def branch : Patch := ⟨0, 2, 6, 0, 133, true, -6, true⟩

example : branch.check (View.ofArray #[15, 133, 250, 255, 255, 255]) 0 6 = true := by decide
example : branch.check (View.ofArray #[15, 133, 251, 255, 255, 255]) 0 6 = false := by decide
example : branch.check (View.ofArray #[15, 132, 250, 255, 255, 255]) 0 6 = false := by decide
example : branch.check (View.ofArray #[15, 133, 250, 255, 255]) 0 6 = false := by decide
example : branch.check (hexView "0f85faffffff") 0 6 = true := by decide

end Controls

end Mettapedia.Machines.TIsa.NativeImage
