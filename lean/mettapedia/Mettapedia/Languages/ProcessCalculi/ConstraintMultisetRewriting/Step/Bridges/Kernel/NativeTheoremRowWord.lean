import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeKeyMemoryLoadAdmission

/-!
# A locally licensed second word of a theorem-row image

The finite producer checks a literal's word range and invokes the existing
captured load checker on actual keys and values. Its certificate is consumed
by the established native load theorem. Only the eight selected bytes are
observed; a complete physical row or table is not inferred.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeTheoremRowWord

open Mettapedia.Machines.TIsa Cells CellEffects Control
open _root_.X86Registers X86RegisterRefinement X86Execution
open NativeKeyMemoryLoadAdmission

local instance : MemoryPrimitives := X86Memory.ordinary

def point (entry : X86MemoryFieldLoad.EntryFixture) : Word := entry.origin.address.signExtend 64
def next (entry : X86MemoryFieldLoad.EntryFixture) : Word := (address entry.base 316).signExtend 64
def invalid (entry : X86MemoryFieldLoad.EntryFixture) : Word := (address entry.base 590).signExtend 64

def snapshot (keys : Finset Key) (values : Key → Word) (atPoint : Word) : Snapshot where
  keys := insert (.inl 0) (keys.image Sum.inr)
  values := fun location => match location with
    | .inl activation => if activation = 0 then atPoint else 0
    | .inr key => values key
  generations := fun _ => 0

def candidate (values : Key → Word) (n : Nat) : Key → Word :=
  Function.update values (.register 6) (BitVec.ofNat 64 n)

/-- Literal/cell evidence returned by the actual existing admission checker. -/
structure Projection (n address : Nat) (atPoint nextPoint invalidPoint : Word)
    (keys : Finset Key) (values : Key → Word) where
  fits : n < 2 ^ 64
  afterValues : Location Key → Word
  checked : CheckedAdmission.step? (edges address 0 atPoint nextPoint invalidPoint) 0
    (snapshot keys values atPoint).keys (snapshot keys values atPoint).values (candidate values n) = some afterValues

def projectHeadSecond? (n address : Nat) (atPoint nextPoint invalidPoint : Word)
    (keys : Finset Key) (values : Key → Word) : Option (Projection n address atPoint nextPoint invalidPoint keys values) :=
  if fits : n < 2 ^ 64 then
    match checked : CheckedAdmission.step? (edges address 0 atPoint nextPoint invalidPoint) 0
      (snapshot keys values atPoint).keys (snapshot keys values atPoint).values (candidate values n) with
    | none => none
    | some afterValues => some ⟨fits,afterValues,checked⟩
  else none

abbrev AtEntry (n : Nat) (entry : X86MemoryFieldLoad.EntryFixture) :=
  Projection n entry.address (point entry) (next entry) (invalid entry) entry.view.keys entry.values

def fromEntry? (n : Nat) (entry : X86MemoryFieldLoad.EntryFixture) : Option (AtEntry n entry) :=
  projectHeadSecond? n entry.address (point entry) (next entry) (invalid entry) entry.view.keys entry.values

def Projection.word {n address : Nat} {atPoint nextPoint invalidPoint : Word}
    {keys : Finset Key} {values : Key → Word}
    (_projection : Projection n address atPoint nextPoint invalidPoint keys values) : Word := BitVec.ofNat 64 n

theorem Projection.word_exact {n address : Nat} {atPoint nextPoint invalidPoint : Word}
    {keys : Finset Key} {values : Key → Word}
    (projection : Projection n address atPoint nextPoint invalidPoint keys values) : projection.word.toNat = n := by
  change (BitVec.ofNat 64 n).toNat = n
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt projection.fits]

theorem Projection.destination {n address : Nat} {atPoint nextPoint invalidPoint : Word}
    {keys : Finset Key} {values : Key → Word}
    (projection : Projection n address atPoint nextPoint invalidPoint keys values) :
    projection.afterValues (.inr (.register 6)) = projection.word := by
  rw [(checked_eligible address 0 atPoint nextPoint invalidPoint (snapshot keys values atPoint)
    (candidate values n) projection.afterValues projection.checked).2]
  rfl

theorem overflow_refused (n address : Nat) (atPoint nextPoint invalidPoint : Word)
    (keys : Finset Key) (values : Key → Word) (large : 2 ^ 64 ≤ n) :
    projectHeadSecond? n address atPoint nextPoint invalidPoint keys values = none := by
  unfold projectHeadSecond?
  rw [dif_neg (by omega)]

/-- The complete existing native outcome, including its auxiliary effects. -/
structure Execution (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {n : Nat} (entry : X86MemoryFieldLoad.EntryFixture) (projection : AtEntry n entry) where
  admitted : (CellOccurrences.step (edges entry.address 0 (point entry) (next entry) (invalid entry))).Admits
    (s := snapshot entry.view.keys entry.values (point entry))
    (firing entry.address 0 (point entry) (next entry) (invalid entry) (candidate entry.values n))
  after : State
  nextFlags : BitVec 32
  result_values : ((CellOccurrences.step (edges entry.address 0 (point entry) (next entry) (invalid entry))).result
    (firing entry.address 0 (point entry) (next entry) (invalid entry) (candidate entry.values n)) admitted).values = projection.afterValues
  run : letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 10).run entry.native = .ok () after
  frame : RegisterFrame (insert .r10 X86Bounds.writes) entry.native after
  represented : X86MemoryView.represents entry.view
    (Cells.encode entry.view.keys (fun key => projection.afterValues (.inr key))) after
  destination : X86MemoryView.readback entry.view.modes after (.register 6) = some projection.word
  beforePC : entry.native.regs.get? .rip = some ((snapshot entry.view.keys entry.values (point entry)).values (.inl 0))
  afterPC : after.regs.get? .rip = some (projection.afterValues (.inl 0))
  flags : after.regs.get? .rflags = some nextFlags
  image : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after entry.base
  controls : X86ControlFlags.Preserved entry.native after
  profile : entry.profile.Holds after

theorem load_execution (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {n : Nat} (entry : X86MemoryFieldLoad.EntryFixture) (projection : AtEntry n entry) :
    Nonempty (Execution other extra vector entry projection) := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨admitted,after,nextFlags,result,run,frame,represented,beforePC,afterPC,flags,image,controls,profile⟩ :=
    checked_load_executes other extra vector entry.view (snapshot entry.view.keys entry.values (point entry))
      entry.native entry.base entry.origin entry.profile entry.flags entry.address 0 (point entry) (next entry) (invalid entry)
      (candidate entry.values n) projection.afterValues rfl entry.known rfl rfl
      entry.frameArea entry.frameAligned entry.holds entry.flagsKnown entry.quiet entry.placed entry.upper entry.loaded
      entry.rangeFits entry.pointerLower entry.pointerUpper entry.aligned projection.checked
  have destination : X86MemoryView.readback entry.view.modes after (.register 6) = some projection.word := by
    obtain ⟨assigned,encoded,seen⟩ := represented
    have same := ((Cells.encode_le_iff entry.view.keys entry.view.keys assigned
      (fun key => projection.afterValues (.inr key))).mp (le_of_eq encoded.symm)).2
      (.register 6) (entry.view.registers 6)
    exact ((seen (.register 6) (entry.view.registers 6)).trans (congrArg some same)).trans
      (congrArg some projection.destination)
  exact ⟨⟨admitted,after,nextFlags,result,run,frame,represented,destination,beforePC,afterPC,flags,image,controls,profile⟩⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeTheoremRowWord
