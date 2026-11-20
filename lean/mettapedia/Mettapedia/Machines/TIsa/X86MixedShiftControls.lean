import Mettapedia.Machines.TIsa.X86MixedRegion

/-! A high-bit shift produces a Boolean branch condition, followed by a dependent ADD. -/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86MixedRegion.ShiftControls
open _root_.X86Registers X86RegisterRefinement X86Execution X86Assembler
local instance : MemoryPrimitives := X86Memory.ordinary

def shift : Node := .word ⟨0,100,101,.inr ⟨.rightUnsigned,7,1,63,by decide⟩⟩
def choice : Node := .branch ⟨0,101,7,102,104⟩
def addition : Node := .word ⟨0,102,103,.inl (.binary 0 2 7 7 (by decide))⟩
def program : List Node := [shift,choice,addition]
def live (point : Word) : Finset Key :=
  if point = 100 then {1} else if point = 101 ∨ point = 102 then {7}
  else if point = 103 then {2} else ∅
def tail : List Chunk := [.bytes [0x90,0x90,0x90,0x90,0x90],.label 104,.bytes [0x90]]
def emission : Emission :=
  ⟨[0x49,0x89,0xf3,0x49,0xc1,0xeb,63,0x4d,0x85,0xdb,0x0f,0x84,14,0,0,0,
    0x4d,0x89,0xde,0x4d,0x01,0xde,0x4c,0x89,0xf2,0x90,0x90,0x90,0x90,0x90,0x90],
    [⟨10,some 4,104,30⟩]⟩
def labels : Labels := [(100,0),(101,7),(102,16),(103,25),(104,30)]
theorem compiled : compile? live 0 103 program [] tail = some emission := by decide
theorem boundaries : labelsAt 0 (code 103 program [] tail) = some labels := by decide
theorem actual_labels (layout : Layout live 0 103 program [] tail emission) : layout.labels = labels :=
  Option.some.inj (layout.resolved.symm.trans boundaries)

def keys : Finset Location := {.inl 0,.inr 1,.inr 7,.inr 2}
def initial (take : Bool) : Values
  | .inl activation => if activation = 0 then 100 else 0
  | .inr register => if register = 1 then (if take then (0x8000000000000000#64) else 0) else 0
def afterShift (take : Bool) := shift.nextValues (initial take)
def afterChoice (take : Bool) := choice.nextValues (afterShift take)
def afterAdd := addition.nextValues (afterChoice true)

theorem shift_source (take : Bool) :
    Counted program (Cells.encode keys (initial take),0) (Cells.encode keys (afterShift take),2) := by
  apply counted_realized program shift (by simp [program]) keys (initial take) (afterShift take) 0 (by decide)
  cases take <;> decide

theorem branch_source (take : Bool) :
    Counted program (Cells.encode keys (afterShift take),2) (Cells.encode keys (afterChoice take),4) := by
  apply counted_realized program choice (by simp [program]) keys (afterShift take) (afterChoice take) 2 (by decide)
  cases take <;> decide

theorem add_source :
    Counted program (Cells.encode keys (afterChoice true),4) (Cells.encode keys afterAdd,7) := by
  apply counted_realized program addition (by simp [program]) keys (afterChoice true) afterAdd 4 (by decide)
  decide

theorem prefix_source (take : Bool) :
    Relation.ReflTransGen (Counted program) (Cells.encode keys (initial take),0) (Cells.encode keys (afterChoice take),4) :=
  (Relation.ReflTransGen.single (shift_source take)).tail (branch_source take)
theorem success_source :
    Relation.ReflTransGen (Counted program) (Cells.encode keys (initial true),0) (Cells.encode keys afterAdd,7) :=
  (prefix_source true).tail add_source

private noncomputable abbrev seed := X86BranchGate.Controls.entryFixture 6 0
private noncomputable abbrev seedOrigin := seed.2.toBasis
private def initialFlags : BitVec 32 := 0x40246#32
private def cells : List (Nat × Byte) := (List.finRange emission.bytes.length).map (fun index =>
  (4096 + index.val,emission.bytes[index.val]'index.isLt))
private theorem distinct : cells.Pairwise (fun left right => (left.1 == right.1) = false) := by decide

private noncomputable def before (take : Bool) : State :=
  let regs := ((seed.1.regs.erase .r11).erase .rdx).erase .r14
  let native := X86Flags.putFlags { seed.1 with regs := regs, mem := Std.ExtHashMap.ofList cells } initialFlags
  X86Move.putPointer (put native 6 (if take then (0x8000000000000000#64) else (0#64))) (address 4096 0)

theorem physical_one : physical 1 = (6 : Fin 16) := by decide
theorem physical_seven : physical 7 = (11 : Fin 16) := by decide
theorem physical_two : physical 2 = (2 : Fin 16) := by decide
theorem scratch_fourteen : X86BinCapture.scratch = (14 : Fin 16) := by decide

theorem absent_destinations (take : Bool) :
    X86RegisterRefinement.lookup (before take) (physical 7) = none ∧
    X86RegisterRefinement.lookup (before take) (physical 2) = none ∧
    X86RegisterRefinement.lookup (before take) X86BinCapture.scratch = none := by
  rw [physical_seven,physical_two,scratch_fourteen]
  simp [before,put,X86Flags.putFlags,X86Move.putPointer,X86RegisterRefinement.lookup,key,
    Std.ExtDHashMap.get?_insert,Std.ExtDHashMap.get?_erase]

private theorem physical_address (index : Nat) (within : index < 31) :
    ((address 4096 index).signExtend 52).toNat = 4096 + index := by interval_cases index <;> decide
private theorem loaded (take : Bool) : X86CodePlacement.Placed (before take) 4096 (view emission.bytes) := by
  intro index byte present
  change emission.bytes[index]? = some byte at present
  have within := (List.getElem?_eq_some_iff.mp present).1
  have actual : emission.bytes[index]'within = byte :=
    Option.some.inj ((List.getElem?_eq_getElem within).symm.trans present)
  have member : (4096 + index,byte) ∈ cells := by
    apply List.mem_map.mpr
    refine ⟨⟨index,within⟩,by simp,?_⟩
    simp only [actual]
  rw [physical_address index (by change index < 31 at within; exact within)]
  exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) distinct member

private noncomputable def origin (take : Bool) : X86LegacyFetch.Basis (before take) where
  address := address 4096 0
  opcodeAddress := address 4096 1
  modrmAddress := address 4096 2
  next := address 4096 3
  control := seedOrigin.control
  attributes := seedOrigin.attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by simpa [before,put,X86Flags.putFlags,X86Move.putPointer,key,
    Std.ExtDHashMap.get?_insert,Std.ExtDHashMap.get?_erase] using seedOrigin.status
  fault := by simpa [before,put,X86Flags.putFlags,X86Move.putPointer,key,
    Std.ExtDHashMap.get?_insert,Std.ExtDHashMap.get?_erase] using seedOrigin.fault
  msrs := by simpa [before,put,X86Flags.putFlags,X86Move.putPointer,key,
    Std.ExtDHashMap.get?_insert,Std.ExtDHashMap.get?_erase] using seedOrigin.msrs
  segments := by simpa [before,put,X86Flags.putFlags,X86Move.putPointer,key,
    Std.ExtDHashMap.get?_insert,Std.ExtDHashMap.get?_erase] using seedOrigin.segments
  longMode := seedOrigin.longMode
  codeMode := seedOrigin.codeMode
  application := by simpa [before,put,X86Flags.putFlags,X86Move.putPointer,key,
    Std.ExtDHashMap.get?_insert,Std.ExtDHashMap.get?_erase] using seedOrigin.application
  rip := by simp [before,X86Move.putPointer]

private noncomputable def ready (take : Bool) (layout : Layout live 0 103 program [] tail emission) :
    Ready layout 4096 (initial take) (before take) where
  origin := origin take
  lower := by decide
  upper := by decide
  offset := 0
  control := by rw [actual_labels layout]; change X86Assembler.lookup labels 100 = some 0; decide
  location := by change (address 4096 0).toInt = (4096 : Int) + (0 : Nat); decide
  loaded := loaded take
  reads := by
    intro register present
    have same : register = 1 := by simpa [initial,live] using present
    subst register
    rw [physical_one]
    change X86RegisterRefinement.lookup (X86Move.putPointer (put _ 6 _) _) 6 = _
    rw [X86Move.lookup_putPointer]
    exact lookup_put_same _ 6 _
  flags := initialFlags
  flagsKnown := by simp [before,put,X86Flags.putFlags,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert]
  quiet := by simpa [before,put,X86Flags.putFlags,X86Move.putPointer,key,
    Std.ExtDHashMap.get?_insert,Std.ExtDHashMap.get?_erase] using seed.2.quiet

theorem not_all_initialized (take : Bool) :
    ¬ ∃ values : Key → Word, ∀ register, X86RegisterRefinement.lookup (before take) (physical register) = some (values register) := by
  rintro ⟨values,known⟩
  have present := known 7
  rw [(absent_destinations take).1] at present
  cases present

theorem pointer_at (layout : Layout live 0 103 program [] tail emission) (values : Values) (native : State)
    (input : Ready layout 4096 values native) (point : Word) (offset : Nat)
    (current : values (.inl 0) = point) (named : X86Assembler.lookup labels point.toNat = some offset) :
    native.regs.get? .rip = some ((address 4096 offset).signExtend 64) := by
  have bound := input.control
  rw [actual_labels layout,current] at bound
  have position : input.offset = offset := Option.some.inj (bound.symm.trans named)
  have pointer := Ready.pointer layout input
  rw [position] at pointer
  exact pointer

theorem success (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 7).run (before true) = .ok () after ∧
      X86RegisterRefinement.lookup after (physical 2) = some (2#64) ∧
      after.regs.get? .rip = some ((address 4096 25).signExtend 64) ∧
      RegisterFrame (footprint program) (before true) after ∧
      X86CodePlacement.Placed after 4096 (view emission.bytes) ∧ X86ControlFlags.Preserved (before true) after ∧
      ∀ count ≤ 7, ∀ observed, (X86FuelPrefix.fetches count).run (before true) = .ok () observed →
        RegisterFrame (footprint program) (before true) observed := by
  let : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨layout⟩ := ofCompilation live 0 103 program [] tail emission compiled
  obtain ⟨nextValues,after,next,_monotone,endpoint,run,frame,control,prefixes⟩ :=
    realizes_counted layout other extra vector keys (initial true) (before true) (ready true layout) 0
      (Cells.encode keys afterAdd,7) success_source
  have agree := ((Cells.encode_le_iff keys keys nextValues afterAdd).mp (le_of_eq endpoint.symm)).2
  have current : nextValues (.inl 0) = (103#64) := (agree _ (by decide)).trans (by decide)
  have value : nextValues (.inr 2) = (2#64) := (agree _ (by decide)).trans (by decide)
  have result := next.reads 2 (by rw [current]; decide)
  rw [value] at result
  exact ⟨after,run,result,pointer_at layout nextValues after next 103 25 current (by decide),
    frame,next.loaded,control,prefixes⟩

theorem early_exit (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 4).run (before false) = .ok () after ∧
      after.regs.get? .rip = some ((address 4096 30).signExtend 64) ∧
      RegisterFrame (footprint program) (before false) after ∧
      ∀ count ≤ 4, ∀ observed, (X86FuelPrefix.fetches count).run (before false) = .ok () observed →
        RegisterFrame (footprint program) (before false) observed := by
  let : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨layout⟩ := ofCompilation live 0 103 program [] tail emission compiled
  obtain ⟨nextValues,after,next,_monotone,endpoint,run,frame,_control,prefixes⟩ :=
    realizes_counted layout other extra vector keys (initial false) (before false) (ready false layout) 0
      (Cells.encode keys (afterChoice false),4) (prefix_source false)
  have agree := ((Cells.encode_le_iff keys keys nextValues (afterChoice false)).mp (le_of_eq endpoint.symm)).2
  have current : nextValues (.inl 0) = (104#64) := (agree _ (by decide)).trans (by decide)
  exact ⟨after,run,pointer_at layout nextValues after next 104 30 current (by decide),frame,prefixes⟩

#print axioms compiled
#print axioms success
#print axioms early_exit
#print axioms absent_destinations
end Mettapedia.Machines.TIsa.X86MixedRegion.ShiftControls
