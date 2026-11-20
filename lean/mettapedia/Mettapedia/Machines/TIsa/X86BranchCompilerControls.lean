import Mettapedia.Machines.TIsa.X86BranchCompiler
import Mettapedia.Machines.TIsa.X86MemoryFieldLoad
import Mettapedia.Machines.TIsa.X86P1IfCapture

/-!
# Generated source branches with logical continuation names

The witnesses use source names 100,101,102 and separately placed machine
addresses. Backward and colocated continuation cases exercise both Boolean
values. Non-Boolean source input remains outside the guarded branch domain.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86BranchCompiler.Controls
open _root_.X86Registers X86RegisterRefinement X86Execution X86Assembler
local instance : MemoryPrimitives := X86Memory.ordinary

def branch : Control.Branch Nat := ⟨0,100,0,101,102⟩
def first (shared : Bool) : List Chunk := if shared then [] else [.label 102,.bytes [0x90,0x90,0x90,0x90,0x90]]
def tail (shared : Bool) : List Chunk := if shared then [.label 102] else []
def emission (shared : Bool) : Emission :=
  if shared then ⟨[0x4d,0x85,0xdb,0x0f,0x84,0,0,0,0],[⟨3,some 4,102,9⟩]⟩
  else ⟨[0x90,0x90,0x90,0x90,0x90,0x4d,0x85,0xdb,0x0f,0x84,0xf2,0xff,0xff,0xff],[⟨8,some 4,102,0⟩]⟩

theorem assembled (shared : Bool) :
    assemble (first shared ++ (lower branch 11 ++ tail shared)) = some (emission shared) := by
  cases shared <;> decide

private noncomputable abbrev seed := X86MemoryFieldLoad.entryFixture
private def cells (shared : Bool) : List (Nat × Byte) :=
  (List.finRange (emission shared).bytes.length).map (fun index =>
    (4096 + index.val,(emission shared).bytes[index.val]'index.isLt))

private theorem distinct (shared : Bool) :
    (cells shared).Pairwise (fun left right => (left.1 == right.1) = false) := by
  cases shared <;> decide

private noncomputable def before (shared : Bool) (value : Word) : State :=
  let native := X86Move.putPointer (put seed.native 11 value) (address 4096 (width (first shared)))
  { native with mem := Std.ExtHashMap.ofList (cells shared) }

private theorem physical (index : Nat) (within : index < 14) :
    ((address 4096 index).signExtend 52).toNat = 4096 + index := by interval_cases index <;> decide

private theorem loaded (shared : Bool) (value : Word) :
    X86CodePlacement.Placed (before shared value) 4096 (X86Assembler.view (emission shared).bytes) := by
  intro index byte present
  change (emission shared).bytes[index]? = some byte at present
  have within := (List.getElem?_eq_some_iff.mp present).1
  have small : (emission shared).bytes.length ≤ 14 := by cases shared <;> decide
  have actual : (emission shared).bytes[index]'within = byte :=
    Option.some.inj ((List.getElem?_eq_getElem within).symm.trans present)
  have member : (4096 + index,byte) ∈ cells shared := by
    apply List.mem_map.mpr
    refine ⟨⟨index,within⟩,by simp,?_⟩
    simp only [actual]
  rw [physical index (by omega)]
  simp only [before]
  exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (distinct shared) member

private noncomputable def origin (shared : Bool) (value : Word) : X86LegacyFetch.Basis (before shared value) where
  address := address 4096 (width (first shared))
  opcodeAddress := address 4096 (width (first shared) + 1)
  modrmAddress := address 4096 (width (first shared) + 2)
  next := address 4096 (width (first shared) + 3)
  control := seed.origin.control
  attributes := seed.origin.attributes
  step1 := by cases shared <;> decide
  step2 := by cases shared <;> decide
  step3 := by cases shared <;> decide
  status := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert] using seed.origin.status
  fault := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert] using seed.origin.fault
  msrs := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert] using seed.origin.msrs
  segments := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert] using seed.origin.segments
  longMode := seed.origin.longMode
  codeMode := seed.origin.codeMode
  application := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert] using seed.origin.application
  rip := by simp [before,X86Move.putPointer]

private noncomputable def entry (shared : Bool) (value : Word) : Entry 11 (width (first shared)) (emission shared) (before shared value) where
  base := 4096
  origin := origin shared value
  lower := by decide
  upper := by cases shared <;> decide
  location := by
    change (address 4096 (width (first shared))).toInt = (4096 : Int) + (width (first shared) : Int)
    cases shared <;> decide
  loaded := loaded shared value
  value := value
  known := by
    change X86RegisterRefinement.lookup
      (X86Move.putPointer (put seed.native 11 value) (address 4096 (width (first shared)))) 11 = some value
    rw [X86Move.lookup_putPointer]
    exact lookup_put_same _ 11 _
  flags := seed.flags
  flagsKnown := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert] using seed.flagsKnown
  quiet := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert] using seed.quiet

def keys : Finset (Control.Location Nat) := {.inl 0,.inr 0}
def values (value : Word) : Control.Location Nat → Word
  | .inl _ => 100
  | .inr _ => value

theorem generated_realization (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (shared : Bool) (value : Word) (canonical : value = 0 ∨ value = 1) :
    letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ compiled : Compilation branch 11 (first shared) (tail shared) (emission shared), ∃ after,
      Result compiled (entry shared value) keys (values value) after := by
  exact realizes other extra vector branch 11 (first shared) (tail shared) (emission shared) (assembled shared)
    (before shared value) (entry shared value) keys (values value) (by decide) rfl rfl canonical

def expectedLabels (shared : Bool) : Labels :=
  if shared then [(100,0),(101,9),(102,9)] else [(102,0),(100,5),(101,14)]

theorem labels_exact (shared : Bool) (compiled : Compilation branch 11 (first shared) (tail shared) (emission shared)) :
    compiled.labels = expectedLabels shared := by
  have computed : labelsAt 0 (first shared ++ (lower branch 11 ++ tail shared)) = some (expectedLabels shared) := by
    cases shared <;> decide
  exact Option.some.inj (compiled.resolved.symm.trans computed)

theorem false_target (shared : Bool) (compiled : Compilation branch 11 (first shared) (tail shared) (emission shared)) :
    compiled.target = if shared then 9 else 0 := by
  have computed : X86Assembler.lookup compiled.labels 102 = some (if shared then 9 else 0) := by
    rw [labels_exact shared compiled]
    cases shared <;> decide
  exact Option.some.inj (compiled.no.symm.trans computed)

theorem logical_and_native (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (shared : Bool) (value : Word) (canonical : value = 0 ∨ value = 1) :
    letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after,
      (CellEffects.profile [branch.recipe]).theory.rewrites (Cells.encode keys (values value))
        (Cells.encode keys (Function.update (values value) (.inl 0) (if value = (0#64) then 102 else 101))) ∧
      (X86FuelPrefix.fetches 2).run (before shared value) = .ok () after ∧
      after.regs.get? .rip = some ((address 4096
        (if shared then 9 else if value = (0#64) then 0 else 14)).signExtend 64) ∧
      RegisterFrame X86BranchGate.writes (before shared value) after := by
  let : OtherOpcodeHandlers := X86BranchGate.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨compiled,after,correct⟩ := generated_realization other extra vector shared value canonical
  have source := correct.sourceStep
  change (CellEffects.profile [branch.recipe]).theory.rewrites (Cells.encode keys (values value))
    (Cells.encode keys (Function.update (values value) (.inl 0) (if value = (0#64) then 102 else 101))) at source
  have pointer := correct.pointer
  change after.regs.get? .rip = some ((address 4096 (chosenOffset compiled value)).signExtend 64) at pointer
  rw [chosenOffset,false_target shared compiled] at pointer
  refine ⟨after,source,correct.run,?_,correct.frame⟩
  cases shared <;> simpa [first,width,Chunk.width] using pointer

theorem colocated_distinct_names :
    branch.yes ≠ branch.no ∧
      ∀ compiled : Compilation branch 11 (first true) (tail true) (emission true),
        X86Assembler.lookup compiled.labels branch.yes.toNat = X86Assembler.lookup compiled.labels branch.no.toNat := by
  refine ⟨by decide,?_⟩
  intro compiled
  rw [labels_exact true compiled]
  decide

theorem nonboolean_no_target : branch.target? (values 2 (.inr branch.condition)) = none := by decide

theorem nonboolean_no_source_step (result : Multiset (Cells.Cell (Control.Location Nat))) :
    ¬ (CellEffects.profile [branch.recipe]).theory.rewrites (Cells.encode keys (values 2)) result := by
  intro source
  obtain ⟨recipe,member,produced,_support,guarded,_endpoint⟩ :=
    (CellEffects.profile_rewrite_iff [branch.recipe] keys (values 2) result).mp source
  have same : recipe = branch.recipe := List.mem_singleton.mp member
  subst recipe
  obtain ⟨_current,target⟩ := (branch.guard_iff (values 2) produced).mp guarded
  rw [nonboolean_no_target] at target
  cases target

theorem raw_nonboolean_runs (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (shared : Bool) :
    letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run (before shared 2) = .ok () after ∧
      after.regs.get? .rip = some ((address 4096 (width (first shared) + 9)).signExtend 64) := by
  let : OtherOpcodeHandlers := X86BranchGate.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨compiled⟩ := ofAssembly branch 11 (first shared) (tail shared) (emission shared) (assembled shared)
  let start := entry shared 2
  let input := nativeInput branch 11 (first shared) (tail shared) (emission shared) compiled (before shared 2)
    start.base start.origin start.lower start.upper start.location start.loaded start.value start.known
    start.flags start.flagsKnown start.quiet
  obtain ⟨after,_flags,run,_frame,_value,_known,pointer,_control⟩ :=
    X86BranchGate.executes_control other extra vector (before shared 2) 11 input
  change after.regs.get? .rip = some
    ((if (2 : Word) = (0#64) then address 4096 compiled.target else address (origin shared 2).address.toInt 9).signExtend 64) at pointer
  rw [if_neg (by decide : (2 : Word) ≠ (0#64))] at pointer
  have shifted : address (origin shared 2).address.toInt 9 = address 4096 (width (first shared) + 9) := by
    have location : (origin shared 2).address.toInt = (4096 : Int) + (width (first shared) : Int) := (entry shared 2).location
    rw [location]
    simp only [address,Nat.cast_add,Int.add_assoc]
  exact ⟨after,run,by simpa only [shifted] using pointer⟩

theorem reflection (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (shared : Bool) (value : Word) (canonical : value = 0 ∨ value = 1) (after : State) :
    letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 2).run (before shared value) = .ok () after →
      ∃ compiled : Compilation branch 11 (first shared) (tail shared) (emission shared),
        Result compiled (entry shared value) keys (values value) after := by
  exact reflects other extra vector branch 11 (first shared) (tail shared) (emission shared) (assembled shared)
    (before shared value) (entry shared value) keys (values value) (by decide) rfl rfl canonical after

theorem captured_register : X86MemoryFieldLoad.physical 7 = 11 := by decide

/-- The branch compiler's TEST/JZ gate on a materialized Boolean is not the form the current
R_DERIVE_IS_PROP image emits: its first IF is the fused IF-FLAGS JNE at 74, opening with the escape
byte `0x0f` rather than the REX prefix `0x4d`, and the bytes before it are the CMP-FLAGS span. -/
theorem image_branch_is_fused :
    (X86BranchGate.code 11 (472#32))[0]? = some 0x4d ∧ X86P1IfCapture.code[0]? = some 0x0f ∧
    X86P1LoadCapture.propImage.view.read 74 = some (0x0f#8) ∧
    X86P1LoadCapture.propImage.view.read 67 = some (0x41#8) := by
  refine ⟨by decide, by decide, ?_, ?_⟩ <;> kernel_reflexivity

end Mettapedia.Machines.TIsa.X86BranchCompiler.Controls
