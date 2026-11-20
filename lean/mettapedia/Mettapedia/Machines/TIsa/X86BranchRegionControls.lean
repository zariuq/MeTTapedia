import Mettapedia.Machines.TIsa.X86BranchRegion
import Mettapedia.Machines.TIsa.X86MemoryFieldLoad

/-!
# Generated two-branch regions

The shared continuation is bound once. Both second-branch outcomes execute
four actual fetches; early exit executes two even when the skipped source
resource is absent and its native value lies outside the Boolean domain.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86BranchRegion.Controls
open _root_.X86Registers X86RegisterRefinement X86Execution X86Assembler X86BranchCompiler
local instance : MemoryPrimitives := X86Memory.ordinary

def left : Control.Branch Nat := ⟨0,100,0,101,102⟩
def right : Control.Branch Nat := ⟨0,101,1,103,102⟩
def tail : List Chunk := [.bytes [0x90,0x90,0x90,0x90,0x90],.label 102,.bytes [0x90]]
def chunks : List Chunk := program [] left right 11 12 tail
def emission : Emission :=
  ⟨[0x4d,0x85,0xdb,0x0f,0x84,14,0,0,0,0x4d,0x85,0xe4,0x0f,0x84,5,0,0,0,
    0x90,0x90,0x90,0x90,0x90,0x90],[⟨3,some 4,102,23⟩,⟨12,some 4,102,23⟩]⟩
def labels : Labels := [(100,0),(101,9),(103,18),(102,23)]

theorem assembled : assemble chunks = some emission := by decide
theorem boundaries : labelsAt 0 chunks = some labels := by decide
theorem duplicated_boundary_refused : assemble (lower left 11 ++ (lower right 12 ++ tail)) = none := by decide

private noncomputable abbrev seed := X86MemoryFieldLoad.entryFixture
private def cells : List (Nat × Byte) :=
  (List.finRange emission.bytes.length).map (fun index =>
    (4096 + index.val,emission.bytes[index.val]'index.isLt))
private theorem distinct : cells.Pairwise (fun left right => (left.1 == right.1) = false) := by decide

private noncomputable def before (first second : Word) : State :=
  let native := X86Move.putPointer (put (put seed.native 12 second) 11 first) (address 4096 0)
  { native with mem := Std.ExtHashMap.ofList cells }

private theorem physical (index : Nat) (within : index < 24) :
    ((address 4096 index).signExtend 52).toNat = 4096 + index := by interval_cases index <;> decide

private theorem loaded (first second : Word) :
    X86CodePlacement.Placed (before first second) 4096 (view emission.bytes) := by
  intro index byte present
  change emission.bytes[index]? = some byte at present
  have within := (List.getElem?_eq_some_iff.mp present).1
  have actual : emission.bytes[index]'within = byte :=
    Option.some.inj ((List.getElem?_eq_getElem within).symm.trans present)
  have member : (4096 + index,byte) ∈ cells := by
    apply List.mem_map.mpr
    refine ⟨⟨index,within⟩,by simp,?_⟩
    simp only [actual]
  rw [physical index (by change index < 24 at within; exact within)]
  simp only [before]
  exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) distinct member

private noncomputable def origin (first second : Word) : X86LegacyFetch.Basis (before first second) where
  address := address 4096 0
  opcodeAddress := address 4096 1
  modrmAddress := address 4096 2
  next := address 4096 3
  control := seed.origin.control
  attributes := seed.origin.attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert] using seed.origin.status
  fault := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert] using seed.origin.fault
  msrs := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert] using seed.origin.msrs
  segments := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert] using seed.origin.segments
  longMode := seed.origin.longMode
  codeMode := seed.origin.codeMode
  application := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert] using seed.origin.application
  rip := by simp [before,X86Move.putPointer]

private noncomputable def entry (first second : Word) : Entry 11 0 emission (before first second) where
  base := 4096
  origin := origin first second
  lower := by decide
  upper := by decide
  location := by change (address 4096 0).toInt = (4096 : Int) + (0 : Nat); decide
  loaded := loaded first second
  value := first
  known := by
    change X86RegisterRefinement.lookup
      (X86Move.putPointer (put (put seed.native 12 second) 11 first) (address 4096 0)) 11 = some first
    rw [X86Move.lookup_putPointer]
    exact lookup_put_same _ 11 _
  flags := seed.flags
  flagsKnown := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert] using seed.flagsKnown
  quiet := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert] using seed.quiet

def keys : Finset (Control.Location Nat) := {.inl 0,.inr 0,.inr 1}
def earlyKeys : Finset (Control.Location Nat) := {.inl 0,.inr 0}
def values (first second : Word) : Control.Location Nat → Word
  | .inl _ => 100
  | .inr 0 => first
  | .inr _ => second

theorem second_outcomes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (second : Word) (canonical : second = 0 ∨ second = 1) :
    letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ middle after,
      (CellEffects.profile [left.recipe,right.recipe]).theory.rewrites (Cells.encode keys (values 1 second))
        (Cells.encode keys (Function.update (values 1 second) (.inl 0) 101)) ∧
      (CellEffects.profile [left.recipe,right.recipe]).theory.rewrites
        (Cells.encode keys (Function.update (values 1 second) (.inl 0) 101))
        (Cells.encode keys (Function.update (Function.update (values 1 second) (.inl 0) 101)
          (.inl 0) (chosen right second))) ∧
      (X86FuelPrefix.fetches 2).run (before 1 second) = .ok () middle ∧
      (X86FuelPrefix.fetches 2).run middle = .ok () after ∧
      (X86FuelPrefix.fetches 4).run (before 1 second) = .ok () after ∧
      after.regs.get? .rip = some ((address 4096 (if second = (0#64) then 23 else 18)).signExtend 64) ∧
      RegisterFrame X86BranchGate.writes (before 1 second) after ∧
      ∀ count ≤ 4, ∀ observed, (X86FuelPrefix.fetches count).run (before 1 second) = .ok () observed →
        RegisterFrame X86BranchGate.writes (before 1 second) observed := by
  let : OtherOpcodeHandlers := X86BranchGate.handlers other extra
  let : VectorOpcodeHandlers := vector
  have known : X86RegisterRefinement.lookup (before 1 second) 12 = some second := by
    change X86RegisterRefinement.lookup
      (X86Move.putPointer (put (put seed.native 12 second) 11 1) (address 4096 0)) 12 = some second
    rw [X86Move.lookup_putPointer,lookup_put_other _ 11 12 _ (by decide)]
    exact lookup_put_same _ 12 _
  obtain ⟨middle,after,resolved,target,firstStep,secondStep,firstRun,secondRun,full,frame,
    _image,_control,bound,output,pointer,prefixes⟩ :=
    fallthrough other extra vector [] tail left right 11 12 emission assembled rfl rfl
      (before 1 second) (entry 1 second) keys (values 1 second) (by decide) (by decide) rfl rfl rfl
      second rfl known canonical
  have same : resolved = labels := Option.some.inj (bound.symm.trans boundaries)
  rw [same] at output
  have destination : target = if second = (0#64) then 23 else 18 := by
    have expected : X86Assembler.lookup labels (chosen right second).toNat =
        some (if second = (0#64) then 23 else 18) := by
      by_cases zero : second = (0#64) <;> simp [chosen,zero,right,labels,X86Assembler.lookup]
    exact Option.some.inj (output.symm.trans expected)
  rw [destination] at pointer
  exact ⟨middle,after,firstStep,secondStep,firstRun,secondRun,full,pointer,frame,prefixes⟩

theorem skipped_resource_missing : .inr 1 ∉ earlyKeys ∧ ¬ right.recipe.support ⊆ earlyKeys := by decide

theorem second_nonboolean_refused (result : Multiset (Cells.Cell (Control.Location Nat))) :
    ¬ (CellEffects.profile [left.recipe,right.recipe]).theory.rewrites
      (Cells.encode keys (Function.update (values 1 2) (.inl 0) 101)) result := by
  intro source
  obtain ⟨recipe,member,produced,_support,guarded,_endpoint⟩ :=
    (CellEffects.profile_rewrite_iff [left.recipe,right.recipe] keys _ result).mp source
  rcases List.mem_cons.mp member with same | rest
  · rw [same] at guarded
    have current := ((left.guard_iff _ produced).mp guarded).1
    simp [left] at current
  · have same := List.mem_singleton.mp rest
    rw [same] at guarded
    have target := ((right.guard_iff _ produced).mp guarded).2
    have refused : right.target? ((Function.update (values 1 2) (.inl 0) 101) (.inr right.condition)) = none := by decide
    rw [refused] at target
    cases target

theorem early_skips_missing_resource (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after,
      (CellEffects.profile [left.recipe,right.recipe]).theory.rewrites (Cells.encode earlyKeys (values 0 2))
        (Cells.encode earlyKeys (Function.update (values 0 2) (.inl 0) 102)) ∧
      (X86FuelPrefix.fetches 2).run (before 0 2) = .ok () after ∧
      after.regs.get? .rip = some ((address 4096 23).signExtend 64) ∧
      RegisterFrame X86BranchGate.writes (before 0 2) after := by
  let : OtherOpcodeHandlers := X86BranchGate.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,resolved,target,source,run,frame,_image,_control,bound,output,pointer,_prefixes⟩ :=
    early_exit other extra vector [] tail left right 11 12 emission assembled rfl
      (before 0 2) (entry 0 2) earlyKeys (values 0 2) (by decide) rfl rfl rfl
  have same : resolved = labels := Option.some.inj (bound.symm.trans boundaries)
  rw [same] at output
  have expected : X86Assembler.lookup labels left.no.toNat = some 23 := by decide
  have destination : target = 23 := Option.some.inj (output.symm.trans expected)
  rw [destination] at pointer
  exact ⟨after,source,run,pointer,frame⟩

end Mettapedia.Machines.TIsa.X86BranchRegion.Controls
