import Mettapedia.Machines.TIsa.X86MixedRegion

/-!
# Mixed region with initially absent destinations

A self-copy is elided, a live input is copied into an uninitialized physical
destination, and the branch either skips arithmetic or initializes another
destination with ADD. Source steps retain the zero-cost control transition.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86MixedRegion.Controls
open _root_.X86Registers X86RegisterRefinement X86Execution X86Assembler
local instance : MemoryPrimitives := X86Memory.ordinary

def elision : Node := .word ⟨0,99,100,.inl (.copy ⟨1,1,by decide⟩)⟩
def copy : Node := .word ⟨0,100,101,.inl (.copy ⟨1,7,by decide⟩)⟩
def choice : Node := .branch ⟨0,101,7,102,104⟩
def addition : Node := .word ⟨0,102,103,.inl (.binary 0 2 7 1 (by decide))⟩
def program : List Node := [elision,copy,choice,addition]
def live (point : Word) : Finset Key :=
  if point = 99 ∨ point = 100 then {1}
  else if point = 101 ∨ point = 102 then {1,7}
  else if point = 103 then {2} else ∅
def tail : List Chunk := [.bytes [0x90,0x90,0x90,0x90,0x90],.label 104,.bytes [0x90]]
def emission : Emission :=
  ⟨[0x49,0x89,0xf3,0x4d,0x85,0xdb,0x0f,0x84,14,0,0,0,
    0x4d,0x89,0xde,0x49,0x01,0xf6,0x4c,0x89,0xf2,0x90,0x90,0x90,0x90,0x90,0x90],
    [⟨6,some 4,104,26⟩]⟩
def labels : Labels := [(99,0),(100,0),(101,3),(102,12),(103,21),(104,26)]

theorem compiled : compile? live 0 103 program [] tail = some emission := by decide
theorem boundaries : labelsAt 0 (code 103 program [] tail) = some labels := by decide
theorem actual_labels (layout : Layout live 0 103 program [] tail emission) : layout.labels = labels :=
  Option.some.inj (layout.resolved.symm.trans boundaries)

def badLive (point : Word) : Finset Key := if point = 101 then {1} else live point
def badTransfer (point : Word) : Finset Key := if point = 100 then {1,7} else live point
theorem missing_live_input_refused : compile? badLive 0 103 program [] tail = none := by decide
theorem missing_live_transfer_refused : compile? badTransfer 0 103 program [] tail = none := by decide
theorem same_raw_bytes : assemble (code 103 program [] tail) = some emission := by decide
theorem colocated_points :
    X86Assembler.lookup labels 99 = X86Assembler.lookup labels 100 ∧ (99#64) ≠ (100#64) := by decide

theorem elided_exit_address_admitted : checkExitOffsets labels program [100] = true := by decide

theorem executing_exit_collision_refused : checkExitOffsets labels program [99] = false := by decide

theorem whole_template_exits_admitted : checkExitSpans labels program [103,104] = true := by decide

theorem exit_between_test_and_jump_refused :
    checkExitOffsets ((105,6) :: labels) program [105] = true ∧
      checkExitSpans ((105,6) :: labels) program [105] = false := by
  constructor <;> decide

def duplicatePoints : List Node := [.word ⟨0,100,100,.inl (.copy ⟨1,1,by decide⟩)⟩,copy,choice,addition]

theorem duplicate_logical_point_refused :
    Valid live 0 103 duplicatePoints ∧ compile? live 0 103 duplicatePoints [] tail = none := by
  constructor <;> decide

def uninitializedSelf : List Node := [.word ⟨0,99,100,.inl (.copy ⟨7,7,by decide⟩)⟩,copy,choice,addition]
theorem unreadable_elision_same_bytes : assemble (code 103 uninitializedSelf [] tail) = some emission := by decide
theorem unreadable_elision_refused : compile? live 0 103 uninitializedSelf [] tail = none := by decide

def keys : Finset Location := {.inl 0,.inr 1,.inr 7,.inr 2}
def initial (take : Bool) : Values
  | .inl activation => if activation = 0 then 99 else 0
  | .inr register => if register = 1 then (if take then 1 else 0) else 0
def afterElision (take : Bool) := elision.nextValues (initial take)
def afterCopy (take : Bool) := copy.nextValues (afterElision take)
def afterChoice (take : Bool) := choice.nextValues (afterCopy take)
def afterAdd := addition.nextValues (afterChoice true)

theorem self_source (take : Bool) :
    Counted program (Cells.encode keys (initial take),0) (Cells.encode keys (afterElision take),0) := by
  apply counted_realized program elision (by simp [program]) keys (initial take) (afterElision take) 0 (by decide)
  cases take <;> decide

theorem copy_source (take : Bool) :
    Counted program (Cells.encode keys (afterElision take),0) (Cells.encode keys (afterCopy take),1) := by
  apply counted_realized program copy (by simp [program]) keys (afterElision take) (afterCopy take) 0 (by decide)
  cases take <;> decide

theorem branch_source (take : Bool) :
    Counted program (Cells.encode keys (afterCopy take),1) (Cells.encode keys (afterChoice take),3) := by
  apply counted_realized program choice (by simp [program]) keys (afterCopy take) (afterChoice take) 1 (by decide)
  cases take <;> decide

theorem add_source :
    Counted program (Cells.encode keys (afterChoice true),3) (Cells.encode keys afterAdd,6) := by
  apply counted_realized program addition (by simp [program]) keys (afterChoice true) afterAdd 3 (by decide) (by decide)

theorem prefix_source (take : Bool) :
    Relation.ReflTransGen (Counted program) (Cells.encode keys (initial take),0) (Cells.encode keys (afterChoice take),3) :=
  ((Relation.ReflTransGen.single (self_source take)).tail (copy_source take)).tail (branch_source take)
theorem success_source :
    Relation.ReflTransGen (Counted program) (Cells.encode keys (initial true),0) (Cells.encode keys afterAdd,6) :=
  (prefix_source true).tail add_source

private noncomputable abbrev seed := X86BranchGate.Controls.entryFixture 6 0
private noncomputable abbrev seedOrigin := seed.2.toBasis
private def cells : List (Nat × Byte) := (List.finRange emission.bytes.length).map (fun index =>
  (4096 + index.val,emission.bytes[index.val]'index.isLt))
private theorem distinct : cells.Pairwise (fun left right => (left.1 == right.1) = false) := by decide

private noncomputable def before (take : Bool) : State :=
  let regs := ((seed.1.regs.erase .r11).erase .rdx).erase .r14
  let native := { seed.1 with regs := regs, mem := Std.ExtHashMap.ofList cells }
  X86Move.putPointer (put native 6 (if take then (1#64) else (0#64))) (address 4096 0)

theorem physical_one : physical 1 = (6 : Fin 16) := by decide
theorem physical_seven : physical 7 = (11 : Fin 16) := by decide
theorem physical_two : physical 2 = (2 : Fin 16) := by decide
theorem scratch_fourteen : X86BinCapture.scratch = (14 : Fin 16) := by decide

theorem absent_destinations (take : Bool) :
    X86RegisterRefinement.lookup (before take) (physical 7) = none ∧
    X86RegisterRefinement.lookup (before take) (physical 2) = none ∧
    X86RegisterRefinement.lookup (before take) X86BinCapture.scratch = none := by
  rw [physical_seven,physical_two,scratch_fourteen]
  simp [before,put,X86Move.putPointer,X86RegisterRefinement.lookup,key,Std.ExtDHashMap.get?_insert,Std.ExtDHashMap.get?_erase]

private theorem physical_address (index : Nat) (within : index < 27) :
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
  rw [physical_address index (by change index < 27 at within; exact within)]
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
  status := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert,Std.ExtDHashMap.get?_erase] using seedOrigin.status
  fault := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert,Std.ExtDHashMap.get?_erase] using seedOrigin.fault
  msrs := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert,Std.ExtDHashMap.get?_erase] using seedOrigin.msrs
  segments := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert,Std.ExtDHashMap.get?_erase] using seedOrigin.segments
  longMode := seedOrigin.longMode
  codeMode := seedOrigin.codeMode
  application := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert,Std.ExtDHashMap.get?_erase] using seedOrigin.application
  rip := by simp [before,X86Move.putPointer]

private noncomputable def ready (take : Bool) (layout : Layout live 0 103 program [] tail emission) :
    Ready layout 4096 (initial take) (before take) where
  origin := origin take
  lower := by decide
  upper := by decide
  offset := 0
  control := by rw [actual_labels layout]; change X86Assembler.lookup labels 99 = some 0; decide
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
  flags := seed.2.flags
  flagsKnown := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert,Std.ExtDHashMap.get?_erase] using seed.2.flagsKnown
  quiet := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert,Std.ExtDHashMap.get?_erase] using seed.2.quiet

theorem elision_reflects (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (take : Bool) (layout : Layout live 0 103 program [] tail emission) :
    ∃ next : Ready layout 4096 (afterElision take) (before take), next.offset = 0 ∧
      Counted program (Cells.encode keys (initial take),0) (Cells.encode keys (afterElision take),0) := by
  let : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
  let : VectorOpcodeHandlers := vector
  have steps : elision.count = 0 := by decide
  have run : (X86FuelPrefix.fetches elision.count).run (before take) = .ok () (before take) := by
    rw [steps]
    exact X86FuelPrefix.fetches_zero (before take)
  obtain ⟨next,source,_,_⟩ := reflect_native_node layout other extra vector elision (by simp [program])
    keys (initial take) (before take) (before take) (ready take layout) 0 (by decide) (by rfl)
    (by intro choice impossible; cases impossible) run
  refine ⟨next,?_,?_⟩
  · have control := next.control
    rw [actual_labels layout] at control
    have point : afterElision take (.inl 0) = 100 := by cases take <;> decide
    change X86Assembler.lookup labels (afterElision take (.inl 0)).toNat = some next.offset at control
    rw [point] at control
    exact Option.some.inj (control.symm.trans (by decide : X86Assembler.lookup labels 100 = some 0))
  · simpa only [afterElision,steps,Nat.add_zero] using source

theorem zero_fuel_reaches_logical_exit (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (take : Bool) (layout : Layout live 0 103 program [] tail emission) :
    ∃ _ : Ready layout 4096 (afterElision take) (before take),
      Relation.ReflTransGen (Counted program) (Cells.encode keys (initial take),0)
        (Cells.encode keys (afterElision take),0) := by
  let : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
  let : VectorOpcodeHandlers := vector
  let admitted (values : Values) := values = initial take ∨ values = afterElision take
  have entry : ∀ values, admitted values → values (.inl 0) ∉ ([100] : List Word) →
      ∃ node ∈ program, values (.inl 0) = node.point ∧
        (∀ choice, node = .branch choice →
          values (.inr choice.condition) = 0 ∨ values (.inr choice.condition) = 1) ∧
        admitted (node.nextValues values) := by
    rintro values (rfl | rfl) outside
    · refine ⟨elision,by simp [program],rfl,?_,Or.inr rfl⟩
      intro choice impossible
      cases impossible
    · exact (outside (by cases take <;> decide)).elim
  have resources : ∀ node ∈ program, node.recipe.support ⊆ keys := by
    intro node member
    simp only [program,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  have checked : checkExitSpans layout.labels program [100] = true := by
    rw [actual_labels layout]
    decide
  obtain ⟨fuel, observed, following, input, within, run, _, _, known, atExit, path, _, _⟩ :=
    first_exit_of_counted layout other extra vector [100] keys admitted entry resources checked
      (initial take) (afterElision take) (before take) (ready take layout) (Or.inl rfl) 0 0
      (by decide) (by cases take <;> decide) (Relation.ReflTransGen.single (self_source take))
  have zero : fuel = 0 := by omega
  subst fuel
  have same := X86FuelPrefix.fetches_deterministic 0 (before take) observed (before take)
    run (X86FuelPrefix.fetches_zero (before take))
  subst observed
  rcases known with first | last
  · subst following
    exact ((by cases take <;> decide : initial take (.inl 0) ∉ ([100] : List Word)) atExit).elim
  · subst following
    exact ⟨input,path⟩

theorem later_row_requires_later_point (take : Bool) (written : Values) :
    copy.recipe.guard (copy.recipe.inputs.map (initial take)) (copy.recipe.outputs.map written) ≠ true := by
  intro guard
  have point := copy.source_point (initial take) written guard
  change (99#64) = (100#64) at point
  exact (by decide : (99#64) ≠ (100#64)) point

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
    ∃ after, (X86FuelPrefix.fetches 6).run (before true) = .ok () after ∧
      X86RegisterRefinement.lookup after (physical 2) = some (2#64) ∧
      after.regs.get? .rip = some ((address 4096 21).signExtend 64) ∧
      RegisterFrame (footprint program) (before true) after ∧
      X86CodePlacement.Placed after 4096 (view emission.bytes) ∧ X86ControlFlags.Preserved (before true) after ∧
      ∀ count ≤ 6, ∀ observed, (X86FuelPrefix.fetches count).run (before true) = .ok () observed →
        RegisterFrame (footprint program) (before true) observed := by
  let : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨layout⟩ := ofCompilation live 0 103 program [] tail emission compiled
  obtain ⟨nextValues,after,next,_monotone,endpoint,run,frame,control,prefixes⟩ :=
    realizes_counted layout other extra vector keys (initial true) (before true) (ready true layout) 0
      (Cells.encode keys afterAdd,6) success_source
  have agree := ((Cells.encode_le_iff keys keys nextValues afterAdd).mp (le_of_eq endpoint.symm)).2
  have current : nextValues (.inl 0) = (103#64) := (agree _ (by decide)).trans (by decide)
  have value : nextValues (.inr 2) = (2#64) := (agree _ (by decide)).trans (by decide)
  have result := next.reads 2 (by rw [current]; decide)
  rw [value] at result
  exact ⟨after,run,result,pointer_at layout nextValues after next 103 21 current (by decide),
    frame,next.loaded,control,prefixes⟩

theorem early_exit (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 3).run (before false) = .ok () after ∧
      after.regs.get? .rip = some ((address 4096 26).signExtend 64) ∧
      RegisterFrame (footprint program) (before false) after ∧
      ∀ count ≤ 3, ∀ observed, (X86FuelPrefix.fetches count).run (before false) = .ok () observed →
        RegisterFrame (footprint program) (before false) observed := by
  let : OtherOpcodeHandlers := X86DataPrimitive.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨layout⟩ := ofCompilation live 0 103 program [] tail emission compiled
  obtain ⟨nextValues,after,next,_monotone,endpoint,run,frame,_control,prefixes⟩ :=
    realizes_counted layout other extra vector keys (initial false) (before false) (ready false layout) 0
      (Cells.encode keys (afterChoice false),3) (prefix_source false)
  have agree := ((Cells.encode_le_iff keys keys nextValues (afterChoice false)).mp (le_of_eq endpoint.symm)).2
  have current : nextValues (.inl 0) = (104#64) := (agree _ (by decide)).trans (by decide)
  exact ⟨after,run,pointer_at layout nextValues after next 104 26 current (by decide),frame,prefixes⟩

#print axioms reflect_native_prefix
#print axioms settle_native_exit
#print axioms reflect_native_exit
#print axioms first_exit_of_counted
#print axioms exit_between_test_and_jump_refused
#print axioms elision_reflects
#print axioms zero_fuel_reaches_logical_exit
#print axioms later_row_requires_later_point
#print axioms duplicate_logical_point_refused

end Mettapedia.Machines.TIsa.X86MixedRegion.Controls
