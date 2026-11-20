import Mettapedia.Machines.TIsa.X86BranchGraph

/-!
# Finite branch-region compiler controls

A three-test region and a backward cycle share the same compiler and native
path theorem. Bad fallthrough and foreign control ownership retain identical
raw bytes but are refused by structural admission.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86BranchGraph.Controls
open _root_.X86Registers X86RegisterRefinement X86Execution X86Assembler X86BranchCompiler
local instance : MemoryPrimitives := X86Memory.ordinary

def registers (key : Nat) : Fin 16 := if key = 0 then 11 else if key = 1 then 12 else 13
def firstBranch : Control.Branch Nat := ⟨0,100,0,101,104⟩
def secondBranch : Control.Branch Nat := ⟨0,101,1,102,104⟩
def thirdBranch : Control.Branch Nat := ⟨0,102,2,103,104⟩
def loopBranch : Control.Branch Nat := ⟨0,100,0,103,100⟩
def branches (chain : Bool) : List (Control.Branch Nat) :=
  if chain then [firstBranch,secondBranch,thirdBranch] else [loopBranch]
def tail (chain : Bool) : List Chunk :=
  if chain then [.bytes [0x90,0x90,0x90,0x90,0x90],.label 104,.bytes [0x90]] else [.bytes [0x90]]
def emission (chain : Bool) : Emission :=
  if chain then
    ⟨[0x4d,0x85,0xdb,0x0f,0x84,23,0,0,0,
      0x4d,0x85,0xe4,0x0f,0x84,14,0,0,0,
      0x4d,0x85,0xed,0x0f,0x84,5,0,0,0,0x90,0x90,0x90,0x90,0x90,0x90],
      [⟨3,some 4,104,32⟩,⟨12,some 4,104,32⟩,⟨21,some 4,104,32⟩]⟩
  else ⟨[0x4d,0x85,0xdb,0x0f,0x84,0xf7,0xff,0xff,0xff,0x90],[⟨3,some 4,100,0⟩]⟩
def labels (chain : Bool) : Labels :=
  if chain then [(100,0),(101,9),(102,18),(103,27),(104,32)] else [(100,0),(103,9)]

theorem compiled (chain : Bool) :
    compile? registers 0 103 (branches chain) [] (tail chain) = some (emission chain) := by
  cases chain <;> decide

theorem boundaries (chain : Bool) :
    labelsAt 0 (code registers 103 (branches chain) [] (tail chain)) = some (labels chain) := by
  cases chain <;> decide

theorem exit_offsets_checked (chain : Bool) :
    checkExitOffsets (labels chain) ((branches chain).map Control.Branch.point)
      (if chain then [103,104] else [103]) = true := by
  cases chain <;> decide

theorem collocated_exit_refused :
    checkExitOffsets [(100,0),(103,0)] [100] [103] = false := by decide

theorem actual_labels (chain : Bool) (layout : Layout registers 0 103 (branches chain) [] (tail chain) (emission chain)) :
    layout.labels = labels chain := Option.some.inj (layout.resolved.symm.trans (boundaries chain))

private noncomputable abbrev seed := X86BranchGate.Controls.entryFixture 0 0
private noncomputable abbrev seedOrigin := seed.2.toBasis
private def cells (chain : Bool) : List (Nat × Byte) :=
  (List.finRange (emission chain).bytes.length).map (fun index =>
    (4096 + index.val,(emission chain).bytes[index.val]'index.isLt))
private theorem distinct (chain : Bool) :
    (cells chain).Pairwise (fun left right => (left.1 == right.1) = false) := by cases chain <;> decide

private noncomputable def before (chain : Bool) (first second third : Word) : State :=
  let native := X86Move.putPointer (put (put (put seed.1 13 third) 12 second) 11 first) (address 4096 0)
  { native with mem := Std.ExtHashMap.ofList (cells chain) }

private theorem physical (index : Nat) (within : index < 33) :
    ((address 4096 index).signExtend 52).toNat = 4096 + index := by interval_cases index <;> decide

private theorem loaded (chain : Bool) (first second third : Word) :
    X86CodePlacement.Placed (before chain first second third) 4096 (view (emission chain).bytes) := by
  intro index byte present
  change (emission chain).bytes[index]? = some byte at present
  have within := (List.getElem?_eq_some_iff.mp present).1
  have small : (emission chain).bytes.length ≤ 33 := by cases chain <;> decide
  have actual : (emission chain).bytes[index]'within = byte :=
    Option.some.inj ((List.getElem?_eq_getElem within).symm.trans present)
  have member : (4096 + index,byte) ∈ cells chain := by
    apply List.mem_map.mpr
    refine ⟨⟨index,within⟩,by simp,?_⟩
    simp only [actual]
  rw [physical index (by omega)]
  simp only [before]
  exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (distinct chain) member

private noncomputable def origin (chain : Bool) (first second third : Word) :
    X86LegacyFetch.Basis (before chain first second third) where
  address := address 4096 0
  opcodeAddress := address 4096 1
  modrmAddress := address 4096 2
  next := address 4096 3
  control := seedOrigin.control
  attributes := seedOrigin.attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert] using seedOrigin.status
  fault := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert] using seedOrigin.fault
  msrs := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert] using seedOrigin.msrs
  segments := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert] using seedOrigin.segments
  longMode := seedOrigin.longMode
  codeMode := seedOrigin.codeMode
  application := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert] using seedOrigin.application
  rip := by simp [before,X86Move.putPointer]

private theorem known (chain : Bool) (first second third : Word) :
    X86RegisterRefinement.lookup (before chain first second third) 11 = some first ∧
    X86RegisterRefinement.lookup (before chain first second third) 12 = some second ∧
    X86RegisterRefinement.lookup (before chain first second third) 13 = some third := by
  change X86RegisterRefinement.lookup
    (X86Move.putPointer (put (put (put seed.1 13 third) 12 second) 11 first) (address 4096 0)) 11 = _ ∧ _
  simp only [X86Move.lookup_putPointer]
  refine ⟨lookup_put_same _ _ _,?_,?_⟩
  · change X86RegisterRefinement.lookup
      (X86Move.putPointer (put (put (put seed.1 13 third) 12 second) 11 first) (address 4096 0)) 12 = some second
    rw [X86Move.lookup_putPointer,lookup_put_other _ 11 12 _ (by decide)]
    exact lookup_put_same _ _ _
  · change X86RegisterRefinement.lookup
      (X86Move.putPointer (put (put (put seed.1 13 third) 12 second) 11 first) (address 4096 0)) 13 = some third
    rw [X86Move.lookup_putPointer,lookup_put_other _ 11 13 _ (by decide),lookup_put_other _ 12 13 _ (by decide)]
    exact lookup_put_same _ _ _

def values (point first second third : Word) : Control.Location Nat → Word
  | .inl activation => if activation = 0 then point else 0
  | .inr key => if key = 0 then first else if key = 1 then second else third

def keys : Finset (Control.Location Nat) := {.inl 0,.inr 0,.inr 1,.inr 2}
def earlyKeys : Finset (Control.Location Nat) := {.inl 0,.inr 0}
def middleKeys : Finset (Control.Location Nat) := {.inl 0,.inr 0,.inr 1}
def noConditions : Finset (Control.Location Nat) := {.inl 0}

theorem update_values (point next first second third : Word) :
    Function.update (values point first second third) (.inl 0) next = values next first second third := by
  funext location
  cases location with
  | inl activation => by_cases same : activation = 0 <;> simp [values,same]
  | inr key => simp [values]

private noncomputable def ready (chain : Bool) (first second third : Word)
    (layout : Layout registers 0 103 (branches chain) [] (tail chain) (emission chain))
    (held : Finset (Control.Location Nat)) :
    Ready layout 4096 held (values 100 first second third) (before chain first second third) where
  origin := origin chain first second third
  lower := by decide
  upper := by cases chain <;> decide
  offset := 0
  control := by
    rw [actual_labels chain layout]
    change X86Assembler.lookup (labels chain) 100 = some 0
    cases chain <;> decide
  location := by change (address 4096 0).toInt = (4096 : Int) + (0 : Nat); decide
  loaded := loaded chain first second third
  reads := by
    intro branch member _present
    obtain ⟨knownFirst,knownSecond,knownThird⟩ := known chain first second third
    cases chain with
    | false =>
      have same : branch = loopBranch := by simpa [branches] using member
      subst branch
      exact knownFirst
    | true =>
      have listed : branch = firstBranch ∨ branch = secondBranch ∨ branch = thirdBranch := by simpa [branches] using member
      rcases listed with rfl | rfl | rfl
      · exact knownFirst
      · exact knownSecond
      · exact knownThird
  flags := seed.2.flags
  flagsKnown := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert] using seed.2.flagsKnown
  quiet := by simpa [before,put,X86Move.putPointer,key,Std.ExtDHashMap.get?_insert] using seed.2.quiet

def wrongFlow : List (Control.Branch Nat) := [{firstBranch with yes := 999},secondBranch,thirdBranch]
def wrongOwner : List (Control.Branch Nat) := [{firstBranch with activation := 1},secondBranch,thirdBranch]

theorem wrong_flow_same_bytes :
    assemble (code registers 103 wrongFlow [] (tail true)) = some (emission true) := by decide
theorem wrong_flow_refused : compile? registers 0 103 wrongFlow [] (tail true) = none := by decide
theorem wrong_owner_same_bytes :
    assemble (code registers 103 wrongOwner [] (tail true)) = some (emission true) := by decide
theorem wrong_owner_refused : compile? registers 0 103 wrongOwner [] (tail true) = none := by decide

theorem source_branch (chain : Bool) (held : Finset (Control.Location Nat))
    (branch : Control.Branch Nat) (member : branch ∈ branches chain) (owner : branch.activation = 0)
    (point next first second third : Word) (included : branch.recipe.support ⊆ held)
    (current : point = branch.point)
    (target : branch.target? (values point first second third (.inr branch.condition)) = some next) :
    (CellEffects.profile ((branches chain).map Control.Branch.recipe)).theory.rewrites
      (Cells.encode held (values point first second third)) (Cells.encode held (values next first second third)) := by
  obtain ⟨invocation,enabled,fired⟩ := branch.realized held (values point first second third) next included
    (by simp [values,owner,current]) target
  have source := X86BranchRegion.system_step_in ((branches chain).map Control.Branch.recipe) branch.recipe
    (List.mem_map.mpr ⟨branch,member,rfl⟩) invocation held (values point first second third) _ enabled fired
  rw [owner,update_values] at source
  exact source

def world (held : Finset (Control.Location Nat)) (point first second third : Word) :=
  Cells.encode held (values point first second third)

theorem three_source :
    List.IsChain (CellEffects.profile ((branches true).map Control.Branch.recipe)).theory.rewrites
      [world keys 100 1 1 1,world keys 101 1 1 1,world keys 102 1 1 1,world keys 103 1 1 1] := by
  refine List.isChain_cons_cons.mpr ⟨?_,List.isChain_cons_cons.mpr ⟨?_,List.isChain_cons_cons.mpr ⟨?_,.singleton _⟩⟩⟩
  · exact source_branch true keys firstBranch (by simp [branches]) rfl 100 101 1 1 1 (by decide) rfl (by decide)
  · exact source_branch true keys secondBranch (by simp [branches]) rfl 101 102 1 1 1 (by decide) rfl (by decide)
  · exact source_branch true keys thirdBranch (by simp [branches]) rfl 102 103 1 1 1 (by decide) rfl (by decide)

theorem exit_ready (chain : Bool) (held : Finset (Control.Location Nat))
    (layout : Layout registers 0 103 (branches chain) [] (tail chain) (emission chain))
    (nextValues : Control.Location Nat → Word) (native : State)
    (input : Ready layout 4096 held nextValues native) (point first second third : Word)
    (controlPresent : .inl 0 ∈ held) (target : Nat)
    (named : X86Assembler.lookup (labels chain) point.toNat = some target)
    (sameWorld : Cells.encode held nextValues = world held point first second third) :
    native.regs.get? .rip = some ((address 4096 target).signExtend 64) := by
  have agree := ((Cells.encode_le_iff held held nextValues (values point first second third)).mp (le_of_eq sameWorld)).2
  let output := Ready.revalue layout input (values point first second third) controlPresent agree
  have bound := output.control
  rw [actual_labels chain layout] at bound
  change X86Assembler.lookup (labels chain) point.toNat = some output.offset at bound
  have position : output.offset = target := Option.some.inj (bound.symm.trans named)
  have pointer := Ready.pointer layout output
  rw [position] at pointer
  exact pointer

theorem three_native (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 6).run (before true 1 1 1) = .ok () after ∧
      after.regs.get? .rip = some ((address 4096 27).signExtend 64) ∧
      RegisterFrame X86BranchGate.writes (before true 1 1 1) after ∧
      X86CodePlacement.Placed after 4096 (view (emission true).bytes) ∧
      X86ControlFlags.Preserved (before true 1 1 1) after ∧
      ∀ count ≤ 6, ∀ observed, (X86FuelPrefix.fetches count).run (before true 1 1 1) = .ok () observed →
        RegisterFrame X86BranchGate.writes (before true 1 1 1) observed := by
  let : OtherOpcodeHandlers := X86BranchGate.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨layout⟩ := ofCompilation registers 0 103 (branches true) [] (tail true) (emission true) (compiled true)
  obtain ⟨nextValues,after,next,endpoint,run,frame,control,prefixes⟩ :=
    realizes_path other extra vector layout (values 100 1 1 1) (before true 1 1 1) (ready true 1 1 1 layout keys)
      [world keys 101 1 1 1,world keys 102 1 1 1,world keys 103 1 1 1] three_source
  have final : Cells.encode keys nextValues = world keys 103 1 1 1 := endpoint
  exact ⟨after,run,exit_ready true keys layout nextValues after next 103 1 1 1 (by decide) 27 (by decide) final,
    frame,next.loaded,control,prefixes⟩

theorem early_source :
    List.IsChain (CellEffects.profile ((branches true).map Control.Branch.recipe)).theory.rewrites
      [world earlyKeys 100 0 2 2,world earlyKeys 104 0 2 2] := by
  refine List.isChain_cons_cons.mpr ⟨?_,.singleton _⟩
  exact source_branch true earlyKeys firstBranch (by simp [branches]) rfl 100 104 0 2 2 (by decide) rfl (by decide)

theorem early_native (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run (before true 0 2 2) = .ok () after ∧
      after.regs.get? .rip = some ((address 4096 32).signExtend 64) ∧
      RegisterFrame X86BranchGate.writes (before true 0 2 2) after := by
  let : OtherOpcodeHandlers := X86BranchGate.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨layout⟩ := ofCompilation registers 0 103 (branches true) [] (tail true) (emission true) (compiled true)
  obtain ⟨nextValues,after,next,endpoint,run,frame,_control,_prefixes⟩ :=
    realizes_path other extra vector layout (values 100 0 2 2) (before true 0 2 2) (ready true 0 2 2 layout earlyKeys)
      [world earlyKeys 104 0 2 2] early_source
  have final : Cells.encode earlyKeys nextValues = world earlyKeys 104 0 2 2 := endpoint
  exact ⟨after,run,exit_ready true earlyKeys layout nextValues after next 104 0 2 2 (by decide) 32 (by decide) final,frame⟩

theorem middle_source :
    List.IsChain (CellEffects.profile ((branches true).map Control.Branch.recipe)).theory.rewrites
      [world middleKeys 100 1 0 2,world middleKeys 101 1 0 2,world middleKeys 104 1 0 2] := by
  refine List.isChain_cons_cons.mpr ⟨?_,List.isChain_cons_cons.mpr ⟨?_,.singleton _⟩⟩
  · exact source_branch true middleKeys firstBranch (by simp [branches]) rfl 100 101 1 0 2 (by decide) rfl (by decide)
  · exact source_branch true middleKeys secondBranch (by simp [branches]) rfl 101 104 1 0 2 (by decide) rfl (by decide)

theorem middle_native (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 4).run (before true 1 0 2) = .ok () after ∧
      after.regs.get? .rip = some ((address 4096 32).signExtend 64) ∧
      RegisterFrame X86BranchGate.writes (before true 1 0 2) after ∧
      ∀ count ≤ 4, ∀ observed, (X86FuelPrefix.fetches count).run (before true 1 0 2) = .ok () observed →
        RegisterFrame X86BranchGate.writes (before true 1 0 2) observed := by
  let : OtherOpcodeHandlers := X86BranchGate.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨layout⟩ := ofCompilation registers 0 103 (branches true) [] (tail true) (emission true) (compiled true)
  obtain ⟨nextValues,after,next,endpoint,run,frame,_control,prefixes⟩ :=
    realizes_path other extra vector layout (values 100 1 0 2) (before true 1 0 2) (ready true 1 0 2 layout middleKeys)
      [world middleKeys 101 1 0 2,world middleKeys 104 1 0 2] middle_source
  have final : Cells.encode middleKeys nextValues = world middleKeys 104 1 0 2 := endpoint
  exact ⟨after,run,exit_ready true middleKeys layout nextValues after next 104 1 0 2 (by decide) 32 (by decide) final,
    frame,prefixes⟩

theorem missing_active_resource (following : Multiset (Cells.Cell (Control.Location Nat))) :
    ¬ (CellEffects.profile ((branches true).map Control.Branch.recipe)).theory.rewrites
      (world noConditions 100 1 1 1) following := by
  intro source
  obtain ⟨recipe,member,_written,included,_guarded,_endpoint⟩ :=
    (CellEffects.profile_rewrite_iff ((branches true).map Control.Branch.recipe) noConditions _ following).mp source
  obtain ⟨branch,_present,rfl⟩ := List.mem_map.mp member
  have conditionPresent : .inr branch.condition ∈ noConditions :=
    included (by simp [CellEffects.Recipe.support,Control.Branch.recipe])
  simp [noConditions] at conditionPresent

theorem raw_execution_without_source_authority
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run (before true 1 1 1) = .ok () after ∧
      ∀ following, ¬ (CellEffects.profile ((branches true).map Control.Branch.recipe)).theory.rewrites
        (world noConditions 100 1 1 1) following := by
  let : OtherOpcodeHandlers := X86BranchGate.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,run,_pointer,_frame,_image,_control,_prefixes⟩ := three_native other extra vector
  obtain ⟨middle,firstRun,_rest⟩ := X86BlockCompiler.fetches_split 2 4 (before true 1 1 1) after run
  exact ⟨middle,firstRun,missing_active_resource⟩

theorem loop_source (count : Nat) :
    List.IsChain (CellEffects.profile ((branches false).map Control.Branch.recipe)).theory.rewrites
      (world earlyKeys 100 0 2 2 :: List.replicate count (world earlyKeys 100 0 2 2)) := by
  induction count with
  | zero => exact .singleton _
  | succ count ih =>
    refine List.isChain_cons_cons.mpr ⟨?_,ih⟩
    exact source_branch false earlyKeys loopBranch (by simp [branches]) rfl 100 100 0 2 2 (by decide) rfl (by decide)

theorem repeated_last {α : Type} (value : α) (count : Nat) : (List.replicate count value).getLastD value = value := by
  induction count with
  | zero => rfl
  | succ count ih => simpa only [List.replicate_succ,List.getLastD_cons] using ih

theorem loop_native (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (count : Nat) :
    letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (2 * count)).run (before false 0 2 2) = .ok () after ∧
      after.regs.get? .rip = some ((address 4096 0).signExtend 64) ∧
      RegisterFrame X86BranchGate.writes (before false 0 2 2) after ∧
      ∀ prefixCount ≤ 2 * count, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run (before false 0 2 2) = .ok () observed →
          RegisterFrame X86BranchGate.writes (before false 0 2 2) observed := by
  let : OtherOpcodeHandlers := X86BranchGate.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨layout⟩ := ofCompilation registers 0 103 (branches false) [] (tail false) (emission false) (compiled false)
  obtain ⟨nextValues,after,next,endpoint,run,frame,_control,prefixes⟩ :=
    realizes_path other extra vector layout (values 100 0 2 2) (before false 0 2 2) (ready false 0 2 2 layout earlyKeys)
      (List.replicate count (world earlyKeys 100 0 2 2)) (loop_source count)
  have final : Cells.encode earlyKeys nextValues = world earlyKeys 100 0 2 2 :=
    endpoint.trans (repeated_last (world earlyKeys 100 0 2 2) count)
  exact ⟨after,by simpa using run,
    exit_ready false earlyKeys layout nextValues after next 100 0 2 2 (by decide) 0 (by decide) final,
    frame,by simpa using prefixes⟩

theorem reflected_loop (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (count : Nat) (observed : State)
    (run : letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
      letI : VectorOpcodeHandlers := vector
      (X86FuelPrefix.fetches (2 * count)).run (before false 0 2 2) = .ok () observed) :
    ∃ visited : List (Multiset (Cells.Cell (Control.Location Nat))),
      List.IsChain (CellEffects.profile ((branches false).map Control.Branch.recipe)).theory.rewrites
        (world earlyKeys 100 0 2 2 :: visited) ∧
      visited.length = count ∧ RegisterFrame X86BranchGate.writes (before false 0 2 2) observed := by
  let : OtherOpcodeHandlers := X86BranchGate.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨layout⟩ := ofCompilation registers 0 103 (branches false) [] (tail false) (emission false) (compiled false)
  let exits : List Word := [103]
  have targets : ∀ branch ∈ branches false,
      (branch.yes ∈ exits ∨ branch.yes ∈ (branches false).map Control.Branch.point) ∧
      (branch.no ∈ exits ∨ branch.no ∈ (branches false).map Control.Branch.point) := by
    intro branch member
    have one : branch = loopBranch := by simpa [branches] using member
    subst branch
    decide
  have resources : ∀ branch ∈ branches false, branch.recipe.support ⊆ earlyKeys := by
    intro branch member
    have one : branch = loopBranch := by simpa [branches] using member
    subst branch
    decide
  have canonical : ∀ branch ∈ branches false,
      values 100 0 2 2 (.inr branch.condition) = 0 ∨ values 100 0 2 2 (.inr branch.condition) = 1 := by
    intro branch member
    have one : branch = loopBranch := by simpa [branches] using member
    subst branch
    decide
  have inside : ∀ prefixCount < count, ∀ state,
      (X86FuelPrefix.fetches (2 * prefixCount)).run (before false 0 2 2) = .ok () state →
        ¬ AtExit layout.labels 4096 exits state := by
    intro prefixCount _ state candidate
    obtain ⟨loopState,stepped,atLoop,_frame,_⟩ := loop_native other extra vector prefixCount
    have same := X86FuelPrefix.fetches_deterministic (2 * prefixCount) (before false 0 2 2)
      loopState state stepped candidate
    subst state
    rintro ⟨label,named,offset,found,pointer⟩
    have finish : label = 103 := List.mem_singleton.mp named
    subst label
    rw [actual_labels false layout] at found
    have expected : X86Assembler.lookup (labels false) (103 : Word).toNat = some 9 := by decide
    have exactOffset : offset = 9 := Option.some.inj (found.symm.trans expected)
    subst offset
    have distinct : some ((address 4096 0).signExtend 64) ≠ some ((address 4096 9).signExtend 64) := by decide
    exact distinct (atLoop.symm.trans pointer)
  obtain ⟨_following,_entry,visited,chain,length,_endpoint,_atLabel,frame,_flags,_prefixes⟩ :=
    reflect_native_run other extra vector layout exits targets resources (values 100 0 2 2)
      (before false 0 2 2) observed (ready false 0 2 2 layout earlyKeys) (by decide) canonical count run inside
  exact ⟨visited,chain,length,frame⟩

theorem exit_104_ends_walk (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (layout : Layout registers 0 103 (branches true) [] (tail true) (emission true))
    (count : Nat) (longer : 1 < count) :
    letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ¬ (∀ prefixCount < count, ∀ state,
      (X86FuelPrefix.fetches (2 * prefixCount)).run (before true 0 2 2) = .ok () state →
        ¬ AtExit layout.labels 4096 [103,104] state) := by
  let : OtherOpcodeHandlers := X86BranchGate.handlers other extra
  let : VectorOpcodeHandlers := vector
  intro accepted
  obtain ⟨after,run,pointer,_frame⟩ := early_native other extra vector
  apply accepted 1 longer after run
  refine ⟨104,by simp,32,?_,pointer⟩
  rw [actual_labels true layout]
  decide

#print axioms reflected_loop
#print axioms exit_104_ends_walk
end Mettapedia.Machines.TIsa.X86BranchGraph.Controls
