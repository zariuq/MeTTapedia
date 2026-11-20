import Mettapedia.Machines.TIsa.X86WordLibrary
import Mettapedia.Machines.TIsa.Control

/-!
# Certified word bodies preserve loop data and transfer their continuation

The source actions and native compiler are the existing captured MOV/ADD/SUB
library. A structural write footprint proves readback preservation outside
actual destinations. Native register preservation follows through the checked
block boundary, not from an assumed liveness or compiler-correctness field.

The same body run has an ordered trace of genuine guarded cell recipes over
register/control locations. Data firings keep control resources; a final guarded
control-token transfer records the body's fallthrough without another native
instruction. The native endpoint represents the resulting data and control.
This is a compilation view over existing GSLT actions and resource firings.

Source WP, exact native counts, every-prefix frames and data/control readback
compose for every admitted word body. A wraparound/aliased-add control preserves
its loop index and bound, while unsafe counter writes, changed code and wrong
control labels have separate controls. Whole-loop repetition, actual hosted
admission and non-word body libraries remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86WordBody
open _root_.X86Registers X86RegisterRefinement X86Execution
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.Causality.ResourceInteraction
open X86WordLibrary
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Program := X86BlockCompiler.Program Instruction
abbrev Location := Control.Location (Fin 12)

def writes : Program → Finset (Fin 12)
  | .ret _ => ∅
  | .call instruction next => insert (effect instruction).destination (writes (next ()))

theorem encode_injective (before after : Fin 12 → Word)
    (same : Cells.encode Finset.univ before = Cells.encode Finset.univ after) : before = after := by
  funext register
  have member : (⟨register,before register⟩ : Cells.Cell (Fin 12)) ∈ Cells.encode Finset.univ before :=
    (Cells.mem_encode _ _ _ _).mpr ⟨Finset.mem_univ _,rfl⟩
  rw [same] at member
  exact ((Cells.mem_encode _ _ _ _).mp member).2.symm

theorem source_frame (program : Program) (before : Fin 12 → Word) (following : World)
    (run : program.Runs action (Cells.encode Finset.univ before) () following) :
    ∃ after : Fin 12 → Word, following = Cells.encode Finset.univ after ∧
      ∀ register ∉ writes program, after register = before register := by
  induction program generalizing before following with
  | ret value =>
    obtain ⟨_, same⟩ := run
    exact ⟨before,same.symm,fun _ _ => rfl⟩
  | call instruction next ih =>
    obtain ⟨reply,middle,step,rest⟩ := run
    cases reply
    obtain ⟨result,_,endpoint⟩ := (source_step_iff instruction before middle).mp step
    rw [endpoint] at rest
    obtain ⟨after,encoded,preserved⟩ := ih () _ _ rest
    refine ⟨after,encoded,?_⟩
    intro register outside
    have neither : register ≠ (effect instruction).destination ∧ register ∉ writes (next ()) := by
      simpa only [writes, Finset.mem_insert, not_or] using outside
    rw [preserved register neither.2, Function.update_of_ne neither.1]

def scope (activation : Nat) : Finset Location :=
  insert (.inl activation) ((Finset.univ : Finset (Fin 12)).image Sum.inr)

def data (values : Location → Word) : Fin 12 → Word := fun register => values (.inr register)

def recipe (instruction : Instruction) : CellEffects.Recipe Location where
  inputs := (effect instruction).inputs.map Sum.inr
  outputs := [.inr (effect instruction).destination]
  guard := fun inputs outputs => match outputs with
    | [result] => (effect instruction).scalar.evaluate inputs == some result
    | _ => false

def updated (instruction : Instruction) (before : Location → Word) (result : Word) : Location → Word :=
  Function.update before (.inr (effect instruction).destination) result

theorem recipe_scope (activation : Nat) (instruction : Instruction) :
    (recipe instruction).support ⊆ scope activation := by
  intro location member
  cases location with
  | inl name => simp [CellEffects.Recipe.support,CellEffects.Recipe.writes,recipe] at member
  | inr register => simp [scope]

theorem updated_data (instruction : Instruction) (before : Location → Word) (result : Word) :
    data (updated instruction before result) = Function.update (data before) (effect instruction).destination result := by
  funext register
  by_cases same : register = (effect instruction).destination <;> simp [data,updated,same]

theorem updated_control (instruction : Instruction) (before : Location → Word) (result : Word) (activation : Nat) :
    updated instruction before result (.inl activation) = before (.inl activation) := by simp [updated]

theorem update_realized (activation : Nat) (instruction : Instruction) (before : Location → Word) (result : Word)
    (computed : (effect instruction).scalar.evaluate ((effect instruction).inputs.map (data before)) = some result) :
    ∃ invocation : CellEffects.Invocation (recipe instruction),
      CellEffects.system.Enables (Cells.encode (scope activation) before) invocation ∧
      CellEffects.system.fire (Cells.encode (scope activation) before) invocation =
        Cells.encode (scope activation) (updated instruction before result) := by
  have guarded : (recipe instruction).guard ((recipe instruction).inputs.map before)
      ((recipe instruction).outputs.map (updated instruction before result)) = true := by
    simp only [recipe,List.map_map,List.map_cons,List.map_nil,updated,Function.update_self]
    change ((effect instruction).scalar.evaluate ((effect instruction).inputs.map (data before)) == some result) = true
    exact beq_iff_eq.mpr computed
  obtain ⟨invocation,enabled,fired⟩ := CellEffects.effect_realized (recipe instruction) (scope activation) before
    (updated instruction before result) (recipe_scope activation instruction) guarded
  refine ⟨invocation,enabled,?_⟩
  rw [fired]
  apply congrArg (Cells.encode (scope activation))
  funext location
  by_cases same : location = .inr (effect instruction).destination
  · subst location
    simp [CellEffects.overwrite,CellEffects.Recipe.writes,recipe,updated]
  · simp [CellEffects.overwrite,CellEffects.Recipe.writes,recipe,updated,same]

def recipes : Program → List (CellEffects.Recipe Location)
  | .ret _ => []
  | .call instruction next => recipe instruction :: recipes (next ())

theorem source_fires (activation : Nat) (program : Program) (before : Location → Word) (following : World)
    (run : program.Runs action (Cells.encode Finset.univ (data before)) () following) :
    ∃ after : Location → Word, ∃ entries : List (CellEffects.system (Key := Location)).Entry,
      following = Cells.encode Finset.univ (data after) ∧
      CellEffects.system.Fires entries (Cells.encode (scope activation) before) (Cells.encode (scope activation) after) ∧
      entries.map Sigma.fst = recipes program ∧
      (∀ name, after (.inl name) = before (.inl name)) ∧
      ∀ register ∉ writes program, after (.inr register) = before (.inr register) := by
  induction program generalizing before following with
  | ret value =>
    obtain ⟨_,same⟩ := run
    exact ⟨before,[],same.symm,rfl,rfl,fun _ => rfl,fun _ _ => rfl⟩
  | call instruction next ih =>
    obtain ⟨reply,middle,step,rest⟩ := run
    cases reply
    obtain ⟨result,computed,endpoint⟩ := (source_step_iff instruction (data before) middle).mp step
    obtain ⟨invocation,enabled,fired⟩ := update_realized activation instruction before result computed
    have rest' : (next ()).Runs action (Cells.encode Finset.univ (data (updated instruction before result))) () following := by
      rw [updated_data]
      simpa only [endpoint] using rest
    obtain ⟨after,entries,encoded,fires,sites,controls,preserved⟩ := ih () _ _ rest'
    refine ⟨after,⟨recipe instruction,invocation⟩ :: entries,encoded,?_,?_,?_,?_⟩
    · exact ⟨enabled,by simpa only [fired] using fires⟩
    · exact congrArg (List.cons (recipe instruction)) sites
    · intro name
      exact (controls name).trans (updated_control instruction before result name)
    · intro register outside
      have neither : register ≠ (effect instruction).destination ∧ register ∉ writes (next ()) := by
        simpa only [writes, Finset.mem_insert, not_or] using outside
      rw [preserved register neither.2]
      simp [updated,neither.1]

theorem run_preserves (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (stop : Int) (program : Program) (before : Fin 12 → Word) (native after : State)
    (input : X86BlockCompiler.At spec stop program (Cells.encode Finset.univ before) native)
    (safe : program.Safe action (Cells.encode Finset.univ before)) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches (X86BlockCompiler.steps spec program)).run native = .ok () after →
    ∀ register ∉ writes program, lookup after (X86CopyBlock.physical register) = some (before register) := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  intro run
  let post : Unit → World → Prop := fun _ world => ∃ values : Fin 12 → Word,
    world = Cells.encode Finset.univ values ∧ ∀ register ∉ writes program, values register = before register
  have wp : program.wp action post (Cells.encode Finset.univ before) := by
    refine ⟨safe,?_⟩
    intro reply following sourceRun
    cases reply
    exact source_frame program before following sourceRun
  obtain ⟨following,_,holds,_,observed⟩ := X86BlockCompiler.compile_reflects spec (correct other vector) progress stop program
    (Cells.encode Finset.univ before) native after input post wp run
  obtain ⟨values,encoded,preserved⟩ := holds
  obtain ⟨represented,representedEncoded,known⟩ := observed.1
  have same := encode_injective represented values (representedEncoded.symm.trans encoded)
  subst represented
  intro register outside
  have value := known register (Finset.mem_univ _)
  rw [preserved register outside] at value
  fin_cases register <;>
    simpa only [X86CopyBlock.physical,X86MovCapture.physical,placed,Registers.canonical,
      Registers.Placement.resolve,Registers.logicalSlot] using value

def transfer (activation : Nat) (point destination : Word) : CellEffects.Recipe Location where
  inputs := [.inl activation]
  outputs := [.inl activation]
  guard := fun inputs outputs => match inputs,outputs with
    | [current],[next] => current == point && next == destination
    | _,_ => false

theorem transfer_realized (activation : Nat) (point destination : Word) (before : Location → Word)
    (current : before (.inl activation) = point) :
    ∃ invocation : CellEffects.Invocation (transfer activation point destination),
      CellEffects.system.Enables (Cells.encode (scope activation) before) invocation ∧
      CellEffects.system.fire (Cells.encode (scope activation) before) invocation =
        Cells.encode (scope activation) (Function.update before (.inl activation) destination) := by
  have included : (transfer activation point destination).support ⊆ scope activation := by
    simp [transfer,CellEffects.Recipe.support,CellEffects.Recipe.writes,scope]
  have guarded : (transfer activation point destination).guard ((transfer activation point destination).inputs.map before)
      ((transfer activation point destination).outputs.map (Function.update before (.inl activation) destination)) = true := by
    simp [transfer,current]
  obtain ⟨invocation,enabled,fired⟩ := CellEffects.effect_realized (transfer activation point destination) (scope activation)
    before (Function.update before (.inl activation) destination) included guarded
  refine ⟨invocation,enabled,?_⟩
  rw [fired]
  apply congrArg (Cells.encode (scope activation))
  funext location
  by_cases same : location = .inl activation
  · subst location
    simp [CellEffects.overwrite,CellEffects.Recipe.writes,transfer]
  · simp [CellEffects.overwrite,CellEffects.Recipe.writes,transfer,same]

theorem fires_append (first second : List (CellEffects.system (Key := Location)).Entry)
    (before middle after : Multiset (Cells.Cell Location))
    (one : CellEffects.system.Fires first before middle) (two : CellEffects.system.Fires second middle after) :
    CellEffects.system.Fires (first ++ second) before after := by
  induction first generalizing before with
  | nil => cases one; exact two
  | cons entry later ih => exact ⟨one.1,ih _ one.2⟩

def Represents (activation : Nat) (values : Location → Word) (native : State) : Prop :=
  X86CopyBlock.RegistersRepresented (data values) native ∧ native.regs.get? .rip = some (values (.inl activation))

theorem execute (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (activation : Nat) (stop : Int) (program : Program) (before : Location → Word) (native : State)
    (input : X86BlockCompiler.At spec stop program (Cells.encode Finset.univ (data before)) native)
    (current : before (.inl activation) = input.origin.address.signExtend 64)
    (post : Unit → World → Prop) (wp : program.wp action post (Cells.encode Finset.univ (data before))) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after : Location → Word, ∃ entries : List (CellEffects.system (Key := Location)).Entry, ∃ machine,
      CellEffects.system.Fires entries (Cells.encode (scope activation) before) (Cells.encode (scope activation) after) ∧
      entries.map Sigma.fst = recipes program ++
        [transfer activation (input.origin.address.signExtend 64) ((BitVec.ofInt 48 stop).signExtend 64)] ∧
      post () (Cells.encode Finset.univ (data after)) ∧
      (X86FuelPrefix.fetches (X86BlockCompiler.steps spec program)).run native = .ok () machine ∧
      X86StateFrame.Frame registers ∅ native machine ∧ Represents activation after machine ∧ ready machine ∧
      after (.inl activation) = (BitVec.ofInt 48 stop).signExtend 64 ∧
      (∀ name ≠ activation, after (.inl name) = before (.inl name)) ∧
      (∀ register ∉ writes program, after (.inr register) = before (.inr register)) ∧
      ∀ count ≤ X86BlockCompiler.steps spec program, ∀ reached,
        (X86FuelPrefix.fetches count).run native = .ok () reached → X86StateFrame.Frame registers ∅ native reached := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨following,machine,sourceRun,holds,executed,framed,observed⟩ :=
    X86BlockCompiler.compile_wp spec (correct other vector) progress stop program _ native input post wp
  obtain ⟨middle,entries,encoded,fires,sites,controls,preserved⟩ := source_fires activation program before following sourceRun
  let target := (BitVec.ofInt 48 stop).signExtend 64
  let after := Function.update middle (.inl activation) target
  obtain ⟨invocation,enabled,fired⟩ := transfer_realized activation (input.origin.address.signExtend 64) target middle
    ((controls activation).trans current)
  have last : CellEffects.system.Fires [⟨transfer activation (input.origin.address.signExtend 64) target,invocation⟩]
      (Cells.encode (scope activation) middle) (Cells.encode (scope activation) after) := ⟨enabled,fired.symm⟩
  have dataSame : data after = data middle := by funext register; simp [data,after]
  have registersKnown : X86CopyBlock.RegistersRepresented (data after) machine := by
    obtain ⟨values,same,known⟩ := observed.1
    have equal := encode_injective values (data middle) (same.symm.trans encoded)
    rw [dataSame,←equal]
    exact known
  refine ⟨after,entries ++ [⟨transfer activation (input.origin.address.signExtend 64) target,invocation⟩],machine,
    fires_append _ _ _ _ _ fires last,?_,?_,executed,framed,⟨registersKnown,?_⟩,observed.2.1,?_,?_,?_,?_⟩
  · simp only [List.map_append,List.map_cons,List.map_nil]
    rw [sites]
    rfl
  · rw [dataSame,←encoded]
    exact holds
  · simpa [after] using observed.2.2
  · simp [after,target]
  · intro name different
    simpa [after,different] using controls name
  · intro register outside
    simpa [after] using preserved register outside
  · intro count within reached run
    exact X86BlockCompiler.prefix_frame spec (correct other vector) progress stop program _ native reached input wp.1 count within run

theorem effect_evaluates (instruction : Instruction) (values : Fin 12 → Word) :
    ∃ result, (effect instruction).scalar.evaluate ((effect instruction).inputs.map values) = some result := by
  cases instruction with
  | copy instruction => exact ⟨values instruction.source,rfl⟩
  | binary operation destination left right unlocked =>
    fin_cases operation
    · exact ⟨values left + values right,rfl⟩
    · exact ⟨values left - values right,rfl⟩

theorem all_safe (program : Program) (values : Fin 12 → Word) :
    program.Safe action (Cells.encode Finset.univ values) := by
  induction program generalizing values with
  | ret value => exact Prog.safe_ret _ _ _
  | call instruction next ih =>
    obtain ⟨result,computed⟩ := effect_evaluates instruction values
    obtain ⟨invocation,enabled,_⟩ := Cells.scalar_update_realized (effect instruction) Finset.univ values result
      (Finset.subset_univ _) computed
    refine ⟨⟨invocation,enabled⟩,?_⟩
    intro reply following step
    cases reply
    obtain ⟨_,_,endpoint⟩ := (source_step_iff instruction values following).mp step
    rw [endpoint]
    exact ih () _

namespace Controls

private def add : Instruction := .binary 0 2 2 6 (by decide)
private def program : Program := Prog.prim add
private def values (register : Fin 12) : Word :=
  if register = 0 then 8192 else if register = 2 then 0xffffffffffffffff#64
  else if register = 5 then 10 else if register = 6 then 3 else 0
private def before : Location → Word
  | .inl name => if name = 0 then 4096 else 777
  | .inr register => values register
private def finalData : Fin 12 → Word := Function.update values 2 2
private def raw : List Nat := [0x49,0x89,0xd6,0x4d,0x01,0xd6,0x4c,0x89,0xf2]

theorem compiled_bytes : X86BlockCompiler.code spec program = raw := by
  rw [program,X86BlockCompiler.code_prim]
  simp only [spec,bytes,add]
  rw [binaryBytes_exact]
  rfl

theorem protected_registers : (5 : Fin 12) ∉ writes program ∧ (6 : Fin 12) ∉ writes program := by decide
theorem unsafe_body_detected : (6 : Fin 12) ∈ writes (Prog.prim (.binary 0 6 6 1 (by decide))) := by decide

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def cells : List (Nat × BitVec 8) :=
  (List.range 9).map fun offset => (4096 + offset,BitVec.ofNat 8 ((raw[offset]?).getD 0))
private theorem distinct : cells.Pairwise (fun left right => (left.1 == right.1) = false) := by decide

private noncomputable def native : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .rdi (values 0)
  let registers := registers.insert .rsi (values 1)
  let registers := registers.insert .rdx (values 2)
  let registers := registers.insert .rcx (values 3)
  let registers := registers.insert .r8 (values 4)
  let registers := registers.insert .r9 (values 5)
  let registers := registers.insert .r10 (values 6)
  let registers := registers.insert .r11 (values 7)
  let registers := registers.insert .rax (values 8)
  let registers := registers.insert .rbx (values 9)
  let registers := registers.insert .r12 (values 10)
  let registers := registers.insert .r13 (values 11)
  let registers := registers.insert .rsp (16384#64)
  let registers := registers.insert .rflags (0x246#32)
  let registers := registers.insert .log_register_writes false
  ⟨registers,(),Std.ExtHashMap.ofList cells,(),0,#[]⟩

private def origin : X86LegacyFetch.Basis native where
  address := 4096#48
  opcodeAddress := 4097#48
  modrmAddress := 4098#48
  next := 4099#48
  control := modeControl
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by simp [native,Std.ExtDHashMap.get?_insert]
  fault := by simp [native,Std.ExtDHashMap.get?_insert]
  msrs := by simp [native,Std.ExtDHashMap.get?_insert]
  segments := by simp [native,Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by simp [native,Std.ExtDHashMap.get?_insert]
  rip := by simp [native,Std.ExtDHashMap.get?_insert]

private def input : X86BlockCompiler.At spec 4105 program (Cells.encode Finset.univ (data before)) native where
  origin := origin
  placed := by rw [compiled_bytes]; decide
  upper := by decide
  represented := by
    refine ⟨data before,rfl,?_⟩
    intro register _
    fin_cases register <;>
      simp [lookup,placed,Registers.canonical,Registers.Placement.resolve,Registers.logicalSlot,
        key,native,Std.ExtDHashMap.get?_insert,data,before] <;> rfl
  ready := ⟨0x246#32,by simp [native,Std.ExtDHashMap.get?_insert],by simp [native]⟩
  loaded := by
    rw [compiled_bytes]
    intro offset byte present
    have within : offset < 9 := (List.getElem?_eq_some_iff.mp present).1
    have point : ((address 4096 offset).signExtend 52).toNat = 4096 + offset := by interval_cases offset <;> decide
    have member : (4096 + offset,BitVec.ofNat 8 byte) ∈ cells :=
      List.mem_map.mpr ⟨offset,List.mem_range.mpr within,by simp only [present,Option.getD_some]⟩
    change native.mem.get? ((address 4096 offset).signExtend 52).toNat = some (BitVec.ofNat 8 byte)
    rw [point]
    exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) distinct member
  outside := by intros; simp [spec]

private theorem source_wp : program.wp action (fun _ world => world = Cells.encode Finset.univ finalData)
    (Cells.encode Finset.univ (data before)) :=
  source_wp_step add (data before) 2 (by rfl) _ rfl

theorem native_body (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after : Location → Word, ∃ entries : List (CellEffects.system (Key := Location)).Entry, ∃ machine,
      CellEffects.system.Fires entries (Cells.encode (scope 0) before) (Cells.encode (scope 0) after) ∧
      entries.length = 2 ∧ (X86FuelPrefix.fetches 3).run native = .ok () machine ∧
      lookup machine 2 = some (2#64) ∧ lookup machine 9 = some (10#64) ∧ lookup machine 10 = some (3#64) ∧
      after (.inl 0) = 4105 ∧ after (.inr 5) = 10 ∧ after (.inr 6) = 3 ∧
      X86StateFrame.Frame registers ∅ native machine := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,entries,machine,fires,sites,post,run,framed,represented,_,control,_,preserved,_⟩ :=
    execute other vector 0 4105 program before native input (by rfl) _ source_wp
  have equal := encode_injective (data after) finalData post
  have known := represented.1
  have answer : lookup machine 2 = some (2#64) := by
    have found := known 2 (Finset.mem_univ _)
    rw [equal] at found
    exact found
  have bound : lookup machine 9 = some (10#64) := by
    have found := known 5 (Finset.mem_univ _)
    rw [equal] at found
    exact found
  have index : lookup machine 10 = some (3#64) := by
    have found := known 6 (Finset.mem_univ _)
    rw [equal] at found
    exact found
  refine ⟨after,entries,machine,fires,?_,run,answer,bound,index,control,?_,?_,framed⟩
  · have length := congrArg List.length sites
    rw [List.length_map] at length
    change entries.length = 2 at length
    exact length
  · exact preserved 5 protected_registers.1
  · exact preserved 6 protected_registers.2

private noncomputable def changed : State := { native with mem := native.mem.insert 4100 (0x29#8) }
theorem changed_arithmetic_rejected : ¬codeLoaded changed 4096 raw := by
  intro loaded
  have wrong := loaded 4 1 (by rfl)
  simp [changed,address] at wrong

theorem wrong_control_refused : (transfer 0 4096 4105).guard [4097] [4105] = false := by decide

end Controls
end Mettapedia.Machines.TIsa.X86WordBody
