import Mettapedia.Machines.TIsa.NativeRefinement
import Mettapedia.Machines.TIsa.X86MovCapture
import Mettapedia.Machines.TIsa.X86FuelPrefix
import Mettapedia.Machines.TIsa.X86StateFrame
import Mettapedia.Machines.TIsa.P1Scalar

/-!
# Existing resource/WP programs compiled to captured x86 copy blocks

Source copies are genuine cell-resource firings and agree with the existing
p1 U64 move recipe. Programs use the established GSLT program and WP semantics.
The compiler concatenates the actual captured MOV-helper outputs; total row
coverage supplies each lookup's proof, with no missing-template fallback.

A program-indexed representation pins the remaining bytes and native PC.
Primitive certificates execute the original Sail fetch body, preserve the
live-register representation and advance the layout. A counted boundary then
proves source/WP-to-native correctness for every finite copy block satisfying
the architectural, initialized-register and code-placement premises.

Every fetched prefix preserves memory, RSP and the immutable frame pointer.
Dependent-copy, self-elision, high-bit value and changed-byte controls exercise
real loaded code. The block ends at its fallthrough PC, before a public return.
Other instruction families, native control/loops, typed source admission,
control-token hosting and the complete emitter/ABI theorem remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86CopyBlock

open _root_.X86Registers X86RegisterRefinement X86Execution
open Mettapedia.GSLT.Logic.AbstractSeparationLogic

local instance : MemoryPrimitives := X86Memory.ordinary

structure Copy where
  source : Fin 12
  destination : Fin 12
  unlocked : destination ≠ 0

abbrev World := Multiset (Cells.Cell (Fin 12))
abbrev Program := Prog Copy (fun _ => Unit) Unit

def Copy.effect (copy : Copy) : Cells.Action (Fin 12) :=
  X86ResourceCopy.copyAction copy.source copy.destination

def action (copy : Copy) : Mettapedia.GSLT.Logic.AbstractSeparationLogic.Action World Unit where
  Safe world := ∃ invocation : Cells.Invocation copy.effect, Cells.system.Enables world invocation
  Step world _ after := ∃ invocation : Cells.Invocation copy.effect,
    Cells.system.Enables world invocation ∧ Cells.system.fire world invocation = after

theorem action_progress (copy : Copy) : (action copy).Progress := by
  rintro world ⟨invocation, enabled⟩
  exact ⟨(), Cells.system.fire world invocation, invocation, enabled, rfl⟩

noncomputable def emit (copy : Copy) : List Nat :=
  (X86MovCapture.lookup (Registers.logicalSlot copy.destination) (Registers.logicalSlot copy.source)).get
    (by rw [X86MovCapture.every_output_exact]; rfl)

theorem emit_exact (copy : Copy) : emit copy =
    X86MovCapture.expected (Registers.logicalSlot copy.destination) (Registers.logicalSlot copy.source) := by
  simp only [emit, X86MovCapture.every_output_exact, Option.get_some]

noncomputable def code : Program → List Nat
  | .ret _ => []
  | .call copy next => emit copy ++ code (next ())

def steps : Program → Nat
  | .ret _ => 0
  | .call copy next => (if copy.destination = copy.source then 0 else 1) + steps (next ())

def physical (register : Fin 12) : Fin 16 := X86MovCapture.physical (Registers.logicalSlot register)
def registerWrites : Finset Register :=
  (((Finset.univ : Finset (Fin 12)).erase 0).image (fun register => key (physical register))) ∪ {.rip}

theorem destination_written (copy : Copy) : key (physical copy.destination) ∈ registerWrites := by
  exact Finset.mem_union_left _ (Finset.mem_image.mpr
    ⟨copy.destination, Finset.mem_erase.mpr ⟨copy.unlocked, Finset.mem_univ _⟩, rfl⟩)

theorem writes_data : registerWrites ⊆ dataRegisters := by decide
theorem stack_not_written : Register.rsp ∉ registerWrites := by decide
theorem frame_not_written : Register.rdi ∉ registerWrites := by decide

abbrev RegistersRepresented (values : Fin 12 → Word) (state : State) :=
  RepresentsOn (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64) Finset.univ values state

structure At (stop : Int) (program : Program) (world : World) (state : State) where
  origin : X86LegacyFetch.Basis state
  placed : origin.address.toInt = stop - (code program).length
  upper : stop + 3 < (2 ^ 47 : Int)
  values : Fin 12 → Word
  source : world = Cells.encode Finset.univ values
  registers : RegistersRepresented values state
  loaded : codeLoaded state origin.address.toInt (code program)
  quiet : state.regs.get? .log_register_writes = some false

def Observed (stop : Int) (_ : Unit) (world : World) (state : State) : Prop :=
  ∃ values : Fin 12 → Word, world = Cells.encode Finset.univ values ∧ RegistersRepresented values state ∧
    state.regs.get? .rip = some ((BitVec.ofInt 48 stop).signExtend 64)

section Machine
variable [OtherOpcodeHandlers] [VectorOpcodeHandlers]

noncomputable def machine : NativeRefinement.Machine State where
  executes count before after := (X86FuelPrefix.fetches count).run before = .ok () after
  zero := X86FuelPrefix.fetches_zero
  append := fun {first second before middle after} one two =>
    X86FuelPrefix.fetches_then first second before middle after one two
  deterministic := fun {count before left right} one two =>
    X86FuelPrefix.fetches_deterministic count before left right one two
  frame := X86StateFrame.Frame registerWrites ∅
  frame_refl := X86StateFrame.Frame.refl _ _
  frame_trans := by
    intro before middle after first second
    exact (first.trans second).mono (by simp) (by simp)

theorem returned (stop : Int) (value : Unit) (world : World) (state : State)
    (input : At stop (.ret value) world state) :
    ∃ after, machine.executes 0 state after ∧ machine.frame state after ∧ Observed stop value world after := by
  refine ⟨state, X86FuelPrefix.fetches_zero state, X86StateFrame.Frame.refl _ _ _,
    input.values, input.source, input.registers, ?_⟩
  have place : input.origin.address.toInt = stop := by simpa only [code, List.length_nil, Int.natCast_zero, sub_zero] using input.placed
  rw [← place, BitVec.ofInt_toInt]
  exact input.origin.rip

omit [OtherOpcodeHandlers] [VectorOpcodeHandlers] in
theorem source_step (copy : Copy) (values : Fin 12 → Word) (world : World)
    (step : (action copy).Step (Cells.encode Finset.univ values) () world) :
    world = Cells.encode Finset.univ (Function.update values copy.destination (values copy.source)) := by
  obtain ⟨invocation, enabled, endpoint⟩ := step
  exact endpoint.symm.trans
    (X86ResourceCopy.copy_reflected Finset.univ values copy.source copy.destination invocation enabled).2

omit [OtherOpcodeHandlers] [VectorOpcodeHandlers] in
theorem source_step_iff (copy : Copy) (values : Fin 12 → Word) (world : World) :
    (action copy).Step (Cells.encode Finset.univ values) () world ↔
      world = Cells.encode Finset.univ (Function.update values copy.destination (values copy.source)) := by
  constructor
  · exact source_step copy values world
  · intro endpoint
    obtain ⟨invocation, enabled, resource⟩ := X86ResourceCopy.copy_realized Finset.univ values
      copy.source copy.destination (Finset.mem_univ _) (Finset.mem_univ _)
    exact ⟨invocation, enabled, resource.trans endpoint.symm⟩

omit [OtherOpcodeHandlers] [VectorOpcodeHandlers] in
theorem p1_move_iff (copy : Copy) (values : Fin 12 → Word) (world : World) :
    (action copy).Step (Cells.encode Finset.univ values) () world ↔
      (CellEffects.profile [P1Scalar.recipe (.move .u64 copy.destination copy.source) copy.destination]).theory.rewrites
        (Cells.encode Finset.univ values) world := by
  rw [source_step_iff, P1Scalar.rewrite_iff]
  constructor
  · intro endpoint
    exact ⟨values copy.source, Finset.subset_univ _, rfl, endpoint⟩
  · rintro ⟨result, _, computed, endpoint⟩
    have same : values copy.source = result := by
      change some (values copy.source) = some result at computed
      exact Option.some.inj computed
    simpa only [← same] using endpoint

omit [OtherOpcodeHandlers] [VectorOpcodeHandlers] in
theorem emit_self (copy : Copy) (same : copy.destination = copy.source) : emit copy = [] := by
  rw [emit_exact, X86MovCapture.expected, same, if_pos rfl]

omit [OtherOpcodeHandlers] [VectorOpcodeHandlers] in
theorem emit_distinct (copy : Copy) (different : copy.destination ≠ copy.source) :
    emit copy = [(X86RegisterEncoding.rex true (physical copy.source) (physical copy.destination)).toNat,
      137, (X86RegisterEncoding.modRM (physical copy.source) (physical copy.destination)).toNat] := by
  have slots : Registers.logicalSlot copy.destination ≠ Registers.logicalSlot copy.source := by
    intro same
    exact different (Registers.logicalSlot_injective same)
  rw [emit_exact, X86MovCapture.expected, if_neg slots]
  rfl

omit [OtherOpcodeHandlers] [VectorOpcodeHandlers] in
theorem code_length (program : Program) : (code program).length = 3 * steps program := by
  induction program with
  | ret value => rfl
  | call copy next ih =>
      rw [code, List.length_append, ih ()]
      by_cases same : copy.destination = copy.source
      · rw [emit_self copy same]
        simp only [List.length_nil, steps, if_pos same, zero_add]
      · rw [emit_distinct copy same]
        simp only [List.length_cons, List.length_nil, steps, if_neg same]
        omega

omit [OtherOpcodeHandlers] [VectorOpcodeHandlers] in
theorem next_int {state : State} (origin : X86LegacyFetch.Basis state) :
    origin.next.toInt = origin.address.toInt + 3 := by
  have := origin.step2
  have := origin.step3
  omega

omit [OtherOpcodeHandlers] [VectorOpcodeHandlers] in
theorem next_address {state : State} (origin : X86LegacyFetch.Basis state) :
    origin.next = address origin.address.toInt 3 := by
  unfold address
  change origin.next = BitVec.ofInt 48 (origin.address.toInt + (3 : Int))
  rw [← next_int origin, BitVec.ofInt_toInt]

theorem self_primitive (stop : Int) (copy : Copy) (next : Unit → Program)
    (source following : World) (state : State) (input : At stop (.call copy next) source state)
    (step : (action copy).Step source () following) (same : copy.destination = copy.source) :
    ∃ after, machine.executes 0 state after ∧ machine.frame state after ∧
      Nonempty (At stop (next ()) following after) := by
  have sourceStep : (action copy).Step (Cells.encode Finset.univ input.values) () following := by
    simpa only [← input.source] using step
  have sourceAfter := source_step copy input.values following sourceStep
  have unchanged : Function.update input.values copy.destination (input.values copy.source) = input.values := by
    funext register
    by_cases selected : register = copy.destination
    · subst register
      simp [same]
    · rw [Function.update_of_ne selected]
  have codeSame : code (.call copy next) = code (next ()) := by
    simp only [code, emit_self copy same, List.nil_append]
  refine ⟨state, X86FuelPrefix.fetches_zero state, X86StateFrame.Frame.refl _ _ _, ?_⟩
  refine ⟨{ input with
    placed := ?_
    source := ?_
    loaded := ?_ }⟩
  · simpa only [codeSame] using input.placed
  · simpa only [unchanged] using sourceAfter
  · simpa only [codeSame] using input.loaded

omit [OtherOpcodeHandlers] [VectorOpcodeHandlers] in
def window (stop : Int) (copy : Copy) (next : Unit → Program) (world : World) (state : State)
    (input : At stop (.call copy next) world state) (different : copy.destination ≠ copy.source) :
    X86ResourceCopy.Window state (physical copy.source) (physical copy.destination) := by
  refine { toBasis := input.origin, prefixByte := ?_, opcodeByte := ?_, modrmByte := ?_ }
  · have read := input.loaded 0
      (X86RegisterEncoding.rex true (physical copy.source) (physical copy.destination)).toNat
      (by simp only [code, emit_distinct copy different, List.cons_append, List.getElem?_cons_zero])
    simpa only [address, Int.natCast_zero, add_zero, BitVec.ofInt_toInt, BitVec.ofNat_toNat,
      BitVec.setWidth_eq] using read
  · have read := input.loaded 1 137 (by simp only [code, emit_distinct copy different, List.cons_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero])
    have place : address input.origin.address.toInt 1 = input.origin.opcodeAddress := by
      change BitVec.ofInt 48 (input.origin.address.toInt + (1 : Int)) = _
      rw [input.origin.step1, BitVec.ofInt_toInt]
    simpa only [place] using read
  · have read := input.loaded 2
      (X86RegisterEncoding.modRM (physical copy.source) (physical copy.destination)).toNat
      (by simp only [code, emit_distinct copy different, List.cons_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero])
    have place : address input.origin.address.toInt 2 = input.origin.modrmAddress := by
      change BitVec.ofInt 48 (input.origin.address.toInt + (2 : Int)) = _
      rw [input.origin.step2, BitVec.ofInt_toInt]
    simpa only [place, BitVec.ofNat_toNat, BitVec.setWidth_eq] using read

theorem distinct_primitive (stop : Int) (copy : Copy) (next : Unit → Program)
    (source following : World) (state : State) (input : At stop (.call copy next) source state)
    (step : (action copy).Step source () following) (different : copy.destination ≠ copy.source) :
    ∃ after, machine.executes 1 state after ∧ machine.frame state after ∧
      Nonempty (At stop (next ()) following after) := by
  have sourceStep : (action copy).Step (Cells.encode Finset.univ input.values) () following := by
    simpa only [← input.source] using step
  have sourceAfter := source_step copy input.values following sourceStep
  let site := window stop copy next source state input different
  let target := address input.origin.address.toInt 3
  let after := X86Move.putPointer (put state (physical copy.destination) (input.values copy.source)) target
  have executed := site.executes state _ _ (input.values copy.source)
    (input.registers copy.source (Finset.mem_univ _)) input.quiet
  have sameNext : site.next = input.origin.next := rfl
  rw [sameNext, next_address input.origin] at executed
  have framed : RegisterFrame registerWrites state after := by
    apply ((put_frame state (physical copy.destination) (input.values copy.source)).trans
      (pointer_frame _ target)).mono
    intro register member
    simp only [Finset.mem_union, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact destination_written copy
    · exact Finset.mem_union_right _ (by simp)
  have length : (code (.call copy next)).length = 3 + (code (next ())).length := by
    simp only [code, List.length_append, emit_distinct copy different, List.length_cons, List.length_nil]
  have upper : input.origin.address.toInt + (((code (.call copy next)).length + 3 : Nat) : Int) < (2 ^ 47 : Int) := by
    have := input.placed
    have := input.upper
    omega
  let origin := rebase state after input.origin (framed.mono writes_data)
    (extent := (code (.call copy next)).length + 3) upper 3
    (by rw [length]; omega) (X86FuelPrefix.pointer_rip _ _)
  have nextPlaced : origin.address.toInt = stop - (code (next ())).length := by
    change (address input.origin.address.toInt 3).toInt = _
    rw [address_toInt input.origin.address.toInt (by simpa using BitVec.le_toInt input.origin.address)
      upper 3 (by omega)]
    have := input.placed
    rw [length] at this
    omega
  have nextRegisters : RegistersRepresented
      (Function.update input.values copy.destination (input.values copy.source)) after := by
    apply X86ResourceCopy.pointer_preserves_representation
    apply put_logical_represents
    intro register member
    exact input.registers register (Finset.mem_of_mem_erase member)
  refine ⟨after, X86FuelPrefix.fetches_one state after executed,
    X86StateFrame.registerOnly framed, ?_⟩
  refine ⟨{
    origin := origin
    placed := nextPlaced
    upper := input.upper
    values := Function.update input.values copy.destination (input.values copy.source)
    source := sourceAfter
    registers := nextRegisters
    loaded := ?_
    quiet := (framed.registers .log_register_writes (by decide : .log_register_writes ∉ registerWrites)).trans input.quiet }⟩
  intro index byte present
  have inWhole : (code (.call copy next))[3 + index]? = some byte := by
    rw [code, emit_distinct copy different, List.getElem?_append_right (by simp)]
    simpa using present
  rw [framed.memory]
  have shifted : address origin.address.toInt index = address input.origin.address.toInt (3 + index) := by
    dsimp only [origin, rebase]
    rw [address_toInt input.origin.address.toInt (by simpa using BitVec.le_toInt input.origin.address)
      upper 3 (by omega)]
    simp only [address, Int.natCast_add, Int.add_assoc]
  rw [shifted]
  exact input.loaded _ _ inWhole

theorem counted_boundary (stop : Int) :
    NativeRefinement.CountedBoundary action machine (fun program source state => Nonempty (At stop program source state))
      (Observed stop) (fun program _ => steps program) where
  returned value source native represented := by
    obtain ⟨input⟩ := represented
    exact returned stop value source native input
  primitive copy next source reply following native _ represented step := by
    cases reply
    obtain ⟨input⟩ := represented
    by_cases same : copy.destination = copy.source
    · obtain ⟨after, executed, framed, representedNext⟩ :=
        self_primitive stop copy next source following native input step same
      exact ⟨0, after, executed, framed, representedNext, by simp only [steps, if_pos same]⟩
    · obtain ⟨after, executed, framed, representedNext⟩ :=
        distinct_primitive stop copy next source following native input step same
      exact ⟨1, after, executed, framed, representedNext, by simp only [steps, if_neg same]⟩

theorem boundary (stop : Int) :
    NativeRefinement.Boundary action machine (fun program source state => Nonempty (At stop program source state))
      (Observed stop) := (counted_boundary stop).forget

omit [OtherOpcodeHandlers] [VectorOpcodeHandlers] in
theorem copy_safe (copy : Copy) (values : Fin 12 → Word) :
    (action copy).Safe (Cells.encode Finset.univ values) := by
  obtain ⟨invocation, enabled, _⟩ := X86ResourceCopy.copy_realized Finset.univ values
    copy.source copy.destination (Finset.mem_univ _) (Finset.mem_univ _)
  exact ⟨invocation, enabled⟩

omit [OtherOpcodeHandlers] [VectorOpcodeHandlers] in
theorem source_safe (program : Program) (values : Fin 12 → Word) :
    program.Safe action (Cells.encode Finset.univ values) := by
  induction program generalizing values with
  | ret value => trivial
  | call copy next ih =>
      refine ⟨copy_safe copy values, ?_⟩
      rintro ⟨⟩ following step
      rw [source_step copy values following step]
      exact ih () (Function.update values copy.destination (values copy.source))

omit [OtherOpcodeHandlers] [VectorOpcodeHandlers] in
theorem copy_wp (copy : Copy) (values : Fin 12 → Word) (post : Unit → World → Prop)
    (expected : post () (Cells.encode Finset.univ (Function.update values copy.destination (values copy.source)))) :
    (Prog.prim copy).wp action post (Cells.encode Finset.univ values) := by
  apply (wp_prim action copy post _).mpr
  refine ⟨copy_safe copy values, ?_⟩
  rintro ⟨⟩ following step
  rw [source_step copy values following step]
  exact expected

theorem compile_wp (stop : Int) (program : Program) (world : World) (state : State)
    (input : At stop program world state) (post : Unit → World → Prop) (wp : program.wp action post world) :
    ∃ following after, program.Runs action world () following ∧ post () following ∧
      (X86FuelPrefix.fetches (steps program)).run state = .ok () after ∧
      X86StateFrame.Frame registerWrites ∅ state after ∧ Observed stop () following after := by
  obtain ⟨⟨⟩, following, after, run, holds, executed, framed, observed⟩ :=
    (counted_boundary stop).wp_native action_progress program post world state wp ⟨input⟩
  exact ⟨following, after, run, holds, executed, framed, observed⟩

theorem compile (stop : Int) (program : Program) (world : World) (state : State)
    (input : At stop program world state) :
    ∃ following after, program.Runs action world () following ∧
      (X86FuelPrefix.fetches (steps program)).run state = .ok () after ∧
      X86StateFrame.Frame registerWrites ∅ state after ∧ Observed stop () following after := by
  have safe : program.Safe action world := by
    rw [input.source]
    exact source_safe program input.values
  obtain ⟨⟨⟩, following, run⟩ := program.exists_runs action action_progress world safe
  obtain ⟨after, executed, framed, observed⟩ :=
    (counted_boundary stop).realizes program world following state () safe ⟨input⟩ run
  exact ⟨following, after, run, executed, framed, observed⟩

theorem compile_reflects (stop : Int) (program : Program) (world : World) (state after : State)
    (input : At stop program world state) (post : Unit → World → Prop) (wp : program.wp action post world)
    (run : (X86FuelPrefix.fetches (steps program)).run state = .ok () after) :
    ∃ following, program.Runs action world () following ∧ post () following ∧
      X86StateFrame.Frame registerWrites ∅ state after ∧ Observed stop () following after := by
  obtain ⟨⟨⟩, following, sourceRun, holds, framed, observed⟩ :=
    (counted_boundary stop).wp_native_reflects action_progress program post world state wp ⟨input⟩ after run
  exact ⟨following, sourceRun, holds, framed, observed⟩

theorem prefix_executes (stop : Int) (program : Program) (world : World) (state : State)
    (input : At stop program world state) (count : Nat) (within : count ≤ steps program) :
    ∃ after, (X86FuelPrefix.fetches count).run state = .ok () after ∧
      X86StateFrame.Frame registerWrites ∅ state after := by
  induction program generalizing world state count with
  | ret value =>
      have zero : count = 0 := by simpa only [steps, Nat.le_zero] using within
      subst count
      exact ⟨state, X86FuelPrefix.fetches_zero state, X86StateFrame.Frame.refl _ _ _⟩
  | call copy next ih =>
      have safe : (action copy).Safe world := by rw [input.source]; exact copy_safe copy input.values
      obtain ⟨⟨⟩, following, step⟩ := action_progress copy world safe
      by_cases same : copy.destination = copy.source
      · obtain ⟨middle, first, firstFrame, ⟨nextInput⟩⟩ :=
          self_primitive stop copy next world following state input step same
        have tailWithin : count ≤ steps (next ()) := by
          simpa only [steps, if_pos same, zero_add] using within
        obtain ⟨after, rest, restFrame⟩ := ih () following middle nextInput count tailWithin
        refine ⟨after, ?_, ?_⟩
        · simpa only [Nat.zero_add] using X86FuelPrefix.fetches_then 0 count state middle after first rest
        · exact (firstFrame.trans restFrame).mono (by simp) (by simp)
      · cases count with
        | zero => exact ⟨state, X86FuelPrefix.fetches_zero state, X86StateFrame.Frame.refl _ _ _⟩
        | succ count =>
            obtain ⟨middle, first, firstFrame, ⟨nextInput⟩⟩ :=
              distinct_primitive stop copy next world following state input step same
            have tailWithin : count ≤ steps (next ()) := by
              simp only [steps, if_neg same] at within
              omega
            obtain ⟨after, rest, restFrame⟩ := ih () following middle nextInput count tailWithin
            refine ⟨after, ?_, ?_⟩
            · simpa only [Nat.add_comm 1 count] using
                X86FuelPrefix.fetches_then 1 count state middle after first rest
            · exact (firstFrame.trans restFrame).mono (by simp) (by simp)

theorem prefix_frame (stop : Int) (program : Program) (world : World) (state after : State)
    (input : At stop program world state) (count : Nat) (within : count ≤ steps program)
    (run : (X86FuelPrefix.fetches count).run state = .ok () after) :
    X86StateFrame.Frame registerWrites ∅ state after := by
  obtain ⟨proved, executed, framed⟩ := prefix_executes stop program world state input count within
  have same := X86FuelPrefix.fetches_deterministic count state proved after executed run
  subst after
  exact framed

theorem prefix_preserves (stop : Int) (program : Program) (world : World) (state after : State)
    (input : At stop program world state) (count : Nat) (within : count ≤ steps program)
    (run : (X86FuelPrefix.fetches count).run state = .ok () after) :
    lookup after 4 = lookup state 4 ∧ lookup after 7 = lookup state 7 ∧
      ∀ address, after.mem.get? address = state.mem.get? address := by
  have framed := prefix_frame stop program world state after input count within run
  exact ⟨framed.lookup 4 stack_not_written, framed.lookup 7 frame_not_written,
    fun address => framed.memory address (by simp)⟩

end Machine

namespace Controls

private def first : Copy := ⟨1, 2, by decide⟩
private def second : Copy := ⟨2, 3, by decide⟩
private def selfCopy : Copy := ⟨3, 3, by decide⟩
private def program : Program := do
  let _ ← Prog.prim first
  let _ ← Prog.prim second
  Prog.prim selfCopy

private def value : Word := 0xfedcba9876543210#64
private def values (register : Fin 12) : Word :=
  if register = 0 then (8192#64) else if register = 1 then value else 0
private def firstValues : Fin 12 → Word := Function.update values first.destination (values first.source)
private def secondValues : Fin 12 → Word := Function.update firstValues second.destination (firstValues second.source)
private def finalValues : Fin 12 → Word := Function.update secondValues selfCopy.destination (secondValues selfCopy.source)

theorem compiled_bytes : code program = [0x48,0x89,0xf2,0x48,0x89,0xd1] := by kernel_reflexivity
theorem compiled_steps : steps program = 2 := rfl

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def cells : List (Nat × BitVec 8) :=
  [(4096,0x48#8),(4097,0x89#8),(4098,0xf2#8),(4099,0x48#8),(4100,0x89#8),(4101,0xd1#8)]

private noncomputable def before : State :=
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
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList cells, (), 0, #[]⟩

private def origin : X86LegacyFetch.Basis before where
  address := 4096#48
  opcodeAddress := 4097#48
  modrmAddress := 4098#48
  next := 4099#48
  control := modeControl
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by simp [before, Std.ExtDHashMap.get?_insert]
  fault := by simp [before, Std.ExtDHashMap.get?_insert]
  msrs := by simp [before, Std.ExtDHashMap.get?_insert]
  segments := by simp [before, Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by simp [before, Std.ExtDHashMap.get?_insert]
  rip := by simp [before, Std.ExtDHashMap.get?_insert]

private theorem distinct : cells.Pairwise (fun left right => (left.1 == right.1) = false) := by decide

private theorem cell (address : Nat) (byte : BitVec 8) (present : (address, byte) ∈ cells) :
    before.mem.get? address = some byte := Std.ExtHashMap.getElem?_ofList_of_mem (by simp) distinct present

private def input : At 4102 program (Cells.encode Finset.univ values) before where
  origin := origin
  placed := by rw [compiled_bytes]; decide
  upper := by decide
  values := values
  source := rfl
  registers := by
    intro register _
    fin_cases register <;>
      simp [lookup, placed, Registers.canonical, Registers.Placement.resolve,
        Registers.logicalSlot, key, before, Std.ExtDHashMap.get?_insert] <;> rfl
  loaded := by
    intro index byte present
    rw [compiled_bytes] at present
    have within : index < 6 := by
      have := (List.getElem?_eq_some_iff.mp present).1
      change index < 6 at this
      exact this
    interval_cases index <;>
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at present <;>
      subst byte <;> apply cell <;> decide
  quiet := by simp [before]

private theorem source_wp : program.wp action
    (fun _ world => world = Cells.encode Finset.univ finalValues) (Cells.encode Finset.univ values) := by
  unfold program
  rw [wp_bind']
  apply copy_wp
  rw [wp_bind']
  apply copy_wp
  exact copy_wp selfCopy secondValues _ rfl

theorem two_copies_and_elision [OtherOpcodeHandlers] [VectorOpcodeHandlers] :
    ∃ state after, (X86FuelPrefix.fetches 2).run state = .ok () after ∧
      lookup after (physical 3) = some value ∧ after.regs.get? .rip = some (4102#64) ∧
      lookup after 4 = lookup state 4 ∧ lookup after 7 = lookup state 7 ∧
      ∀ address, after.mem.get? address = state.mem.get? address := by
  obtain ⟨following, after, _, expected, run, frame, outputValues, encoded, represented, pointer⟩ :=
    compile_wp 4102 program _ before input _ source_wp
  have equalValues := (Cells.encode_le_iff Finset.univ Finset.univ outputValues finalValues).mp
    (le_of_eq (encoded.symm.trans expected))
  have read := represented 3 (Finset.mem_univ _)
  rw [equalValues.2 3 (Finset.mem_univ _)] at read
  have result : finalValues 3 = value := by simp [finalValues, secondValues, firstValues, first, second, selfCopy, values]
  rw [result] at read
  refine ⟨before, after, ?_, read, pointer, frame.lookup 4 stack_not_written,
    frame.lookup 7 frame_not_written, fun address => frame.memory address (by simp)⟩
  simpa only [compiled_steps] using run

theorem wrong_copy_result_refused [OtherOpcodeHandlers] [VectorOpcodeHandlers] :
    ∃ state, ∀ after, lookup after (physical 3) = some (0#64) →
      (X86FuelPrefix.fetches 2).run state ≠ .ok () after := by
  obtain ⟨state, proved, run, valueRead, _⟩ := two_copies_and_elision
  refine ⟨state, ?_⟩
  intro after wrong observed
  have same := X86FuelPrefix.fetches_deterministic 2 state proved after run observed
  rw [same, wrong] at valueRead
  contradiction

theorem changed_byte_rejected :
    let changed : State := { before with mem := before.mem.insert 4098 (0xf3#8) }
    ¬ Nonempty (At 4102 program (Cells.encode Finset.univ values) changed) := by
  let changed : State := { before with mem := before.mem.insert 4098 (0xf3#8) }
  change ¬ Nonempty (At 4102 program (Cells.encode Finset.univ values) changed)
  rintro ⟨candidate⟩
  have place : candidate.origin.address.toInt = 4096 := by
    have placed := candidate.placed
    rw [compiled_bytes] at placed
    simpa using placed
  have read := candidate.loaded 2 0xf2 (by rw [compiled_bytes]; rfl)
  rw [place] at read
  change changed.mem.get? 4098 = some (0xf2#8) at read
  have actual : changed.mem.get? 4098 = some (0xf3#8) := Std.ExtHashMap.getElem?_insert_self
  rw [actual] at read
  contradiction

end Controls

end Mettapedia.Machines.TIsa.X86CopyBlock
