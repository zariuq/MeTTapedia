import Mettapedia.Machines.TIsa.P1WordExecution

/-!
# Observations after a p1 branch

Liveness before a scalar, capability or memory instruction includes
its exact input register inventory. A returned packet observes the
status, payload and private storage. A continuing block also observes
the registers read by its continuation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.P1WordLiveness

open P1Source P1WordExecution

structure Storage (left right : State) : Prop where
  regions : left.regions = right.regions
  frame : left.frame = right.frame
  memory : left.memory = right.memory
  budget : left.budget = right.budget
  spent : left.spent = right.spent

structure Agree (live : Finset Reg) (left right : State) : Prop extends Storage left right where
  registers : ∀ reg ∈ live, left.registers reg = right.registers reg

theorem Agree.mono {before after : State} {small large : Finset Reg}
    (agrees : Agree large before after) (kept : small ⊆ large) : Agree small before after :=
  ⟨agrees.toStorage, fun reg present => agrees.registers reg (kept present)⟩

theorem Agree.write {before after : State} {live : Finset Reg} {destination : Reg}
    (same : Agree (live.erase destination) before after) (value : Word) :
    Agree live (before.write destination value) (after.write destination value) := by
  refine ⟨⟨same.regions, same.frame, same.memory, same.budget, same.spent⟩, ?_⟩
  intro reg present
  by_cases recently : reg = destination
  · subst reg
    simp [State.write]
  · simpa only [State.write, Function.update_of_ne recently] using
      same.registers reg (Finset.mem_erase.mpr ⟨recently, present⟩)

theorem Agree.store {before after : State} {live : Finset Reg}
    (same : Agree live before after) (address : Nat) (value : Word) :
    Agree live (before.store address value) (after.store address value) := by
  refine ⟨⟨same.regions, same.frame, ?_, same.budget, same.spent⟩, same.registers⟩
  change Function.update before.memory address (some value) =
    Function.update after.memory address (some value)
  rw [same.memory]

theorem Agree.all {left right : State} (same : Agree Finset.univ left right) : left = right := by
  have regs : left.registers = right.registers := funext fun index => same.registers index (Finset.mem_univ _)
  cases left
  cases right
  simp only [State.mk.injEq]
  exact ⟨regs, same.regions, same.frame, same.memory, same.budget, same.spent⟩

inductive Observes (live : Finset Reg) : Flow → Flow → Prop where
  | continuing {left right} (same : Agree live left right) : Observes live (.continuing left) (.continuing right)
  | returned {status payload left right} (same : Storage left right) :
      Observes live (.returned status payload left) (.returned status payload right)

theorem observes_refl (live : Finset Reg) (flow : Flow) : Observes live flow flow := by
  cases flow
  · exact .continuing ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩
  · exact .returned ⟨rfl, rfl, rfl, rfl, rfl⟩

def inputs : Instr → List Reg
  | .loadFrame .. => []
  | other => other.reads

def keeps (destination : Option Reg) (live : Finset Reg) : Finset Reg :=
  match destination with
  | none => live
  | some slot => live.erase slot

def beforeInstruction (code : Instr) (after : Finset Reg) : Finset Reg :=
  (inputs code).toFinset ∪ keeps code.destination? after

private def commit (before : State) : Except ExitStatus State → Flow
  | .ok after => .continuing after
  | .error status => fail status before

private theorem shared_result {left right : State} (live : Finset Reg) (destination : Reg)
    (same : Agree (live.erase destination) left right) (result : Option Word) :
    Observes live
      (commit left (match result with | some value => .ok (left.write destination value) | none => .error .invalidInput))
      (commit right (match result with | some value => .ok (right.write destination value) | none => .error .invalidInput)) := by
  cases result with
  | none => exact .returned same.toStorage
  | some value => exact .continuing (same.write value)

private theorem register_read {code : Instr} {live : Finset Reg} {left right : State}
    (same : Agree (beforeInstruction code live) left right) (reg : Reg) (read : reg ∈ inputs code) :
    left.registers reg = right.registers reg :=
  same.registers reg (Finset.mem_union_left _ (List.mem_toFinset.mpr read))

private theorem kept_registers {code : Instr} {live : Finset Reg} {left right : State}
    (same : Agree (beforeInstruction code live) left right) :
    Agree (keeps code.destination? live) left right := same.mono Finset.subset_union_right

theorem instruction_observes (code : Instr) (live : Finset Reg) (left right : State)
    (same : Agree (beforeInstruction code live) left right) :
    Observes live (execute left (.instruction code)) (execute right (.instruction code)) := by
  have kept := kept_registers same
  have val (reg : Reg) (member : reg ∈ inputs code) : left.registers reg = right.registers reg :=
    register_read same reg member
  change Observes live (commit left (instruction left code)) (commit right (instruction right code))
  have scalar (dst : Reg) (sameInputs : inputs code = code.reads) (written : code.destination? = some dst)
      (meaning : ∀ before, instruction before code =
        match P1Scalar.evaluate code (code.reads.map before.registers) with
        | some word => .ok (before.write dst word)
        | none => .error .invalidInput) :
      Observes live (commit left (instruction left code)) (commit right (instruction right code)) := by
    have readback : code.reads.map left.registers = code.reads.map right.registers := by
      apply List.map_congr_left
      intro reg known
      exact val reg (sameInputs.symm ▸ known)
    rw [meaning, meaning, readback]
    exact shared_result live dst (by simpa only [written, keeps] using kept) _
  cases code with
  | loadFrame ty dst slot =>
    have stored := same.frame
    simp only [instruction, stored]
    exact shared_result live dst kept _
  | address region dst base index scale displacement =>
    have baseRead := val base (by simp [inputs, Instr.reads])
    have indexRead :
        index.map (fun reg => (left.registers reg).toNat) = index.map (fun reg => (right.registers reg).toNat) := by
      cases index with
      | none => rfl
      | some reg =>
        simp only [Option.map_some, Option.some.injEq]
        exact congrArg BitVec.toNat (val reg (by simp [inputs, Instr.reads]))
    simp only [instruction, same.regions, baseRead, indexRead]
    split
    · exact .returned same.toStorage
    · split
      · exact .continuing (kept.write _)
      · exact .returned same.toStorage
  | load ty width region dst base displacement =>
    have value := val base (by simp [inputs, Instr.reads])
    cases width
    · exact .returned same.toStorage
    · exact .returned same.toStorage
    · simp only [instruction, same.regions, value, same.memory]
      split
      · exact .returned same.toStorage
      · cases loaded : (wordAddress (right.regions region) (right.registers base) displacement).bind right.memory with
        | some word => exact shared_result live dst kept (P1Memory.checkedWord ty word)
        | none => exact .returned same.toStorage
  | store width region base displacement source =>
    have pointer := val base (by simp [inputs, Instr.reads])
    have value := val source (by simp [inputs, Instr.reads])
    cases width
    · exact .returned same.toStorage
    · exact .returned same.toStorage
    · simp only [instruction, same.regions, pointer, value]
      split
      · exact .returned same.toStorage
      · split
        · exact .continuing (kept.store ..)
        · exact .returned same.toStorage
  | _ =>
    exact scalar _ rfl rfl (by
      intro state
      simp only [instruction, scalarInstruction, Instr.destination?]
      rfl)

def liveBefore : Stmt → Finset Reg → Finset Reg
  | .skip, after => after
  | .instruction code, after => beforeInstruction code after
  | .seq first second, after => liveBefore first (liveBefore second after)
  | .branch condition yes no, after => insert condition (liveBefore yes after ∪ liveBefore no after)
  | .ret _ source, _ => {source}
  | .fund _, after => after
  | .counted .., _ | .early .., _ => Finset.univ

private theorem then_observes {inside outside : Finset Reg} {first second : Flow}
    (same : Observes inside first second) (next : State → Flow)
    (later : ∀ left right, Agree inside left right → Observes outside (next left) (next right)) :
    Observes outside (first.thenContinue next) (second.thenContinue next) := by
  cases same with
  | continuing related => exact later _ _ related
  | returned storage => exact .returned storage

theorem statement_observes (code : Stmt) (live : Finset Reg) (left right : State)
    (same : Agree (liveBefore code live) left right) :
    Observes live (execute left code) (execute right code) := by
  induction code generalizing live left right with
  | skip => exact .continuing same
  | instruction code => exact instruction_observes code live left right same
  | seq first second ihFirst ihSecond =>
    simp only [execute]
    exact then_observes (ihFirst _ _ _ same) (execute · second)
      (fun first second ready => ihSecond live first second ready)
  | branch condition yes no ihYes ihNo =>
    have flag : left.registers condition = right.registers condition :=
      same.registers condition (Finset.mem_insert_self ..)
    simp only [execute, flag]
    split
    · exact ihYes _ _ _ (same.mono fun reg present =>
        Finset.mem_insert_of_mem (Finset.mem_union_left _ present))
    · split
      · exact ihNo _ _ _ (same.mono fun reg present =>
          Finset.mem_insert_of_mem (Finset.mem_union_right _ present))
      · exact .returned same.toStorage
  | ret status source =>
    have returned : left.registers source = right.registers source := same.registers source (Finset.mem_singleton_self _)
    simp only [execute, returned]
    exact .returned same.toStorage
  | fund units =>
    simp only [execute, fund, same.budget, same.spent]
    split
    · exact .returned same.toStorage
    · exact .continuing ⟨⟨same.regions, same.frame, same.memory, rfl, rfl⟩, same.registers⟩
  | counted | early =>
    have equal := same.all
    subst right
    exact observes_refl _ _

/-- The false-edge jump may consume a Boolean directly from flags when
neither continuation reads the comparison's destination before writing it. -/
theorem branch_elides_flag (state : State) (register : Reg) (flag : Bool) (yes no : Stmt)
    (live : Finset Reg) (dead : register ∉ liveBefore yes live ∪ liveBefore no live) :
    Observes live (execute (state.write register (booleanWord flag)) (if flag then yes else no))
      (execute state (if flag then yes else no)) := by
  apply statement_observes
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  intro candidate read
  have retains : candidate ≠ register := by
    intro same
    subst candidate
    cases flag
    · exact dead (Finset.mem_union_right _ read)
    · exact dead (Finset.mem_union_left _ read)
  exact Function.update_of_ne retains ..

def operandWord (state : State) : Operand → Word
  | .register register => state.registers register
  | .immediate word => word

theorem compare_then_branch (state : State) (test : Comparison) (destination left : Reg)
    (right : Operand) (yes no : Stmt) (live : Finset Reg)
    (dead : destination ∉ liveBefore yes live ∪ liveBefore no live) :
    let flag := test.evaluate (state.registers left) (operandWord state right)
    Observes live (execute state (.seq (.instruction (.compare test .u64 destination left right))
      (.branch destination yes no))) (execute state (if flag then yes else no)) := by
  let flag := test.evaluate (state.registers left) (operandWord state right)
  have fetched : execute state (.instruction (.compare test .u64 destination left right)) =
      .continuing (state.write destination (booleanWord flag)) := by
    cases right <;> rfl
  rw [execute, fetched]
  change Observes live (execute (state.write destination (booleanWord flag)) (.branch destination yes no))
    (execute state (if flag then yes else no))
  have reads : (state.write destination (booleanWord flag)).registers destination = booleanWord flag := by
    simp [State.write]
  rw [branch_bool _ destination flag _ _ reads]
  exact branch_elides_flag state destination flag yes no live dead

private theorem guarded_loop {head live : Finset Reg} {left right : State}
    (guard : Option Reg) (agrees : Agree head left right) (visible : live ⊆ head)
    (observed : guard.toList.toFinset ⊆ head) (action : State → Flow)
    (related : Observes live (action left) (action right)) :
    Observes live (continueLoop left guard action) (continueLoop right guard action) := by
  cases guard with
  | none => exact related
  | some register =>
    have equal := agrees.registers register (observed (by simp))
    simp only [continueLoop, equal]
    split
    · exact related
    · split
      · exact .continuing (agrees.mono visible)
      · exact .returned agrees.toStorage

theorem loop_observes (body : Stmt) (index : Reg) (guard : Option Reg) (head live : Finset Reg)
    (visible : live ⊆ head) (guarded : guard.toList.toFinset ⊆ head) (advances : index ∈ head)
    (stable : liveBefore body head ⊆ head)
    (steps : Nat) (left right : State) (agrees : Agree head left right) :
    Observes live (loop (execute · body) index guard steps left)
      (loop (execute · body) index guard steps right) := by
  induction steps generalizing left right with
  | zero => exact .continuing (agrees.mono visible)
  | succ steps ih =>
    simp only [loop]
    apply guarded_loop guard agrees visible guarded
    apply then_observes (statement_observes body head left right (agrees.mono stable))
    intro left right reached
    apply guarded_loop guard reached visible guarded
    rw [reached.registers index advances]
    exact ih _ _ ((reached.mono (Finset.erase_subset index head)).write _)

/-- A closed loop-head liveness set is what the emitter's saturation
ensures. The initial index need not be live because both executions
write it before entering the loop. -/
theorem early_loop_observes (body : Stmt) (index bound guard : Reg) (cap : BitVec 32)
    (head live : Finset Reg) (visible : live ⊆ head) (guarded : guard ∈ head) (advances : index ∈ head)
    (stable : liveBefore body head ⊆ head) (left right : State)
    (agrees : Agree (insert bound (head.erase index)) left right) :
    Observes live (execute left (.early index bound guard cap body))
      (execute right (.early index bound guard cap body)) := by
  have read := agrees.registers bound (Finset.mem_insert_self ..)
  simp only [execute, read]
  split
  · exact .returned agrees.toStorage
  · exact loop_observes body index (some guard) head live visible
      (by simpa using Finset.singleton_subset_iff.mpr guarded) advances stable _
      _ _ ((agrees.mono (fun _ located => Finset.mem_insert_of_mem located)).write 0)

end Mettapedia.Machines.TIsa.P1WordLiveness
