import Mettapedia.Machines.TIsa.P1WordExecution

/-! Scalar slices inside the same word and capability state. -/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.P1WordScalar

open P1Source P1WordExecution
inductive Exit where
  | following (registers : Registers)
  | returned (status : ExitStatus) (code : Word)

/-- Compose structured scalar statements via the existing p1 instruction algebra. -/
def executeScalar (registers : Registers) : Stmt → Option Exit
  | .skip => some (.following registers)
  | .instruction instruction => do
    let destination ← instruction.destination?
    let word ← P1Scalar.evaluate instruction (instruction.reads.map registers)
    return .following (Function.update registers destination word)
  | .seq first second => do
    match ← executeScalar registers first with
    | .following after => executeScalar after second
    | .returned status code => some (.returned status code)
  | .branch condition yes no =>
    if registers condition = 1 then executeScalar registers yes
    else if registers condition = 0 then executeScalar registers no else none
  | .ret status result => some (.returned status (registers result))
  | .fund .. | .counted .. | .early .. => none

def Agrees (before : State) (scalar : Exit) (actual : Flow) : Prop :=
  match scalar with
  | .following registers => actual = .continuing {before with registers}
  | .returned status payload => ∃ registers, actual = .returned status payload {before with registers}

private theorem instruction_agrees (code : Instr) (state : State) (result : Word) (destination : Reg)
    (value : P1Scalar.evaluate code (code.reads.map state.registers) = some result)
    (whereTo : code.destination? = some destination) :
    instruction state code = .ok (state.write destination result) := by
  cases code <;>
    first
    | solve | simp only [instruction, scalarInstruction, value, whereTo]
    | simp [P1Scalar.evaluate] at value

theorem execute_agrees (code : Stmt) (state : State) (expected : Exit)
    (accepted : executeScalar state.registers code = some expected) :
    Agrees state expected (execute state code) := by
  induction code generalizing state expected with
  | skip =>
    cases accepted
    rfl
  | instruction code =>
    simp only [executeScalar, Option.bind_eq_bind] at accepted
    obtain ⟨destination, read, rest⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨result, typed, checked⟩ := Option.bind_eq_some_iff.mp rest
    cases checked
    rw [execute, instruction_agrees code state result destination typed read]
    rfl
  | seq first second firstIH laterIH =>
    simp only [executeScalar, Option.bind_eq_bind] at accepted
    obtain ⟨middle, computed, later⟩ := Option.bind_eq_some_iff.mp accepted
    have seen := firstIH state middle computed
    cases middle with
    | following registers =>
      rw [execute, show execute state first = .continuing { state with registers } from seen]
      exact laterIH {state with registers} expected later
    | returned status payload =>
      cases later
      obtain ⟨registers, finished⟩ := seen
      rw [execute, finished]
      exact ⟨registers, rfl⟩
  | branch condition yes no yesIH noIH =>
    by_cases trueValue : state.registers condition = 1
    · rw [execute, if_pos trueValue]
      apply yesIH
      simpa only [executeScalar, if_pos trueValue] using accepted
    · by_cases falseValue : state.registers condition = 0
      · rw [execute, if_neg trueValue, if_pos falseValue]
        apply noIH
        simpa only [executeScalar, if_neg trueValue, if_pos falseValue] using accepted
      · unfold executeScalar at accepted
        rw [if_neg trueValue, if_neg falseValue] at accepted
        cases accepted
  | ret status payload =>
    cases accepted
    exact ⟨state.registers, rfl⟩
  | fund | counted | early => cases accepted

def writes : Stmt → Finset Reg
  | .instruction code => code.destination?.toList.toFinset
  | .seq first second | .branch _ first second => writes first ∪ writes second
  | .counted index _ _ body | .early index _ _ _ body => insert index (writes body)
  | _ => ∅

theorem continuing_retains (code : Stmt) (before after : Registers) (register : Reg)
    (outside : register ∉ writes code)
    (ran : executeScalar before code = some (.following after)) :
    after register = before register := by
  induction code generalizing before after with
  | skip => cases ran; rfl
  | instruction instruction =>
    simp only [executeScalar, Option.bind_eq_bind] at ran
    obtain ⟨destination, located, rest⟩ := Option.bind_eq_some_iff.mp ran
    obtain ⟨value, _, last⟩ := Option.bind_eq_some_iff.mp rest
    cases last
    simp [writes, located] at outside
    exact Function.update_of_ne outside ..
  | seq first second ihFirst ihSecond =>
    simp only [executeScalar, Option.bind_eq_bind] at ran
    obtain ⟨middle, entered, later⟩ := Option.bind_eq_some_iff.mp ran
    have separate := Finset.notMem_union.mp outside
    cases middle with
    | following interim =>
      exact (ihSecond interim after separate.2 later).trans (ihFirst before interim separate.1 entered)
    | returned => cases later
  | branch condition yes no ihYes ihNo =>
    have separate := Finset.notMem_union.mp outside
    simp only [executeScalar] at ran
    split at ran
    · exact ihYes before after separate.1 ran
    · split at ran
      · exact ihNo before after separate.2 ran
      · cases ran
  | ret | fund | counted | early => cases ran

private def joinWrites : Option (Finset Reg) → Option (Finset Reg) → Option (Finset Reg)
  | none, right => right
  | left, none => left
  | some left, some right => some (left ∪ right)

/-- Registers that can change along a scalar path that continues.
The payload register of a decline need not be reserved by its caller. -/
def continuingWrites : Stmt → Option (Finset Reg)
  | .skip => some ∅
  | .instruction instruction => some (instruction.destination?.toList.toFinset)
  | .seq first second => do
    let left ← continuingWrites first
    let right ← continuingWrites second
    return left ∪ right
  | .branch _ yes no => joinWrites (continuingWrites yes) (continuingWrites no)
  | _ => none

private theorem join_left {left : Finset Reg} (right : Option (Finset Reg)) :
    ∃ writes, joinWrites (some left) right = some writes ∧ left ⊆ writes := by
  cases right
  · exact ⟨left, rfl, Set.Subset.rfl⟩
  · exact ⟨_, rfl, Finset.subset_union_left⟩

private theorem join_right (left : Option (Finset Reg)) {right : Finset Reg} :
    ∃ writes, joinWrites left (some right) = some writes ∧ right ⊆ writes := by
  cases left
  · exact ⟨right, rfl, Set.Subset.rfl⟩
  · exact ⟨_, rfl, Finset.subset_union_right⟩

theorem continuing_scope (code : Stmt) (before after : Registers)
    (ran : executeScalar before code = some (.following after)) :
    ∃ footprint, continuingWrites code = some footprint ∧
      ∀ register ∉ footprint, after register = before register := by
  induction code generalizing before after with
  | skip =>
    cases ran
    exact ⟨∅, rfl, fun _ _ => rfl⟩
  | instruction code =>
    exact ⟨writes (.instruction code), rfl,
      fun register outside => continuing_retains _ _ _ register outside ran⟩
  | seq first second ihFirst ihSecond =>
    simp only [executeScalar, Option.bind_eq_bind] at ran
    obtain ⟨middle, started, remained⟩ := Option.bind_eq_some_iff.mp ran
    cases middle with
    | returned => cases remained
    | following next =>
      obtain ⟨left, one, keepsLeft⟩ := ihFirst before next started
      obtain ⟨right, two, keepsRight⟩ := ihSecond next after remained
      refine ⟨left ∪ right, ?_, ?_⟩
      · simp [continuingWrites, one, two]
      · intro register outside
        obtain ⟨leftOut, rightOut⟩ := Finset.notMem_union.mp outside
        exact (keepsRight register rightOut).trans (keepsLeft register leftOut)
  | branch condition yes no ihYes ihNo =>
    simp only [executeScalar] at ran
    split at ran
    · obtain ⟨first, known, preserved⟩ := ihYes before after ran
      obtain ⟨all, joined, included⟩ := join_left (continuingWrites no) (left := first)
      refine ⟨all, ?_, fun register outside => preserved register (fun present => outside (included present))⟩
      simpa only [continuingWrites, known] using joined
    · split at ran
      · obtain ⟨later, known, preserved⟩ := ihNo before after ran
        obtain ⟨all, joined, included⟩ := join_right (continuingWrites yes) (right := later)
        refine ⟨all, ?_, fun register outside => preserved register (fun present => outside (included present))⟩
        simpa only [continuingWrites, known] using joined
      · cases ran
  | ret | fund | counted | early => cases ran

end Mettapedia.Machines.TIsa.P1WordScalar
