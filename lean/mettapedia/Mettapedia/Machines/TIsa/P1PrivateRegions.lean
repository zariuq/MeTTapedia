import Mettapedia.Machines.TIsa.P1WordExecution

/-!
# Private memory of a prepared p1 slice

Replacing memory outside the mapped capabilities commutes with execution,
including loop turns, early returns and exhausted dispatch fuel.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.P1PrivateRegions

open P1Source P1WordExecution

def InRegion (regions : Region → Capability) (key : Nat) : Prop :=
  ∃ region : Region, (regions region).mode ≠ .absent ∧
    (regions region).base.toNat ≤ key ∧
    key < (regions region).base.toNat + (regions region).length.toNat

abbrev Words := Nat → Option Word

noncomputable def replace (outside : Words) (state : State) : State := by
  classical
  exact {state with memory := fun key =>
    if (InRegion state.regions key) then state.memory key else outside key}

theorem reads_inside (outside : Words) (state : State) (key : Nat)
    (inside : InRegion state.regions key) :
    (replace outside state).memory key = state.memory key := by
  classical
  simp [replace, inside]

theorem reads_outside (outside : Words) (state : State) (key : Nat)
    (elsewhere : ¬InRegion state.regions key) :
    (replace outside state).memory key = outside key := by
  classical
  simp [replace, elsewhere]

private theorem replace_write (outside : Words) (state : State) (register : Reg) (word : Word) :
    replace outside (state.write register word) = (replace outside state).write register word := rfl

private theorem replace_store (outside : Words) (state : State) (key : Nat) (word : Word)
    (inside : InRegion state.regions key) :
    replace outside (state.store key word) = (replace outside state).store key word := by
  classical
  unfold replace State.store
  congr 1
  funext other
  by_cases atWrite : other = key
  · subst other
    simp [inside]
  · simp only [Function.update_of_ne atWrite]

private theorem address_inside {state : State} {region : Region} {pointer : Word}
    {displacement : BitVec 32} {key : Nat}
    (usable : (state.regions region).mode ≠ .absent)
    (located : wordAddress (state.regions region) pointer displacement = some key) :
    InRegion state.regions key := by
  unfold wordAddress at located
  obtain ⟨physical, mapped, aligned⟩ := Option.bind_eq_some_iff.mp located
  have same : physical = key := by
    split at aligned
    · exact Option.some.inj aligned
    · cases aligned
  subst physical
  have range := Memory.access?_inside (state.regions region).base
    (state.regions region).length pointer displacement.toInt 8 key 0 mapped (by decide)
  exact ⟨region, usable, by simpa [ByteRange.Contains, ByteRange.stop] using range⟩

noncomputable def mapResult (outside : Words) : Except ExitStatus State → Except ExitStatus State
  | .error status => .error status
  | .ok state => .ok (replace outside state)

private theorem instruction_replace (outside : Words) (state : State) (code : Instr) :
    instruction (replace outside state) code = mapResult outside (instruction state code) := by
  have registers : (replace outside state).registers = state.registers := rfl
  have regions : (replace outside state).regions = state.regions := rfl
  have frame : (replace outside state).frame = state.frame := rfl
  cases code with
  | loadFrame type destination slot =>
    simp only [instruction, frame]
    split
    · rw [mapResult, replace_write]
    · rfl
  | address region dst base index scale displacement =>
    simp only [instruction, regions, registers]
    split
    · rfl
    · split
      · rw [mapResult, replace_write]
      · rfl
  | load type width region dst src displacement =>
    cases width
    · rfl
    · rfl
    · simp only [instruction, regions, registers]
      split
      next _ => rfl
      next available =>
        cases located : wordAddress (state.regions region) (state.registers src) displacement with
        | none => rfl
        | some key =>
          simp only [Option.bind_some, reads_inside outside state key (address_inside available located)]
          cases stored : state.memory key with
          | none => rfl
          | some word =>
            dsimp only
            cases P1Memory.checkedWord type word with
            | none => rfl
            | some value =>
              change Except.ok ((replace outside state).write dst value) =
                Except.ok (replace outside (state.write dst value))
              exact congrArg Except.ok (replace_write outside state dst value).symm
  | store width region base displacement source =>
    cases width
    · rfl
    · rfl
    · simp only [instruction, regions, registers]
      split
      next _ => rfl
      next canWrite =>
        cases located : wordAddress (state.regions region) (state.registers base) displacement with
        | none => rfl
        | some key =>
          have writable : (state.regions region).mode = .readWrite := not_not.mp canWrite
          have available : (state.regions region).mode ≠ .absent := by rw [writable]; decide
          change Except.ok ((replace outside state).store key (state.registers source)) =
            Except.ok (replace outside (state.store key (state.registers source)))
          exact congrArg Except.ok (replace_store outside state key _ (address_inside available located)).symm
  | _ =>
    simp only [instruction, scalarInstruction, registers]
    split
    · rfl
    · split
      · rw [mapResult, replace_write]
      · rfl

noncomputable def mapFlow (outside : Words) : Flow → Flow
  | .continuing state => .continuing (replace outside state)
  | .returned status payload state => .returned status payload (replace outside state)

private theorem guard_replace (outside : Words) (state : State) (guard : Option Reg) (next : State → Flow)
    (same : ∀ before, next (replace outside before) = mapFlow outside (next before)) :
    continueLoop (replace outside state) guard next = mapFlow outside (continueLoop state guard next) := by
  cases guard with
  | none => exact same state
  | some reg =>
    have reads : (replace outside state).registers reg = state.registers reg := rfl
    simp only [continueLoop, reads, same]
    split
    · rfl
    · split <;> rfl

private theorem loop_replace (outside : Words) (body : State → Flow) (index : Reg) (guard : Option Reg)
    (same : ∀ state, body (replace outside state) = mapFlow outside (body state))
    (count : Nat) (state : State) :
    loop body index guard count (replace outside state) = mapFlow outside (loop body index guard count state) := by
  induction count generalizing state with
  | zero => rfl
  | succ remaining ih =>
    simp only [loop]
    apply guard_replace
    intro started
    rw [same]
    cases ran : body started with
    | returned => rfl
    | continuing after =>
      simp only [mapFlow, Flow.thenContinue]
      apply guard_replace
      intro following
      change loop body index guard remaining ((replace outside following).write index
        (following.registers index + 1)) = _
      rw [← replace_write]
      exact ih _

theorem executes_in_regions (outside : Words) (state : State) (code : Stmt) :
    execute (replace outside state) code = mapFlow outside (execute state code) := by
  induction code generalizing state with
  | skip | ret => rfl
  | instruction code =>
    simp only [execute, instruction_replace]
    cases instruction state code <;> rfl
  | seq first rest ihFirst ihRest =>
    simp only [execute, ihFirst]
    cases execute state first with
    | continuing reached => exact ihRest reached
    | returned => rfl
  | branch condition yes no ihYes ihNo =>
    have flag : (replace outside state).registers condition = state.registers condition := rfl
    simp only [execute, flag]
    split
    · exact ihYes state
    · split
      · exact ihNo state
      · rfl
  | fund units =>
    have budget : (replace outside state).budget = state.budget := rfl
    have spent : (replace outside state).spent = state.spent := rfl
    simp only [execute, fund, budget, spent]
    split <;> rfl
  | counted index bound cap body ih =>
    have actual : (replace outside state).registers bound = state.registers bound := rfl
    simp only [execute, actual]
    split
    · rfl
    · rw [← replace_write]
      exact loop_replace outside (execute · body) index none ih _ _
  | early index bound guard cap body ih =>
    have actual : (replace outside state).registers bound = state.registers bound := rfl
    simp only [execute, actual]
    split
    · rfl
    · rw [← replace_write]
      exact loop_replace outside (execute · body) index (some guard) ih _ _

private theorem replace_self (state : State) : replace state.memory state = state := by
  classical
  cases state
  simp [replace]

theorem outside_is_untouched (state : State) (code : Stmt) (key : Nat)
    (outside : ¬InRegion (execute state code).after.regions key) :
    (execute state code).after.memory key = state.memory key := by
  have ran := executes_in_regions state.memory state code
  rw [replace_self] at ran
  have same (outcome : Flow) : (mapFlow state.memory outcome).after =
      replace state.memory outcome.after := by cases outcome <;> rfl
  have observes := congrArg Flow.after ran
  rw [same] at observes
  rw [observes, reads_outside _ _ _ outside]

end Mettapedia.Machines.TIsa.P1PrivateRegions
