import Mettapedia.GSLT.LanguageDef.NativeOpsTargetFunctions

/-!
# Target invocation-cell readback and teardown

Parameter storage is an actual cell in the independent target memory.
Teardown removes that cell and restores the caller memory when invocation
storage was fresh. Private temporaries and arm scope changes do not alter the
storage extent used to release the parameter.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

/-- Ordered parameter-cell contents, independent of parameter names and
types. The actual invocation binder is compared with this memory fold below. -/
def targetParameterMemory (memory : TargetMemory) (storage first : Nat) :
    List TargetValue → TargetMemory
  | [] => memory
  | value :: rest => targetParameterMemory (targetStoreCell memory storage first value)
      storage (first + 1) rest

/-- Actual successful binding preserves the complete caller state outside
its ordered parameter cells, and derives the allocation extent and arity. -/
theorem target_bind_parameters_facts {World : Type} (parameters : List Parameter)
    (arguments : List TargetValue) (frame : TargetFrame) (state : TargetState World)
    (after : TargetFrame) (post : TargetState World)
    (bound : targetBindParameters parameters arguments frame state = some (after, post)) :
    parameters.length = arguments.length ∧ after.storage = frame.storage ∧
      after.nextLocal = frame.nextLocal + arguments.length ∧
      post = { state with memory := (targetParameterMemory state.memory frame.storage
        frame.nextLocal arguments) } := by
  induction parameters generalizing arguments frame state after post with
  | nil =>
    cases arguments with
    | nil =>
      have pair := Option.some.inj bound
      obtain ⟨sameFrame, sameState⟩ := Prod.mk.inj pair
      subst after
      subst post
      exact ⟨rfl, rfl, Nat.add_zero _, rfl⟩
    | cons _ _ => cases bound
  | cons parameter rest ih =>
    cases arguments with
    | nil => cases bound
    | cons value values =>
      let declared := targetDeclareLocal frame state parameter.name parameter.type value
      have facts := ih values declared.1 declared.2 after post bound
      refine ⟨by simpa only [List.length_cons] using congrArg Nat.succ facts.1,
        facts.2.1, ?_, ?_⟩
      · have extent : after.nextLocal = frame.nextLocal + 1 + values.length := facts.2.2.1
        simp only [List.length_cons]
        omega
      · simpa only [declared, targetDeclareLocal, targetParameterMemory] using facts.2.2.2

theorem target_singleton_parameter_readback {World : Type}
    (state : TargetState World) (storage : Nat) (parameter : Parameter) (value : TargetValue) :
    let bound := targetDeclareLocal (targetEmptyFrame storage) state parameter.name parameter.type value
    targetLocalValue bound.1 bound.2 parameter.name = some value := by
  have emptyPath (contents : TargetValue) : targetReadPath [] contents = some contents := by
    cases contents <;> rfl
  have self : (parameter.name == parameter.name) = true := decide_eq_true rfl
  dsimp only [targetDeclareLocal, targetEmptyFrame, targetLocalValue, targetLocalAddress,
    targetRead, targetStoreCell]
  rw [List.find?_cons_of_pos (p := fun binding : LocalBinding => binding.name == parameter.name)
    (a := ⟨parameter.name, parameter.type, 0⟩) self]
  change (if storage = storage then
      (if (0 : Nat) = 0 then some value else state.memory.cells storage 0)
    else state.memory.cells storage 0).bind (targetReadPath []) = some value
  rw [if_pos rfl, if_pos rfl]
  exact emptyPath value

/-- Removing a lexical interval from unused invocation storage changes no
caller cell. The extent is independent of the number of function parameters. -/
theorem targetDropLocals_fresh {memory : TargetMemory} {storage : Nat}
    (fresh : targetFreshFrame memory storage) (first last : Nat) :
    targetDropLocals memory storage first last = memory := by
  have cells : (targetDropLocals memory storage first last).cells = memory.cells := by
    funext candidate position
    by_cases same : candidate = storage
    · subst candidate
      simp [targetDropLocals, fresh.2]
    · simp [targetDropLocals, same]
  exact congrArg (fun cells => TargetMemory.mk cells memory.owned) cells

theorem targetDropLocals_storeCell_inside (memory : TargetMemory)
    (storage first last position : Nat) (value : TargetValue)
    (low : first ≤ position) (high : position < last) :
    targetDropLocals (targetStoreCell memory storage position value) storage first last =
      targetDropLocals memory storage first last := by
  have cells : (targetDropLocals (targetStoreCell memory storage position value)
      storage first last).cells = (targetDropLocals memory storage first last).cells := by
    funext candidate index
    by_cases same : candidate = storage
    · subst candidate
      by_cases atCell : index = position
      · subst index
        simp [targetDropLocals, low, high]
      · simp [targetDropLocals, targetStoreCell, atCell]
    · simp [targetDropLocals, targetStoreCell, same]
  exact congrArg (fun cells => TargetMemory.mk cells memory.owned) cells

/-- Dropping the complete allocated interval removes every ordered
parameter write; no per-function enumeration of cells is needed. -/
theorem target_parameter_memory_drop (memory : TargetMemory) (storage first last start : Nat)
    (values : List TargetValue) (low : first ≤ start) (high : start + values.length ≤ last) :
    targetDropLocals (targetParameterMemory memory storage start values) storage first last =
      targetDropLocals memory storage first last := by
  induction values generalizing memory start with
  | nil => rfl
  | cons value rest ih =>
    simp only [targetParameterMemory]
    rw [ih (targetStoreCell memory storage start value) (start + 1)
      (by omega) (by simp only [List.length_cons] at high; omega)]
    exact targetDropLocals_storeCell_inside memory storage first last start value low
      (by simp only [List.length_cons] at high; omega)

/-- Fresh invocation storage is restored after any finite parameter list. -/
theorem target_parameter_memory_release (memory : TargetMemory) (storage : Nat)
    (values : List TargetValue) (fresh : targetFreshFrame memory storage) :
    targetDropLocals (targetParameterMemory memory storage 0 values) storage 0 values.length =
      memory := by
  rw [target_parameter_memory_drop memory storage 0 values.length 0 values
    (Nat.zero_le _) (by simp)]
  exact targetDropLocals_fresh fresh 0 values.length

/-- A write to the caller's separate storage commutes with the whole
parameter-memory fold, retaining undefined writes as undefined. -/
theorem targetWrite_parameter_memory_other_storage (memory : TargetMemory) (storage first : Nat)
    (values : List TargetValue) (address : Address) (replacement : TargetValue)
    (different : address.storage ≠ storage) :
    targetWrite (targetParameterMemory memory storage first values) address replacement =
      (targetWrite memory address replacement).map
        (fun written => targetParameterMemory written storage first values) := by
  induction values generalizing memory first with
  | nil =>
    cases written : targetWrite memory address replacement <;>
      simp only [targetParameterMemory, written, Option.map_none, Option.map_some]
  | cons value rest ih =>
    simp only [targetParameterMemory]
    rw [ih, targetWrite_storeCell_other_storage _ address storage first value replacement different]
    cases targetWrite memory address replacement <;> rfl

/-- The actual binder's parameter cells are released in one law, with
extent and arity obtained from its successful computation. -/
theorem target_bound_parameters_release {World : Type} (parameters : List Parameter)
    (arguments : List TargetValue) (storage : Nat) (state : TargetState World)
    (after : TargetFrame) (post : TargetState World)
    (fresh : targetFreshFrame state.memory storage)
    (bound : targetBindParameters parameters arguments (targetEmptyFrame storage) state =
      some (after, post)) :
    after.storage = storage ∧ after.nextLocal = arguments.length ∧
      targetDropLocals post.memory storage 0 after.nextLocal = state.memory := by
  obtain ⟨_, sameStorage, sameExtent, postExact⟩ :=
    target_bind_parameters_facts parameters arguments (targetEmptyFrame storage) state after post bound
  have extent : after.nextLocal = arguments.length := by simpa only [targetEmptyFrame, Nat.zero_add] using sameExtent
  refine ⟨sameStorage, extent, ?_⟩
  rw [postExact, extent]
  exact target_parameter_memory_release state.memory storage arguments fresh

/-- Omitting freshness can erase an earlier caller cell when the newly
bound parameter is released. Scope cleanup does not restore overwritten data. -/
theorem target_parameter_release_requires_freshness (memory : TargetMemory) (storage : Nat) :
    targetDropLocals (targetParameterMemory (targetStoreCell memory storage 0 (.word 7))
      storage 0 [.word 1]) storage 0 1 ≠ targetStoreCell memory storage 0 (.word 7) := by
  intro same
  have cell := congrArg (fun result => result.cells storage 0) same
  simp [targetParameterMemory, targetDropLocals, targetStoreCell] at cell

theorem target_singleton_cell_released {memory : TargetMemory} {storage : Nat}
    (value : TargetValue) (fresh : targetFreshFrame memory storage) :
    targetDropLocals (targetStoreCell memory storage 0 value) storage 0 1 = memory := by
  rw [targetDropLocals_storeCell_inside memory storage 0 1 0 value (by decide) (by decide)]
  exact targetDropLocals_fresh fresh 0 1

/-- Independent outer writes retain the invocation storage's freshness.
Ownership and every position in that storage are checked, not just the
overflow flag's own location. -/
theorem targetFreshFrame_storeCell_other_storage {memory : TargetMemory} {storage : Nat}
    (fresh : targetFreshFrame memory storage) (other position : Nat) (value : TargetValue)
    (different : storage ≠ other) :
    targetFreshFrame (targetStoreCell memory other position value) storage := by
  exact ⟨fresh.1, fun index => by simp [targetStoreCell, different, fresh.2 index]⟩

theorem targetFreshFrame_after_write {memory written : TargetMemory} {storage : Nat}
    (fresh : targetFreshFrame memory storage) {address : Address} {value : TargetValue}
    (different : storage ≠ address.storage)
    (writeDefined : targetWrite memory address value = some written) :
    targetFreshFrame written storage := by
  cases previous : memory.cells address.storage address.element with
  | none => simp [targetWrite, previous] at writeDefined
  | some before =>
      cases updated : targetWritePath address.fields value before with
      | none => simp [targetWrite, previous, updated] at writeDefined
      | some after =>
          have same : targetStoreCell memory address.storage address.element after = written := by
            simpa [targetWrite, previous, updated] using writeDefined
          rw [← same]
          exact targetFreshFrame_storeCell_other_storage fresh _ _ _ different

/-- A readable caller address cannot lie in a completely fresh invocation
storage. Nullness alone would not justify this separation. -/
theorem targetFreshFrame_storage_ne_read {memory : TargetMemory} {storage : Nat}
    (fresh : targetFreshFrame memory storage) {address : Address} {value : TargetValue}
    (read : targetRead memory address = some value) : storage ≠ address.storage := by
  intro same
  have missing := fresh.2 address.element
  rw [same] at missing
  simp [targetRead, missing] at read

/-- Releasing an invocation interval keeps independently written outer
storage. -/
theorem targetDropLocals_storeCell_other_storage (memory : TargetMemory)
    (storage first last other position : Nat) (value : TargetValue)
    (different : storage ≠ other) :
    targetDropLocals (targetStoreCell memory other position value) storage first last =
      targetStoreCell (targetDropLocals memory storage first last) other position value := by
  have cells : (targetDropLocals (targetStoreCell memory other position value)
      storage first last).cells =
      (targetStoreCell (targetDropLocals memory storage first last) other position value).cells := by
    funext candidate index
    by_cases same : candidate = storage
    · subst candidate
      simp [targetDropLocals, targetStoreCell, different]
    · simp [targetDropLocals, targetStoreCell, same]
  exact congrArg (fun cells => TargetMemory.mk cells memory.owned) cells

/-- Releasing a known invocation extent retains the complete caller state
outside the stated memory update. -/
theorem target_invocation_teardown {World : Type} (state : TargetState World)
    (storage extent : Nat) (current : TargetFrame) (memory restored : TargetMemory)
    (sameStorage : current.storage = storage) (sameExtent : current.nextLocal = extent)
    (released : targetDropLocals memory storage 0 extent = restored) :
    (targetLeaveScope (targetEmptyFrame storage) current { state with memory := memory }).2 =
      { state with memory := restored } := by
  change { state with memory := (targetDropLocals memory current.storage 0 current.nextLocal) } = _
  rw [sameStorage, sameExtent, released]

/-- A conditional outer write and both invocation-release paths retain the
same caller state. This law is independent of any particular function body. -/
theorem target_conditional_invocation_teardown {World : Type} (state : TargetState World)
    (storage extent : Nat) (current : TargetFrame) (final : TargetState World)
    (untouchedParameters writtenParameters writtenMemory : TargetMemory)
    (condition : Prop) [Decidable condition]
    (sameStorage : current.storage = storage) (sameExtent : current.nextLocal = extent)
    (stateExact : final = if condition then { state with memory := writtenParameters }
      else { state with memory := untouchedParameters })
    (releaseUntouched : targetDropLocals untouchedParameters storage 0 extent = state.memory)
    (releaseWritten : targetDropLocals writtenParameters storage 0 extent = writtenMemory) :
    (targetLeaveScope (targetEmptyFrame storage) current final).2 =
      if condition then { state with memory := writtenMemory } else state := by
  by_cases selected : condition
  · rw [if_pos selected] at stateExact ⊢
    rw [stateExact]
    exact target_invocation_teardown state storage extent current writtenParameters
      writtenMemory sameStorage sameExtent releaseWritten
  · rw [if_neg selected] at stateExact ⊢
    rw [stateExact]
    exact target_invocation_teardown state storage extent current untouchedParameters
      state.memory sameStorage sameExtent releaseUntouched

theorem target_singleton_parameter_teardown {World : Type}
    (state : TargetState World) (storage : Nat) (parameter : Parameter) (value : TargetValue)
    (fresh : targetFreshFrame state.memory storage) (current : TargetFrame)
    (sameStorage : current.storage = storage) (extent : current.nextLocal = 1) :
    let bound := targetDeclareLocal (targetEmptyFrame storage) state parameter.name parameter.type value
    (targetLeaveScope (targetEmptyFrame storage) current bound.2).2 = state := by
  change { state with memory := (targetDropLocals
    (targetStoreCell state.memory storage 0 value) current.storage 0 current.nextLocal) } = state
  rw [sameStorage, extent, target_singleton_cell_released value fresh]

end Mettapedia.GSLT.LanguageDef.NativeOps
