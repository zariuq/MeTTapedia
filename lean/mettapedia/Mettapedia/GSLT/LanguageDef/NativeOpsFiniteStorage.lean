import Mettapedia.GSLT.LanguageDef.NativeOpsSourceFunctions
import Mettapedia.GSLT.LanguageDef.NativeOpsTargetFunctions

/-!
# Finite storage support and fresh invocation frames

The support bound ranges over logical storage identities, independently of
guest words, cell positions and execution lengths. It may grow after every
allocation or declaration. Empty storage at the bound supplies a fresh frame.

The preservation laws concern the defined memory operations and parameter
binding. Arbitrary abstract allocator and external-call relations need their
own support laws; they cannot obtain them from the evaluator's type alone.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

def SourceStorageBound (memory : SourceMemory) (bound : Nat) : Prop :=
  ∀ storage, bound ≤ storage →
    memory.owned storage = none ∧ ∀ position, memory.cells storage position = none

def TargetStorageBound (memory : TargetMemory) (bound : Nat) : Prop :=
  ∀ storage, bound ≤ storage →
    memory.owned storage = none ∧ ∀ position, memory.cells storage position = none

def SourceFiniteStorage (memory : SourceMemory) : Prop :=
  ∃ bound, SourceStorageBound memory bound

def TargetFiniteStorage (memory : TargetMemory) : Prop :=
  ∃ bound, TargetStorageBound memory bound

theorem source_storage_bound_mono {memory : SourceMemory} {bound larger : Nat}
    (bounded : SourceStorageBound memory bound) (increase : bound ≤ larger) :
    SourceStorageBound memory larger :=
  fun storage above => bounded storage (Nat.le_trans increase above)

theorem target_storage_bound_mono {memory : TargetMemory} {bound larger : Nat}
    (bounded : TargetStorageBound memory bound) (increase : bound ≤ larger) :
    TargetStorageBound memory larger :=
  fun storage above => bounded storage (Nat.le_trans increase above)

theorem source_finite_fresh {memory : SourceMemory} (finite : SourceFiniteStorage memory) :
    ∃ storage, sourceFreshFrame memory storage := by
  obtain ⟨bound, bounded⟩ := finite
  have empty := bounded bound (Nat.le_refl bound)
  exact ⟨bound, empty.2, empty.1⟩

theorem target_finite_fresh {memory : TargetMemory} (finite : TargetFiniteStorage memory) :
    ∃ storage, targetFreshFrame memory storage := by
  obtain ⟨bound, bounded⟩ := finite
  exact ⟨bound, bounded bound (Nat.le_refl bound)⟩

theorem storage_bound_correspondence {source : SourceMemory} {target : TargetMemory}
    (related : MemoryRelated source target) (bound : Nat) :
    SourceStorageBound source bound ↔ TargetStorageBound target bound := by
  constructor
  · intro bounded storage above
    obtain ⟨owned, cells⟩ := bounded storage above
    constructor
    · rw [related.2 storage, owned]
      rfl
    · intro position
      rw [related.1 storage position, cells position]
      rfl
  · intro bounded storage above
    obtain ⟨owned, cells⟩ := bounded storage above
    constructor
    · cases selected : source.owned storage with
      | none => rfl
      | some extent =>
          have impossible : some (NativeWord64.encode extent) = none := by
            simpa only [related.2 storage, selected, Option.map_some] using owned
          cases impossible
    · intro position
      cases selected : source.cells storage position with
      | none => rfl
      | some value =>
          have impossible : some (encodeValue value) = none := by
            simpa only [related.1 storage position, selected, Option.map_some] using cells position
          cases impossible

theorem finite_storage_correspondence {source : SourceMemory} {target : TargetMemory}
    (related : MemoryRelated source target) :
    SourceFiniteStorage source ↔ TargetFiniteStorage target := by
  constructor
  · rintro ⟨bound, bounded⟩
    exact ⟨bound, (storage_bound_correspondence related bound).mp bounded⟩
  · rintro ⟨bound, bounded⟩
    exact ⟨bound, (storage_bound_correspondence related bound).mpr bounded⟩

theorem source_store_cell_below_bound {memory : SourceMemory} {bound storage : Nat}
    (bounded : SourceStorageBound memory bound) (inside : storage < bound)
    (position : Nat) (value : SourceValue) :
    SourceStorageBound (sourceStoreCell memory storage position value) bound := by
  intro candidate above
  obtain ⟨owned, cells⟩ := bounded candidate above
  have different : candidate ≠ storage := by
    intro same
    subst candidate
    exact Nat.not_le_of_gt inside above
  constructor
  · exact owned
  · intro index
    change (if candidate = storage ∧ index = position then some value
      else memory.cells candidate index) = none
    rw [if_neg (fun hit => different hit.1)]
    exact cells index

theorem target_store_cell_below_bound {memory : TargetMemory} {bound storage : Nat}
    (bounded : TargetStorageBound memory bound) (inside : storage < bound)
    (position : Nat) (value : TargetValue) :
    TargetStorageBound (targetStoreCell memory storage position value) bound := by
  intro candidate above
  obtain ⟨owned, cells⟩ := bounded candidate above
  have different : candidate ≠ storage := by
    intro same
    subst candidate
    exact Nat.not_le_of_gt inside above
  exact ⟨owned, fun index => by
    simp only [targetStoreCell, if_neg different]
    exact cells index⟩

theorem source_store_cell_bound {memory : SourceMemory} {bound : Nat}
    (bounded : SourceStorageBound memory bound) (storage position : Nat) (value : SourceValue) :
    SourceStorageBound (sourceStoreCell memory storage position value) (max bound (storage + 1)) :=
  source_store_cell_below_bound
    (source_storage_bound_mono bounded (Nat.le_max_left _ _))
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self storage) (Nat.le_max_right _ _)) position value

theorem target_store_cell_bound {memory : TargetMemory} {bound : Nat}
    (bounded : TargetStorageBound memory bound) (storage position : Nat) (value : TargetValue) :
    TargetStorageBound (targetStoreCell memory storage position value) (max bound (storage + 1)) :=
  target_store_cell_below_bound
    (target_storage_bound_mono bounded (Nat.le_max_left _ _))
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self storage) (Nat.le_max_right _ _)) position value

theorem source_store_cell_finite {memory : SourceMemory} (finite : SourceFiniteStorage memory)
    (storage position : Nat) (value : SourceValue) :
    SourceFiniteStorage (sourceStoreCell memory storage position value) := by
  obtain ⟨bound, bounded⟩ := finite
  exact ⟨max bound (storage + 1), source_store_cell_bound bounded storage position value⟩

theorem target_store_cell_finite {memory : TargetMemory} (finite : TargetFiniteStorage memory)
    (storage position : Nat) (value : TargetValue) :
    TargetFiniteStorage (targetStoreCell memory storage position value) := by
  obtain ⟨bound, bounded⟩ := finite
  exact ⟨max bound (storage + 1), target_store_cell_bound bounded storage position value⟩

theorem source_write_bound {memory post : SourceMemory} {bound : Nat}
    (bounded : SourceStorageBound memory bound) {address : Address} {value : SourceValue}
    (written : sourceWrite memory address value = some post) : SourceStorageBound post bound := by
  cases old : memory.cells address.storage address.element with
  | none => simp only [sourceWrite, old, bind, Option.bind, reduceCtorEq] at written
  | some previous =>
      cases changed : sourceWritePath address.fields value previous with
      | none => simp only [sourceWrite, old, bind, Option.bind, changed, reduceCtorEq] at written
      | some updated =>
          have same : sourceStoreCell memory address.storage address.element updated = post := by
            simpa only [sourceWrite, old, bind, Option.bind, changed, Option.some.injEq] using written
          have inside : address.storage < bound := by
            apply Nat.lt_of_not_ge
            intro above
            have missing := (bounded address.storage above).2 address.element
            rw [old] at missing
            cases missing
          rw [← same]
          exact source_store_cell_below_bound bounded inside address.element updated

theorem target_write_bound {memory post : TargetMemory} {bound : Nat}
    (bounded : TargetStorageBound memory bound) {address : Address} {value : TargetValue}
    (written : targetWrite memory address value = some post) : TargetStorageBound post bound := by
  cases old : memory.cells address.storage address.element with
  | none => simp only [targetWrite, old, bind, Option.bind, reduceCtorEq] at written
  | some previous =>
      cases changed : targetWritePath address.fields value previous with
      | none => simp only [targetWrite, old, bind, Option.bind, changed, reduceCtorEq] at written
      | some updated =>
          have same : targetStoreCell memory address.storage address.element updated = post := by
            simpa only [targetWrite, old, bind, Option.bind, changed, Option.some.injEq] using written
          have inside : address.storage < bound := by
            apply Nat.lt_of_not_ge
            intro above
            have missing := (bounded address.storage above).2 address.element
            rw [old] at missing
            cases missing
          rw [← same]
          exact target_store_cell_below_bound bounded inside address.element updated

theorem source_write_finite {memory post : SourceMemory} (finite : SourceFiniteStorage memory)
    {address : Address} {value : SourceValue} (written : sourceWrite memory address value = some post) :
    SourceFiniteStorage post := by
  obtain ⟨bound, bounded⟩ := finite
  exact ⟨bound, source_write_bound bounded written⟩

theorem target_write_finite {memory post : TargetMemory} (finite : TargetFiniteStorage memory)
    {address : Address} {value : TargetValue} (written : targetWrite memory address value = some post) :
    TargetFiniteStorage post := by
  obtain ⟨bound, bounded⟩ := finite
  exact ⟨bound, target_write_bound bounded written⟩

theorem source_release_bound {memory : SourceMemory} {bound : Nat}
    (bounded : SourceStorageBound memory bound) (storage : Nat) :
    SourceStorageBound (sourceRelease memory storage) bound := by
  intro candidate above
  obtain ⟨owned, cells⟩ := bounded candidate above
  constructor
  · by_cases same : candidate = storage <;> simp only [sourceRelease, same, if_true, if_false, owned]
  · intro position
    by_cases same : candidate = storage <;> simp only [sourceRelease, same, if_true, if_false, cells position]

theorem target_release_bound {memory : TargetMemory} {bound : Nat}
    (bounded : TargetStorageBound memory bound) (storage : Nat) :
    TargetStorageBound (targetRelease memory storage) bound := by
  intro candidate above
  obtain ⟨owned, cells⟩ := bounded candidate above
  constructor
  · by_cases same : candidate = storage <;> simp only [targetRelease, same, if_true, if_false, owned]
  · intro position
    by_cases same : candidate = storage <;> simp only [targetRelease, same, if_true, if_false, cells position]

theorem source_release_finite {memory : SourceMemory} (finite : SourceFiniteStorage memory)
    (storage : Nat) : SourceFiniteStorage (sourceRelease memory storage) := by
  obtain ⟨bound, bounded⟩ := finite
  exact ⟨bound, source_release_bound bounded storage⟩

theorem target_release_finite {memory : TargetMemory} (finite : TargetFiniteStorage memory)
    (storage : Nat) : TargetFiniteStorage (targetRelease memory storage) := by
  obtain ⟨bound, bounded⟩ := finite
  exact ⟨bound, target_release_bound bounded storage⟩

theorem source_drop_locals_bound {memory : SourceMemory} {bound : Nat}
    (bounded : SourceStorageBound memory bound) (storage first last : Nat) :
    SourceStorageBound (sourceDropLocals memory storage first last) bound := by
  intro candidate above
  obtain ⟨owned, cells⟩ := bounded candidate above
  constructor
  · exact owned
  · intro position
    change (if candidate = storage ∧ first ≤ position ∧ position < last then none
      else memory.cells candidate position) = none
    by_cases dropped : candidate = storage ∧ first ≤ position ∧ position < last
    · rw [if_pos dropped]
    · rw [if_neg dropped]
      exact cells position

theorem target_drop_locals_bound {memory : TargetMemory} {bound : Nat}
    (bounded : TargetStorageBound memory bound) (storage first last : Nat) :
    TargetStorageBound (targetDropLocals memory storage first last) bound := by
  intro candidate above
  obtain ⟨owned, cells⟩ := bounded candidate above
  constructor
  · exact owned
  · intro position
    change (if candidate = storage then
      if first ≤ position then
        if position < last then none else memory.cells candidate position
      else memory.cells candidate position
      else memory.cells candidate position) = none
    by_cases same : candidate = storage
    · rw [if_pos same]
      by_cases lower : first ≤ position
      · rw [if_pos lower]
        by_cases upper : position < last
        · rw [if_pos upper]
        · rw [if_neg upper]
          exact cells position
      · rw [if_neg lower]
        exact cells position
    · rw [if_neg same]
      exact cells position

theorem source_drop_locals_finite {memory : SourceMemory} (finite : SourceFiniteStorage memory)
    (storage first last : Nat) : SourceFiniteStorage (sourceDropLocals memory storage first last) := by
  obtain ⟨bound, bounded⟩ := finite
  exact ⟨bound, source_drop_locals_bound bounded storage first last⟩

theorem target_drop_locals_finite {memory : TargetMemory} (finite : TargetFiniteStorage memory)
    (storage first last : Nat) : TargetFiniteStorage (targetDropLocals memory storage first last) := by
  obtain ⟨bound, bounded⟩ := finite
  exact ⟨bound, target_drop_locals_bound bounded storage first last⟩

theorem source_declare_local_bound {World : Type} {state : SourceState World} {bound : Nat}
    (bounded : SourceStorageBound state.memory bound) (frame : SourceFrame)
    (name : String) (type : NativeType) (value : SourceValue) :
    SourceStorageBound (sourceDeclareLocal frame state name type value).2.memory
      (max bound (frame.storage + 1)) :=
  source_store_cell_bound bounded frame.storage frame.nextLocal value

theorem target_declare_local_bound {World : Type} {state : TargetState World} {bound : Nat}
    (bounded : TargetStorageBound state.memory bound) (frame : TargetFrame)
    (name : String) (type : NativeType) (value : TargetValue) :
    TargetStorageBound (targetDeclareLocal frame state name type value).2.memory
      (max bound (frame.storage + 1)) :=
  target_store_cell_bound bounded frame.storage frame.nextLocal value

theorem source_declare_local_finite {World : Type} {state : SourceState World}
    (finite : SourceFiniteStorage state.memory) (frame : SourceFrame)
    (name : String) (type : NativeType) (value : SourceValue) :
    SourceFiniteStorage (sourceDeclareLocal frame state name type value).2.memory :=
  source_store_cell_finite finite frame.storage frame.nextLocal value

theorem target_declare_local_finite {World : Type} {state : TargetState World}
    (finite : TargetFiniteStorage state.memory) (frame : TargetFrame)
    (name : String) (type : NativeType) (value : TargetValue) :
    TargetFiniteStorage (targetDeclareLocal frame state name type value).2.memory :=
  target_store_cell_finite finite frame.storage frame.nextLocal value

theorem source_leave_scope_bound {World : Type} {state : SourceState World} {bound : Nat}
    (bounded : SourceStorageBound state.memory bound) (marker frame : SourceFrame) :
    SourceStorageBound (sourceLeaveScope marker frame state).2.memory bound :=
  source_drop_locals_bound bounded frame.storage marker.nextLocal frame.nextLocal

theorem target_leave_scope_bound {World : Type} {state : TargetState World} {bound : Nat}
    (bounded : TargetStorageBound state.memory bound) (marker frame : TargetFrame) :
    TargetStorageBound (targetLeaveScope marker frame state).2.memory bound :=
  target_drop_locals_bound bounded frame.storage marker.nextLocal frame.nextLocal

theorem source_leave_scope_finite {World : Type} {state : SourceState World}
    (finite : SourceFiniteStorage state.memory) (marker frame : SourceFrame) :
    SourceFiniteStorage (sourceLeaveScope marker frame state).2.memory :=
  source_drop_locals_finite finite frame.storage marker.nextLocal frame.nextLocal

theorem target_leave_scope_finite {World : Type} {state : TargetState World}
    (finite : TargetFiniteStorage state.memory) (marker frame : TargetFrame) :
    TargetFiniteStorage (targetLeaveScope marker frame state).2.memory :=
  target_drop_locals_finite finite frame.storage marker.nextLocal frame.nextLocal

theorem source_bind_parameters_finite {World : Type} (parameters : List Parameter)
    {arguments : List SourceValue} {frame outFrame : SourceFrame} {state outState : SourceState World}
    (finite : SourceFiniteStorage state.memory)
    (bound : sourceBindParameters parameters arguments frame state = some (outFrame, outState)) :
    SourceFiniteStorage outState.memory := by
  induction parameters generalizing arguments frame state with
  | nil =>
      cases arguments with
      | nil =>
          have same : (frame, state) = (outFrame, outState) := Option.some.inj bound
          cases same
          exact finite
      | cons value rest => cases bound
  | cons parameter parameters ih =>
      cases arguments with
      | nil => cases bound
      | cons value values =>
          exact ih
            (source_declare_local_finite finite frame parameter.name parameter.type value) bound

theorem target_bind_parameters_finite {World : Type} (parameters : List Parameter)
    {arguments : List TargetValue} {frame outFrame : TargetFrame} {state outState : TargetState World}
    (finite : TargetFiniteStorage state.memory)
    (bound : targetBindParameters parameters arguments frame state = some (outFrame, outState)) :
    TargetFiniteStorage outState.memory := by
  induction parameters generalizing arguments frame state with
  | nil =>
      cases arguments with
      | nil =>
          have same : (frame, state) = (outFrame, outState) := Option.some.inj bound
          cases same
          exact finite
      | cons value rest => cases bound
  | cons parameter parameters ih =>
      cases arguments with
      | nil => cases bound
      | cons value values =>
          exact ih
            (target_declare_local_finite finite frame parameter.name parameter.type value) bound

theorem empty_source_storage_bound :
    SourceStorageBound ⟨fun _ _ => none, fun _ => none⟩ 0 :=
  fun _ _ => ⟨rfl, fun _ => rfl⟩

theorem empty_target_storage_bound :
    TargetStorageBound ⟨fun _ _ => none, fun _ => none⟩ 0 :=
  fun _ _ => ⟨rfl, fun _ => rfl⟩

theorem empty_source_storage_finite :
    SourceFiniteStorage ⟨fun _ _ => none, fun _ => none⟩ :=
  ⟨0, empty_source_storage_bound⟩

theorem empty_target_storage_finite :
    TargetFiniteStorage ⟨fun _ _ => none, fun _ => none⟩ :=
  ⟨0, empty_target_storage_bound⟩

theorem infinite_source_cells_not_finite :
    ¬ SourceFiniteStorage ⟨fun _ _ => some .unit, fun _ => none⟩ := by
  rintro ⟨bound, bounded⟩
  have impossible : (some .unit : Option SourceValue) = none :=
    (bounded bound (Nat.le_refl bound)).2 0
  cases impossible

theorem infinite_target_cells_not_finite :
    ¬ TargetFiniteStorage ⟨fun _ _ => some .unit, fun _ => none⟩ := by
  rintro ⟨bound, bounded⟩
  have impossible : (some .unit : Option TargetValue) = none :=
    (bounded bound (Nat.le_refl bound)).2 0
  cases impossible

theorem infinite_source_cells_no_fresh_frame :
    ¬ ∃ storage, sourceFreshFrame ⟨fun _ _ => some .unit, fun _ => none⟩ storage := by
  rintro ⟨storage, fresh⟩
  have impossible : (some .unit : Option SourceValue) = none := fresh.1 0
  cases impossible

theorem infinite_target_cells_no_fresh_frame :
    ¬ ∃ storage, targetFreshFrame ⟨fun _ _ => some .unit, fun _ => none⟩ storage := by
  rintro ⟨storage, fresh⟩
  have impossible : (some .unit : Option TargetValue) = none := fresh.2 0
  cases impossible

end Mettapedia.GSLT.LanguageDef.NativeOps
