import Mettapedia.Machines.CMemory.DependencyCollectionStep
import Mettapedia.Machines.OrderedDependencyCPreparationLoop

/-!
# The retained collection loop over a private physical pending array

Every fresh append gets room from the remaining-input extent. The actual
outer condition, increment, complete body and counter scope are executed.
The specification is ordered identity insertion, independently of the block
interpreter. Module links and the input allocation remain unchanged.

This connection starts after pending storage has been allocated. Allocation,
reservation, cleanup, native byte layout and concurrent currency are separate
obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace Mettapedia.Machines.CMemory.DependencyCollectionLoop

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open ReadExpressions DependencyExpressionReads DependencyReadScan
open DependencyValidationOperands DependencyCollectionOperands DependencyCollectionStep Lift
open OrderedDependencyCPreparationCollection (iterationSyntax)
open OrderedDependencyCPreparationLoop (outerCondition outerStep loopSyntax)
open CellPermission

universe u

def frame (reader array pending : Ptr) (index count added : UInt32) (ok : Bool)
    (base : ReadExpressions.Environment) : ReadExpressions.Environment := fun name =>
  if name = "importer".toList then some (.ptr (some reader))
  else if name = "dependencies".toList then some (.ptr (some array))
  else if name = "pending".toList then some (.ptr (some pending))
  else if name = "i".toList then some (.u32 index)
  else if name = "count".toList then some (.u32 count)
  else if name = "added".toList then some (.u32 added)
  else if name = "ok".toList then some (.bool ok) else base name

theorem frame_updates_index (reader array pending : Ptr) (index after count added : UInt32)
    (ok : Bool) (base : ReadExpressions.Environment) :
    Function.update (frame reader array pending index count added ok base) "i".toList
      (some (.u32 after)) = frame reader array pending after count added ok base := by
  funext name
  by_cases same : name = "i".toList
  · subst name
    simp [frame]
  · rw [Function.update_of_ne same]
    simp only [frame, if_neg same]

theorem frame_updates_added (reader array pending : Ptr) (index count before after : UInt32)
    (ok : Bool) (base : ReadExpressions.Environment) :
    Function.update (frame reader array pending index count before ok base) "added".toList
      (some (.u32 after)) = frame reader array pending index count after ok base := by
  funext name
  by_cases same : name = "added".toList
  · subst name
    simp [frame]
  · rw [Function.update_of_ne same]
    simp only [frame, if_neg same]

theorem frame_updates_ok (reader array pending : Ptr) (index count added : UInt32)
    (before after : Bool) (base : ReadExpressions.Environment) :
    Function.update (frame reader array pending index count added before base) "ok".toList
      (some (.bool after)) = frame reader array pending index count added after base := by
  funext name
  by_cases same : name = "ok".toList
  · subst name
    simp [frame]
  · rw [Function.update_of_ne same]
    simp only [frame, if_neg same]

theorem outer_condition_reads_current_locals (layout : ReadExpressions.Layout)
    (reader array pending : Ptr) (index count added : UInt32) (ok : Bool)
    (base : ReadExpressions.Environment) :
    expression layout (frame reader array pending index count added ok base) outerCondition =
      pure (.bool (ok && decide (index < count))) := by
  cases ok <;> simp [outerCondition, expression, expressionWith_equation, frame, resolved, truth, binary, word]

theorem outer_increment_executes_actual_step (reader array pending : Ptr)
    (index count added : UInt32) (ok : Bool) (base : ReadExpressions.Environment) :
    ReadLoops.increment (frame reader array pending index count added ok base) outerStep =
      pure (frame reader array pending (index + 1) count added ok base) := by
  change (pure (Function.update (frame reader array pending index count added ok base) "i".toList
    (some (.u32 (index + 1)))) : CProg CVal ReadExpressions.Environment) = _
  rw [frame_updates_index]

section IndependentInsertion

variable {Id : Type} [DecidableEq Id]

theorem ordered_collection_length_bound (existing values sources : List Id) :
    (OrderedDependencyBatch.collectMissing existing values sources).length ≤
      values.length + sources.length := by
  induction sources generalizing values with
  | nil => simp [OrderedDependencyBatch.collectMissing]
  | cons source rest ih =>
    rw [OrderedDependencyBatch.collectMissing]
    split
    · have bound := ih values
      simp only [List.length_cons]
      omega
    · have bound := ih (values ++ [source])
      simp only [List.length_append, List.length_cons, List.length_nil] at bound ⊢
      omega

theorem one_input_length_increases_at_most_one (existing values : List Id) (source : Id) :
    (OrderedDependencyBatch.collectMissing existing values [source]).length ≤ values.length + 1 := by
  simpa using ordered_collection_length_bound existing values [source]

theorem one_input_domain_is_preserved (existing values : List Id) (source : Id) (D : List Id)
    (closed : ∀ identity ∈ values, identity ∈ D) (sourceIn : source ∈ D) :
    ∀ identity ∈ OrderedDependencyBatch.collectMissing existing values [source], identity ∈ D := by
  intro identity member
  by_cases present : source ∈ existing ∨ source ∈ values
  · simp [OrderedDependencyBatch.collectMissing, present] at member
    exact closed identity member
  · simp [OrderedDependencyBatch.collectMissing, present] at member
    rcases member with old | rfl
    · exact closed identity old
    · exact sourceIn

theorem one_input_counter_is_exact (existing values : List Id) (source : Id)
    (added : UInt32) (capacity : Nat) (extent : added.toNat = values.length)
    (bounded : capacity < 2 ^ 32)
    (roomWhenNew : ¬ (source ∈ existing ∨ source ∈ values) → values.length < capacity) :
    (if source ∈ existing ∨ source ∈ values then added else added + 1).toNat =
      (OrderedDependencyBatch.collectMissing existing values [source]).length := by
  by_cases present : source ∈ existing ∨ source ∈ values
  · simpa [OrderedDependencyBatch.collectMissing, present] using extent
  · simp only [if_neg present, OrderedDependencyBatch.collectMissing, List.length_append,
      List.length_cons, List.length_nil]
    rw [UInt32.toNat_add, extent]
    change (values.length + 1) % (2 ^ 32) = values.length + 1
    apply Nat.mod_eq_of_lt
    have room := roomWhenNew present
    omega

end IndependentInsertion

section PhysicalLoop

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]
variable {Id : Type} [DecidableEq Id] (addr : Id → Ptr)

theorem run_refines_ordered_physical_batch (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {reader : Id} (readerIn : reader ∈ D)
    (closed : ∀ identity ∈ (H.forward reader).active, identity ∈ D)
    (within : (H.forward reader).count.toNat ≤ (H.forward reader).slots.length)
    (array : Ptr) (inputCapacity : Nat) (prior remaining : List Id) (spare : List (Option Id))
    (pending : Ptr) (capacity : Nat) (values : List Id) (index count added : UInt32)
    (base : ReadExpressions.Environment)
    (position : index.toNat = prior.length) (extent : count.toNat = (prior ++ remaining).length)
    (pendingExtent : added.toNat = values.length)
    (allocation : values.length + remaining.length ≤ capacity) (bounded : capacity < 2 ^ 32)
    (valid : ∀ source ∈ remaining, source ≠ reader)
    (represented : ∀ source ∈ remaining, source ∈ D)
    (pendingClosed : ∀ source ∈ values, source ∈ D) (F : Heap L → Prop) :
    CTriple (PendingState addr layout D H array inputCapacity ((prior ++ remaining).map some ++ spare)
      pending capacity values F)
      (StatementBlock.loop PostIndexWrites.assign (fields layout)
        ((H.forward reader).active.length + capacity) 12 outerCondition outerStep iterationSyntax
        remaining.length (frame (addr reader) array pending index count added true base))
      (fun result σ => ∃ finalAdded,
        finalAdded.toNat = (OrderedDependencyBatch.collectMissing (H.forward reader).active values remaining).length ∧
        result = .finished (.next (frame (addr reader) array pending count count finalAdded true base)) ∧
          PendingState addr layout D H array inputCapacity ((prior ++ remaining).map some ++ spare)
            pending capacity (OrderedDependencyBatch.collectMissing (H.forward reader).active values remaining) F σ) := by
  induction remaining generalizing prior values index added with
  | nil =>
    have ending : prior.length = count.toNat := by simpa using extent.symm
    have final : index = count := UInt32.toNat_inj.mp (position.trans ending)
    subst index
    rw [StatementBlock.loop.eq_def, outer_condition_reads_current_locals]
    have halted : ¬ count < count := by rw [UInt32.lt_iff_toNat_lt]; exact Nat.lt_irrefl _
    simp only [Bool.true_and, decide_eq_false halted, truth, Prog.pure_eq, Prog.bind_eq,
      Prog.ret_bind, Bool.false_eq_true, ↓reduceIte]
    exact triple_pre _ (fun _ held => ⟨added, pendingExtent, rfl, held⟩) (triple_ret _ _ _)
  | cons source rest ih =>
    have active : index < count := by
      rw [UInt32.lt_iff_toNat_lt]
      simp only [List.length_append, List.length_cons] at extent
      omega
    have exactIncrement : (index + 1).toNat = index.toNat + 1 :=
      OrderedDependencyCPreparationLoop.bounded_increment_is_exact index count active
    have inside : index.toNat < ((prior ++ source :: rest).map some ++ spare).length := by
      simp only [List.length_append, List.length_map, List.length_cons]
      omega
    have loaded : ((prior ++ source :: rest).map some ++ spare)[index.toNat]'inside = some source := by
      rw [List.getElem_append_left (by simp [position]), List.getElem_map,
        List.getElem_append_right (by omega)]
      simp [position]
    have room : values.length < capacity := by
      simp only [List.length_cons] at allocation
      omega
    let afterValues := OrderedDependencyBatch.collectMissing (H.forward reader).active values [source]
    let afterAdded := if source ∈ (H.forward reader).active ∨ source ∈ values then added else added + 1
    have exactAdded : afterAdded.toNat = afterValues.length :=
      one_input_counter_is_exact (H.forward reader).active values source added capacity pendingExtent
        bounded (fun _ => room)
    have nextPosition : (index + 1).toNat = (prior ++ [source]).length := by simp [exactIncrement, position]
    have nextExtent : count.toNat = ((prior ++ [source]) ++ rest).length := by
      simpa only [List.append_assoc, List.singleton_append] using extent
    have nextAllocation : afterValues.length + rest.length ≤ capacity := by
      have growth := one_input_length_increases_at_most_one (H.forward reader).active values source
      simp only [List.length_cons] at allocation
      calc
        afterValues.length + rest.length ≤ (values.length + 1) + rest.length :=
          Nat.add_le_add_right growth _
        _ ≤ capacity := by omega
    have nextClosed : ∀ identity ∈ afterValues, identity ∈ D :=
      one_input_domain_is_preserved (H.forward reader).active values source D pendingClosed
        (represented source (by simp))
    have following := ih (prior ++ [source]) afterValues (index + 1) afterAdded nextPosition nextExtent
      exactAdded nextAllocation (fun identity member => valid identity (by simp [member]))
      (fun identity member => represented identity (by simp [member])) nextClosed
    rw [StatementBlock.loop.eq_def, outer_condition_reads_current_locals]
    simp only [Bool.true_and, decide_eq_true active, truth, Prog.pure_eq, Prog.bind_eq,
      Prog.ret_bind, ↓reduceIte]
    have body := valid_body_refines_physical_input (L := L) addr layout H readerIn
      (represented source (by simp)) (valid source (by simp)) closed within array inputCapacity
      ((prior ++ source :: rest).map some ++ spare) index inside loaded pending capacity values added
      pendingExtent pendingClosed ((H.forward reader).active.length + capacity) (by omega) (by omega)
      (fun _ => room) (frame (addr reader) array pending index count added true base)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) F
    refine triple_bind _ body fun result => ?_
    apply triple_pure
    intro same
    subst result
    rw [frame_updates_added]
    dsimp only
    rw [outer_increment_executes_actual_step]
    simp only [Prog.pure_eq, Prog.ret_bind]
    simpa only [afterValues, afterAdded, List.append_assoc, List.singleton_append,
      OrderedDependencyCPreparationLoop.one_input_collection_precedes_tail] using following

def executeNode (layout : ReadExpressions.Layout) (innerFuel fuel : Nat)
    (environment : ReadExpressions.Environment) : Option CStatement → CProg CVal ReadBlock.Result
  | some statement => StatementBlock.counted PostIndexWrites.assign layout innerFuel 12 fuel environment statement
  | none => CProg.undefined

theorem quoted_loop_retains_actual_body_service (layout : ReadExpressions.Layout)
    (innerFuel fuel : Nat) (environment : ReadExpressions.Environment) :
    executeNode layout innerFuel fuel environment OrderedDependencyCPreparationLoop.quotedLoop =
      StatementBlock.counted PostIndexWrites.assign layout innerFuel 12 fuel environment loopSyntax := by
  rw [OrderedDependencyCPreparationLoop.quoted_loop_is_actual,
    OrderedDependencyCPreparationLoop.complete_loop_is_retained]
  rfl

theorem quoted_loop_refines_allocated_ordered_batch (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {reader : Id} (readerIn : reader ∈ D)
    (closed : ∀ identity ∈ (H.forward reader).active, identity ∈ D)
    (within : (H.forward reader).count.toNat ≤ (H.forward reader).slots.length)
    (array : Ptr) (inputCapacity : Nat) (inputs : List Id) (spare : List (Option Id))
    (pending : Ptr) (savedIndex count : UInt32) (base : ReadExpressions.Environment)
    (extent : count.toNat = inputs.length) (valid : ∀ source ∈ inputs, source ≠ reader)
    (represented : ∀ source ∈ inputs, source ∈ D) (F : Heap L → Prop) :
    CTriple (PendingState addr layout D H array inputCapacity (inputs.map some ++ spare)
      pending count.toNat [] F)
      (executeNode (fields layout) ((H.forward reader).active.length + count.toNat) inputs.length
        (frame (addr reader) array pending savedIndex count 0 true base)
        OrderedDependencyCPreparationLoop.quotedLoop)
      (fun result σ => ∃ finalAdded,
        finalAdded.toNat = (OrderedDependencyBatch.collectMissing (H.forward reader).active [] inputs).length ∧
        result = .finished (.next (frame (addr reader) array pending savedIndex count finalAdded true base)) ∧
          PendingState addr layout D H array inputCapacity (inputs.map some ++ spare) pending count.toNat
            (OrderedDependencyBatch.collectMissing (H.forward reader).active [] inputs) F σ) := by
  rw [quoted_loop_retains_actual_body_service, loopSyntax,
    StatementBlock.counted_retains_initializer_and_scope, frame_updates_index]
  have completed := run_refines_ordered_physical_batch addr layout H readerIn closed within
    array inputCapacity [] inputs spare pending count.toNat [] 0 count 0 base rfl (by simpa using extent)
    rfl (by simpa using extent.symm.le) count.toNat_lt valid represented (by simp) F
  simp only [List.nil_append] at completed
  refine triple_bind _ completed fun result => ?_
  apply triple_exists
  intro finalAdded
  apply triple_pure
  intro exactCount
  apply triple_pure
  intro same
  subst result
  simp only [ReadBlock.restore]
  have previous : frame (addr reader) array pending savedIndex count 0 true base "i".toList =
      some (.u32 savedIndex) := rfl
  rw [previous, frame_updates_index]
  exact triple_pre _ (fun _ held => ⟨finalAdded, exactCount, rfl, held⟩) (triple_ret _ _ _)

theorem invalid_input_exits_without_increment (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {reader : Id} (readerIn : reader ∈ D)
    (array : Ptr) (inputCapacity : Nat) (inputs : List (Option Id)) (index count added : UInt32)
    (inside : index.toNat < inputs.length) (value : Option Id)
    (loaded : inputs[index.toNat] = value) (invalid : value = none ∨ value = some reader)
    (pending : Ptr) (capacity : Nat) (values : List Id) (base : ReadExpressions.Environment)
    (innerFuel fuel : Nat) (active : index < count) (F : Heap L → Prop) :
    CTriple (PendingState addr layout D H array inputCapacity inputs pending capacity values F)
      (StatementBlock.loop PostIndexWrites.assign (fields layout) innerFuel 12 outerCondition outerStep
        iterationSyntax (fuel + 1) (frame (addr reader) array pending index count added true base))
      (fun result σ => result = .finished (.next
        (frame (addr reader) array pending index count added false base)) ∧
          PendingState addr layout D H array inputCapacity inputs pending capacity values F σ) := by
  rw [StatementBlock.loop.eq_def, outer_condition_reads_current_locals]
  simp only [Bool.true_and, decide_eq_true active, truth, Prog.pure_eq, Prog.bind_eq,
    Prog.ret_bind, ↓reduceIte]
  have failed := invalid_body_refines_physical_input (L := L) addr layout H readerIn
    array inputCapacity inputs index inside value loaded invalid pending capacity values
    (frame (addr reader) array pending index count added true base) innerFuel true
    (by rfl) (by rfl) (by rfl) (by rfl) F
  refine triple_bind _ failed fun result => ?_
  apply triple_pure
  intro same
  subst result
  rw [frame_updates_ok]
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩) (triple_ret _ _ _)

theorem valid_prefix_then_invalid_input_preserves_private_prefix (layout : SpaceLayout)
    {D : List Id} (H : SplitHeap Id) {reader : Id} (readerIn : reader ∈ D)
    (closed : ∀ identity ∈ (H.forward reader).active, identity ∈ D)
    (within : (H.forward reader).count.toNat ≤ (H.forward reader).slots.length)
    (array : Ptr) (inputCapacity : Nat) (prior accepted : List Id)
    (value : Option Id) (suffix : List (Option Id))
    (invalid : value = none ∨ value = some reader)
    (pending : Ptr) (capacity : Nat) (values : List Id) (index count added : UInt32)
    (base : ReadExpressions.Environment) (position : index.toNat = prior.length)
    (beforeBound : (prior ++ accepted).length < count.toNat)
    (pendingExtent : added.toNat = values.length)
    (allocation : values.length + accepted.length ≤ capacity) (bounded : capacity < 2 ^ 32)
    (valid : ∀ source ∈ accepted, source ≠ reader)
    (represented : ∀ source ∈ accepted, source ∈ D)
    (pendingClosed : ∀ source ∈ values, source ∈ D) (F : Heap L → Prop) :
    CTriple (PendingState addr layout D H array inputCapacity
      ((prior ++ accepted).map some ++ value :: suffix) pending capacity values F)
      (StatementBlock.loop PostIndexWrites.assign (fields layout)
        ((H.forward reader).active.length + capacity) 12 outerCondition outerStep iterationSyntax
        (accepted.length + 1) (frame (addr reader) array pending index count added true base))
      (fun result σ => ∃ stopped finalAdded,
        stopped.toNat = (prior ++ accepted).length ∧
        finalAdded.toNat = (OrderedDependencyBatch.collectMissing (H.forward reader).active values accepted).length ∧
        result = .finished (.next (frame (addr reader) array pending stopped count finalAdded false base)) ∧
          PendingState addr layout D H array inputCapacity
            ((prior ++ accepted).map some ++ value :: suffix) pending capacity
            (OrderedDependencyBatch.collectMissing (H.forward reader).active values accepted) F σ) := by
  induction accepted generalizing prior values index added with
  | nil =>
    have active : index < count := by
      rw [UInt32.lt_iff_toNat_lt]
      simpa [position] using beforeBound
    have inside : index.toNat < ((prior ++ []).map some ++ value :: suffix).length := by
      simp only [List.append_nil, List.length_append, List.length_map, List.length_cons]
      omega
    have loaded : ((prior ++ []).map some ++ value :: suffix)[index.toNat]'inside = value := by
      rw [List.getElem_append_right (by simp [position])]
      simp [position]
    have failed := invalid_input_exits_without_increment addr layout H readerIn array inputCapacity
      ((prior ++ []).map some ++ value :: suffix) index count added inside value loaded invalid
      pending capacity values base ((H.forward reader).active.length + capacity) 0 active F
    refine triple_post _ failed ?_
    intro result σ held
    exact ⟨index, added, by simpa using position, by simpa [OrderedDependencyBatch.collectMissing] using pendingExtent,
      held.1, by simpa [OrderedDependencyBatch.collectMissing] using held.2⟩
  | cons source rest ih =>
    have active : index < count := by
      rw [UInt32.lt_iff_toNat_lt]
      simp only [List.length_append, List.length_cons] at beforeBound
      omega
    have exactIncrement : (index + 1).toNat = index.toNat + 1 :=
      OrderedDependencyCPreparationLoop.bounded_increment_is_exact index count active
    have inside : index.toNat < ((prior ++ source :: rest).map some ++ value :: suffix).length := by
      simp only [List.length_append, List.length_map, List.length_cons]
      omega
    have loaded : ((prior ++ source :: rest).map some ++ value :: suffix)[index.toNat]'inside = some source := by
      rw [List.getElem_append_left (by simp [position]), List.getElem_map,
        List.getElem_append_right (by omega)]
      simp [position]
    have room : values.length < capacity := by
      simp only [List.length_cons] at allocation
      omega
    let afterValues := OrderedDependencyBatch.collectMissing (H.forward reader).active values [source]
    let afterAdded := if source ∈ (H.forward reader).active ∨ source ∈ values then added else added + 1
    have exactAdded : afterAdded.toNat = afterValues.length :=
      one_input_counter_is_exact (H.forward reader).active values source added capacity pendingExtent
        bounded (fun _ => room)
    have nextPosition : (index + 1).toNat = (prior ++ [source]).length := by simp [exactIncrement, position]
    have nextBound : ((prior ++ [source]) ++ rest).length < count.toNat := by
      simpa only [List.append_assoc, List.singleton_append] using beforeBound
    have nextAllocation : afterValues.length + rest.length ≤ capacity := by
      have growth := one_input_length_increases_at_most_one (H.forward reader).active values source
      simp only [List.length_cons] at allocation
      calc
        afterValues.length + rest.length ≤ (values.length + 1) + rest.length :=
          Nat.add_le_add_right growth _
        _ ≤ capacity := by omega
    have nextClosed : ∀ identity ∈ afterValues, identity ∈ D :=
      one_input_domain_is_preserved (H.forward reader).active values source D pendingClosed
        (represented source (by simp))
    have following := ih (prior ++ [source]) afterValues (index + 1) afterAdded nextPosition nextBound
      exactAdded nextAllocation (fun identity member => valid identity (by simp [member]))
      (fun identity member => represented identity (by simp [member])) nextClosed
    rw [StatementBlock.loop.eq_def, outer_condition_reads_current_locals]
    simp only [Bool.true_and, decide_eq_true active, truth, Prog.pure_eq, Prog.bind_eq,
      Prog.ret_bind, ↓reduceIte]
    have body := valid_body_refines_physical_input (L := L) addr layout H readerIn
      (represented source (by simp)) (valid source (by simp)) closed within array inputCapacity
      ((prior ++ source :: rest).map some ++ value :: suffix) index inside loaded pending capacity values added
      pendingExtent pendingClosed ((H.forward reader).active.length + capacity) (by omega) (by omega)
      (fun _ => room) (frame (addr reader) array pending index count added true base)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) F
    refine triple_bind _ body fun result => ?_
    apply triple_pure
    intro same
    subst result
    rw [frame_updates_added]
    dsimp only
    rw [outer_increment_executes_actual_step]
    simp only [Prog.pure_eq, Prog.ret_bind]
    simpa only [afterValues, afterAdded, List.append_assoc, List.singleton_append,
      List.length_cons, Nat.add_comm 1,
      OrderedDependencyCPreparationLoop.one_input_collection_precedes_tail] using following

theorem quoted_invalid_suffix_retains_only_ordered_private_prefix (layout : SpaceLayout)
    {D : List Id} (H : SplitHeap Id) {reader : Id} (readerIn : reader ∈ D)
    (closed : ∀ identity ∈ (H.forward reader).active, identity ∈ D)
    (within : (H.forward reader).count.toNat ≤ (H.forward reader).slots.length)
    (array : Ptr) (inputCapacity : Nat) (accepted : List Id)
    (value : Option Id) (suffix : List (Option Id))
    (invalid : value = none ∨ value = some reader)
    (pending : Ptr) (savedIndex count : UInt32) (base : ReadExpressions.Environment)
    (beforeBound : accepted.length < count.toNat)
    (valid : ∀ source ∈ accepted, source ≠ reader)
    (represented : ∀ source ∈ accepted, source ∈ D) (F : Heap L → Prop) :
    CTriple (PendingState addr layout D H array inputCapacity
      (accepted.map some ++ value :: suffix) pending count.toNat [] F)
      (executeNode (fields layout) ((H.forward reader).active.length + count.toNat) (accepted.length + 1)
        (frame (addr reader) array pending savedIndex count 0 true base)
        OrderedDependencyCPreparationLoop.quotedLoop)
      (fun result σ => ∃ finalAdded,
        finalAdded.toNat = (OrderedDependencyBatch.collectMissing (H.forward reader).active [] accepted).length ∧
        result = .finished (.next (frame (addr reader) array pending savedIndex count finalAdded false base)) ∧
          PendingState addr layout D H array inputCapacity (accepted.map some ++ value :: suffix)
            pending count.toNat (OrderedDependencyBatch.collectMissing (H.forward reader).active [] accepted) F σ) := by
  rw [quoted_loop_retains_actual_body_service, loopSyntax,
    StatementBlock.counted_retains_initializer_and_scope, frame_updates_index]
  have failed := valid_prefix_then_invalid_input_preserves_private_prefix addr layout H readerIn
    closed within array inputCapacity [] accepted value suffix invalid pending count.toNat [] 0 count 0
    base rfl (by simpa using beforeBound) rfl (by simpa using beforeBound.le) count.toNat_lt
    valid represented (by simp) F
  simp only [List.nil_append] at failed
  refine triple_bind _ failed fun result => ?_
  apply triple_exists
  intro stopped
  apply triple_exists
  intro finalAdded
  apply triple_pure
  intro stoppedAt
  apply triple_pure
  intro exactCount
  apply triple_pure
  intro same
  subst result
  simp only [ReadBlock.restore]
  rw [show frame (addr reader) array pending savedIndex count 0 true base "i".toList =
    some (.u32 savedIndex) from rfl, frame_updates_index]
  exact triple_pre _ (fun _ held => ⟨finalAdded, exactCount, rfl, held⟩) (triple_ret _ _ _)

theorem quoted_invalid_first_input_restores_scope (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {reader : Id} (readerIn : reader ∈ D)
    (array : Ptr) (inputCapacity : Nat) (value : Option Id) (suffix : List (Option Id))
    (invalid : value = none ∨ value = some reader) (pending : Ptr) (capacity : Nat)
    (values : List Id) (savedIndex count added : UInt32) (base : ReadExpressions.Environment)
    (innerFuel fuel : Nat) (positive : 0 < count) (F : Heap L → Prop) :
    CTriple (PendingState addr layout D H array inputCapacity (value :: suffix) pending capacity values F)
      (executeNode (fields layout) innerFuel (fuel + 1)
        (frame (addr reader) array pending savedIndex count added true base)
        OrderedDependencyCPreparationLoop.quotedLoop)
      (fun result σ => result = .finished (.next
        (frame (addr reader) array pending savedIndex count added false base)) ∧
          PendingState addr layout D H array inputCapacity (value :: suffix) pending capacity values F σ) := by
  rw [quoted_loop_retains_actual_body_service, loopSyntax,
    StatementBlock.counted_retains_initializer_and_scope, frame_updates_index]
  have failed := invalid_input_exits_without_increment addr layout H readerIn array inputCapacity
    (value :: suffix) 0 count added (by simp) value rfl invalid pending capacity values base
    innerFuel fuel positive F
  refine triple_bind _ failed fun result => ?_
  apply triple_pure
  intro same
  subst result
  simp only [ReadBlock.restore]
  rw [show frame (addr reader) array pending savedIndex count added true base "i".toList =
    some (.u32 savedIndex) from rfl, frame_updates_index]
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩) (triple_ret _ _ _)

end PhysicalLoop

namespace Controls

def base : ReadExpressions.Environment := fun _ => none

theorem zero_count_does_not_touch_physical_arrays (layout : ReadExpressions.Layout)
    (reader array pending : Ptr) (savedIndex added : UInt32) (innerFuel fuel : Nat) :
    executeNode layout innerFuel fuel (frame reader array pending savedIndex 0 added true base)
      OrderedDependencyCPreparationLoop.quotedLoop =
      pure (.finished (.next (frame reader array pending savedIndex 0 added true base))) := by
  rw [quoted_loop_retains_actual_body_service, loopSyntax,
    StatementBlock.counted_retains_initializer_and_scope, frame_updates_index,
    StatementBlock.loop.eq_def, outer_condition_reads_current_locals]
  simp only [Bool.true_and, show decide ((0 : UInt32) < 0) = false from rfl, truth,
    Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, Bool.false_eq_true, ↓reduceIte, ReadBlock.restore]
  rw [show frame reader array pending savedIndex 0 added true base "i".toList =
    some (.u32 savedIndex) from rfl, frame_updates_index]

theorem false_ok_skips_even_missing_bound (layout : ReadExpressions.Layout)
    (innerFuel fuel : Nat) :
    StatementBlock.loop PostIndexWrites.assign layout innerFuel 12 outerCondition outerStep
      iterationSyntax fuel (Function.update base "ok".toList (some (.bool false))) =
      pure (.finished (.next (Function.update base "ok".toList (some (.bool false))))) := by
  rw [StatementBlock.loop.eq_def]
  rfl

theorem positive_bound_with_no_fuel_is_not_false_return (layout : ReadExpressions.Layout)
    (reader array pending : Ptr) (added : UInt32) (innerFuel : Nat) :
    StatementBlock.loop PostIndexWrites.assign layout innerFuel 12 outerCondition outerStep
      iterationSyntax 0 (frame reader array pending 0 1 added true base) = pure .exhausted := by
  rw [StatementBlock.loop.eq_def, outer_condition_reads_current_locals]
  rfl

theorem independent_insertion_keeps_order_and_deduplicates :
    OrderedDependencyBatch.collectMissing ([1] : List Nat) [] [2, 2, 3, 1] = [2, 3] := by decide

theorem reading_existing_spare_as_active_suppresses_a_new_identity :
    OrderedDependencyBatch.collectMissing ([] : List Nat) [] [2] = [2] ∧
    OrderedDependencyBatch.collectMissing ([2] : List Nat) [] [2] = [] := by decide

end Controls

end Mettapedia.Machines.CMemory.DependencyCollectionLoop
