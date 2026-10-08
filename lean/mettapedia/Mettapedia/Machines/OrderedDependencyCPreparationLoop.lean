import Mettapedia.GSLT.LanguageDef.NativeOpsCLocalLoop
import Mettapedia.Machines.OrderedDependencyCPreparationCollection

/-!
# The retained collection loop and its initialized pending bound

The actual outer condition and increment execute over the complete retained
collection body. Input count is separate from provider capacity, and pending
room follows from the number of remaining inputs. Logical typed field/array
services retain their separate physical realization obligations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.Machines.OrderedDependencyCPreparationLoop

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open ScalarRead PostIndex
open OrderedDependencyCPreparationSource OrderedDependencyCPreparationScan
open OrderedDependencyCPreparationCollection

variable {Ptr : Type} [DecidableEq Ptr]

def outerCondition : CExpr := .binary .and (.identifier "ok".toList)
  (.binary .lt (.identifier "i".toList) (.identifier "count".toList))

def outerStep : CExpr := .postIncrement (.identifier "i".toList)

def loopSyntax : CStatement := .forLoop ⟨"uint32_t".toList, 0⟩ "i".toList
  (.unsignedInteger 0) outerCondition outerStep iterationSyntax

def actualLoop : Option CStatement := preparationFunction.body[10]?

theorem complete_loop_is_retained : actualLoop = some loopSyntax := rfl

def quotedLoop : Option CStatement :=
  (declaratorFunctionText? typeNames preparationSource.toList).bind (fun function => function.body[10]?)

theorem quoted_loop_is_actual : quotedLoop = actualLoop := by
  rw [quotedLoop, complete_preparation_source_admitted]
  rfl

omit [DecidableEq Ptr] in
theorem index_binding (reader source : Ptr) (pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) (seen : Bool) :
    frame reader source pending inputs index count seen "i".toList = some (.unsigned index) := by
  simp [frame, extend]

omit [DecidableEq Ptr] in
theorem count_binding (reader source : Ptr) (pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) (seen : Bool) :
    frame reader source pending inputs index count seen "count".toList = some (.unsigned count) := by
  simp [frame, extend]

omit [DecidableEq Ptr] in
theorem frame_updates_index (reader source : Ptr) (pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index after count : UInt32) (seen : Bool) :
    Function.update (frame reader source pending inputs index count seen)
      "i".toList (some (.unsigned after)) = frame reader source pending inputs after count seen := by
  funext name
  by_cases isIndex : name = "i".toList
  · subst name
    simp [frame, extend]
  · rw [Function.update_of_ne isIndex]
    simp only [frame, extend, if_neg isIndex]

theorem condition_reads_actual_bound (reader source : Ptr) (existing pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) (seen : Bool) :
    (expression (frame reader source pending inputs index count seen)
      (fields reader existing.slots existing.count) outerCondition).bind truth? =
      some (decide (index < count)) := by
  simp [expression, outerCondition, frame, extend, numericBinary, truth?]

omit [DecidableEq Ptr] in
theorem increment_uses_actual_index (reader source : Ptr) (pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) (seen : Bool) :
    increment (frame reader source pending inputs index count seen) outerStep =
      some (frame reader source pending inputs (index + 1) count seen) := by
  change (do
    let .unsigned value ← frame reader source pending inputs index count seen "i".toList | none
    some (Function.update (frame reader source pending inputs index count seen)
      "i".toList (some (.unsigned (value + 1))))) = _
  rw [index_binding]
  dsimp only [bind, Option.bind]
  rw [frame_updates_index]

theorem bounded_increment_is_exact (index count : UInt32) (before : index < count) :
    (index + 1).toNat = index.toNat + 1 := by
  rw [UInt32.toNat_add]
  apply Nat.mod_eq_of_lt
  have upper := count.toNat_lt
  have live := UInt32.lt_iff_toNat_lt.mp before
  change index.toNat + 1 < 2 ^ 32
  omega

def provider (prior remaining spare : List Ptr) : List (Option Ptr) :=
  ((prior ++ remaining) ++ spare).map some

omit [DecidableEq Ptr] in
theorem provider_rethreads_consumed_input (prior remaining spare : List Ptr) (source : Ptr) :
    provider prior (source :: remaining) spare = provider (prior ++ [source]) remaining spare := by
  simp [provider, List.append_assoc]

theorem one_input_collection_precedes_tail (existing pending : List Ptr) (source : Ptr)
    (remaining : List Ptr) :
    OrderedDependencyBatch.collectMissing existing
      (OrderedDependencyBatch.collectMissing existing pending [source]) remaining =
      OrderedDependencyBatch.collectMissing existing pending (source :: remaining) := by
  by_cases present : source ∈ existing ∨ source ∈ pending <;>
    simp [OrderedDependencyBatch.collectMissing, present]

/-- The capacity hypothesis is an input-allocation extent, not an assumed
successful loop or append. Every fresh-store room obligation is derived from
the positive remaining-input count; unsigned progression is derived from the
actual loop bound. Provider slots past that bound are retained but unread. -/
theorem run_refines_initialized_batch (reader : Ptr) (existing pending : Array32 Ptr)
    (prior remaining spare : List Ptr) (index count : UInt32) (fuel : Nat)
    (position : index.toNat = prior.length)
    (extent : count.toNat = (prior ++ remaining).length)
    (valid : ∀ source ∈ remaining, source ≠ reader)
    (oldLive : existing.count.toNat ≤ existing.slots.length)
    (pendingLive : pending.count.toNat ≤ pending.slots.length) (sized : pending.Sized)
    (capacity : pending.count.toNat + remaining.length ≤ pending.slots.length)
    (enough : remaining.length ≤ fuel) :
    ∃ after, LocalLoop.run (fields reader existing.slots existing.count) outerCondition outerStep
        iterationSyntax 12 fuel (frame reader reader pending (provider prior remaining spare) index count) =
        .finished (some (.next (frame reader reader after (provider prior remaining spare) count count))) ∧
      after.active = OrderedDependencyBatch.collectMissing existing.active pending.active remaining ∧
      after.count.toNat = after.active.length ∧ after.slots.length = pending.slots.length ∧
      after.Sized ∧ after.count.toNat ≤ pending.count.toNat + remaining.length := by
  induction remaining generalizing prior pending index fuel with
  | nil =>
    have stopped : index = count := UInt32.toNat_inj.mp (by simpa [position] using extent.symm)
    have inactive : ¬ index < count := by simp [stopped]
    refine ⟨pending, ?_, rfl, ?_, rfl, sized, by simp⟩
    · rw [LocalLoop.false_condition_skips_body (test := by
        rw [condition_reads_actual_bound, decide_eq_false inactive]), stopped]
    · simp [Array32.active, List.length_take, Nat.min_eq_left pendingLive]
  | cons source rest ih =>
    have active : index < count := by
      rw [UInt32.lt_iff_toNat_lt]
      simp only [List.length_append, List.length_cons] at extent
      omega
    have loaded : (provider prior (source :: rest) spare)[index.toNat]? = some (some source) := by
      have sourceRead : ((prior ++ source :: rest) ++ spare)[index.toNat]? = some source := by
        rw [List.append_assoc, position, List.getElem?_append_right (Nat.le_refl _)]
        simp
      simp only [provider, List.getElem?_map, sourceRead, Option.map_some]
    have room : pending.Room := by
      simp only [List.length_cons] at capacity
      unfold Array32.Room
      omega
    obtain ⟨written, chosen, activeList, writtenCount, writtenCapacity, writtenSized, growth⟩ :=
      OrderedDependencyCPreparationAppend.one_input_slot_outcome source existing pending
        pendingLive sized (fun _ => room)
    have completed := valid_iteration_executes_actual_body reader source existing pending written
      (provider prior (source :: rest) spare) index count loaded (valid source (by simp))
        oldLive pendingLive chosen
    have followingLive : written.count.toNat ≤ written.slots.length := by
      rw [writtenCount, Array32.active, List.length_take]
      exact Nat.min_le_right _ _
    have followingCapacity : written.count.toNat + rest.length ≤ written.slots.length := by
      rw [writtenCapacity]
      simp only [List.length_cons] at capacity
      omega
    have followingPosition : (index + 1).toNat = (prior ++ [source]).length := by
      rw [bounded_increment_is_exact index count active, position]
      simp
    have followingExtent : count.toNat = ((prior ++ [source]) ++ rest).length := by
      simpa [List.append_assoc] using extent
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      obtain ⟨after, following, activeAfter, afterCount, afterCapacity, afterSized, afterGrowth⟩ :=
        ih written (prior ++ [source]) (index + 1) fuel followingPosition followingExtent
          (fun member included => valid member (List.mem_cons_of_mem source included))
          followingLive writtenSized followingCapacity (by simpa using enough)
      refine ⟨after, ?_, ?_, afterCount, afterCapacity.trans writtenCapacity, afterSized, ?_⟩
      · rw [LocalLoop.true_condition_continues_actual_body
          (test := by rw [condition_reads_actual_bound, decide_eq_true active])
          (completed := completed) (incremented := increment_uses_actual_index
            reader reader written (provider prior (source :: rest) spare) index count false),
          provider_rethreads_consumed_input]
        exact following
      · rw [activeAfter, activeList, one_input_collection_precedes_tail]
      · simp only [List.length_cons]
        omega

def executeLoop (node : Option CStatement) (reader : Ptr) (existing pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (savedIndex count : UInt32) (fuel : Nat) :
    Option (LocalBlock.Result Ptr) :=
  node.bind (LocalLoop.counted (fields reader existing.slots existing.count) 12 fuel
    (frame reader reader pending inputs savedIndex count))

/-- The retained header, rather than a supplied starting index, initializes
the loop counter. Its enclosing scope restores that caller binding after all
ordered inputs have been consumed. The input provider may have unread spare
slots beyond the separately supplied count. -/
theorem actual_loop_refines_ordered_batch (reader : Ptr) (existing pending : Array32 Ptr)
    (inputs spare : List Ptr) (savedIndex count : UInt32) (fuel : Nat)
    (extent : count.toNat = inputs.length) (valid : ∀ source ∈ inputs, source ≠ reader)
    (oldLive : existing.count.toNat ≤ existing.slots.length)
    (pendingLive : pending.count.toNat ≤ pending.slots.length) (sized : pending.Sized)
    (capacity : pending.count.toNat + inputs.length ≤ pending.slots.length)
    (enough : inputs.length ≤ fuel) :
    ∃ after, executeLoop actualLoop reader existing pending (provider [] inputs spare)
        savedIndex count fuel =
        some (.finished (some (.next (frame reader reader after (provider [] inputs spare)
          savedIndex count)))) ∧
      after.active = OrderedDependencyBatch.collectMissing existing.active pending.active inputs ∧
      after.count.toNat = after.active.length ∧ after.slots.length = pending.slots.length ∧
      after.Sized ∧ after.count.toNat ≤ pending.count.toNat + inputs.length := by
  obtain ⟨after, completed, collected, exactCount, extentAfter, sizedAfter, countBound⟩ :=
    run_refines_initialized_batch reader existing pending [] inputs spare 0 count fuel rfl
      (by simpa using extent) valid oldLive pendingLive sized capacity enough
  refine ⟨after, ?_, collected, exactCount, extentAfter, sizedAfter, countBound⟩
  rw [executeLoop, complete_loop_is_retained, Option.bind_some, loopSyntax,
    LocalLoop.zero_initialization_keeps_counter_scope, frame_updates_index, completed]
  simp only [index_binding, LocalBlock.restore, frame_updates_index]

omit [DecidableEq Ptr] in
/-- No initialized element is read from a newly provisioned pending extent.
The UInt32 input count supplies its size bound; no append success is assumed. -/
theorem allocated_pending_extent_is_sized (slots : List Ptr) (count : UInt32)
    (extent : slots.length = count.toNat) : (⟨slots, 0⟩ : Array32 Ptr).Sized := by
  have bounded := count.toNat_lt
  change slots.length ≤ 4294967295
  rw [extent]
  change count.toNat < 4294967296 at bounded
  omega

theorem collection_from_allocated_extent (reader : Ptr) (existing : Array32 Ptr)
    (slots inputs spare : List Ptr) (savedIndex count : UInt32) (fuel : Nat)
    (extent : count.toNat = inputs.length) (allocated : slots.length = count.toNat)
    (valid : ∀ source ∈ inputs, source ≠ reader)
    (oldLive : existing.count.toNat ≤ existing.slots.length) (enough : inputs.length ≤ fuel) :
    ∃ after, executeLoop actualLoop reader existing ⟨slots, 0⟩ (provider [] inputs spare)
        savedIndex count fuel =
        some (.finished (some (.next (frame reader reader after (provider [] inputs spare)
          savedIndex count)))) ∧
      after.active = OrderedDependencyBatch.collectMissing existing.active [] inputs ∧
      after.count.toNat = after.active.length ∧ after.slots.length = slots.length ∧
      after.Sized ∧ after.count.toNat ≤ count.toNat := by
  simpa only [Array32.active, UInt32.toNat_zero, List.take_zero, Nat.zero_add, ← extent] using
    actual_loop_refines_ordered_batch reader existing ⟨slots, 0⟩ inputs spare savedIndex count fuel
      extent valid oldLive (by simp) (allocated_pending_extent_is_sized slots count allocated)
      (by simpa [allocated] using extent.symm.le) enough

/-- Completed null/self rejection consumes the actual break and never executes
the loop increment, membership scans, or any later input. This needs no live
old/pending scan extents because validation precedes those reads. -/
theorem invalid_input_exits_without_increment (reader : Ptr) (existing pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) (fuel : Nat) (value : Option Ptr)
    (active : index < count) (loaded : inputs[index.toNat]? = some value)
    (invalid : value = none ∨ value = some reader) :
    LocalLoop.run (fields reader existing.slots existing.count) outerCondition outerStep
      iterationSyntax 12 (fuel + 1) (frame reader reader pending inputs index count) =
      .finished (some (.next (Function.update (frame reader reader pending inputs index count)
        "ok".toList (some (.boolean false))))) := by
  have completed := invalid_input_rejects_before_membership_reads reader existing pending
    inputs index count value loaded invalid
  simp only [executeBody, complete_iteration_is_retained, Option.map_some] at completed
  apply LocalLoop.break_exits_without_increment
  · rw [condition_reads_actual_bound, decide_eq_true active]
  · exact Option.some.inj completed

theorem actual_invalid_first_input_restores_scope (reader : Ptr) (existing pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (savedIndex count : UInt32) (fuel : Nat) (value : Option Ptr)
    (active : 0 < count) (loaded : inputs[0]? = some value)
    (invalid : value = none ∨ value = some reader) :
    executeLoop actualLoop reader existing pending inputs savedIndex count (fuel + 1) =
      some (.finished (some (.next (Function.update
        (frame reader reader pending inputs savedIndex count) "ok".toList
          (some (.boolean false)))))) := by
  rw [executeLoop, complete_loop_is_retained, Option.bind_some, loopSyntax,
    LocalLoop.zero_initialization_keeps_counter_scope, frame_updates_index,
    invalid_input_exits_without_increment reader existing pending inputs 0 count fuel value
      active loaded invalid]
  simp only [index_binding, LocalBlock.restore]
  rw [Function.update_comm (by decide : "ok".toList ≠ "i".toList), frame_updates_index]

def nullableProvider (prior consumed : List Ptr) (suffix : List (Option Ptr)) : List (Option Ptr) :=
  (prior ++ consumed).map some ++ suffix

omit [DecidableEq Ptr] in
theorem nullable_provider_rethreads_prefix (prior consumed : List Ptr)
    (suffix : List (Option Ptr)) (source : Ptr) :
    nullableProvider prior (source :: consumed) suffix =
      nullableProvider (prior ++ [source]) consumed suffix := by
  simp [nullableProvider, List.append_assoc]

/-- Prefix execution composes with the actual remaining loop, not with a
replacement list fold. The unread suffix may contain null identities; only
the consumed prefix is required to pass validation. -/
theorem valid_prefix_preserves_remaining_continuation (reader : Ptr)
    (existing pending : Array32 Ptr) (prior consumed : List Ptr) (suffix : List (Option Ptr))
    (index count : UInt32) (fuel : Nat) (position : index.toNat = prior.length)
    (extent : (prior ++ consumed).length ≤ count.toNat)
    (valid : ∀ source ∈ consumed, source ≠ reader)
    (oldLive : existing.count.toNat ≤ existing.slots.length)
    (pendingLive : pending.count.toNat ≤ pending.slots.length) (sized : pending.Sized)
    (capacity : pending.count.toNat + consumed.length ≤ pending.slots.length) :
    ∃ after nextIndex,
      LocalLoop.run (fields reader existing.slots existing.count) outerCondition outerStep
        iterationSyntax 12 (consumed.length + fuel)
        (frame reader reader pending (nullableProvider prior consumed suffix) index count) =
      LocalLoop.run (fields reader existing.slots existing.count) outerCondition outerStep
        iterationSyntax 12 fuel
        (frame reader reader after (nullableProvider prior consumed suffix) nextIndex count) ∧
      nextIndex.toNat = (prior ++ consumed).length ∧
      after.active = OrderedDependencyBatch.collectMissing existing.active pending.active consumed ∧
      after.count.toNat = after.active.length ∧ after.slots.length = pending.slots.length ∧
      after.Sized ∧ after.count.toNat ≤ pending.count.toNat + consumed.length := by
  induction consumed generalizing prior pending index with
  | nil =>
    refine ⟨pending, index, by simp, by simpa using position, rfl, ?_, rfl, sized, by simp⟩
    simp [Array32.active, List.length_take, Nat.min_eq_left pendingLive]
  | cons source rest ih =>
    have active : index < count := by
      rw [UInt32.lt_iff_toNat_lt]
      simp only [List.length_append, List.length_cons] at extent
      omega
    have loaded : (nullableProvider prior (source :: rest) suffix)[index.toNat]? =
        some (some source) := by
      have boundary : (prior.map some).length ≤ index.toNat := by simp [position]
      simp only [nullableProvider, List.map_append]
      rw [List.append_assoc, List.getElem?_append_right boundary]
      simp [position]
    have room : pending.Room := by
      simp only [List.length_cons] at capacity
      unfold Array32.Room
      omega
    obtain ⟨written, chosen, activeList, writtenCount, writtenCapacity, writtenSized, growth⟩ :=
      OrderedDependencyCPreparationAppend.one_input_slot_outcome source existing pending
        pendingLive sized (fun _ => room)
    have completed := valid_iteration_executes_actual_body reader source existing pending written
      (nullableProvider prior (source :: rest) suffix) index count loaded (valid source (by simp))
        oldLive pendingLive chosen
    have followingLive : written.count.toNat ≤ written.slots.length := by
      rw [writtenCount, Array32.active, List.length_take]
      exact Nat.min_le_right _ _
    have followingCapacity : written.count.toNat + rest.length ≤ written.slots.length := by
      rw [writtenCapacity]
      simp only [List.length_cons] at capacity
      omega
    have followingPosition : (index + 1).toNat = (prior ++ [source]).length := by
      rw [bounded_increment_is_exact index count active, position]
      simp
    have followingExtent : ((prior ++ [source]) ++ rest).length ≤ count.toNat := by
      simpa [List.append_assoc] using extent
    obtain ⟨after, nextIndex, following, nextPosition, activeAfter, afterCount, afterCapacity,
        afterSized, afterGrowth⟩ :=
      ih written (prior ++ [source]) (index + 1) followingPosition followingExtent
        (fun member included => valid member (List.mem_cons_of_mem source included))
        followingLive writtenSized followingCapacity
    refine ⟨after, nextIndex, ?_, by simpa [List.append_assoc] using nextPosition,
      ?_, afterCount, afterCapacity.trans writtenCapacity, afterSized, ?_⟩
    · simp only [List.length_cons, Nat.succ_add]
      rw [LocalLoop.true_condition_continues_actual_body
        (test := by rw [condition_reads_actual_bound, decide_eq_true active])
        (completed := completed) (incremented := increment_uses_actual_index
          reader reader written (nullableProvider prior (source :: rest) suffix) index count false),
        nullable_provider_rethreads_prefix]
      exact following
    · rw [activeAfter, activeList, one_input_collection_precedes_tail]
    · simp only [List.length_cons]
      omega

/-- A failed suffix is observed after exactly its preceding valid inputs.
The pending prefix remains private, the outer index is restored, and no later
input is inspected. No successful reservation or publication is assumed. -/
theorem actual_invalid_suffix_keeps_ordered_prefix (reader : Ptr) (existing pending : Array32 Ptr)
    (consumed : List Ptr) (value : Option Ptr) (suffix : List (Option Ptr))
    (savedIndex count : UInt32) (active : consumed.length < count.toNat)
    (valid : ∀ source ∈ consumed, source ≠ reader)
    (invalid : value = none ∨ value = some reader)
    (oldLive : existing.count.toNat ≤ existing.slots.length)
    (pendingLive : pending.count.toNat ≤ pending.slots.length) (sized : pending.Sized)
    (capacity : pending.count.toNat + consumed.length ≤ pending.slots.length) :
    ∃ after, executeLoop actualLoop reader existing pending
        (nullableProvider [] consumed (value :: suffix)) savedIndex count (consumed.length + 1) =
        some (.finished (some (.next (Function.update
          (frame reader reader after (nullableProvider [] consumed (value :: suffix)) savedIndex count)
          "ok".toList (some (.boolean false)))))) ∧
      after.active = OrderedDependencyBatch.collectMissing existing.active pending.active consumed ∧
      after.count.toNat = after.active.length ∧ after.slots.length = pending.slots.length ∧
      after.Sized ∧ after.count.toNat ≤ pending.count.toNat + consumed.length := by
  obtain ⟨after, index, completed, position, collected, exactCount, extentAfter, sizedAfter, growth⟩ :=
    valid_prefix_preserves_remaining_continuation reader existing pending [] consumed (value :: suffix)
      0 count 1 rfl (by simpa using active.le) valid oldLive pendingLive sized capacity
  have position' : index.toNat = consumed.length := by simpa using position
  have loaded : (nullableProvider [] consumed (value :: suffix))[index.toNat]? = some value := by
    simp only [nullableProvider, List.nil_append]
    rw [List.getElem?_append_right (by simp [position'])]
    simp [position']
  have liveIndex : index < count := by simpa [UInt32.lt_iff_toNat_lt, position'] using active
  refine ⟨after, ?_, collected, exactCount, extentAfter, sizedAfter, growth⟩
  rw [executeLoop, complete_loop_is_retained, Option.bind_some, loopSyntax,
    LocalLoop.zero_initialization_keeps_counter_scope, frame_updates_index, completed,
    invalid_input_exits_without_increment reader existing after
      (nullableProvider [] consumed (value :: suffix)) index count 0 value liveIndex loaded invalid]
  simp only [index_binding, LocalBlock.restore]
  rw [Function.update_comm (by decide : "ok".toList ≠ "i".toList), frame_updates_index]

theorem quoted_loop_uses_same_execution (reader : Ptr) (existing pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (savedIndex count : UInt32) (fuel : Nat) :
    executeLoop quotedLoop reader existing pending inputs savedIndex count fuel =
      executeLoop actualLoop reader existing pending inputs savedIndex count fuel := by
  rw [quoted_loop_is_actual]

theorem collected_batch_is_distinct (existing sources : List Ptr) (distinct : existing.Nodup) :
    (OrderedDependencyBatch.collectMissing existing [] sources).Nodup := by
  have prepared := OrderedDependencyBatch.prepared_distinct existing sources distinct
  exact (List.nodup_append.mp prepared).2.1

theorem collected_batch_member_has_input_provenance (existing sources : List Ptr) (source : Ptr)
    (included : source ∈ OrderedDependencyBatch.collectMissing existing [] sources)
    (distinct : existing.Nodup) : source ∈ sources ∧ source ∉ existing := by
  have prepared := OrderedDependencyBatch.prepared_distinct existing sources distinct
  have disjoint := (List.nodup_append.mp prepared).2.2
  have absent : source ∉ existing := fun old => disjoint source old source included rfl
  have member := (OrderedDependencyBatch.prepared_membership existing sources source).mp
    (List.mem_append_right existing included)
  exact ⟨member.resolve_left absent, absent⟩

def observeLoop : Option (LocalBlock.Result Ptr) → Option (Bool × List (Option Ptr) × UInt32 × UInt32)
  | some (.finished (some (.next environment))) => do
      let ok ← (environment "ok".toList).bind truth?
      let .identities slots ← environment "pending".toList | none
      let .unsigned added ← environment "added".toList | none
      let .unsigned saved ← environment "i".toList | none
      some (ok, slots.take added.toNat, added, saved)
  | _ => none

namespace Controls

def old : Array32 Nat := ⟨[2], 1⟩
def pending : Array32 Nat := ⟨[99, 99, 99, 99], 0⟩

theorem ordered_first_occurrences_suppress_duplicate_identities :
    observeLoop (executeLoop actualLoop 1 old pending
      [some 3, some 2, some 3, some 4] 7 4 4) = some (true, [some 3, some 4], 2, 7) := by
  decide

theorem header_initializes_instead_of_reusing_outer_counter :
    observeLoop (executeLoop actualLoop 1 old pending [some 3] 4294967295 1 1) =
      some (true, [some 3], 1, 4294967295) := by decide

theorem provider_slots_past_count_are_not_inputs :
    observeLoop (executeLoop actualLoop 1 old pending [some 3, some 4] 7 1 1) =
      some (true, [some 3], 1, 7) := by decide

theorem zero_count_skips_impossible_scan_extent :
    observeLoop (executeLoop actualLoop 1 ⟨[], 4294967295⟩ ⟨[], 0⟩ [none] 7 0 0) =
      some (true, [], 0, 7) := by decide

theorem null_input_keeps_pending_and_restores_outer_index :
    observeLoop (executeLoop actualLoop 1 ⟨[], 4294967295⟩ ⟨[], 0⟩ [none] 7 1 1) =
      some (false, [], 0, 7) := by decide

theorem self_input_rejects_before_impossible_scan_extent :
    observeLoop (executeLoop actualLoop 1 ⟨[], 4294967295⟩ ⟨[], 0⟩ [some 1] 7 1 1) =
      some (false, [], 0, 7) := by decide

theorem invalid_suffix_keeps_completed_pending_prefix :
    observeLoop (executeLoop actualLoop 1 old pending [some 3, none, some 4] 7 3 3) =
      some (false, [some 3], 1, 7) := by decide

theorem insufficient_iteration_fuel_is_exhaustion_not_rejection :
    (executeLoop actualLoop 1 old pending [some 3, some 4] 7 2 1).map
      (fun result => match result with | .exhausted => true | _ => false) = some true := by decide

theorem missing_increment_has_no_completed_batch :
    observeLoop (executeLoop (some (.forLoop ⟨"uint32_t".toList, 0⟩ "i".toList
      (.unsignedInteger 0) outerCondition (.identifier "i".toList) iterationSyntax))
      1 old pending [some 3] 7 1 1) = none := by decide

theorem changed_outer_condition_changes_batch :
    observeLoop (executeLoop (some (.forLoop ⟨"uint32_t".toList, 0⟩ "i".toList
      (.unsignedInteger 0) (.bool false) outerStep iterationSyntax))
      1 old pending [some 3] 7 1 1) = some (true, [], 0, 7) := by decide

theorem missing_actual_loop_is_not_synthesized :
    executeLoop none 1 old pending [some 3] 7 1 1 = none := rfl

end Controls

#print axioms complete_loop_is_retained
#print axioms quoted_loop_is_actual
#print axioms index_binding
#print axioms count_binding
#print axioms frame_updates_index
#print axioms condition_reads_actual_bound
#print axioms increment_uses_actual_index
#print axioms bounded_increment_is_exact
#print axioms provider_rethreads_consumed_input
#print axioms one_input_collection_precedes_tail
#print axioms run_refines_initialized_batch
#print axioms actual_loop_refines_ordered_batch
#print axioms allocated_pending_extent_is_sized
#print axioms collection_from_allocated_extent
#print axioms invalid_input_exits_without_increment
#print axioms actual_invalid_first_input_restores_scope
#print axioms nullable_provider_rethreads_prefix
#print axioms valid_prefix_preserves_remaining_continuation
#print axioms actual_invalid_suffix_keeps_ordered_prefix
#print axioms quoted_loop_uses_same_execution
#print axioms collected_batch_is_distinct
#print axioms collected_batch_member_has_input_provenance
#print axioms Controls.ordered_first_occurrences_suppress_duplicate_identities
#print axioms Controls.header_initializes_instead_of_reusing_outer_counter
#print axioms Controls.provider_slots_past_count_are_not_inputs
#print axioms Controls.zero_count_skips_impossible_scan_extent
#print axioms Controls.null_input_keeps_pending_and_restores_outer_index
#print axioms Controls.self_input_rejects_before_impossible_scan_extent
#print axioms Controls.invalid_suffix_keeps_completed_pending_prefix
#print axioms Controls.insufficient_iteration_fuel_is_exhaustion_not_rejection
#print axioms Controls.missing_increment_has_no_completed_batch
#print axioms Controls.changed_outer_condition_changes_batch
#print axioms Controls.missing_actual_loop_is_not_synthesized

end Mettapedia.Machines.OrderedDependencyCPreparationLoop
