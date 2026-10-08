import Mettapedia.GSLT.LanguageDef.NativeOpsCLocalStore
import Mettapedia.Machines.OrderedDependencyCPreparationScan
import Mettapedia.Machines.OrderedDependencyBatch

/-!
# Retained conditional pending append and one-input deduplication

The actual old and pending scans flow into the actual conditional append node.
The selected pointer-array assignment uses its retained array, counter and RHS
identities. The independent specification is ordered identity insertion into
the initialized pending list, excluding existing dependencies.

This boundary starts with a resolved, non-null input identity. It does not
execute the surrounding input load, validation, outer loop, allocations or
reserve/cleanup procedure. Its physical heap and read-window obligations remain
separate from the logical UInt32-counted slot realization.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.Machines.OrderedDependencyCPreparationAppend

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open ScalarRead IdentityScan PostIndex
open OrderedDependencyCPreparationSource OrderedDependencyCPreparationScan

variable {Ptr : Type} [DecidableEq Ptr]

def appendSite : LocalStore.Site :=
  ⟨"pending".toList, "added".toList, "dependency".toList⟩

def appendCondition : CExpr := .unary .not (.identifier flag)

def appendStatement : CStatement := .branch appendCondition [appendSite.statement] []

def appendNode : Option CStatement := scanAt preparationFunction 10 5

theorem conditional_node_is_retained : appendNode = some appendStatement := rfl

theorem quoted_conditional_node_is_actual : quotedScan 10 5 = appendNode := by
  rw [quotedScan, complete_preparation_source_admitted]
  rfl

def context (reader source : Ptr) (pending : Array32 Ptr) (savedCounter : UInt32)
    (seen : Bool) : Environment Ptr :=
  locals (bindings reader source pending.slots pending.count) savedCounter seen

omit [DecidableEq Ptr] in
theorem updated_context (reader source : Ptr) (pending after : Array32 Ptr)
    (savedCounter : UInt32) (seen : Bool) :
    LocalStore.writeBindings (context reader source pending savedCounter seen) appendSite
      (LocalStore.nullable after) = context reader source after savedCounter seen := by
  funext name
  by_cases isCount : name = "added".toList
  · subst name
    simp [LocalStore.writeBindings, LocalStore.nullable, appendSite, context, locals,
      bindings, counter, flag]
  · by_cases isArray : name = "pending".toList
    · subst name
      simp [LocalStore.writeBindings, LocalStore.nullable, appendSite, context, locals,
        bindings, counter, flag]
    · change Function.update (Function.update (context reader source pending savedCounter seen)
        "pending".toList (some (.identities (after.slots.map some)))) "added".toList
          (some (.unsigned after.count)) name = _
      rw [Function.update_of_ne isCount, Function.update_of_ne isArray]
      unfold context locals
      split
      · rfl
      · split
        · rfl
        · simp only [bindings, if_neg isCount, if_neg isArray]

omit [DecidableEq Ptr] in
theorem append_store_executes_actual_operands (reader source : Ptr) (pending : Array32 Ptr)
    (savedCounter : UInt32) (seen : Bool) :
    LocalStore.execute (context reader source pending savedCounter seen) appendSite.statement =
      (store pending source).map (fun written => context reader source written savedCounter seen) := by
  rw [LocalStore.execute_resolved_site (context reader source pending savedCounter seen)
    appendSite pending source (by decide) (by decide)
    (by simp [context, locals, bindings, appendSite, counter, flag])
    (by simp [context, locals, bindings, appendSite, counter, flag])
    (by simp [context, locals, bindings, appendSite, counter, flag])]
  congr 1
  funext written
  exact updated_context reader source pending written savedCounter seen

theorem condition_observes_actual_flag (reader source : Ptr) (pending : Array32 Ptr)
    (savedCounter : UInt32) (seen : Bool) (readerFields : FieldReader Ptr) :
    (expression (context reader source pending savedCounter seen) readerFields
      appendCondition).bind truth? = some (!seen) := by
  simp [expression, appendCondition, context, locals, truth?, flag, counter]

theorem append_branch_selects_actual_store (reader source : Ptr) (pending : Array32 Ptr)
    (savedCounter : UInt32) (seen : Bool) (readerFields : FieldReader Ptr) :
    LocalStore.branch readerFields (context reader source pending savedCounter seen)
      appendStatement =
      if seen then some (context reader source pending savedCounter seen)
      else (store pending source).map
        (fun written => context reader source written savedCounter seen) := by
  rw [appendStatement, LocalStore.branch_selects_actual_continuation _ _ _ _ _ (!seen)
    (condition_observes_actual_flag reader source pending savedCounter seen readerFields)]
  cases seen <;> simp [LocalStore.sequence_single, append_store_executes_actual_operands,
    LocalStore.sequence]

def executeScans (reader source : Ptr) (existing pending : Array32 Ptr)
    (savedCounter : UInt32) : Option (Result Ptr) :=
  let readerFields := fields reader existing.slots existing.count
  (existingScan.bind (countedLoop readerFields existing.count.toNat
    (context reader source pending savedCounter false))).bind (fun result =>
      match result with
      | .finished (some environment) => pendingScan.bind
          (countedLoop readerFields pending.count.toNat environment)
      | .finished none => some (.finished none)
      | .exhausted => some .exhausted)

def executeStep (reader source : Ptr) (existing pending : Array32 Ptr)
    (savedCounter : UInt32) : Option (Result Ptr) :=
  (executeScans reader source existing pending savedCounter).bind (fun result =>
    match result with
    | .finished (some environment) => appendNode.map
        (fun statement => .finished (LocalStore.branch
          (fields reader existing.slots existing.count) environment statement))
    | .finished none => some (.finished none)
    | .exhausted => some .exhausted)

theorem actual_scans_execute_union (reader source : Ptr) (existing pending : Array32 Ptr)
    (savedCounter : UInt32)
    (oldLive : existing.count.toNat ≤ existing.slots.length)
    (pendingLive : pending.count.toNat ≤ pending.slots.length) :
    executeScans reader source existing pending savedCounter = some (.finished (some
      (context reader source pending savedCounter
        (decide (source ∈ existing.active ∨ source ∈ pending.active))))) := by
  have first := existing_scan_refines_active_slots reader source existing pending.slots
    pending.count savedCounter false oldLive
  change executeNode existingScan reader source existing.slots pending.slots existing.count
    pending.count savedCounter false existing.count.toNat = _ at first
  unfold executeScans
  change (executeNode existingScan reader source existing.slots pending.slots existing.count
    pending.count savedCounter false existing.count.toNat).bind _ = _
  rw [first]
  simp only [Bool.false_eq_true, false_or, Option.bind_some]
  change executeNode pendingScan reader source existing.slots pending.slots existing.count
    pending.count savedCounter (decide (source ∈ existing.active)) pending.count.toNat = _
  rw [pending_scan_refines_active_slots reader source existing.slots pending existing.count
    savedCounter (decide (source ∈ existing.active)) pendingLive]
  simp [context]

theorem actual_step_selects_deduplicated_append (reader source : Ptr)
    (existing pending : Array32 Ptr) (savedCounter : UInt32)
    (oldLive : existing.count.toNat ≤ existing.slots.length)
    (pendingLive : pending.count.toNat ≤ pending.slots.length) :
    executeStep reader source existing pending savedCounter =
      some (.finished
        (if source ∈ existing.active ∨ source ∈ pending.active then
          some (context reader source pending savedCounter true)
        else (store pending source).map
          (fun written => context reader source written savedCounter false))) := by
  rw [executeStep, actual_scans_execute_union reader source existing pending savedCounter
    oldLive pendingLive, conditional_node_is_retained]
  simp only [Option.bind_some, Option.map_some]
  rw [append_branch_selects_actual_store]
  by_cases present : source ∈ existing.active ∨ source ∈ pending.active <;> simp [present]

/-- No room is required on the already-present path. A fresh identity needs a
live slot; the outer preparation loop must derive this from its allocation. -/
theorem one_input_slot_outcome (source : Ptr) (existing pending : Array32 Ptr)
    (pendingLive : pending.count.toNat ≤ pending.slots.length)
    (sized : pending.Sized)
    (roomWhenNew : ¬ (source ∈ existing.active ∨ source ∈ pending.active) → pending.Room) :
    ∃ after, (if source ∈ existing.active ∨ source ∈ pending.active then some pending
        else store pending source) = some after ∧
      after.active = OrderedDependencyBatch.collectMissing existing.active pending.active [source] ∧
      after.count.toNat = after.active.length ∧ after.slots.length = pending.slots.length ∧
      after.Sized ∧ after.count.toNat ≤ pending.count.toNat + 1 := by
  by_cases present : source ∈ existing.active ∨ source ∈ pending.active
  · refine ⟨pending, ?_, ?_, ?_, rfl, sized, by omega⟩
    · simp only [if_pos present]
    · simp [OrderedDependencyBatch.collectMissing, present]
    · simp [Array32.active, List.length_take, Nat.min_eq_left pendingLive]
  · let written : Array32 Ptr :=
      ⟨pending.slots.set pending.count.toNat source, pending.count + 1⟩
    have stored : store pending source = some written := store_defined pending source (roomWhenNew present)
    have law := store_realizes_append sized stored
    refine ⟨written, ?_, ?_, ?_, law.2.2.1, law.2.2.2, ?_⟩
    · simp only [if_neg present, stored]
    · simpa [OrderedDependencyBatch.collectMissing, present] using law.1
    · rw [law.1, law.2.1]
      simp [Array32.active, List.length_take, Nat.min_eq_left pendingLive]
    · exact Nat.le_of_eq law.2.1

theorem actual_step_refines_one_input (reader source : Ptr)
    (existing pending : Array32 Ptr) (savedCounter : UInt32)
    (oldLive : existing.count.toNat ≤ existing.slots.length)
    (pendingLive : pending.count.toNat ≤ pending.slots.length)
    (sized : pending.Sized)
    (roomWhenNew : ¬ (source ∈ existing.active ∨ source ∈ pending.active) → pending.Room) :
    ∃ after, executeStep reader source existing pending savedCounter =
        some (.finished (some (context reader source after savedCounter
          (decide (source ∈ existing.active ∨ source ∈ pending.active))))) ∧
      after.active = OrderedDependencyBatch.collectMissing existing.active pending.active [source] ∧
      after.count.toNat = after.active.length ∧
      after.slots.length = pending.slots.length ∧ after.Sized := by
  obtain ⟨after, chosen, active, countExact, capacity, afterSized, _⟩ :=
    one_input_slot_outcome source existing pending pendingLive sized roomWhenNew
  refine ⟨after, ?_, active, countExact, capacity, afterSized⟩
  rw [actual_step_selects_deduplicated_append reader source existing pending savedCounter
    oldLive pendingLive]
  have mapped := congrArg (fun result : Option (Array32 Ptr) => some (Result.finished
    (result.map (fun written => context reader source written savedCounter
      (decide (source ∈ existing.active ∨ source ∈ pending.active)))))) chosen
  by_cases present : source ∈ existing.active ∨ source ∈ pending.active <;>
    simpa [present] using mapped

def observePending : Result Ptr → Option (List (Option Ptr) × UInt32)
  | .finished (some environment) => do
      let .identities slots ← environment "pending".toList | none
      let .unsigned count ← environment "added".toList | none
      some (slots.take count.toNat, count)
  | _ => none

namespace Controls

def empty : Array32 Nat := ⟨[99, 99, 99], 0⟩
def old : Array32 Nat := ⟨[1, 99, 99], 1⟩

theorem new_identity_is_appended_once :
    (executeStep 0 2 old empty 91).bind observePending = some ([some 2], 1) := by decide +kernel

theorem old_identity_does_not_use_pending_room :
    (executeStep 0 1 old (⟨[], 0⟩ : Array32 Nat) 91).bind observePending = some ([], 0) :=
  by decide +kernel

theorem pending_duplicate_is_not_appended :
    (executeStep 0 2 old (⟨[2, 99], 1⟩ : Array32 Nat) 91).bind observePending =
      some ([some 2], 1) := by decide +kernel

theorem spare_identity_does_not_prevent_append :
    (executeStep 0 2 old (⟨[2, 99], 0⟩ : Array32 Nat) 91).bind observePending =
      some ([some 2], 1) := by decide +kernel

theorem fresh_identity_without_room_has_no_execution :
    executeStep 0 2 old (⟨[], 0⟩ : Array32 Nat) 91 = some (.finished none) := rfl

theorem earlier_pending_occurrences_keep_order :
    (executeStep 0 3 old (⟨[2, 99], 1⟩ : Array32 Nat) 91).bind observePending =
      some ([some 2, some 3], 2) := by decide +kernel

end Controls

#print axioms conditional_node_is_retained
#print axioms quoted_conditional_node_is_actual
#print axioms updated_context
#print axioms append_store_executes_actual_operands
#print axioms condition_observes_actual_flag
#print axioms append_branch_selects_actual_store
#print axioms actual_scans_execute_union
#print axioms actual_step_selects_deduplicated_append
#print axioms one_input_slot_outcome
#print axioms actual_step_refines_one_input
#print axioms Controls.new_identity_is_appended_once
#print axioms Controls.old_identity_does_not_use_pending_room
#print axioms Controls.pending_duplicate_is_not_appended
#print axioms Controls.spare_identity_does_not_prevent_append
#print axioms Controls.fresh_identity_without_room_has_no_execution
#print axioms Controls.earlier_pending_occurrences_keep_order

end Mettapedia.Machines.OrderedDependencyCPreparationAppend
