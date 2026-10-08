import Mettapedia.GSLT.LanguageDef.NativeOpsCLocalBlock
import Mettapedia.Machines.OrderedDependencyCPreparationAppend

/-!
# Retained input load and collection-loop body execution

The complete body of the preparation's collection loop executes through the
typed local statement fragment. The dependency load uses its actual input
index, the validation branch retains its assignment and break, both scan nodes
remain executable syntax, and the selected append continuation remains intact.
Outer counting, allocation/reservation and physical-heap realization are
separate obligations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.Machines.OrderedDependencyCPreparationCollection

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open ScalarRead IdentityScan PostIndex
open OrderedDependencyCPreparationSource OrderedDependencyCPreparationScan
open OrderedDependencyCPreparationAppend

variable {Ptr : Type} [DecidableEq Ptr]

def inputExpression : CExpr :=
  .index (.identifier "dependencies".toList) (.identifier "i".toList)

def invalidCondition : CExpr :=
  .binary .or (.unary .not (.identifier "dependency".toList))
    (.binary .eq (.identifier "dependency".toList) (.identifier "importer".toList))

def iterationSyntax : List CStatement := [
  .declare ⟨"Space".toList, 1⟩ "dependency".toList inputExpression,
  .branch invalidCondition
    [.assign (.identifier "ok".toList) (.bool false), .break] [],
  .declare ⟨"bool".toList, 0⟩ flag (.bool false),
  scanStatement oldArray oldLimit needle,
  scanStatement pendingArray pendingLimit needle,
  appendStatement]

def actualIteration : Option (List CStatement) := do
  let loop ← preparationFunction.body[10]?
  loopBody? loop

theorem complete_iteration_is_retained : actualIteration = some iterationSyntax := rfl

def quotedIteration : Option (List CStatement) :=
  (declaratorFunctionText? typeNames preparationSource.toList).bind (fun function => do
    let loop ← function.body[10]?
    loopBody? loop)

theorem quoted_iteration_is_actual : quotedIteration = actualIteration := by
  rw [quotedIteration, complete_preparation_source_admitted]
  rfl

def extend (environment : Environment Ptr) (inputs : List (Option Ptr))
    (index count : UInt32) : Environment Ptr := fun name =>
  if name = "dependencies".toList then some (.identities inputs)
  else if name = "i".toList then some (.unsigned index)
  else if name = "count".toList then some (.unsigned count)
  else if name = "ok".toList then some (.boolean true) else environment name

def frame (reader source : Ptr) (pending : Array32 Ptr) (inputs : List (Option Ptr))
    (index count : UInt32) (seen : Bool := false) : Environment Ptr :=
  extend (context reader source pending 0 seen) inputs index count

omit [DecidableEq Ptr] in
theorem dependency_binding (reader source : Ptr) (pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) (seen : Bool) :
    frame reader source pending inputs index count seen "dependency".toList =
      some (.identity (some source)) := by
  simp [frame, extend, context, locals, bindings, counter, flag]

omit [DecidableEq Ptr] in
theorem flag_binding (reader source : Ptr) (pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) (seen : Bool) :
    frame reader source pending inputs index count seen flag = some (.boolean seen) := by
  simp [frame, extend, context, locals, counter, flag]

omit [DecidableEq Ptr] in
theorem importer_binding (reader source : Ptr) (pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) (seen : Bool) :
    frame reader source pending inputs index count seen "importer".toList =
      some (.identity (some reader)) := by
  simp [frame, extend, context, locals, bindings, counter, flag]

omit [DecidableEq Ptr] in
theorem ok_binding (reader source : Ptr) (pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) (seen : Bool) :
    frame reader source pending inputs index count seen "ok".toList = some (.boolean true) := by
  simp [frame, extend]

theorem invalid_condition_uses_pointer_operands (environment : Environment Ptr)
    (readerFields : FieldReader Ptr) (reader : Ptr) (value : Option Ptr)
    (dependencyRead : environment "dependency".toList = some (.identity value))
    (importerRead : environment "importer".toList = some (.identity (some reader)))
    (invalid : value = none ∨ value = some reader) :
    (expression environment readerFields invalidCondition).bind truth? = some true := by
  change environment ['d', 'e', 'p', 'e', 'n', 'd', 'e', 'n', 'c', 'y'] = _ at dependencyRead
  change environment ['i', 'm', 'p', 'o', 'r', 't', 'e', 'r'] = _ at importerRead
  rcases invalid with isNull | isSelf
  · subst value
    simp [invalidCondition, expression, dependencyRead, truth?]
  · subst value
    simp [invalidCondition, expression, dependencyRead, importerRead, truth?, equal?]

omit [DecidableEq Ptr] in
theorem frame_updates_dependency (reader before after : Ptr) (pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) (seen : Bool) :
    Function.update (frame reader before pending inputs index count seen)
      "dependency".toList (some (.identity (some after))) =
      frame reader after pending inputs index count seen := by
  funext name
  by_cases isDependency : name = "dependency".toList
  · subst name
    simp [frame, extend, context, locals, bindings, counter, flag]
  · rw [Function.update_of_ne isDependency]
    simp only [frame, extend, context, locals, bindings, if_neg isDependency]

omit [DecidableEq Ptr] in
theorem frame_updates_flag (reader source : Ptr) (pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) (before after : Bool) :
    Function.update (frame reader source pending inputs index count before)
      flag (some (.boolean after)) = frame reader source pending inputs index count after := by
  funext name
  by_cases isFlag : name = flag
  · subst name
    simp [frame, extend, context, locals, counter, flag]
  · rw [Function.update_of_ne isFlag]
    simp only [frame, extend, context, locals, if_neg isFlag]

omit [DecidableEq Ptr] in
theorem updated_frame (reader source : Ptr) (pending after : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) (seen : Bool) :
    LocalStore.writeBindings (frame reader source pending inputs index count seen) appendSite
      (LocalStore.nullable after) = frame reader source after inputs index count seen := by
  funext name
  by_cases isCount : name = "added".toList
  · subst name
    simp [LocalStore.writeBindings, LocalStore.nullable, appendSite, frame, extend, context,
      locals, bindings, counter, flag]
  · by_cases isArray : name = "pending".toList
    · subst name
      simp [LocalStore.writeBindings, LocalStore.nullable, appendSite, frame, extend, context,
        locals, bindings, counter, flag]
    · change Function.update (Function.update (frame reader source pending inputs index count seen)
        "pending".toList (some (.identities (after.slots.map some)))) "added".toList
          (some (.unsigned after.count)) name = _
      rw [Function.update_of_ne isCount, Function.update_of_ne isArray]
      simp only [frame, extend, context, locals, bindings, if_neg isCount, if_neg isArray]

theorem input_reads_actual_index (reader source : Ptr) (existing pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) (seen : Bool) :
    expression (frame reader source pending inputs index count seen)
      (fields reader existing.slots existing.count) inputExpression =
      (inputs[index.toNat]?).map Value.identity := by
  simp [expression, inputExpression, frame, extend]

theorem valid_identity_avoids_failed_branch (reader source : Ptr) (existing pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) (seen : Bool)
    (different : source ≠ reader) :
    (expression (frame reader source pending inputs index count seen)
      (fields reader existing.slots existing.count) invalidCondition).bind truth? = some false := by
  simp [expression, invalidCondition, frame, extend, context, locals, bindings,
    counter, flag, truth?, equal?, different]

theorem append_condition_in_frame (reader source : Ptr) (existing pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) (seen : Bool) :
    (expression (frame reader source pending inputs index count seen)
      (fields reader existing.slots existing.count) appendCondition).bind truth? = some (!seen) := by
  simp [expression, appendCondition, frame, extend, context, locals, truth?, flag, counter]

omit [DecidableEq Ptr] in
theorem append_store_in_frame (reader source : Ptr) (pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) (seen : Bool) :
    LocalStore.execute (frame reader source pending inputs index count seen) appendSite.statement =
      (store pending source).map (fun written => frame reader source written inputs index count seen) := by
  rw [LocalStore.execute_resolved_site (frame reader source pending inputs index count seen)
    appendSite pending source (by decide) (by decide)
    (by simp [frame, extend, context, locals, bindings, appendSite, counter, flag])
    (by simp [frame, extend, context, locals, bindings, appendSite, counter, flag])
    (by simp [frame, extend, context, locals, bindings, appendSite, counter, flag])]
  congr 1
  funext written
  exact updated_frame reader source pending written inputs index count seen

theorem append_block_in_frame (reader source : Ptr) (existing pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) (seen : Bool) (fuel : Nat) :
    LocalBlock.execute (fields reader existing.slots existing.count) (fuel + 2)
      (frame reader source pending inputs index count seen) [appendStatement] =
      .finished ((if seen then some (frame reader source pending inputs index count seen)
        else (store pending source).map
          (fun written => frame reader source written inputs index count seen)).map
            LocalBlock.Flow.next) := by
  rw [appendStatement, LocalBlock.branch_executes_retained_continuation
    (fields reader existing.slots existing.count) (fuel + 1)
    (frame reader source pending inputs index count seen) appendCondition [appendSite.statement] [] []
    (!seen) (append_condition_in_frame reader source existing pending inputs index count seen)]
  cases seen
  · simp only [Bool.not_false, Bool.false_eq_true, if_true, if_false]
    rw [LocalBlock.local_store_executes_actual_result, append_store_in_frame]
    cases store pending source <;> rfl
  · rfl

omit [DecidableEq Ptr] in
theorem extended_locals (base : Environment Ptr) (inputs : List (Option Ptr))
    (index count savedCounter : UInt32) (seen : Bool) :
    extend (locals base savedCounter seen) inputs index count =
      locals (extend base inputs index count) savedCounter seen := by
  funext name
  by_cases isCounter : name = counter
  · subst name
    simp [extend, locals, counter]
  · by_cases isFlag : name = flag
    · subst name
      simp [extend, locals, flag, counter]
    · simp only [extend, locals, if_neg isCounter, if_neg isFlag]

theorem old_operands (reader source : Ptr) (existing pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) :
    Operands (extend (bindings reader source pending.slots pending.count) inputs index count)
      (fields reader existing.slots existing.count) oldArray oldLimit needle
      (existing.slots.map some) existing.count (some source) := by
  constructor <;> intro localCounter seen <;>
    simp [oldArray, oldLimit, needle, expression, locals, extend, bindings, fields, counter, flag]

theorem pending_operands (reader source : Ptr) (existing pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) :
    Operands (extend (bindings reader source pending.slots pending.count) inputs index count)
      (fields reader existing.slots existing.count) pendingArray pendingLimit needle
      (pending.slots.map some) pending.count (some source) := by
  constructor <;> intro localCounter seen <;>
    simp [pendingArray, pendingLimit, needle, expression, locals, extend, bindings, counter, flag]

theorem old_loop_in_frame (reader source : Ptr) (existing pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) (seen : Bool)
    (live : existing.count.toNat ≤ existing.slots.length) :
    countedLoop (fields reader existing.slots existing.count) existing.count.toNat
      (frame reader source pending inputs index count seen)
      (scanStatement oldArray oldLimit needle) = some (.finished (some
        (frame reader source pending inputs index count
          (decide (seen = true ∨ source ∈ existing.active))))) := by
  unfold frame context
  rw [extended_locals, extended_locals]
  exact counted_scan_refines_pointer_slots existing source
    (old_operands reader source existing pending inputs index count) live 0 seen

theorem pending_loop_in_frame (reader source : Ptr) (existing pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) (seen : Bool)
    (live : pending.count.toNat ≤ pending.slots.length) :
    countedLoop (fields reader existing.slots existing.count) pending.count.toNat
      (frame reader source pending inputs index count seen)
      (scanStatement pendingArray pendingLimit needle) = some (.finished (some
        (frame reader source pending inputs index count
          (decide (seen = true ∨ source ∈ pending.active))))) := by
  unfold frame context
  rw [extended_locals, extended_locals]
  exact counted_scan_refines_pointer_slots pending source
    (pending_operands reader source existing pending inputs index count) live 0 seen

theorem old_loop_fuel (reader source : Ptr) (existing pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) (seen : Bool) :
    LocalBlock.readLoopFuel (fields reader existing.slots existing.count)
      (frame reader source pending inputs index count seen)
      (scanStatement oldArray oldLimit needle) = existing.count.toNat := by
  simp [LocalBlock.readLoopFuel, scanStatement, condition, expression, oldLimit, frame,
    extend, context, locals, bindings, fields, counter, flag]

theorem pending_loop_fuel (reader source : Ptr) (existing pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) (seen : Bool) :
    LocalBlock.readLoopFuel (fields reader existing.slots existing.count)
      (frame reader source pending inputs index count seen)
      (scanStatement pendingArray pendingLimit needle) = pending.count.toNat := by
  simp [LocalBlock.readLoopFuel, scanStatement, condition, expression, pendingLimit, frame,
    extend, context, locals, bindings, counter, flag]

/-- The primitive outcome is a slot-store result, not an assumed statement
execution. The retained load, validation, scan bodies and scope restoration
are executed here before the primitive result is consumed. -/
theorem valid_iteration_executes_actual_body (reader source : Ptr)
    (existing pending after : Array32 Ptr) (inputs : List (Option Ptr)) (index count : UInt32)
    (loaded : inputs[index.toNat]? = some (some source)) (different : source ≠ reader)
    (oldLive : existing.count.toNat ≤ existing.slots.length)
    (pendingLive : pending.count.toNat ≤ pending.slots.length)
    (chosen : (if source ∈ existing.active ∨ source ∈ pending.active then some pending
      else store pending source) = some after) :
    LocalBlock.execute (fields reader existing.slots existing.count) 12
      (frame reader reader pending inputs index count) iterationSyntax =
      .finished (some (.next (frame reader reader after inputs index count))) := by
  have inputRead : (expression (frame reader reader pending inputs index count)
      (fields reader existing.slots existing.count) inputExpression).bind
      (LocalBlock.declaredValue? ⟨"Space".toList, 1⟩) =
      some (.identity (some source)) := by
    rw [input_reads_actual_index, loaded]
    rfl
  have flagRead : (expression (frame reader source pending inputs index count)
      (fields reader existing.slots existing.count) (.bool false)).bind
      (LocalBlock.declaredValue? ⟨"bool".toList, 0⟩) = some (.boolean false) := by
    simp [expression, LocalBlock.declaredValue?, truth?]
  have oldCompleted : countedLoop (fields reader existing.slots existing.count)
      (LocalBlock.readLoopFuel (fields reader existing.slots existing.count)
        (frame reader source pending inputs index count)
        (scanStatement oldArray oldLimit needle))
      (frame reader source pending inputs index count) (scanStatement oldArray oldLimit needle) =
      some (.finished (some (frame reader source pending inputs index count
        (decide (source ∈ existing.active))))) := by
    rw [old_loop_fuel]
    simpa only [Bool.false_eq_true, false_or] using
      old_loop_in_frame reader source existing pending inputs index count false oldLive
  have pendingCompleted : countedLoop (fields reader existing.slots existing.count)
      (LocalBlock.readLoopFuel (fields reader existing.slots existing.count)
        (frame reader source pending inputs index count (decide (source ∈ existing.active)))
        (scanStatement pendingArray pendingLimit needle))
      (frame reader source pending inputs index count (decide (source ∈ existing.active)))
      (scanStatement pendingArray pendingLimit needle) =
      some (.finished (some (frame reader source pending inputs index count
        (decide (source ∈ existing.active ∨ source ∈ pending.active))))) := by
    rw [pending_loop_fuel]
    simpa only [decide_eq_true_eq] using pending_loop_in_frame reader source existing pending
      inputs index count (decide (source ∈ existing.active)) pendingLive
  have selectedEnvironment :
      (if decide (source ∈ existing.active ∨ source ∈ pending.active) then
        some (frame reader source pending inputs index count
          (decide (source ∈ existing.active ∨ source ∈ pending.active)))
      else (store pending source).map (fun written => frame reader source written inputs index count
        (decide (source ∈ existing.active ∨ source ∈ pending.active)))) =
      some (frame reader source after inputs index count
        (decide (source ∈ existing.active ∨ source ∈ pending.active))) := by
    by_cases present : source ∈ existing.active ∨ source ∈ pending.active
    · have same : pending = after := Option.some.inj (by simpa only [if_pos present] using chosen)
      have selected : decide (source ∈ existing.active ∨ source ∈ pending.active) = true :=
        by simp [present]
      rw [selected]
      simp only [if_true]
      rw [same]
    · have stored : store pending source = some after := by
        simpa only [if_neg present] using chosen
      simp only [present, decide_false, Bool.false_eq_true, if_false, stored, Option.map_some]
  rw [iterationSyntax,
    LocalBlock.declaration_executes_retained_scope (read := inputRead), frame_updates_dependency]
  rw [LocalBlock.branch_executes_retained_continuation
    (read := valid_identity_avoids_failed_branch reader source existing pending inputs index count
      false different)]
  simp only [Bool.false_eq_true, if_false, LocalBlock.empty_body_completes, LocalBlock.resume]
  rw [LocalBlock.declaration_executes_retained_scope (read := flagRead), frame_updates_flag]
  simp only [scanStatement]
  rw [
    LocalBlock.counted_loop_executes_actual_result (fuel := 8) (completed := oldCompleted),
    LocalBlock.counted_loop_executes_actual_result (fuel := 7) (completed := pendingCompleted),
    append_block_in_frame reader source existing pending inputs index count
      (decide (source ∈ existing.active ∨ source ∈ pending.active)) 5,
    selectedEnvironment]
  simp only [Option.map_some, dependency_binding, flag_binding, LocalBlock.restore,
    frame_updates_flag, frame_updates_dependency]

def executeBody (node : Option (List CStatement)) (reader : Ptr) (existing pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) : Option (LocalBlock.Result Ptr) :=
  node.map (LocalBlock.execute (fields reader existing.slots existing.count) 12
    (frame reader reader pending inputs index count))

theorem actual_iteration_refines_ordered_one_input (reader source : Ptr)
    (existing pending : Array32 Ptr) (inputs : List (Option Ptr)) (index count : UInt32)
    (loaded : inputs[index.toNat]? = some (some source)) (different : source ≠ reader)
    (oldLive : existing.count.toNat ≤ existing.slots.length)
    (pendingLive : pending.count.toNat ≤ pending.slots.length) (sized : pending.Sized)
    (roomWhenNew : ¬ (source ∈ existing.active ∨ source ∈ pending.active) → pending.Room) :
    ∃ after, executeBody actualIteration reader existing pending inputs index count =
        some (.finished (some (.next (frame reader reader after inputs index count)))) ∧
      after.active = OrderedDependencyBatch.collectMissing existing.active pending.active [source] ∧
      after.count.toNat = after.active.length ∧ after.slots.length = pending.slots.length ∧
      after.Sized ∧ after.count.toNat ≤ pending.count.toNat + 1 := by
  obtain ⟨after, chosen, active, countExact, capacity, afterSized, growth⟩ :=
    one_input_slot_outcome source existing pending pendingLive sized roomWhenNew
  refine ⟨after, ?_, active, countExact, capacity, afterSized, growth⟩
  rw [executeBody, complete_iteration_is_retained, Option.map_some,
    valid_iteration_executes_actual_body reader source existing pending after inputs index count
      loaded different oldLive pendingLive chosen]

theorem absent_input_has_no_completed_iteration (reader : Ptr) (existing pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32)
    (absent : inputs[index.toNat]? = none) :
    executeBody actualIteration reader existing pending inputs index count = some (.finished none) := by
  have missing : (expression (frame reader reader pending inputs index count)
      (fields reader existing.slots existing.count) inputExpression).bind
      (LocalBlock.declaredValue? ⟨"Space".toList, 1⟩) = none := by
    rw [input_reads_actual_index, absent]
    rfl
  rw [executeBody, complete_iteration_is_retained, Option.map_some, iterationSyntax,
    LocalBlock.undefined_declaration_has_no_completed_flow (read := missing)]

theorem invalid_input_rejects_before_membership_reads (reader : Ptr)
    (existing pending : Array32 Ptr) (inputs : List (Option Ptr)) (index count : UInt32)
    (value : Option Ptr) (loaded : inputs[index.toNat]? = some value)
    (invalid : value = none ∨ value = some reader) :
    executeBody actualIteration reader existing pending inputs index count =
      some (.finished (some (.broken (Function.update
        (frame reader reader pending inputs index count) "ok".toList (some (.boolean false)))))) := by
  let initial := frame reader reader pending inputs index count
  let resolved := Function.update initial "dependency".toList (some (.identity value))
  let readerFields := fields reader existing.slots existing.count
  have inputRead : (expression initial readerFields inputExpression).bind
      (LocalBlock.declaredValue? ⟨"Space".toList, 1⟩) = some (.identity value) := by
    rw [input_reads_actual_index, loaded]
    rfl
  have invalidRead : (expression resolved readerFields invalidCondition).bind truth? = some true := by
    exact invalid_condition_uses_pointer_operands resolved readerFields reader value
      (Function.update_self ..)
      (by
        dsimp only [resolved]
        rw [Function.update_of_ne (by decide : "importer".toList ≠ "dependency".toList)]
        exact importer_binding reader reader pending inputs index count false)
      invalid
  have okRead : resolved "ok".toList = some (.boolean true) := by
    dsimp only [resolved]
    rw [Function.update_of_ne (by decide : "ok".toList ≠ "dependency".toList)]
    exact ok_binding reader reader pending inputs index count false
  have assigned : LocalBlock.assign readerFields resolved
      (.assign (.identifier "ok".toList) (.bool false)) =
      some (Function.update resolved "ok".toList (some (.boolean false))) := by
    change resolved ['o', 'k'] = _ at okRead
    simp [LocalBlock.assign, assignment, okRead, expression, assignValue?, truth?]
  rw [executeBody, complete_iteration_is_retained, Option.map_some, iterationSyntax,
    LocalBlock.declaration_executes_retained_scope (read := inputRead),
    LocalBlock.branch_executes_retained_continuation (read := invalidRead)]
  simp only [if_true]
  rw [LocalBlock.assignment_executes_actual_result (assigned := assigned)]
  rw [LocalBlock.execute.eq_def]
  dsimp only [LocalBlock.resume, LocalBlock.restore]
  change some (LocalBlock.Result.finished (some (LocalBlock.Flow.broken
    (Function.update (Function.update (Function.update initial "dependency".toList
      (some (.identity value))) "ok".toList (some (.boolean false)))
      "dependency".toList (initial "dependency".toList))))) = _
  rw [LocalBlock.scope_restoration_keeps_other_assignment initial "dependency".toList
    "ok".toList (some (.identity value)) (some (.boolean false)) (by decide)]

def observeBody : LocalBlock.Result Ptr → Option (Bool × List (Option Ptr) × UInt32)
  | .finished (some (.next environment)) | .finished (some (.broken environment)) => do
      let ok ← (environment "ok".toList).bind truth?
      let .identities slots ← environment "pending".toList | none
      let .unsigned added ← environment "added".toList | none
      some (ok, slots.take added.toNat, added)
  | _ => none

theorem rejected_input_keeps_pending_prefix (reader : Ptr)
    (existing pending : Array32 Ptr) (inputs : List (Option Ptr)) (index count : UInt32)
    (value : Option Ptr) (loaded : inputs[index.toNat]? = some value)
    (invalid : value = none ∨ value = some reader) :
    (executeBody actualIteration reader existing pending inputs index count).bind observeBody =
      some (false, pending.active.map some, pending.count) := by
  rw [invalid_input_rejects_before_membership_reads reader existing pending inputs index count
    value loaded invalid]
  simp [observeBody, frame, extend, context, locals, bindings, flag, counter, truth?,
    Array32.active, List.map_take]

theorem quoted_iteration_uses_same_complete_body (reader : Ptr) (existing pending : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) :
    executeBody quotedIteration reader existing pending inputs index count =
      executeBody actualIteration reader existing pending inputs index count := by
  rw [quoted_iteration_is_actual]

namespace Controls

def old : Array32 Nat := ⟨[1, 99], 1⟩
def pending : Array32 Nat := ⟨[99, 99], 0⟩

theorem actual_input_load_and_append_execute :
    (executeBody actualIteration 0 old pending [some 2] 0 1).bind observeBody =
      some (true, [some 2], 1) := by decide +kernel

theorem actual_index_selects_second_input :
    (executeBody actualIteration 0 old pending [some 1, some 2] 1 2).bind observeBody =
      some (true, [some 2], 1) := by decide +kernel

theorem existing_identity_needs_no_free_pending_slot :
    (executeBody actualIteration 0 old (⟨[], 0⟩ : Array32 Nat) [some 1] 0 1).bind observeBody =
      some (true, [], 0) := by decide +kernel

theorem fresh_identity_without_room_is_not_completed_rejection :
    executeBody actualIteration 0 old (⟨[], 0⟩ : Array32 Nat) [some 2] 0 1 =
      some (.finished none) := rfl

theorem invalid_identity_skips_impossible_scan_extents :
    (executeBody actualIteration 0 (⟨[], 4294967295⟩ : Array32 Nat)
      (⟨[], 4294967295⟩ : Array32 Nat) [some 0] 0 1).bind observeBody =
      some (false, [], 4294967295) := by decide +kernel

theorem self_identity_executes_failed_break :
    (executeBody actualIteration 0 old pending [some 0] 0 1).bind observeBody =
      some (false, [], 0) := by decide +kernel

theorem null_identity_executes_failed_break :
    (executeBody actualIteration 0 old pending [none] 0 1).bind observeBody =
      some (false, [], 0) := by decide +kernel

theorem absent_input_is_undefined_not_rejection :
    executeBody actualIteration 0 old pending [] 0 1 = some (.finished none) := rfl

theorem local_declarations_restore_caller_bindings :
    (executeBody actualIteration 0 old pending [some 2] 0 1).bind (fun result =>
      match result with
      | .finished (some (.next environment)) =>
          (environment "dependency".toList).map (fun value =>
            (value, environment flag, environment counter))
      | _ => none) = some (.identity (some 0), some (.boolean false), some (.unsigned 0)) :=
  by decide +kernel

def withoutValidation : Option (List CStatement) :=
  some (iterationSyntax.take 1 ++ iterationSyntax.drop 2)

theorem removed_validation_changes_self_behavior :
    (executeBody withoutValidation 0 old pending [some 0] 0 1).bind observeBody =
      some (true, [some 0], 1) := by decide +kernel

def missingFailureAssignment : Option (List CStatement) :=
  some (.declare ⟨"Space".toList, 1⟩ "dependency".toList
      (.index (.identifier "dependencies".toList) (.identifier "i".toList)) ::
    .branch (.binary .or (.unary .not (.identifier "dependency".toList))
      (.binary .eq (.identifier "dependency".toList) (.identifier "importer".toList)))
      [.break] [] :: iterationSyntax.drop 2)

theorem missing_failed_assignment_changes_ok_observation :
    (executeBody missingFailureAssignment 0 old pending [some 0] 0 1).bind observeBody =
      some (true, [], 0) := by decide +kernel

def withoutOldMembership : Option (List CStatement) :=
  some (iterationSyntax.take 3 ++ iterationSyntax.drop 4)

theorem removed_old_scan_adds_existing_identity :
    (executeBody withoutOldMembership 0 old pending [some 1] 0 1).bind observeBody =
      some (true, [some 1], 1) := by decide +kernel

def withoutPendingMembership : Option (List CStatement) :=
  some (iterationSyntax.take 4 ++ iterationSyntax.drop 5)

theorem removed_pending_scan_adds_duplicate :
    (executeBody withoutPendingMembership 0 old (⟨[2, 99], 1⟩ : Array32 Nat)
      [some 2] 0 1).bind observeBody = some (true, [some 2, some 2], 2) := by decide +kernel

end Controls

#print axioms complete_iteration_is_retained
#print axioms dependency_binding
#print axioms flag_binding
#print axioms importer_binding
#print axioms ok_binding
#print axioms invalid_condition_uses_pointer_operands
#print axioms frame_updates_dependency
#print axioms frame_updates_flag
#print axioms updated_frame
#print axioms input_reads_actual_index
#print axioms valid_identity_avoids_failed_branch
#print axioms append_condition_in_frame
#print axioms append_store_in_frame
#print axioms append_block_in_frame
#print axioms extended_locals
#print axioms old_operands
#print axioms pending_operands
#print axioms old_loop_in_frame
#print axioms pending_loop_in_frame
#print axioms old_loop_fuel
#print axioms pending_loop_fuel
#print axioms valid_iteration_executes_actual_body
#print axioms actual_iteration_refines_ordered_one_input
#print axioms absent_input_has_no_completed_iteration
#print axioms invalid_input_rejects_before_membership_reads
#print axioms rejected_input_keeps_pending_prefix
#print axioms quoted_iteration_uses_same_complete_body
#print axioms quoted_iteration_is_actual
#print axioms Controls.actual_input_load_and_append_execute
#print axioms Controls.actual_index_selects_second_input
#print axioms Controls.existing_identity_needs_no_free_pending_slot
#print axioms Controls.fresh_identity_without_room_is_not_completed_rejection
#print axioms Controls.invalid_identity_skips_impossible_scan_extents
#print axioms Controls.self_identity_executes_failed_break
#print axioms Controls.null_identity_executes_failed_break
#print axioms Controls.absent_input_is_undefined_not_rejection
#print axioms Controls.local_declarations_restore_caller_bindings
#print axioms Controls.removed_validation_changes_self_behavior
#print axioms Controls.missing_failed_assignment_changes_ok_observation
#print axioms Controls.removed_old_scan_adds_existing_identity
#print axioms Controls.removed_pending_scan_adds_duplicate

end Mettapedia.Machines.OrderedDependencyCPreparationCollection
