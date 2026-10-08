import Mettapedia.Machines.OrderedDependencyCPreparationLoop

/-!
# Retained validation before dependency allocation

The first preparation loop checks every counted input, including inputs after
newness has already been established. Its existing-link scan restores the
exact outer counter binding. Boolean compound OR reads both operands; it is
not logical short circuit. The independent observation is whether any input
identity is absent from the initialized existing links.

These are typed operation connections. Physical pointers, allocation and the
remaining reserve/cleanup statements retain their separate obligations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.Machines.OrderedDependencyCPreparationValidation

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open ScalarRead IdentityScan PostIndex
open OrderedDependencyCPreparationSource OrderedDependencyCPreparationScan
open OrderedDependencyCPreparationCollection

variable {Ptr : Type} [DecidableEq Ptr]

def accumulation : CStatement := .compoundAssign .bitOr (.identifier "has_new".toList)
  (.unary .not (.identifier flag))

def iterationSyntax : List CStatement := [
  .declare ⟨"Space".toList, 1⟩ "dependency".toList inputExpression,
  .branch invalidCondition [.return (some (.bool false))] [],
  .declare ⟨"bool".toList, 0⟩ flag (.bool false),
  scanStatement oldArray oldLimit needle,
  accumulation]

def outerCondition : CExpr :=
  .binary .lt (.identifier "i".toList) (.identifier "count".toList)

def loopSyntax : CStatement := .forLoop ⟨"uint32_t".toList, 0⟩ "i".toList
  (.unsignedInteger 0) outerCondition OrderedDependencyCPreparationLoop.outerStep iterationSyntax

def actualLoop : Option CStatement := preparationFunction.body[3]?

def noNewSyntax : CStatement := .branch (.unary .not (.identifier "has_new".toList))
  [.return (some (.bool true))] []

def actualNoNew : Option CStatement := preparationFunction.body[4]?

theorem validation_loop_is_retained : actualLoop = some loopSyntax := rfl
theorem no_new_return_is_retained : actualNoNew = some noNewSyntax := rfl

def quotedLoop : Option CStatement :=
  (declaratorFunctionText? typeNames preparationSource.toList).bind (fun function => function.body[3]?)

theorem quoted_validation_loop_is_actual : quotedLoop = actualLoop := by
  rw [quotedLoop, complete_preparation_source_admitted]
  rfl

def hasMissing (existing inputs : List Ptr) : Bool :=
  inputs.any (fun source => decide (source ∉ existing))

theorem missing_is_independent_membership (existing inputs : List Ptr) :
    hasMissing existing inputs = true ↔ ∃ source ∈ inputs, source ∉ existing := by
  simp [hasMissing]

theorem missing_cons (existing : List Ptr) (source : Ptr) (rest : List Ptr) :
    hasMissing existing (source :: rest) =
      (!decide (source ∈ existing) || hasMissing existing rest) := by
  simp [hasMissing]

/-- Only function parameters and the enclosing newness flag are installed.
Other bindings, including absent or differently typed local counters, belong
to the caller and are restored by the retained declarations. -/
def frame (reader : Ptr) (inputs : List (Option Ptr)) (index count : UInt32)
    (newness : Bool) (base : Environment Ptr) : Environment Ptr := fun name =>
  if name = "importer".toList then some (.identity (some reader))
  else if name = "dependencies".toList then some (.identities inputs)
  else if name = "i".toList then some (.unsigned index)
  else if name = "count".toList then some (.unsigned count)
  else if name = "has_new".toList then some (.boolean newness) else base name

omit [DecidableEq Ptr] in
theorem importer_binding (reader : Ptr) (inputs : List (Option Ptr)) (index count : UInt32)
    (newness : Bool) (base : Environment Ptr) :
    frame reader inputs index count newness base "importer".toList =
      some (.identity (some reader)) := by simp [frame]

omit [DecidableEq Ptr] in
theorem newness_binding (reader : Ptr) (inputs : List (Option Ptr)) (index count : UInt32)
    (newness : Bool) (base : Environment Ptr) :
    frame reader inputs index count newness base "has_new".toList =
      some (.boolean newness) := by simp [frame]

omit [DecidableEq Ptr] in
theorem frame_updates_newness (reader : Ptr) (inputs : List (Option Ptr)) (index count : UInt32)
    (before after : Bool) (base : Environment Ptr) :
    Function.update (frame reader inputs index count before base) "has_new".toList
      (some (.boolean after)) = frame reader inputs index count after base := by
  funext name
  by_cases isNewness : name = "has_new".toList
  · subst name
    simp [frame]
  · rw [Function.update_of_ne isNewness]
    simp only [frame, if_neg isNewness]

omit [DecidableEq Ptr] in
theorem frame_updates_index (reader : Ptr) (inputs : List (Option Ptr)) (index after count : UInt32)
    (newness : Bool) (base : Environment Ptr) :
    Function.update (frame reader inputs index count newness base) "i".toList
      (some (.unsigned after)) = frame reader inputs after count newness base := by
  funext name
  by_cases isIndex : name = "i".toList
  · subst name
    simp [frame]
  · rw [Function.update_of_ne isIndex]
    simp only [frame, if_neg isIndex]

theorem input_reads_actual_index (reader : Ptr) (inputs : List (Option Ptr)) (index count : UInt32)
    (newness : Bool) (base : Environment Ptr) (readerFields : FieldReader Ptr) :
    expression (frame reader inputs index count newness base) readerFields inputExpression =
      (inputs[index.toNat]?).map Value.identity := by
  simp [expression, inputExpression, frame]

theorem scan_operands (environment : Environment Ptr) (reader : Ptr) (source : Ptr)
    (existing : Array32 Ptr)
    (importerRead : environment "importer".toList = some (.identity (some reader)))
    (sourceRead : environment "dependency".toList = some (.identity (some source))) :
    Operands environment (fields reader existing.slots existing.count) oldArray oldLimit needle
      (existing.slots.map some) existing.count (some source) := by
  change environment ['i', 'm', 'p', 'o', 'r', 't', 'e', 'r'] = _ at importerRead
  change environment ['d', 'e', 'p', 'e', 'n', 'd', 'e', 'n', 'c', 'y'] = _ at sourceRead
  constructor <;> intro localCounter seen <;>
    simp [oldArray, oldLimit, needle, expression, locals, fields, counter, flag,
      importerRead, sourceRead]

theorem old_scan_restores_actual_scope (environment : Environment Ptr) (reader source : Ptr)
    (existing : Array32 Ptr) (seen : Bool)
    (importerRead : environment "importer".toList = some (.identity (some reader)))
    (sourceRead : environment "dependency".toList = some (.identity (some source)))
    (live : existing.count.toNat ≤ existing.slots.length) :
    countedLoop (fields reader existing.slots existing.count) existing.count.toNat
      (Function.update environment flag (some (.boolean seen)))
      (scanStatement oldArray oldLimit needle) = some (.finished (some
        (Function.update environment flag
          (some (.boolean (decide (seen = true ∨ source ∈ existing.active))))))) := by
  let initialized := existing.active.map some
  let spare := (existing.slots.drop existing.count.toNat).map some
  have splitSlots : initialized ++ spare = existing.slots.map some := by
    dsimp [initialized, spare, Array32.active]
    rw [← List.map_append, List.take_append_drop]
  have operands : Operands environment (fields reader existing.slots existing.count)
      oldArray oldLimit needle (initialized ++ spare) existing.count (some source) := by
    rw [splitSlots]
    exact scan_operands environment reader source existing importerRead sourceRead
  have extent : existing.count.toNat = initialized.length := by
    simp [initialized, Array32.active, List.length_take, Nat.min_eq_left live]
  have completed := counted_scan_refines_outer_scope operands extent seen
  rw [← extent] at completed
  simpa [initialized, eq_comm] using completed

theorem old_scan_reads_actual_fuel (environment : Environment Ptr) (reader : Ptr)
    (existing : Array32 Ptr)
    (importerRead : environment "importer".toList = some (.identity (some reader))) :
    LocalBlock.readLoopFuel (fields reader existing.slots existing.count) environment
      (scanStatement oldArray oldLimit needle) = existing.count.toNat := by
  change environment ['i', 'm', 'p', 'o', 'r', 't', 'e', 'r'] = _ at importerRead
  simp [LocalBlock.readLoopFuel, scanStatement, condition, expression, oldLimit,
    importerRead, fields]

theorem condition_reads_actual_bound (reader : Ptr) (inputs : List (Option Ptr))
    (index count : UInt32) (newness : Bool) (base : Environment Ptr)
    (readerFields : FieldReader Ptr) :
    (expression (frame reader inputs index count newness base) readerFields outerCondition).bind
      truth? = some (decide (index < count)) := by
  simp [outerCondition, expression, frame, numericBinary, truth?]

omit [DecidableEq Ptr] in
theorem increment_reads_actual_index (reader : Ptr) (inputs : List (Option Ptr))
    (index count : UInt32) (newness : Bool) (base : Environment Ptr) :
    increment (frame reader inputs index count newness base) OrderedDependencyCPreparationLoop.outerStep =
      some (frame reader inputs (index + 1) count newness base) := by
  change (do
    let .unsigned value ← frame reader inputs index count newness base "i".toList | none
    some (Function.update (frame reader inputs index count newness base) "i".toList
      (some (.unsigned (value + 1))))) = _
  have read : frame reader inputs index count newness base "i".toList =
      some (.unsigned index) := by simp [frame]
  rw [read]
  dsimp only [bind, Option.bind]
  rw [frame_updates_index]

theorem valid_input_avoids_return (environment : Environment Ptr) (readerFields : FieldReader Ptr)
    (reader source : Ptr)
    (importerRead : environment "importer".toList = some (.identity (some reader)))
    (sourceRead : environment "dependency".toList = some (.identity (some source)))
    (different : source ≠ reader) :
    (expression environment readerFields invalidCondition).bind truth? = some false := by
  change environment ['i', 'm', 'p', 'o', 'r', 't', 'e', 'r'] = _ at importerRead
  change environment ['d', 'e', 'p', 'e', 'n', 'd', 'e', 'n', 'c', 'y'] = _ at sourceRead
  simp [invalidCondition, expression, importerRead, sourceRead, truth?, equal?, different]

theorem valid_iteration_executes_newness (reader source : Ptr) (existing : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) (newness : Bool) (base : Environment Ptr)
    (loaded : inputs[index.toNat]? = some (some source)) (different : source ≠ reader)
    (live : existing.count.toNat ≤ existing.slots.length) :
    LocalBlock.execute (fields reader existing.slots existing.count) 8
      (frame reader inputs index count newness base) iterationSyntax =
      .finished (some (.next (frame reader inputs index count
        (newness || !decide (source ∈ existing.active)) base))) := by
  let initial := frame reader inputs index count newness base
  let resolved := Function.update initial "dependency".toList (some (.identity (some source)))
  let readerFields := fields reader existing.slots existing.count
  let matched := decide (source ∈ existing.active)
  let scanned := Function.update resolved flag (some (.boolean matched))
  have inputRead : (expression initial readerFields inputExpression).bind
      (LocalBlock.declaredValue? ⟨"Space".toList, 1⟩) = some (.identity (some source)) := by
    rw [input_reads_actual_index, loaded]
    rfl
  have importerRead : resolved "importer".toList = some (.identity (some reader)) := by
    dsimp only [resolved]
    rw [Function.update_of_ne (by decide : "importer".toList ≠ "dependency".toList)]
    exact importer_binding reader inputs index count newness base
  have sourceRead : resolved "dependency".toList = some (.identity (some source)) :=
    Function.update_self ..
  have invalidRead := valid_input_avoids_return resolved readerFields reader source
    importerRead sourceRead different
  have flagRead : (expression resolved readerFields (.bool false)).bind
      (LocalBlock.declaredValue? ⟨"bool".toList, 0⟩) = some (.boolean false) := rfl
  have oldCompleted : countedLoop readerFields
      (LocalBlock.readLoopFuel readerFields
        (Function.update resolved flag (some (.boolean false)))
        (scanStatement oldArray oldLimit needle))
      (Function.update resolved flag (some (.boolean false))) (scanStatement oldArray oldLimit needle) =
      some (.finished (some scanned)) := by
    rw [old_scan_reads_actual_fuel (importerRead := by
      rw [Function.update_of_ne (by decide : "importer".toList ≠ flag)]
      exact importerRead)]
    simpa only [Bool.false_eq_true, false_or] using
      old_scan_restores_actual_scope resolved reader source existing false importerRead sourceRead live
  have previousRead : scanned "has_new".toList = some (.boolean newness) := by
    dsimp only [scanned, resolved]
    rw [Function.update_of_ne (by decide : "has_new".toList ≠ flag),
      Function.update_of_ne (by decide : "has_new".toList ≠ "dependency".toList)]
    exact newness_binding reader inputs index count newness base
  have valueRead : expression scanned readerFields (.unary .not (.identifier flag)) =
      some (.boolean (!matched)) := by
    simp [expression, scanned, truth?]
  have assigned : LocalBlock.assign readerFields scanned accumulation =
      some (Function.update scanned "has_new".toList (some (.boolean (newness || !matched)))) := by
    change booleanOrAssignment scanned readerFields (.identifier "has_new".toList)
      (.unary .not (.identifier flag)) = _
    exact boolean_or_assignment_reads_both_operands scanned readerFields "has_new".toList
      (.unary .not (.identifier flag)) newness (!matched) previousRead valueRead
  rw [iterationSyntax, LocalBlock.declaration_executes_retained_scope (read := inputRead),
    LocalBlock.branch_executes_retained_continuation (read := invalidRead)]
  simp only [Bool.false_eq_true, if_false, LocalBlock.empty_body_completes, LocalBlock.resume]
  rw [LocalBlock.declaration_executes_retained_scope (read := flagRead)]
  simp only [scanStatement]
  rw [LocalBlock.counted_loop_executes_actual_result (fuel := 4) (completed := oldCompleted)]
  change LocalBlock.restore "dependency".toList (initial "dependency".toList)
    (LocalBlock.restore flag (resolved flag)
      (LocalBlock.execute readerFields 4 scanned [accumulation])) = _
  rw [accumulation, LocalBlock.compound_assignment_executes_actual_result (assigned := assigned),
    LocalBlock.empty_body_completes]
  dsimp only [LocalBlock.restore, scanned]
  rw [LocalBlock.scope_restoration_keeps_other_assignment resolved flag "has_new".toList
    (some (.boolean matched)) (some (.boolean (newness || !matched))) (by decide)]
  dsimp only [resolved]
  rw [LocalBlock.scope_restoration_keeps_other_assignment initial "dependency".toList "has_new".toList
    (some (.identity (some source))) (some (.boolean (newness || !matched))) (by decide),
    frame_updates_newness]

theorem invalid_iteration_returns_before_scan (reader : Ptr) (existing : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) (newness : Bool) (base : Environment Ptr)
    (value : Option Ptr) (loaded : inputs[index.toNat]? = some value)
    (invalid : value = none ∨ value = some reader) :
    LocalBlock.execute (fields reader existing.slots existing.count) 8
      (frame reader inputs index count newness base) iterationSyntax =
      .finished (some (.returned (frame reader inputs index count newness base)
        (some (.boolean false)))) := by
  let initial := frame reader inputs index count newness base
  let resolved := Function.update initial "dependency".toList (some (.identity value))
  let readerFields := fields reader existing.slots existing.count
  have inputRead : (expression initial readerFields inputExpression).bind
      (LocalBlock.declaredValue? ⟨"Space".toList, 1⟩) = some (.identity value) := by
    rw [input_reads_actual_index, loaded]
    rfl
  have invalidRead : (expression resolved readerFields invalidCondition).bind truth? = some true :=
    invalid_condition_uses_pointer_operands resolved readerFields reader value (Function.update_self ..)
      (by
        dsimp only [resolved]
        rw [Function.update_of_ne (by decide : "importer".toList ≠ "dependency".toList)]
        exact importer_binding reader inputs index count newness base) invalid
  rw [iterationSyntax, LocalBlock.declaration_executes_retained_scope (read := inputRead),
    LocalBlock.branch_executes_retained_continuation (read := invalidRead)]
  simp only [if_true]
  rw [LocalBlock.execute.eq_def]
  dsimp only [expression, LocalBlock.resume, LocalBlock.restore, resolved]
  rw [Function.update_idem, Function.update_eq_self]

theorem no_new_return_skips_arbitrary_continuation (readerFields : FieldReader Ptr)
    (environment : Environment Ptr) (rest : List CStatement) (fuel : Nat)
    (notNew : environment "has_new".toList = some (.boolean false)) :
    LocalBlock.execute readerFields (fuel + 2) environment (noNewSyntax :: rest) =
      .finished (some (.returned environment (some (.boolean true)))) := by
  have read : (expression environment readerFields (.unary .not (.identifier "has_new".toList))).bind
      truth? = some true := by
    change environment ['h', 'a', 's', '_', 'n', 'e', 'w'] = _ at notNew
    simp [expression, notNew, truth?]
  rw [noNewSyntax, LocalBlock.branch_executes_retained_continuation (read := read)]
  simp only [if_true]
  rw [LocalBlock.execute.eq_def]
  rfl

theorem valid_prefix_preserves_remaining_validation (reader : Ptr) (existing : Array32 Ptr)
    (prior consumed : List Ptr) (suffix : List (Option Ptr)) (index count : UInt32)
    (newness : Bool) (base : Environment Ptr) (fuel : Nat)
    (position : index.toNat = prior.length) (extent : (prior ++ consumed).length ≤ count.toNat)
    (valid : ∀ source ∈ consumed, source ≠ reader)
    (live : existing.count.toNat ≤ existing.slots.length) :
    ∃ nextIndex,
      LocalLoop.run (fields reader existing.slots existing.count) outerCondition
        OrderedDependencyCPreparationLoop.outerStep iterationSyntax 8 (consumed.length + fuel)
        (frame reader (OrderedDependencyCPreparationLoop.nullableProvider prior consumed suffix)
          index count newness base) =
      LocalLoop.run (fields reader existing.slots existing.count) outerCondition
        OrderedDependencyCPreparationLoop.outerStep iterationSyntax 8 fuel
        (frame reader (OrderedDependencyCPreparationLoop.nullableProvider prior consumed suffix)
          nextIndex count (newness || hasMissing existing.active consumed) base) ∧
      nextIndex.toNat = (prior ++ consumed).length := by
  induction consumed generalizing prior index newness with
  | nil =>
    refine ⟨index, by simp [hasMissing], by simpa using position⟩
  | cons source rest ih =>
    have active : index < count := by
      rw [UInt32.lt_iff_toNat_lt]
      simp only [List.length_append, List.length_cons] at extent
      omega
    have loaded : (OrderedDependencyCPreparationLoop.nullableProvider prior (source :: rest)
        suffix)[index.toNat]? = some (some source) := by
      have boundary : (prior.map some).length ≤ index.toNat := by simp [position]
      simp only [OrderedDependencyCPreparationLoop.nullableProvider, List.map_append]
      rw [List.append_assoc, List.getElem?_append_right boundary]
      simp [position]
    have followingPosition : (index + 1).toNat = (prior ++ [source]).length := by
      simp [OrderedDependencyCPreparationLoop.bounded_increment_is_exact index count active, position]
    have followingExtent : ((prior ++ [source]) ++ rest).length ≤ count.toNat := by
      simpa [List.append_assoc] using extent
    have followingValid : ∀ item ∈ rest, item ≠ reader := fun item included =>
      valid item (by simp [included])
    obtain ⟨nextIndex, following, finalIndex⟩ := ih (prior ++ [source]) (index + 1)
      (newness || !decide (source ∈ existing.active)) followingPosition followingExtent followingValid
    refine ⟨nextIndex, ?_, by simpa [List.append_assoc] using finalIndex⟩
    have budget : (source :: rest).length + fuel = (rest.length + fuel) + 1 := by simp; omega
    rw [budget, LocalLoop.true_condition_continues_actual_body
      (test := by rw [condition_reads_actual_bound, decide_eq_true active])
      (completed := valid_iteration_executes_newness reader source existing
        (OrderedDependencyCPreparationLoop.nullableProvider prior (source :: rest) suffix)
        index count newness base loaded (valid source (by simp)) live)
      (incremented := increment_reads_actual_index reader
        (OrderedDependencyCPreparationLoop.nullableProvider prior (source :: rest) suffix)
        index count (newness || !decide (source ∈ existing.active)) base),
      OrderedDependencyCPreparationLoop.nullable_provider_rethreads_prefix]
    simpa only [missing_cons, Bool.or_assoc] using following

theorem complete_validated_inputs_detect_missing (reader : Ptr) (existing : Array32 Ptr)
    (inputs : List Ptr) (spare : List (Option Ptr)) (count : UInt32) (newness : Bool)
    (base : Environment Ptr) (fuel : Nat) (extent : count.toNat = inputs.length)
    (valid : ∀ source ∈ inputs, source ≠ reader)
    (live : existing.count.toNat ≤ existing.slots.length) :
    LocalLoop.run (fields reader existing.slots existing.count) outerCondition
      OrderedDependencyCPreparationLoop.outerStep iterationSyntax 8 (inputs.length + fuel)
      (frame reader (inputs.map some ++ spare) 0 count newness base) =
      .finished (some (.next (frame reader (inputs.map some ++ spare) count count
        (newness || hasMissing existing.active inputs) base))) := by
  obtain ⟨nextIndex, following, finalIndex⟩ := valid_prefix_preserves_remaining_validation
    reader existing [] inputs spare 0 count newness base fuel rfl (by simp [extent]) valid live
  have final : nextIndex = count := UInt32.toNat_inj.mp (by simpa [extent] using finalIndex)
  subst nextIndex
  simp only [OrderedDependencyCPreparationLoop.nullableProvider, List.nil_append] at following
  rw [following, LocalLoop.false_condition_skips_body
    (test := by rw [condition_reads_actual_bound]; simp)]

def executeLoop (node : Option CStatement) (reader : Ptr) (existing : Array32 Ptr)
    (inputs : List (Option Ptr)) (savedIndex count : UInt32) (newness : Bool)
    (base : Environment Ptr) (fuel : Nat) : Option (LocalBlock.Result Ptr) :=
  node.bind (LocalLoop.counted (fields reader existing.slots existing.count) 8 fuel
    (frame reader inputs savedIndex count newness base))

theorem actual_validation_loop_refines_newness (reader : Ptr) (existing : Array32 Ptr)
    (inputs : List Ptr) (spare : List (Option Ptr)) (savedIndex count : UInt32) (newness : Bool)
    (base : Environment Ptr) (fuel : Nat) (extent : count.toNat = inputs.length)
    (valid : ∀ source ∈ inputs, source ≠ reader)
    (live : existing.count.toNat ≤ existing.slots.length) :
    executeLoop actualLoop reader existing (inputs.map some ++ spare) savedIndex count newness base
      (inputs.length + fuel) = some (.finished (some (.next
        (frame reader (inputs.map some ++ spare) savedIndex count
          (newness || hasMissing existing.active inputs) base)))) := by
  rw [executeLoop, validation_loop_is_retained, Option.bind_some, loopSyntax,
    LocalLoop.zero_initialization_keeps_counter_scope, frame_updates_index,
    complete_validated_inputs_detect_missing reader existing inputs spare count newness base
      fuel extent valid live]
  simp only [LocalBlock.restore]
  have saved : frame reader (inputs.map some ++ spare) savedIndex count newness base "i".toList =
      some (.unsigned savedIndex) := by simp [frame]
  rw [saved, frame_updates_index]

theorem quoted_validation_loop_uses_actual_execution (reader : Ptr) (existing : Array32 Ptr)
    (inputs : List (Option Ptr)) (savedIndex count : UInt32) (newness : Bool)
    (base : Environment Ptr) (fuel : Nat) :
    executeLoop quotedLoop reader existing inputs savedIndex count newness base fuel =
      executeLoop actualLoop reader existing inputs savedIndex count newness base fuel := by
  rw [quoted_validation_loop_is_actual]

def executePrefix (loopNode decisionNode : Option CStatement) (reader : Ptr)
    (existing : Array32 Ptr) (inputs : List (Option Ptr)) (savedIndex count : UInt32)
    (base : Environment Ptr) (loopFuel decisionFuel : Nat) (rest : List CStatement) :
    Option (LocalBlock.Result Ptr) := do
  let decision ← decisionNode
  let completed ← executeLoop loopNode reader existing inputs savedIndex count false base loopFuel
  some (LocalBlock.resume (fun environment => LocalBlock.execute
    (fields reader existing.slots existing.count) decisionFuel environment (decision :: rest)) completed)

theorem all_existing_returns_before_remaining_preparation (reader : Ptr) (existing : Array32 Ptr)
    (inputs : List Ptr) (spare : List (Option Ptr)) (savedIndex count : UInt32)
    (base : Environment Ptr) (fuel decisionFuel : Nat) (rest : List CStatement)
    (extent : count.toNat = inputs.length) (valid : ∀ source ∈ inputs, source ≠ reader)
    (old : ∀ source ∈ inputs, source ∈ existing.active)
    (live : existing.count.toNat ≤ existing.slots.length) :
    executePrefix actualLoop actualNoNew reader existing (inputs.map some ++ spare) savedIndex count
      base (inputs.length + fuel) (decisionFuel + 2) rest = some (.finished (some
        (.returned (frame reader (inputs.map some ++ spare) savedIndex count false base)
          (some (.boolean true))))) := by
  have notMissing : hasMissing existing.active inputs = false := by
    cases present : hasMissing existing.active inputs with
    | false => rfl
    | true =>
      obtain ⟨source, input, absent⟩ := (missing_is_independent_membership existing.active inputs).mp present
      exact False.elim (absent (old source input))
  rw [executePrefix, no_new_return_is_retained]
  rw [actual_validation_loop_refines_newness reader existing inputs spare savedIndex count false base
    fuel extent valid live, notMissing]
  simp only [Bool.false_or]
  dsimp only [bind, Option.bind, LocalBlock.resume]
  rw [no_new_return_skips_arbitrary_continuation (notNew := newness_binding ..)]

theorem new_input_keeps_actual_continuation (readerFields : FieldReader Ptr)
    (environment : Environment Ptr) (rest : List CStatement) (fuel : Nat)
    (isNew : environment "has_new".toList = some (.boolean true)) :
    LocalBlock.execute readerFields (fuel + 1) environment (noNewSyntax :: rest) =
      LocalBlock.execute readerFields fuel environment rest := by
  have read : (expression environment readerFields (.unary .not (.identifier "has_new".toList))).bind
      truth? = some false := by
    change environment ['h', 'a', 's', '_', 'n', 'e', 'w'] = _ at isNew
    simp [expression, isNew, truth?]
  rw [noNewSyntax, LocalBlock.branch_executes_retained_continuation (read := read)]
  simp only [Bool.false_eq_true, if_false, LocalBlock.empty_body_completes, LocalBlock.resume]

theorem missing_input_enters_remaining_preparation (reader : Ptr) (existing : Array32 Ptr)
    (inputs : List Ptr) (spare : List (Option Ptr)) (savedIndex count : UInt32)
    (base : Environment Ptr) (fuel decisionFuel : Nat) (rest : List CStatement)
    (extent : count.toNat = inputs.length) (valid : ∀ source ∈ inputs, source ≠ reader)
    (missing : ∃ source ∈ inputs, source ∉ existing.active)
    (live : existing.count.toNat ≤ existing.slots.length) :
    executePrefix actualLoop actualNoNew reader existing (inputs.map some ++ spare) savedIndex count
      base (inputs.length + fuel) (decisionFuel + 1) rest = some
        (LocalBlock.execute (fields reader existing.slots existing.count) decisionFuel
          (frame reader (inputs.map some ++ spare) savedIndex count true base) rest) := by
  have isMissing := (missing_is_independent_membership existing.active inputs).mpr missing
  rw [executePrefix, no_new_return_is_retained,
    actual_validation_loop_refines_newness reader existing inputs spare savedIndex count false base
      fuel extent valid live, isMissing]
  simp only [Bool.false_or]
  dsimp only [bind, Option.bind, LocalBlock.resume]
  rw [new_input_keeps_actual_continuation (isNew := newness_binding ..)]

theorem empty_validation_returns_before_remaining_preparation (reader : Ptr) (existing : Array32 Ptr)
    (inputs : List (Option Ptr)) (savedIndex : UInt32) (base : Environment Ptr)
    (loopFuel decisionFuel : Nat) (rest : List CStatement) :
    executePrefix actualLoop actualNoNew reader existing inputs savedIndex 0 base
      loopFuel (decisionFuel + 2) rest = some (.finished (some
        (.returned (frame reader inputs savedIndex 0 false base) (some (.boolean true))))) := by
  have stopped : executeLoop actualLoop reader existing inputs savedIndex 0 false base loopFuel =
      some (.finished (some (.next (frame reader inputs savedIndex 0 false base)))) := by
    rw [executeLoop, validation_loop_is_retained, Option.bind_some, loopSyntax,
      LocalLoop.zero_initialization_keeps_counter_scope, frame_updates_index,
      LocalLoop.false_condition_skips_body (test := by rw [condition_reads_actual_bound]; simp)]
    simp only [LocalBlock.restore]
    have saved : frame reader inputs savedIndex 0 false base "i".toList =
        some (.unsigned savedIndex) := by simp [frame]
    rw [saved, frame_updates_index]
  rw [executePrefix, no_new_return_is_retained, stopped]
  dsimp only [bind, Option.bind, LocalBlock.resume]
  rw [no_new_return_skips_arbitrary_continuation (notNew := newness_binding ..)]

theorem invalid_input_exits_loop_without_increment (reader : Ptr) (existing : Array32 Ptr)
    (inputs : List (Option Ptr)) (index count : UInt32) (newness : Bool) (base : Environment Ptr)
    (fuel : Nat) (value : Option Ptr) (active : index < count)
    (loaded : inputs[index.toNat]? = some value) (invalid : value = none ∨ value = some reader) :
    LocalLoop.run (fields reader existing.slots existing.count) outerCondition
      OrderedDependencyCPreparationLoop.outerStep iterationSyntax 8 (fuel + 1)
      (frame reader inputs index count newness base) = .finished (some
        (.returned (frame reader inputs index count newness base) (some (.boolean false)))) := by
  rw [LocalLoop.run.eq_def, condition_reads_actual_bound, decide_eq_true active]
  dsimp only
  rw [invalid_iteration_returns_before_scan reader existing inputs index count newness base
    value loaded invalid]

theorem actual_invalid_first_input_restores_scope (reader : Ptr) (existing : Array32 Ptr)
    (inputs : List (Option Ptr)) (savedIndex count : UInt32) (newness : Bool)
    (base : Environment Ptr) (fuel : Nat) (value : Option Ptr) (active : 0 < count)
    (loaded : inputs[0]? = some value) (invalid : value = none ∨ value = some reader) :
    executeLoop actualLoop reader existing inputs savedIndex count newness base (fuel + 1) =
      some (.finished (some (.returned (frame reader inputs savedIndex count newness base)
        (some (.boolean false))))) := by
  rw [executeLoop, validation_loop_is_retained, Option.bind_some, loopSyntax,
    LocalLoop.zero_initialization_keeps_counter_scope, frame_updates_index,
    invalid_input_exits_loop_without_increment reader existing inputs 0 count newness base
      fuel value active loaded invalid]
  simp only [LocalBlock.restore]
  have saved : frame reader inputs savedIndex count newness base "i".toList =
      some (.unsigned savedIndex) := by simp [frame]
  rw [saved, frame_updates_index]

theorem actual_invalid_suffix_returns_after_valid_prefix (reader : Ptr) (existing : Array32 Ptr)
    (consumed : List Ptr) (value : Option Ptr) (suffix : List (Option Ptr))
    (savedIndex count : UInt32) (newness : Bool) (base : Environment Ptr)
    (active : consumed.length < count.toNat) (valid : ∀ source ∈ consumed, source ≠ reader)
    (live : existing.count.toNat ≤ existing.slots.length)
    (invalid : value = none ∨ value = some reader) :
    executeLoop actualLoop reader existing
      (OrderedDependencyCPreparationLoop.nullableProvider [] consumed (value :: suffix))
      savedIndex count newness base (consumed.length + 1) = some (.finished (some
        (.returned (frame reader
          (OrderedDependencyCPreparationLoop.nullableProvider [] consumed (value :: suffix))
          savedIndex count (newness || hasMissing existing.active consumed) base)
          (some (.boolean false))))) := by
  obtain ⟨nextIndex, following, finalIndex⟩ := valid_prefix_preserves_remaining_validation reader existing
    [] consumed (value :: suffix) 0 count newness base 1 rfl (by simpa using active.le) valid live
  have nextActive : nextIndex < count := by
    rw [UInt32.lt_iff_toNat_lt]
    simpa [finalIndex] using active
  have loaded : (OrderedDependencyCPreparationLoop.nullableProvider [] consumed
      (value :: suffix))[nextIndex.toNat]? = some value := by
    simp only [OrderedDependencyCPreparationLoop.nullableProvider, List.nil_append]
    have boundary : (consumed.map some).length ≤ nextIndex.toNat := by simp [finalIndex]
    rw [List.getElem?_append_right boundary]
    simp [finalIndex]
  rw [executeLoop, validation_loop_is_retained, Option.bind_some, loopSyntax,
    LocalLoop.zero_initialization_keeps_counter_scope, frame_updates_index, following,
    invalid_input_exits_loop_without_increment reader existing _ nextIndex count
      (newness || hasMissing existing.active consumed) base 0 value nextActive loaded invalid]
  simp only [LocalBlock.restore]
  have saved : frame reader
      (OrderedDependencyCPreparationLoop.nullableProvider [] consumed (value :: suffix))
      savedIndex count newness base "i".toList = some (.unsigned savedIndex) := by simp [frame]
  rw [saved, frame_updates_index]

theorem invalid_suffix_cannot_enter_remaining_preparation (reader : Ptr) (existing : Array32 Ptr)
    (consumed : List Ptr) (value : Option Ptr) (suffix : List (Option Ptr))
    (savedIndex count : UInt32) (base : Environment Ptr) (decisionFuel : Nat) (rest : List CStatement)
    (active : consumed.length < count.toNat) (valid : ∀ source ∈ consumed, source ≠ reader)
    (live : existing.count.toNat ≤ existing.slots.length)
    (invalid : value = none ∨ value = some reader) :
    executePrefix actualLoop actualNoNew reader existing
      (OrderedDependencyCPreparationLoop.nullableProvider [] consumed (value :: suffix))
      savedIndex count base (consumed.length + 1) decisionFuel rest = some (.finished (some
        (.returned (frame reader
          (OrderedDependencyCPreparationLoop.nullableProvider [] consumed (value :: suffix))
          savedIndex count (hasMissing existing.active consumed) base) (some (.boolean false))))) := by
  rw [executePrefix, no_new_return_is_retained,
    actual_invalid_suffix_returns_after_valid_prefix reader existing consumed value suffix savedIndex
      count false base active valid live invalid]
  rfl

namespace Controls

def emptyCaller : Environment Nat := fun _ => none

def shadowedCaller : Environment Nat := fun name =>
  if name = "j".toList then some (.identity (some 77))
  else if name = "dependency".toList then some (.boolean false)
  else if name = "present".toList then some (.unsigned 9) else none

def observe : LocalBlock.Result Nat → Option (Option Bool × Bool × UInt32)
  | .finished (some (.next environment)) => do
      let .boolean newness ← environment "has_new".toList | none
      let .unsigned index ← environment "i".toList | none
      some (none, newness, index)
  | .finished (some (.returned environment (some (.boolean returned)))) => do
      let .boolean newness ← environment "has_new".toList | none
      let .unsigned index ← environment "i".toList | none
      some (some returned, newness, index)
  | _ => none

def unavailableContinuation : List CStatement :=
  [.return (some (.identifier "missing".toList))]

theorem new_then_existing_does_not_erase_newness :
    (executeLoop actualLoop 0 (⟨[1], 1⟩ : Array32 Nat) [some 2, some 1] 91 2 false
      emptyCaller 2).bind observe = some (none, true, 91) := by decide +kernel

theorem all_existing_returns_without_entering_continuation :
    (executePrefix actualLoop actualNoNew 0 (⟨[1], 1⟩ : Array32 Nat)
      [some 1, some 1] 91 2 emptyCaller 2 2 unavailableContinuation).bind observe =
      some (some true, false, 91) := by decide +kernel

theorem spare_old_slot_is_not_existing_membership :
    (executeLoop actualLoop 0 (⟨[1, 2], 1⟩ : Array32 Nat) [some 2] 91 1 false
      emptyCaller 1).bind observe = some (none, true, 91) := by decide +kernel

theorem spare_input_is_not_validated :
    (executePrefix actualLoop actualNoNew 0 (⟨[1], 1⟩ : Array32 Nat)
      [some 1, none] 91 1 emptyCaller 1 2 unavailableContinuation).bind observe =
      some (some true, false, 91) := by decide +kernel

theorem null_after_new_returns_false :
    (executePrefix actualLoop actualNoNew 0 (⟨[], 0⟩ : Array32 Nat)
      [some 1, none] 91 2 emptyCaller 2 0 []).bind observe =
      some (some false, true, 91) := by decide +kernel

theorem self_rejects_before_impossible_existing_scan :
    (executeLoop actualLoop 0 (⟨[], 4294967295⟩ : Array32 Nat) [some 0] 91 1 true
      emptyCaller 1).bind observe = some (some false, true, 91) := by decide +kernel

theorem zero_count_skips_invalid_input_and_existing_extents :
    (executePrefix actualLoop actualNoNew 0 (⟨[], 4294967295⟩ : Array32 Nat)
      [none] 91 0 emptyCaller 0 2 unavailableContinuation).bind observe =
      some (some true, false, 91) := by decide +kernel

theorem missing_input_has_no_completed_return :
    executeLoop actualLoop 0 (⟨[], 0⟩ : Array32 Nat) [] 91 1 false emptyCaller 1 =
      some (.finished none) := rfl

theorem insufficient_validation_fuel_is_not_false_return :
    executeLoop actualLoop 0 (⟨[], 0⟩ : Array32 Nat) [some 1] 91 1 false emptyCaller 0 =
      some .exhausted := rfl

theorem previously_new_does_not_short_circuit_existing_scan :
    executeLoop actualLoop 0 (⟨[], 1⟩ : Array32 Nat) [some 1] 91 1 true emptyCaller 1 =
      some (.finished none) := rfl

theorem declarations_restore_unbound_counter :
    (executeLoop actualLoop 0 (⟨[1], 1⟩ : Array32 Nat) [some 1] 91 1 false emptyCaller 1).bind
      (fun result => match result with
        | .finished (some (.next environment)) => environment "j".toList
        | _ => none) = none := by decide +kernel

theorem declarations_restore_differently_typed_outer_values :
    (executeLoop actualLoop 0 (⟨[1], 1⟩ : Array32 Nat) [some 1] 91 1 false shadowedCaller 1).bind
      (fun result => match result with
        | .finished (some (.next environment)) => some
            (environment "j".toList, environment "dependency".toList, environment "present".toList)
        | _ => none) = some
          (some (.identity (some 77)), some (.boolean false), some (.unsigned 9)) := by decide +kernel

theorem replaced_accumulation_loses_previous_newness :
    observe (LocalBlock.execute (fields 0 [1] 1) 8
      (frame 0 [some 1] 0 1 true emptyCaller)
      (iterationSyntax.take 4 ++ [.assign (.identifier "has_new".toList)
        (.unary .not (.identifier flag))])) = some (none, false, 0) := by decide +kernel

theorem early_stop_on_newness_suppresses_later_rejection :
    (executeLoop (some (.forLoop ⟨"uint32_t".toList, 0⟩ "i".toList (.unsignedInteger 0)
      (.binary .and outerCondition (.unary .not (.identifier "has_new".toList)))
      OrderedDependencyCPreparationLoop.outerStep iterationSyntax))
      0 (⟨[], 0⟩ : Array32 Nat) [some 1, none] 91 2 false emptyCaller 2).bind observe =
      some (none, true, 91) := by decide +kernel

theorem removing_no_new_return_enters_invalid_continuation :
    LocalBlock.execute (fields 0 [] 0) 3 (frame 0 [] 0 0 false emptyCaller)
      (.branch (.unary .not (.identifier "has_new".toList)) [] [] :: unavailableContinuation) =
      .finished none := rfl

end Controls

#print axioms validation_loop_is_retained
#print axioms no_new_return_is_retained
#print axioms quoted_validation_loop_is_actual
#print axioms missing_is_independent_membership
#print axioms missing_cons
#print axioms importer_binding
#print axioms newness_binding
#print axioms frame_updates_newness
#print axioms frame_updates_index
#print axioms input_reads_actual_index
#print axioms scan_operands
#print axioms old_scan_restores_actual_scope
#print axioms old_scan_reads_actual_fuel
#print axioms condition_reads_actual_bound
#print axioms increment_reads_actual_index
#print axioms valid_input_avoids_return
#print axioms valid_iteration_executes_newness
#print axioms invalid_iteration_returns_before_scan
#print axioms no_new_return_skips_arbitrary_continuation
#print axioms valid_prefix_preserves_remaining_validation
#print axioms complete_validated_inputs_detect_missing
#print axioms actual_validation_loop_refines_newness
#print axioms quoted_validation_loop_uses_actual_execution
#print axioms all_existing_returns_before_remaining_preparation
#print axioms new_input_keeps_actual_continuation
#print axioms missing_input_enters_remaining_preparation
#print axioms empty_validation_returns_before_remaining_preparation
#print axioms invalid_input_exits_loop_without_increment
#print axioms actual_invalid_first_input_restores_scope
#print axioms actual_invalid_suffix_returns_after_valid_prefix
#print axioms invalid_suffix_cannot_enter_remaining_preparation
#print axioms Controls.new_then_existing_does_not_erase_newness
#print axioms Controls.all_existing_returns_without_entering_continuation
#print axioms Controls.spare_old_slot_is_not_existing_membership
#print axioms Controls.spare_input_is_not_validated
#print axioms Controls.null_after_new_returns_false
#print axioms Controls.self_rejects_before_impossible_existing_scan
#print axioms Controls.zero_count_skips_invalid_input_and_existing_extents
#print axioms Controls.missing_input_has_no_completed_return
#print axioms Controls.insufficient_validation_fuel_is_not_false_return
#print axioms Controls.previously_new_does_not_short_circuit_existing_scan
#print axioms Controls.declarations_restore_unbound_counter
#print axioms Controls.declarations_restore_differently_typed_outer_values
#print axioms Controls.replaced_accumulation_loses_previous_newness
#print axioms Controls.early_stop_on_newness_suppresses_later_rejection
#print axioms Controls.removing_no_new_return_enters_invalid_continuation

end Mettapedia.Machines.OrderedDependencyCPreparationValidation
