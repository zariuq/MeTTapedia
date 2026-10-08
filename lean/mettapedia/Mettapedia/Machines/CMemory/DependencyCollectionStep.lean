import Mettapedia.Machines.CMemory.DependencyCollectionOperands
import Mettapedia.Machines.CMemory.StatementBlock

/-!
# The actual dependency-collection body on physical memory

The supplied body loads the current input, rejects null/self, scans existing
and private initialized identities, then conditionally appends at the actual
post-incremented local count. The physical postcondition keeps module links
and input storage unchanged and observes independent ordered insertion.

This is a sequential body connection. The outer loop, allocation, reservation
and failure cleanup are separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace Mettapedia.Machines.CMemory.DependencyCollectionStep

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open ReadExpressions DependencyExpressionReads DependencyReadScan
open DependencyValidationOperands DependencyCollectionOperands Lift
open OrderedDependencyCPreparationScan (oldArray oldLimit pendingArray pendingLimit needle)
open OrderedDependencyCPreparationCollection (inputExpression invalidCondition iterationSyntax)
open OrderedDependencyCPreparationAppend (appendStatement appendSite appendCondition)
open CellPermission

universe u

def executeNode (layout : ReadExpressions.Layout) (innerFuel fuel : Nat)
    (environment : ReadExpressions.Environment) : Option (List CStatement) → CProg CVal ReadBlock.Result
  | some body => StatementBlock.execute PostIndexWrites.assign layout innerFuel fuel environment body
  | none => CProg.undefined

theorem quoted_body_uses_actual_statement_service (layout : ReadExpressions.Layout)
    (innerFuel fuel : Nat) (environment : ReadExpressions.Environment) :
    executeNode layout innerFuel fuel environment
      OrderedDependencyCPreparationCollection.quotedIteration =
      StatementBlock.execute PostIndexWrites.assign layout innerFuel fuel environment iterationSyntax := by
  rw [OrderedDependencyCPreparationCollection.quoted_iteration_is_actual,
    OrderedDependencyCPreparationCollection.complete_iteration_is_retained]
  rfl

theorem append_condition_reads_current_flag (layout : ReadExpressions.Layout)
    (environment : ReadExpressions.Environment) (seen : Bool)
    (flagRead : environment IdentityScan.flag = some (.bool seen)) :
    expression layout environment appendCondition = pure (.bool (!seen)) := by
  change environment ['p', 'r', 'e', 's', 'e', 'n', 't'] = _ at flagRead
  simp [appendCondition, expression, expressionWith_equation, IdentityScan.flag, flagRead, resolved, truth]

theorem append_block_selects_actual_store (layout : ReadExpressions.Layout)
    (environment : ReadExpressions.Environment) (innerFuel fuel : Nat) (seen : Bool)
    (flagRead : environment IdentityScan.flag = some (.bool seen)) :
    StatementBlock.execute PostIndexWrites.assign layout innerFuel (fuel + 2) environment
      [appendStatement] =
      if seen then pure (.finished (.next environment)) else
        (PostIndexWrites.execute environment appendSite.statement >>= fun updated =>
          pure (.finished (.next updated))) := by
  rw [OrderedDependencyCPreparationAppend.appendStatement,
    StatementBlock.branch_retains_selected_body_and_continuation,
    append_condition_reads_current_flag layout environment seen flagRead]
  cases seen
  · simp only [Bool.not_false, truth, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind,
      Bool.false_eq_true, ↓reduceIte]
    rw [LocalStore.Site.statement, StatementBlock.assignment_executes_supplied_service]
    simp only [PostIndexWrites.assign, appendSite,
      StatementBlock.empty_body_completes, Prog.bind_assoc, Prog.bind_eq,
      Prog.pure_eq, Prog.ret_bind, ReadBlock.resume]
  · simp only [Bool.not_true, truth, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind,
      Bool.false_eq_true, ↓reduceIte, StatementBlock.empty_body_completes, ReadBlock.resume]

theorem restoration_keeps_updated_added (environment : ReadExpressions.Environment)
    (value : CVal) (seen : Bool) (after : UInt32) :
    ReadBlock.restore "dependency".toList (environment "dependency".toList)
      (ReadBlock.restore IdentityScan.flag (environment IdentityScan.flag)
        (.finished (.next (Function.update
          (Function.update (Function.update environment "dependency".toList (some value))
            IdentityScan.flag (some (.bool seen))) "added".toList (some (.u32 after)))))) =
      .finished (.next (Function.update environment "added".toList (some (.u32 after)))) := by
  simp only [ReadBlock.restore]
  have previous : (Function.update environment "dependency".toList (some value))
      IdentityScan.flag = environment IdentityScan.flag :=
    Function.update_of_ne (by decide) _ _
  rw [← previous]
  rw [ReadBlock.scope_restoration_keeps_other_assignment _ IdentityScan.flag
    "added".toList _ _ (by decide)]
  rw [ReadBlock.scope_restoration_keeps_other_assignment _ "dependency".toList
    "added".toList _ _ (by decide)]

section GenericBody

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

theorem valid_body_from_current_operands {P Q : Heap L → Prop}
    (layout : ReadExpressions.Layout) (environment : ReadExpressions.Environment)
    (innerFuel : Nat) (source : Ptr) (oldSeen seen : Bool) (after : UInt32)
    (inputRead : CTriple P (expression layout environment inputExpression)
      (fun result σ => result = .ptr (some source) ∧ P σ))
    (guardRead : CTriple P (expression layout
      (Function.update environment "dependency".toList (some (.ptr (some source)))) invalidCondition)
      (fun result σ => result = .bool false ∧ P σ))
    (oldRead : CTriple P (ReadLoops.counted layout innerFuel
      (Function.update (Function.update environment "dependency".toList (some (.ptr (some source))))
        IdentityScan.flag (some (.bool false)))
      (IdentityScan.scanStatement oldArray oldLimit needle))
      (fun result σ => result = .finished
        (Function.update (Function.update environment "dependency".toList (some (.ptr (some source))))
          IdentityScan.flag (some (.bool oldSeen))) ∧ P σ))
    (pendingRead : CTriple P (ReadLoops.counted layout innerFuel
      (Function.update (Function.update environment "dependency".toList (some (.ptr (some source))))
        IdentityScan.flag (some (.bool oldSeen)))
      (IdentityScan.scanStatement pendingArray pendingLimit needle))
      (fun result σ => result = .finished
        (Function.update (Function.update environment "dependency".toList (some (.ptr (some source))))
          IdentityScan.flag (some (.bool seen))) ∧ P σ))
    (appendRead : CTriple P (StatementBlock.execute PostIndexWrites.assign layout innerFuel 7
      (Function.update (Function.update environment "dependency".toList (some (.ptr (some source))))
        IdentityScan.flag (some (.bool seen))) [appendStatement])
      (fun result σ => result = .finished (.next
        (Function.update (Function.update (Function.update environment "dependency".toList
          (some (.ptr (some source)))) IdentityScan.flag (some (.bool seen)))
          "added".toList (some (.u32 after)))) ∧ Q σ)) :
    CTriple P (StatementBlock.execute PostIndexWrites.assign layout innerFuel 12
      environment iterationSyntax)
      (fun result σ => result = .finished (.next (Function.update environment "added".toList
        (some (.u32 after)))) ∧ Q σ) := by
  rw [iterationSyntax, StatementBlock.declaration_retains_actual_read_and_scope]
  refine triple_bind _ inputRead fun actual => ?_
  apply triple_pure
  intro same
  subst actual
  simp only [ReadBlock.declared_pointer_retains_nullable_value,
    Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  rw [StatementBlock.branch_retains_selected_body_and_continuation]
  simp only [Prog.bind_eq, Prog.bind_assoc]
  refine triple_bind _ guardRead fun actual => ?_
  apply triple_pure
  intro same
  subst actual
  simp only [truth, Prog.pure_eq, Prog.ret_bind, Bool.false_eq_true, ↓reduceIte,
    StatementBlock.empty_body_completes, ReadBlock.resume]
  rw [StatementBlock.declaration_retains_actual_read_and_scope]
  simp only [expression, expressionWith_equation, ReadBlock.declared_boolean_retains_value, Prog.pure_eq,
    Prog.bind_eq, Prog.ret_bind]
  rw [IdentityScan.scanStatement, StatementBlock.nested_loop_retains_actual_read_service]
  simp only [Prog.bind_eq, Prog.bind_assoc]
  refine triple_bind _ oldRead fun result => ?_
  apply triple_pure
  intro same
  subst result
  dsimp only
  rw [IdentityScan.scanStatement, StatementBlock.nested_loop_retains_actual_read_service]
  simp only [Prog.bind_eq, Prog.bind_assoc]
  refine triple_bind _ pendingRead fun result => ?_
  apply triple_pure
  intro same
  subst result
  dsimp only
  refine triple_bind _ appendRead fun result => ?_
  apply triple_pure
  intro same
  subst result
  have savedFlag : (Function.update environment "dependency".toList
      (some (.ptr (some source)))) IdentityScan.flag = environment IdentityScan.flag :=
    Function.update_of_ne (by decide) _ _
  rw [savedFlag]
  simp only [Prog.ret_bind]
  rw [restoration_keeps_updated_added]
  exact triple_pre _ (fun _ holds => ⟨rfl, holds⟩) (triple_ret _ _ _)

theorem invalid_body_from_current_operands {P : Heap L → Prop}
    (layout : ReadExpressions.Layout) (environment : ReadExpressions.Environment)
    (innerFuel : Nat) (value : Option Ptr) (before : Bool)
    (okRead : environment "ok".toList = some (.bool before))
    (inputRead : CTriple P (expression layout environment inputExpression)
      (fun result σ => result = .ptr value ∧ P σ))
    (guardRead : CTriple P (expression layout
      (Function.update environment "dependency".toList (some (.ptr value))) invalidCondition)
      (fun result σ => result = .bool true ∧ P σ)) :
    CTriple P (StatementBlock.execute PostIndexWrites.assign layout innerFuel 12
      environment iterationSyntax)
      (fun result σ => result = .finished (.broken
        (Function.update environment "ok".toList (some (.bool false)))) ∧ P σ) := by
  rw [iterationSyntax, StatementBlock.declaration_retains_actual_read_and_scope]
  refine triple_bind _ inputRead fun actual => ?_
  apply triple_pure
  intro same
  subst actual
  simp only [ReadBlock.declared_pointer_retains_nullable_value,
    Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  rw [StatementBlock.branch_retains_selected_body_and_continuation]
  simp only [Prog.bind_eq, Prog.bind_assoc]
  refine triple_bind _ guardRead fun actual => ?_
  apply triple_pure
  intro same
  subst actual
  simp only [truth, Prog.pure_eq, Prog.ret_bind, ↓reduceIte]
  rw [StatementBlock.assignment_executes_supplied_service,
    PostIndexWrites.local_assignment_reuses_read_service]
  have keptOk : (Function.update environment "dependency".toList (some (.ptr value)))
      "ok".toList = some (.bool before) := by
    rw [Function.update_of_ne (by decide : "ok".toList ≠ "dependency".toList)]
    exact okRead
  simp only [ReadBlock.assign, ReadLoops.statements, keptOk, resolved,
    expression, expressionWith_equation, ReadLoops.assignValue, truth, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  rw [StatementBlock.execute, StatementBlock.executeWith_equation]
  simp only [Prog.pure_eq, Prog.ret_bind, ReadBlock.resume, ReadBlock.restore]
  rw [ReadBlock.scope_restoration_keeps_other_assignment _ "dependency".toList
    "ok".toList _ _ (by decide)]
  exact triple_pre _ (fun _ holds => ⟨rfl, holds⟩) (triple_ret _ _ _)

end GenericBody

section PhysicalBody

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]
variable {Id : Type} [DecidableEq Id] (addr : Id → Ptr)

omit [DecidableEq Id] in
theorem append_branch_refines_private_state (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) (array : Ptr) (inputCapacity : Nat) (inputs : List (Option Id))
    (pending : Ptr) (capacity : Nat) (values : List Id) (source : Id) (added : UInt32)
    (environment : ReadExpressions.Environment) (innerFuel fuel : Nat) (seen : Bool)
    (pendingRead : environment "pending".toList = some (.ptr (some pending)))
    (addedRead : environment "added".toList = some (.u32 added))
    (sourceRead : environment "dependency".toList = some (.ptr (some (addr source))))
    (flagRead : environment IdentityScan.flag = some (.bool seen))
    (extent : added.toNat = values.length) (roomWhenNew : seen = false → values.length < capacity)
    (F : Heap L → Prop) :
    CTriple (PendingState addr layout D H array inputCapacity inputs pending capacity values F)
      (StatementBlock.execute PostIndexWrites.assign (fields layout) innerFuel (fuel + 2)
        environment [appendStatement])
      (fun result σ => result = .finished (.next (Function.update environment "added".toList
        (some (.u32 (if seen then added else added + 1))))) ∧
          PendingState addr layout D H array inputCapacity inputs pending capacity
            (if seen then values else values ++ [source]) F σ) := by
  rw [append_block_selects_actual_store (fields layout) environment innerFuel fuel seen flagRead]
  cases seen
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine triple_bind _ (append_changes_only_private_pending addr layout H array inputCapacity
      inputs pending capacity values source added environment pendingRead addedRead sourceRead
      extent (roomWhenNew rfl) F) fun updated => ?_
    apply triple_pure
    intro same
    subst updated
    exact triple_pre _ (fun _ holds => ⟨rfl, holds⟩) (triple_ret _ _ _)
  · simp only [↓reduceIte]
    rw [← addedRead, Function.update_eq_self]
    exact triple_pre _ (fun _ holds => ⟨rfl, holds⟩) (triple_ret _ _ _)

theorem valid_body_refines_physical_input (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {reader source : Id} (readerIn : reader ∈ D) (sourceIn : source ∈ D)
    (different : source ≠ reader) (closed : ∀ identity ∈ (H.forward reader).active, identity ∈ D)
    (within : (H.forward reader).count.toNat ≤ (H.forward reader).slots.length)
    (array : Ptr) (inputCapacity : Nat) (inputs : List (Option Id)) (index : UInt32)
    (inside : index.toNat < inputs.length) (loaded : inputs[index.toNat] = some source)
    (pending : Ptr) (capacity : Nat) (values : List Id) (added : UInt32)
    (extent : added.toNat = values.length) (pendingClosed : ∀ identity ∈ values, identity ∈ D)
    (innerFuel : Nat) (oldEnough : (H.forward reader).active.length ≤ innerFuel)
    (pendingEnough : values.length ≤ innerFuel)
    (roomWhenNew : ¬ (source ∈ (H.forward reader).active ∨ source ∈ values) → values.length < capacity)
    (environment : ReadExpressions.Environment)
    (readerRead : environment "importer".toList = some (.ptr (some (addr reader))))
    (arrayRead : environment "dependencies".toList = some (.ptr (some array)))
    (indexRead : environment "i".toList = some (.u32 index))
    (pendingRead : environment "pending".toList = some (.ptr (some pending)))
    (addedRead : environment "added".toList = some (.u32 added)) (F : Heap L → Prop) :
    CTriple (PendingState addr layout D H array inputCapacity inputs pending capacity values F)
      (StatementBlock.execute PostIndexWrites.assign (fields layout) innerFuel 12 environment iterationSyntax)
      (fun result σ => result = .finished (.next (Function.update environment "added".toList
        (some (.u32 (if source ∈ (H.forward reader).active ∨ source ∈ values then added else added + 1))))) ∧
          PendingState addr layout D H array inputCapacity inputs pending capacity
            (OrderedDependencyBatch.collectMissing (H.forward reader).active values [source]) F σ) := by
  let resource := DynArray (some pending) capacity (values.map (spacePtr ∘ addr)) ∗ F
  let loadedEnv := Function.update environment "dependency".toList (some (.ptr (some (addr source))))
  have loadedSource : loadedEnv "dependency".toList = some (.ptr (some (addr source))) :=
    Function.update_self _ _ _
  have keptReader : loadedEnv "importer".toList = some (.ptr (some (addr reader))) := by
    dsimp only [loadedEnv]
    rw [Function.update_of_ne (by decide : "importer".toList ≠ "dependency".toList)]
    exact readerRead
  have keptPending : loadedEnv "pending".toList = some (.ptr (some pending)) := by
    dsimp only [loadedEnv]
    rw [Function.update_of_ne (by decide : "pending".toList ≠ "dependency".toList)]
    exact pendingRead
  have keptAdded : loadedEnv "added".toList = some (.u32 added) := by
    dsimp only [loadedEnv]
    rw [Function.update_of_ne (by decide : "added".toList ≠ "dependency".toList)]
    exact addedRead
  have inputRead := input_expression_refines_nullable_identity (L := L) (D := D) addr layout H array inputCapacity
    inputs environment index inside arrayRead indexRead resource
  rw [loaded] at inputRead
  have guardRead := invalid_expression_refines_null_or_self (L := L) (D := D) (reader := reader)
    addr layout H readerIn (some source) (by intro identity same; cases same; exact sourceIn)
    loadedEnv keptReader loadedSource
    (DynArray (some array) inputCapacity (inputValues addr inputs) ∗ resource)
  simp only [Option.some_ne_none, false_or, Option.some.injEq, decide_eq_false different] at guardRead
  have oldReads := extended_existing_operands (L := L) addr layout H readerIn sourceIn closed
    array inputCapacity inputs pending capacity values loadedEnv keptReader loadedSource F
  have oldExtent : (H.forward reader).count.toNat = (H.forward reader).active.length := by
    simp [PostIndex.Array32.active, List.length_take, Nat.min_eq_left within]
  have oldRead := counted_scan_with_sufficient_fuel oldReads oldExtent false innerFuel oldEnough
  simp only [Bool.false_eq_true, false_or] at oldRead
  have pendingReads := extended_pending_operands (L := L) addr layout H reader source sourceIn
    array inputCapacity inputs pending capacity values added pendingClosed loadedEnv
    keptPending keptAdded loadedSource F
  have nextRead := counted_scan_with_sufficient_fuel pendingReads extent
    (decide (source ∈ (H.forward reader).active)) innerFuel pendingEnough
  simp only [decide_eq_true_eq] at nextRead
  let seen := decide (source ∈ (H.forward reader).active ∨ source ∈ values)
  let scanEnv := Function.update loadedEnv IdentityScan.flag (some (.bool seen))
  have appendRead := append_branch_refines_private_state (L := L) (D := D) addr layout H array inputCapacity
    inputs pending capacity values source added scanEnv innerFuel 5 seen
    (by dsimp only [scanEnv]; rw [Function.update_of_ne (by decide : "pending".toList ≠ IdentityScan.flag)]; exact keptPending)
    (by dsimp only [scanEnv]; rw [Function.update_of_ne (by decide : "added".toList ≠ IdentityScan.flag)]; exact keptAdded)
    (by dsimp only [scanEnv]; rw [Function.update_of_ne (by decide : "dependency".toList ≠ IdentityScan.flag)]; exact loadedSource)
    (Function.update_self _ _ _) extent (by intro notSeen; exact roomWhenNew (by simpa [seen] using notSeen)) F
  have composed := valid_body_from_current_operands (fields layout) environment innerFuel (addr source)
    (decide (source ∈ (H.forward reader).active)) seen (if seen then added else added + 1)
    inputRead guardRead oldRead nextRead appendRead
  simpa only [seen, decide_eq_true_eq, OrderedDependencyBatch.collectMissing,
    List.append_nil, PendingState, resource] using composed

theorem invalid_body_refines_physical_input (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {reader : Id} (readerIn : reader ∈ D)
    (array : Ptr) (inputCapacity : Nat) (inputs : List (Option Id)) (index : UInt32)
    (inside : index.toNat < inputs.length) (value : Option Id)
    (loaded : inputs[index.toNat] = value) (invalid : value = none ∨ value = some reader)
    (pending : Ptr) (capacity : Nat) (values : List Id)
    (environment : ReadExpressions.Environment) (innerFuel : Nat) (before : Bool)
    (readerRead : environment "importer".toList = some (.ptr (some (addr reader))))
    (arrayRead : environment "dependencies".toList = some (.ptr (some array)))
    (indexRead : environment "i".toList = some (.u32 index))
    (okRead : environment "ok".toList = some (.bool before)) (F : Heap L → Prop) :
    CTriple (PendingState addr layout D H array inputCapacity inputs pending capacity values F)
      (StatementBlock.execute PostIndexWrites.assign (fields layout) innerFuel 12
        environment iterationSyntax)
      (fun result σ => result = .finished (.broken
        (Function.update environment "ok".toList (some (.bool false)))) ∧
          PendingState addr layout D H array inputCapacity inputs pending capacity values F σ) := by
  let resource := DynArray (some pending) capacity (values.map (spacePtr ∘ addr)) ∗ F
  have inputRead := input_expression_refines_nullable_identity (L := L) (D := D) addr layout H
    array inputCapacity inputs environment index inside arrayRead indexRead resource
  rw [loaded] at inputRead
  have represented : ∀ identity, value = some identity → identity ∈ D := by
    intro identity same
    rcases invalid with null | self
    · simp [null] at same
    · have equalReader : identity = reader := Option.some.inj (same.symm.trans self)
      simpa [equalReader] using readerIn
  have guardRead := invalid_expression_refines_null_or_self (L := L) (D := D) (reader := reader)
    addr layout H readerIn value represented
    (Function.update environment "dependency".toList (some (.ptr (value.map addr))))
    (by rw [Function.update_of_ne (by decide : "importer".toList ≠ "dependency".toList)];
        exact readerRead) (Function.update_self _ _ _)
    (DynArray (some array) inputCapacity (inputValues addr inputs) ∗ resource)
  simp only [decide_eq_true invalid] at guardRead
  exact invalid_body_from_current_operands (fields layout) environment innerFuel (value.map addr)
    before okRead inputRead guardRead

end PhysicalBody

namespace Controls

def emptyLayout : ReadExpressions.Layout := fun _ => none
def seenEnvironment : ReadExpressions.Environment := fun name =>
  if name = IdentityScan.flag then some (.bool true) else none

theorem already_seen_append_needs_no_destination_or_room (innerFuel fuel : Nat) :
    StatementBlock.execute PostIndexWrites.assign emptyLayout innerFuel (fuel + 2)
      seenEnvironment [appendStatement] = pure (.finished (.next seenEnvironment)) := by
  rw [append_block_selects_actual_store emptyLayout seenEnvironment innerFuel fuel true (by rfl)]
  rfl

theorem collection_body_fuel_exhaustion_is_not_false_return
    (environment : ReadExpressions.Environment) (innerFuel : Nat) :
    StatementBlock.execute PostIndexWrites.assign emptyLayout innerFuel 0 environment iterationSyntax =
      pure .exhausted := rfl

end Controls

end Mettapedia.Machines.CMemory.DependencyCollectionStep
