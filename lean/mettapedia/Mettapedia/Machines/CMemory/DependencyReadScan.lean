import Mettapedia.Machines.CMemory.ReadLoops
import Mettapedia.Machines.CMemory.DependencyExpressionReads

/-!
# The retained existing-dependency scan on block memory

Local read contracts connect physical loop execution to independent list
membership. The concrete client derives these contracts from the represented
store's typed cells and module-address validity. It executes the loop node
extracted from the complete supplied C source, including its counter scope.

The scan is over initialized active identities, not spare array capacity.
Fuel bounds exact UInt32 progression, and successful reads retain the whole
store and its frame. This is a sequential read fragment, not the surrounding
allocation, collection, cleanup or concurrent observation certificate.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Machines.CMemory.DependencyReadScan

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open CMemory.ReadExpressions CMemory.DependencyExpressionReads
open IdentityScan (counter flag condition step body scanStatement)
open CellPermission

universe u

theorem locals_as_updates (base : ReadExpressions.Environment) (index : UInt32) (seen : Bool) :
    locals base index seen = Function.update
      (Function.update base flag (some (.bool seen))) counter (some (.u32 index)) := by
  funext name
  by_cases isCounter : name = counter
  · subst name
    simp [locals]
  · by_cases isFlag : name = flag
    · subst name
      simp [locals, counter, flag]
    · simp [locals, isCounter, isFlag]

theorem locals_update_flag (base : ReadExpressions.Environment) (index : UInt32)
    (seen value : Bool) :
    Function.update (locals base index seen) flag (some (.bool value)) =
      locals base index value := by
  funext name
  by_cases isCounter : name = counter
  · subst name
    simp [locals, counter, flag]
  · by_cases isFlag : name = flag
    · subst name
      simp [locals, counter, flag]
    · simp [locals, isCounter, isFlag]

theorem locals_update_counter (base : ReadExpressions.Environment) (index value : UInt32)
    (seen : Bool) :
    Function.update (locals base index seen) counter (some (.u32 value)) =
      locals base value seen := by
  funext name
  by_cases isCounter : name = counter
  · subst name
    simp [locals]
  · simp [locals, isCounter]

theorem increment_is_actual_unsigned_step (base : ReadExpressions.Environment)
    (index : UInt32) (seen : Bool) :
    ReadLoops.increment (locals base index seen) step =
      pure (locals base (index + 1) seen) := by
  change Prog.ret (Function.update (locals base index seen) counter
    (some (.u32 (index + 1)))) = _
  exact congrArg Prog.ret (locals_update_counter base index (index + 1) seen)

section GenericScan

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]
variable {Id : Type} [DecidableEq Id]

/-- These are current single-expression readings and retained resources, not
an assumption of scan success, loop safety, or membership correctness. -/
structure Operands (P : Heap L → Prop) (layout : ReadExpressions.Layout)
    (base : ReadExpressions.Environment) (array limit needle : CExpr)
    (values : List Id) (bound : UInt32) (target : Id) : Prop where
  conditionRead : ∀ index seen,
    CTriple P (ReadExpressions.expression layout (locals base index seen) (condition limit))
      (fun result σ => result = .bool (decide (index < bound) && !seen) ∧ P σ)
  comparisonRead : ∀ (index : UInt32) seen (inside : index.toNat < values.length),
    CTriple P (ReadExpressions.expression layout (locals base index seen)
      (.binary .eq (.index array (.identifier counter)) needle))
      (fun result σ => result = .bool (decide (values[index.toNat] = target)) ∧ P σ)

theorem body_refines_read {P : Heap L → Prop} {layout : ReadExpressions.Layout}
    {base : ReadExpressions.Environment} {array limit needle : CExpr}
    {values : List Id} {bound : UInt32} {target : Id}
    (operands : Operands P layout base array limit needle values bound target)
    (index : UInt32) (seen : Bool) (inside : index.toNat < values.length) :
    CTriple P (ReadLoops.statements layout (locals base index seen) (body array needle))
      (fun result σ => result = locals base index (decide (values[index.toNat] = target)) ∧ P σ) := by
  have flagRead : locals base index seen flag = some (.bool seen) := by
    simp [locals, flag, counter]
  simp only [body, ReadLoops.statements, flagRead,
    ReadExpressions.resolved, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  refine triple_bind _ (operands.comparisonRead index seen inside) fun value => ?_
  apply triple_pure
  intro same
  subst value
  simp only [ReadLoops.assignValue, ReadExpressions.truth, Prog.pure_eq,
    Prog.bind_eq, Prog.ret_bind]
  rw [locals_update_flag]
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩) (triple_ret _ _ _)

/-- Every actually executed indexed load lies in the initialized prefix.
The scan preserves ordered progress and never relies on an unbounded or
wrapped counter. -/
theorem run_refines_initialized {P : Heap L → Prop} {layout : ReadExpressions.Layout}
    {base : ReadExpressions.Environment} {array limit needle : CExpr} {bound : UInt32}
    {target : Id} (prior remaining : List Id)
    (operands : Operands P layout base array limit needle (prior ++ remaining) bound target)
    (index : UInt32) (seen : Bool) (fuel : Nat)
    (position : index.toNat = prior.length) (extent : bound.toNat = (prior ++ remaining).length)
    (enough : remaining.length ≤ fuel) :
    CTriple P (ReadLoops.run layout (condition limit) step (body array needle) fuel
      (locals base index seen)) (fun result σ => ∃ stopped,
        result = .finished (locals base stopped (decide (seen = true ∨ target ∈ remaining))) ∧
          P σ) := by
  induction remaining generalizing prior index seen fuel with
  | nil =>
    have halted : ¬ index < bound := by
      rw [UInt32.lt_iff_toNat_lt]
      simpa [position] using extent.le
    rw [ReadLoops.run.eq_def]
    refine triple_bind _ (operands.conditionRead index seen) fun result => ?_
    apply triple_pure
    intro same
    subst result
    simp only [decide_eq_false halted, Bool.false_and, ReadExpressions.truth,
      Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, Bool.false_eq_true, ↓reduceIte]
    exact triple_pre _ (fun _ held => ⟨index, by cases seen <;> simp, held⟩)
      (triple_ret _ _ _)
  | cons entry rest ih =>
    cases seen with
    | true =>
      rw [ReadLoops.run.eq_def]
      refine triple_bind _ (operands.conditionRead index true) fun result => ?_
      apply triple_pure
      intro same
      subst result
      simp only [Bool.not_true, Bool.and_false, ReadExpressions.truth,
        Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, Bool.false_eq_true, ↓reduceIte]
      exact triple_pre _ (fun _ held => ⟨index, by simp, held⟩) (triple_ret _ _ _)
    | false =>
      have live : index < bound := by
        rw [UInt32.lt_iff_toNat_lt]
        simp only [List.length_append, List.length_cons] at extent
        omega
      have exactIncrement : (index + 1).toNat = index.toNat + 1 := by
        rw [UInt32.toNat_add]
        apply Nat.mod_eq_of_lt
        have upper := bound.toNat_lt
        have before := UInt32.lt_iff_toNat_lt.mp live
        change index.toNat + 1 < 2 ^ 32
        omega
      have inside : index.toNat < (prior ++ entry :: rest).length := by
        simp only [position, List.length_append, List.length_cons]
        omega
      have loaded : (prior ++ entry :: rest)[index.toNat]'inside = entry := by
        simp only [position]
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
        have nextOperands : Operands P layout base array limit needle
            ((prior ++ [entry]) ++ rest) bound target := by
          simpa only [List.append_assoc, List.singleton_append] using operands
        have nextPosition : (index + 1).toNat = (prior ++ [entry]).length := by
          simp [exactIncrement, position]
        have nextExtent : bound.toNat = ((prior ++ [entry]) ++ rest).length := by
          simpa [List.append_assoc] using extent
        have following := ih (prior ++ [entry]) nextOperands (index + 1)
          (decide (entry = target)) fuel nextPosition nextExtent (by simpa using enough)
        rw [ReadLoops.run.eq_def]
        refine triple_bind _ (operands.conditionRead index false) fun result => ?_
        apply triple_pure
        intro same
        subst result
        simp only [decide_eq_true live, Bool.not_false, Bool.true_and, ReadExpressions.truth,
          Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, ↓reduceIte]
        have bodySpec := body_refines_read operands index false inside
        rw [loaded] at bodySpec
        refine triple_bind _ bodySpec fun updated => ?_
        apply triple_pure
        intro same
        subst updated
        rw [increment_is_actual_unsigned_step]
        simp only [Prog.pure_eq, Prog.ret_bind]
        simpa [eq_comm] using following

theorem counted_scan_refines_outer_scope {P : Heap L → Prop} {layout : ReadExpressions.Layout}
    {base : ReadExpressions.Environment} {array limit needle : CExpr} {initialized : List Id}
    {bound : UInt32} {target : Id}
    (operands : Operands P layout base array limit needle initialized bound target)
    (extent : bound.toNat = initialized.length) (seen : Bool) :
    CTriple P (ReadLoops.counted layout initialized.length
      (Function.update base flag (some (.bool seen))) (scanStatement array limit needle))
      (fun result σ => result = .finished (Function.update base flag
        (some (.bool (decide (seen = true ∨ target ∈ initialized))))) ∧ P σ) := by
  rw [scanStatement, ReadLoops.declaration_uses_actual_initializer_and_loop]
  rw [← locals_as_updates]
  have complete := run_refines_initialized (L := L) [] initialized
    (by simpa using operands) 0 seen initialized.length rfl extent (Nat.le_refl _)
  refine triple_bind _ complete fun result => ?_
  apply triple_exists
  intro stopped
  apply triple_pure
  intro same
  subst result
  simp only [ReadLoops.restore]
  rw [Function.update_of_ne (by decide : counter ≠ flag), locals_as_updates,
    Function.update_idem, Function.update_comm (by decide : flag ≠ counter),
    Function.update_eq_self]
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩) (triple_ret _ _ _)

/-- Sequential scans retain an earlier positive observation; the second
scan cannot reset it. Membership is over the two initialized lists, with the
same scoped locals and retained physical resources throughout. -/
theorem consecutive_scans_refine_union {P : Heap L → Prop} {layout : ReadExpressions.Layout}
    {base : ReadExpressions.Environment} {oldArray oldLimit pendingArray pendingLimit needle : CExpr}
    {existing pending : List Id} {count added : UInt32} {target : Id}
    (oldReads : Operands P layout base oldArray oldLimit needle existing count target)
    (pendingReads : Operands P layout base pendingArray pendingLimit needle pending added target)
    (oldExtent : count.toNat = existing.length) (pendingExtent : added.toNat = pending.length) :
    CTriple P
      (ReadLoops.counted layout existing.length (Function.update base flag (some (.bool false)))
        (scanStatement oldArray oldLimit needle) >>= fun result => match result with
          | .finished environment => ReadLoops.counted layout pending.length environment
              (scanStatement pendingArray pendingLimit needle)
          | .exhausted => pure .exhausted)
      (fun result σ => result = .finished (Function.update base flag
        (some (.bool (decide (target ∈ existing ∨ target ∈ pending))))) ∧ P σ) := by
  have first := counted_scan_refines_outer_scope oldReads oldExtent false
  simp only [Bool.false_eq_true, false_or] at first
  refine triple_bind _ first fun result => ?_
  apply triple_pure
  intro same
  subst result
  simpa using counted_scan_refines_outer_scope pendingReads pendingExtent
    (decide (target ∈ existing))

end GenericScan

section StoreClient

open CMemory.Lift OrderedDependencyCPreparationScan

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]
variable {Id : Type} [DecidableEq Id] (addr : Id → Ptr)

theorem store_operands (layout : SpaceLayout) {D : List Id} (H : SplitHeap Id)
    {reader source : Id} (readerIn : reader ∈ D) (sourceIn : source ∈ D)
    (closed : ∀ identity ∈ (H.forward reader).active, identity ∈ D) (F : Heap L → Prop) :
    Operands (StoreState addr layout D H F) (fields layout) (bindings (addr reader) (addr source))
      oldArray oldLimit needle (H.forward reader).active (H.forward reader).count source := by
  exact ⟨fun index seen => old_condition_refines_current_count addr layout H readerIn source
    index seen F, fun index seen inside => old_comparison_refines_current_identity addr
    layout H readerIn sourceIn index inside closed seen F⟩

theorem quoted_scan_refines_current_membership (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {reader source : Id} (readerIn : reader ∈ D) (sourceIn : source ∈ D)
    (closed : ∀ identity ∈ (H.forward reader).active, identity ∈ D)
    (within : (H.forward reader).count.toNat ≤ (H.forward reader).slots.length)
    (seen : Bool) (F : Heap L → Prop) :
    CTriple (StoreState addr layout D H F)
      (ReadLoops.executeNode (fields layout) (H.forward reader).active.length
        (Function.update (bindings (addr reader) (addr source)) flag (some (.bool seen)))
        (quotedScan 10 3))
      (fun result σ => result = .finished
        (Function.update (bindings (addr reader) (addr source)) flag
          (some (.bool (decide (seen = true ∨ source ∈ (H.forward reader).active))))) ∧
        StoreState addr layout D H F σ) := by
  rw [quoted_existing_node_is_actual, existing_node_is_retained]
  exact counted_scan_refines_outer_scope (store_operands addr layout H readerIn sourceIn closed F)
    (by simp [PostIndex.Array32.active, List.length_take, Nat.min_eq_left within]) seen

theorem quoted_validation_scan_refines_current_membership (layout : SpaceLayout)
    {D : List Id} (H : SplitHeap Id) {reader source : Id} (readerIn : reader ∈ D)
    (sourceIn : source ∈ D) (closed : ∀ identity ∈ (H.forward reader).active, identity ∈ D)
    (within : (H.forward reader).count.toNat ≤ (H.forward reader).slots.length)
    (seen : Bool) (F : Heap L → Prop) :
    CTriple (StoreState addr layout D H F)
      (ReadLoops.executeNode (fields layout) (H.forward reader).active.length
        (Function.update (bindings (addr reader) (addr source)) flag (some (.bool seen)))
        (quotedScan 3 3))
      (fun result σ => result = .finished
        (Function.update (bindings (addr reader) (addr source)) flag
          (some (.bool (decide (seen = true ∨ source ∈ (H.forward reader).active))))) ∧
        StoreState addr layout D H F σ) := by
  rw [quoted_validation_node_is_actual, validation_uses_same_retained_scan,
    ← quoted_existing_node_is_actual]
  exact quoted_scan_refines_current_membership addr layout H readerIn sourceIn closed within seen F

def pendingBindings (reader source pending : Ptr) (added : UInt32) :
    ReadExpressions.Environment :=
  Function.update (Function.update (bindings reader source) "pending".toList
    (some (.ptr (some pending)))) "added".toList (some (.u32 added))

theorem pending_condition_reads_actual_added (layout : SpaceLayout)
    (reader source pending : Ptr) (added index : UInt32) (seen : Bool) :
    ReadExpressions.expression (fields layout)
      (locals (pendingBindings reader source pending added) index seen) (condition pendingLimit) =
      pure (.bool (decide (index < added) && !seen)) := by
  simp [ReadExpressions.expression, ReadExpressions.expressionWith_equation, ReadExpressions.resolved, ReadExpressions.binary,
    ReadExpressions.truth, ReadExpressions.word, condition, pendingLimit,
    pendingBindings, locals, counter, flag]
  split <;> simp_all

theorem pending_comparison_follows_actual_pointer (layout : SpaceLayout)
    (reader source pending : Ptr) (added index : UInt32) (seen : Bool) :
    ReadExpressions.expression (fields layout)
      (locals (pendingBindings reader source pending added) index seen)
      (.binary .eq (.index pendingArray (.identifier counter)) needle) =
      (CProg.loadPtr (pending + index.toNat) >>= fun item =>
        CProg.ptrEq item (some source) >>= fun same => pure (.bool same)) := by
  simp [ReadExpressions.expression, ReadExpressions.expressionWith_equation, ReadExpressions.resolved, ReadExpressions.binary,
    ReadExpressions.equal, ReadExpressions.pointer, ReadExpressions.word,
    ReadExpressions.indexed, pendingArray, needle, pendingBindings, DependencyExpressionReads.bindings,
    locals, counter, flag, Prog.bind_assoc]

/-- After an earlier scan found the identity, this actual pending scan does
not dereference its array. It still executes the supplied local bound test. -/
theorem seen_pending_scan_is_read_free (layout : SpaceLayout)
    (reader source pending : Ptr) (added : UInt32) (fuel : Nat) :
    ReadLoops.executeNode (fields layout) fuel
      (Function.update (pendingBindings reader source pending added) flag (some (.bool true)))
      (quotedScan 10 4) =
      pure (.finished (Function.update (pendingBindings reader source pending added) flag
        (some (.bool true)))) := by
  rw [quoted_pending_node_is_actual, pending_node_is_retained]
  change ReadLoops.counted (fields layout) fuel
    (Function.update (pendingBindings reader source pending added) flag (some (.bool true)))
      (scanStatement pendingArray pendingLimit needle) = _
  rw [scanStatement, ReadLoops.declaration_uses_actual_initializer_and_loop, ← locals_as_updates]
  rw [ReadLoops.run.eq_def, pending_condition_reads_actual_added]
  simp only [Bool.not_true, Bool.and_false, ReadExpressions.truth, Prog.pure_eq,
    Prog.bind_eq, Prog.ret_bind, Bool.false_eq_true, ↓reduceIte, ReadLoops.restore]
  rw [Function.update_of_ne (by decide : counter ≠ flag), locals_as_updates,
    Function.update_idem, Function.update_comm (by decide : flag ≠ counter),
    Function.update_eq_self]

/-- The temporary pending array is a real initialized allocation, retained
beside the represented module store. Its uninitialized capacity is not read. -/
theorem pending_operands (layout : SpaceLayout) {D : List Id} (H : SplitHeap Id)
    (reader source : Id) (sourceIn : source ∈ D) (pending : Ptr) (capacity : Nat)
    (values : List Id) (added : UInt32)
    (closed : ∀ identity ∈ values, identity ∈ D) (F : Heap L → Prop) :
    Operands (StoreState addr layout D H
      (DynArray (some pending) capacity (values.map (spacePtr ∘ addr)) ∗ F))
      (fields layout) (pendingBindings (addr reader) (addr source) pending added)
      pendingArray pendingLimit needle values added source := by
  constructor
  · intro index seen
    rw [pending_condition_reads_actual_added]
    exact triple_pre _ (fun _ held => ⟨rfl, held⟩) (triple_ret _ _ _)
  · intro index seen inside
    rw [pending_comparison_follows_actual_pointer]
    have loadSpec : CTriple (StoreState addr layout D H
        (DynArray (some pending) capacity (values.map (spacePtr ∘ addr)) ∗ F))
        (CProg.loadPtr (pending + index.toNat))
        (fun item σ => item = some (addr values[index.toNat]) ∧
          StoreState addr layout D H
            (DynArray (some pending) capacity (values.map (spacePtr ∘ addr)) ∗ F) σ) := by
      apply loadPtr_rule
      intro σ holds
      have array : (DynArray (some pending) capacity (values.map (spacePtr ∘ addr)) ∗
          (StoreRep addr layout D H ∗ F)) σ := by
        simpa only [sepConj_assoc, sepConj_left_comm] using holds.2
      have mappedInside : index.toNat < (values.map (spacePtr ∘ addr)).length := by
        simpa using inside
      have item : (values.map (spacePtr ∘ addr))[index.toNat]'mappedInside =
          spacePtr (addr values[index.toNat]) := by rw [List.getElem_map]; rfl
      have current := CMemory.DependencyReads.read_dynArray (i := index.toNat) mappedInside array
      rw [item] at current
      exact current
    refine triple_bind _ loadSpec fun item => ?_
    apply triple_pure
    intro same
    subst item
    have member : values[index.toNat] ∈ D := closed _ (List.getElem_mem inside)
    refine triple_bind _ (module_pointer_comparison_refines_identity addr layout H
      member sourceIn (DynArray (some pending) capacity (values.map (spacePtr ∘ addr)) ∗ F))
        fun compared => ?_
    apply triple_pure
    intro same
    subst compared
    exact triple_pre _ (fun _ holds => ⟨rfl, holds⟩) (triple_ret _ _ _)

theorem quoted_pending_scan_refines_current_membership (layout : SpaceLayout)
    {D : List Id} (H : SplitHeap Id) (reader source : Id) (sourceIn : source ∈ D)
    (pending : Ptr) (capacity : Nat) (values : List Id) (added : UInt32)
    (extent : added.toNat = values.length) (closed : ∀ identity ∈ values, identity ∈ D)
    (seen : Bool) (F : Heap L → Prop) :
    CTriple (StoreState addr layout D H
      (DynArray (some pending) capacity (values.map (spacePtr ∘ addr)) ∗ F))
      (ReadLoops.executeNode (fields layout) values.length
        (Function.update (pendingBindings (addr reader) (addr source) pending added)
          flag (some (.bool seen))) (quotedScan 10 4))
      (fun result σ => result = .finished
        (Function.update (pendingBindings (addr reader) (addr source) pending added) flag
          (some (.bool (decide (seen = true ∨ source ∈ values))))) ∧
        StoreState addr layout D H
          (DynArray (some pending) capacity (values.map (spacePtr ∘ addr)) ∗ F) σ) := by
  rw [quoted_pending_node_is_actual, pending_node_is_retained]
  exact counted_scan_refines_outer_scope
    (pending_operands addr layout H reader source sourceIn pending capacity values added closed F)
    extent seen

end StoreClient

namespace Controls

open CMemory.Lift OrderedDependencyCPreparationScan

def layout : SpaceLayout := ⟨0, 1, 2, 3, 4, 5⟩
def base : ReadExpressions.Environment := fun name =>
  if name = flag then some (.bool false) else none
def unitBound : CExpr := .unsignedInteger 1
def removedBody : CStatement :=
  .forLoop ⟨"uint32_t".toList, 0⟩ counter (.unsignedInteger 0)
    (condition unitBound) IdentityScan.step []
def constantBody : CStatement :=
  .forLoop ⟨"uint32_t".toList, 0⟩ counter (.unsignedInteger 0)
    (condition unitBound) IdentityScan.step [.assign (.identifier flag) (.bool true)]

theorem actual_assignment_sets_observed_flag :
    ReadLoops.counted (fields layout) 1 base constantBody =
      pure (.finished (Function.update base flag (some (.bool true)))) := by
  simp [ReadLoops.counted, constantBody, ReadLoops.run, ReadLoops.statements,
    ReadLoops.assignValue, ReadLoops.increment, ReadLoops.restore,
    ReadExpressions.expression, ReadExpressions.expressionWith_equation, ReadExpressions.resolved, ReadExpressions.truth,
    ReadExpressions.binary, ReadExpressions.word, condition, unitBound,
    IdentityScan.step, base, counter, flag, Function.update_comm, Function.update_idem]
  have absent : base ['j'] = none := by decide
  have reset : Function.update base ['j'] none = base := by
    rw [← absent]
    exact Function.update_eq_self _ _
  rw [reset]

theorem removed_assignment_does_not_set_flag :
    ReadLoops.counted (fields layout) 1 base removedBody = pure (.finished base) := by
  simp [ReadLoops.counted, removedBody, ReadLoops.run, ReadLoops.statements,
    ReadLoops.increment, ReadLoops.restore, ReadExpressions.expression, ReadExpressions.expressionWith_equation,
    ReadExpressions.resolved, ReadExpressions.truth, ReadExpressions.binary,
    ReadExpressions.word, condition, unitBound, IdentityScan.step, base, counter, flag]

theorem altered_true_condition_exhausts_instead_of_inventing_membership :
    ReadLoops.counted (fields layout) 1 base
      (.forLoop ⟨"uint32_t".toList, 0⟩ counter (.unsignedInteger 0)
        (.bool true) IdentityScan.step []) = pure .exhausted := rfl

section UnsafeReads

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

theorem indeterminate_index_is_not_membership_false (array : Ptr) (index : UInt32)
    (σ : Heap L) (indeterminate :
      read ((σ (array + index.toNat).block).2 (array + index.toNat).offset) = some none) :
    ¬ (ReadExpressions.indexed (.ptr (some array)) (.u32 index)).Safe act σ := by
  rw [index_uses_actual_pointer_and_word]
  intro safe
  have typedSafe := (Prog.safe_bind _ _ _ _).mp safe |>.1
  have loadSafe := (Prog.safe_bind _ _ _ _).mp typedSafe |>.1
  obtain ⟨value, current⟩ := loadSafe.1
  rw [indeterminate] at current
  cases current

theorem seen_flag_does_not_skip_missing_bound (reader source : Ptr) (index : UInt32)
    (σ : Heap L)
    (missing : read ((σ (reader + layout.depCount).block).2
      (reader + layout.depCount).offset) = none) :
    ¬ (ReadExpressions.expression (fields layout)
      (locals (bindings reader source) index true) (condition oldLimit)).Safe act σ := by
  rw [old_condition_executes_bound_before_flag]
  intro safe
  have typedSafe := (Prog.safe_bind _ _ _ _).mp safe |>.1
  have loadSafe := (Prog.safe_bind _ _ _ _).mp typedSafe |>.1
  obtain ⟨value, current⟩ := loadSafe.1
  rw [missing] at current
  cases current

end UnsafeReads

abbrev Permission := Excl (Option CVal)

def deadHeap (pointer : Ptr) : Heap Permission :=
  CMemory.Controls.headerOnly pointer.block ⟨pointer.offset + 1, false⟩

theorem stored_dead_pointer_is_not_comparable (pointer : Ptr) :
    ¬ (ReadExpressions.equal (.ptr (some pointer)) (.ptr (some pointer))).Safe act
      (deadHeap pointer) := by
  rintro ⟨⟨(⟨extent, header, _⟩ | held), _⟩, _⟩
  · simp [deadHeap, CMemory.Controls.headerOnly] at header
  · exact held (by simp [deadHeap, CMemory.Controls.headerOnly])

theorem pointer_spelling_without_owned_lifetime_is_not_truth (pointer : Ptr) :
    ¬ (ReadExpressions.truth (.ptr (some pointer))).Safe act (0 : Heap Permission) := by
  rintro ⟨⟨(⟨extent, header, _⟩ | held), _⟩, _⟩
  · change Excl.empty = Excl.own _ at header
    cases header
  · exact held rfl

/-- A live pointer can be comparable without supplying a current scalar
observation. Storage lifetime is not a load or cache certificate. -/
theorem live_header_without_cell_does_not_supply_count :
    Valid (CMemory.Controls.headerOnly (V := CVal) 0 ⟨1, true⟩) ⟨0, 0⟩ ∧
    ¬ (CProg.loadU32 ⟨0, 0⟩).Safe act
      (CMemory.Controls.headerOnly (V := CVal) 0 ⟨1, true⟩) := by
  refine ⟨Or.inl ⟨1, by simp [CMemory.Controls.headerOnly], by decide⟩, ?_⟩
  intro safe
  have loadSafe := (Prog.safe_bind _ _ _ _).mp safe |>.1
  obtain ⟨value, current⟩ := loadSafe.1
  simp [CMemory.Controls.headerOnly, read_zero] at current

end Controls

end Mettapedia.Machines.CMemory.DependencyReadScan
