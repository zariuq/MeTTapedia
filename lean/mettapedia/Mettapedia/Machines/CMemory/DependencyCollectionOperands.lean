import Mettapedia.Machines.CMemory.PostIndexWrites
import Mettapedia.Machines.CMemory.DependencyValidationOperands

/-!
# Physical operands and private pending writes for dependency collection

Input storage, represented modules and the private pending array are separate
resources. Both scans keep the enclosing local environment. A pending append
updates only its initialized private prefix; the same represented module store
and input allocation remain framed throughout the physical write.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Machines.CMemory.DependencyCollectionOperands

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open ReadExpressions DependencyExpressionReads DependencyReadScan
open DependencyValidationOperands Lift
open OrderedDependencyCPreparationScan
open CellPermission

universe u

theorem pending_condition_in_extended_environment (layout : SpaceLayout)
    (environment : ReadExpressions.Environment) (added index : UInt32) (seen : Bool)
    (addedRead : environment "added".toList = some (.u32 added)) :
    expression (fields layout) (locals environment index seen) (IdentityScan.condition pendingLimit) =
      pure (.bool (decide (index < added) && !seen)) := by
  change environment ['a', 'd', 'd', 'e', 'd'] = _ at addedRead
  simp [IdentityScan.condition, pendingLimit, expression, expressionWith_equation, locals,
    IdentityScan.counter, IdentityScan.flag, addedRead, resolved, binary, word, truth]
  split <;> simp_all

theorem pending_comparison_in_extended_environment (layout : SpaceLayout)
    (environment : ReadExpressions.Environment) (pending source : Ptr)
    (index : UInt32) (seen : Bool)
    (pendingRead : environment "pending".toList = some (.ptr (some pending)))
    (sourceRead : environment "dependency".toList = some (.ptr (some source))) :
    expression (fields layout) (locals environment index seen)
      (.binary .eq (.index pendingArray (.identifier IdentityScan.counter)) needle) =
      (CProg.loadPtr (pending + index.toNat) >>= fun item =>
        CProg.ptrEq item (some source) >>= fun same => pure (.bool same)) := by
  change environment ['p', 'e', 'n', 'd', 'i', 'n', 'g'] = _ at pendingRead
  change environment ['d', 'e', 'p', 'e', 'n', 'd', 'e', 'n', 'c', 'y'] = _ at sourceRead
  simp [pendingArray, needle, expression, expressionWith_equation, locals, IdentityScan.counter, IdentityScan.flag,
    pendingRead, sourceRead, resolved, indexed, pointer, word, binary, equal, Prog.bind_assoc]

section PhysicalState

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]
variable {Id : Type} [DecidableEq Id] (addr : Id → Ptr)

def PendingState (layout : SpaceLayout) (D : List Id) (H : SplitHeap Id)
    (array : Ptr) (inputCapacity : Nat) (inputs : List (Option Id))
    (pending : Ptr) (capacity : Nat) (values : List Id) (F : Heap L → Prop) : Heap L → Prop :=
  InputState addr layout D H array inputCapacity inputs
    (DynArray (some pending) capacity (values.map (spacePtr ∘ addr)) ∗ F)

omit [DecidableEq Id] in
theorem pending_state_as_frame (layout : SpaceLayout) (D : List Id) (H : SplitHeap Id)
    (array : Ptr) (inputCapacity : Nat) (inputs : List (Option Id))
    (pending : Ptr) (capacity : Nat) (values : List Id) (F : Heap L → Prop) :
    PendingState addr layout D H array inputCapacity inputs pending capacity values F =
      StoreState addr layout D H (DynArray (some pending) capacity (values.map (spacePtr ∘ addr)) ∗
        (DynArray (some array) inputCapacity (inputValues addr inputs) ∗ F)) := by
  funext σ
  simp only [PendingState, InputState, StoreState, sepConj_left_comm]

theorem extended_pending_operands (layout : SpaceLayout) {D : List Id} (H : SplitHeap Id)
    (reader source : Id) (sourceIn : source ∈ D) (array : Ptr) (inputCapacity : Nat)
    (inputs : List (Option Id)) (pending : Ptr) (capacity : Nat) (values : List Id)
    (added : UInt32) (closed : ∀ identity ∈ values, identity ∈ D)
    (environment : ReadExpressions.Environment)
    (pendingRead : environment "pending".toList = some (.ptr (some pending)))
    (addedRead : environment "added".toList = some (.u32 added))
    (sourceRead : environment "dependency".toList = some (.ptr (some (addr source))))
    (F : Heap L → Prop) :
    Operands (PendingState addr layout D H array inputCapacity inputs pending capacity values F)
      (fields layout) environment pendingArray pendingLimit needle values added source := by
  constructor
  · intro index seen
    rw [pending_condition_in_extended_environment layout environment added index seen addedRead]
    exact triple_pre _ (fun _ holds => ⟨rfl, holds⟩) (triple_ret _ _ _)
  · intro index seen inside
    rw [pending_comparison_in_extended_environment layout environment pending (addr source)
      index seen pendingRead sourceRead]
    have canonical := (pending_operands addr layout H reader source sourceIn pending capacity
      values added closed (DynArray (some array) inputCapacity (inputValues addr inputs) ∗ F)).comparisonRead
        index seen inside
    rw [pending_comparison_follows_actual_pointer] at canonical
    simpa only [pending_state_as_frame] using canonical

theorem extended_existing_operands (layout : SpaceLayout) {D : List Id} (H : SplitHeap Id)
    {reader source : Id} (readerIn : reader ∈ D) (sourceIn : source ∈ D)
    (closed : ∀ identity ∈ (H.forward reader).active, identity ∈ D)
    (array : Ptr) (inputCapacity : Nat) (inputs : List (Option Id))
    (pending : Ptr) (capacity : Nat) (values : List Id)
    (environment : ReadExpressions.Environment)
    (readerRead : environment "importer".toList = some (.ptr (some (addr reader))))
    (sourceRead : environment "dependency".toList = some (.ptr (some (addr source))))
    (F : Heap L → Prop) :
    Operands (PendingState addr layout D H array inputCapacity inputs pending capacity values F)
      (fields layout) environment oldArray oldLimit needle
      (H.forward reader).active (H.forward reader).count source :=
  extended_scan_operands addr layout H readerIn sourceIn closed environment readerRead sourceRead
    (DynArray (some array) inputCapacity (inputValues addr inputs) ∗
      (DynArray (some pending) capacity (values.map (spacePtr ∘ addr)) ∗ F))

omit [DecidableEq Id] in
theorem append_changes_only_private_pending (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) (array : Ptr) (inputCapacity : Nat) (inputs : List (Option Id))
    (pending : Ptr) (capacity : Nat) (values : List Id) (source : Id) (added : UInt32)
    (environment : ReadExpressions.Environment)
    (pendingRead : environment "pending".toList = some (.ptr (some pending)))
    (addedRead : environment "added".toList = some (.u32 added))
    (sourceRead : environment "dependency".toList = some (.ptr (some (addr source))))
    (extent : added.toNat = values.length) (room : values.length < capacity)
    (F : Heap L → Prop) :
    CTriple (PendingState addr layout D H array inputCapacity inputs pending capacity values F)
      (PostIndexWrites.execute environment OrderedDependencyCPreparationAppend.appendSite.statement)
      (fun updated σ => updated = Function.update environment "added".toList
        (some (.u32 (added + 1))) ∧
          PendingState addr layout D H array inputCapacity inputs pending capacity (values ++ [source]) F σ) := by
  have mappedExtent : added.toNat = (values.map (spacePtr ∘ addr)).length := by simpa using extent
  have mappedRoom : (values.map (spacePtr ∘ addr)).length < capacity := by simpa using room
  have write := PostIndexWrites.physical_append_refines_initialized_prefix (L := L) environment
    OrderedDependencyCPreparationAppend.appendSite pending added (some (addr source)) capacity
    (values.map (spacePtr ∘ addr)) (by decide) (by decide) pendingRead addedRead sourceRead
    mappedExtent mappedRoom
  have framed := CMemory.frame write (StoreRep addr layout D H ∗
    (DynArray (some array) inputCapacity (inputValues addr inputs) ∗ F))
  have checked := PostIndexWrites.triple_preserves_wellFormed framed
  refine triple_post _ (triple_pre _ (fun σ holds => ?_) checked) ?_
  · refine ⟨holds.1, ?_⟩
    simpa only [PendingState, InputState, StoreState, sepConj_assoc, sepConj_comm,
      sepConj_left_comm] using holds.2
  · rintro updated σ ⟨wellFormed, x, y, separate, rfl, ⟨same, written⟩, other⟩
    refine ⟨same, wellFormed, ?_⟩
    have valuesAfter : values.map (spacePtr ∘ addr) ++ [.ptr (some (addr source))] =
        (values ++ [source]).map (spacePtr ∘ addr) := by simp [spacePtr]
    rw [valuesAfter] at written
    have whole : (DynArray (some pending) capacity ((values ++ [source]).map (spacePtr ∘ addr)) ∗
        (StoreRep addr layout D H ∗
          (DynArray (some array) inputCapacity (inputValues addr inputs) ∗ F))) (x + y) :=
      ⟨x, y, separate, rfl, written, other⟩
    simpa only [PendingState, InputState, StoreState, sepConj_assoc, sepConj_comm,
      sepConj_left_comm] using whole

end PhysicalState

section CountedScan

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]
variable {Id : Type} [DecidableEq Id]

theorem counted_scan_with_sufficient_fuel {P : Heap L → Prop} {layout : ReadExpressions.Layout}
    {base : ReadExpressions.Environment} {array limit needle : CExpr} {initialized : List Id}
    {bound : UInt32} {target : Id}
    (operands : Operands P layout base array limit needle initialized bound target)
    (extent : bound.toNat = initialized.length) (seen : Bool) (fuel : Nat)
    (enough : initialized.length ≤ fuel) :
    CTriple P (ReadLoops.counted layout fuel
      (Function.update base IdentityScan.flag (some (.bool seen)))
        (IdentityScan.scanStatement array limit needle))
      (fun result σ => result = .finished (Function.update base IdentityScan.flag
        (some (.bool (decide (seen = true ∨ target ∈ initialized))))) ∧ P σ) := by
  rw [IdentityScan.scanStatement, ReadLoops.declaration_uses_actual_initializer_and_loop,
    ← locals_as_updates]
  have complete := run_refines_initialized (L := L) [] initialized
    (by simpa using operands) 0 seen fuel rfl extent enough
  refine triple_bind _ complete fun result => ?_
  apply triple_exists
  intro stopped
  apply triple_pure
  intro same
  subst result
  simp only [ReadLoops.restore]
  rw [Function.update_of_ne (by decide : IdentityScan.counter ≠ IdentityScan.flag), locals_as_updates,
    Function.update_idem, Function.update_comm (by decide : IdentityScan.flag ≠ IdentityScan.counter),
    Function.update_eq_self]
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩) (triple_ret _ _ _)

end CountedScan

end Mettapedia.Machines.CMemory.DependencyCollectionOperands
