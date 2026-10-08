import Mettapedia.Machines.CMemory.DependencyReadScan
import Mettapedia.Machines.OrderedDependencyCPreparationValidation

/-!
# Physical operands of the first dependency-validation loop

The input is an owned pointer array, including nullable initialized elements.
The invalid-input expression executes the supplied short circuit and compares
actual live module pointers. Existing-link scans work in an arbitrary enclosing
environment, retaining its unrelated bindings and framed input storage.

These are sequential cell-memory contracts. Native byte layout, concurrent
currency and the remaining preparation statements are separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Machines.CMemory.DependencyValidationOperands

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open ReadExpressions DependencyExpressionReads DependencyReadScan
open Lift DependencyReads
open OrderedDependencyCPreparationScan (oldArray oldLimit needle)
open OrderedDependencyCPreparationCollection (inputExpression invalidCondition)
open CellPermission

universe u

theorem old_condition_in_extended_environment (layout : SpaceLayout)
    (environment : ReadExpressions.Environment) (reader source : Ptr)
    (index : UInt32) (seen : Bool)
    (importerRead : environment "importer".toList = some (.ptr (some reader))) :
    expression (fields layout) (locals environment index seen) (IdentityScan.condition oldLimit) =
      expression (fields layout) (locals (bindings reader source) index seen)
        (IdentityScan.condition oldLimit) := by
  change environment ['i', 'm', 'p', 'o', 'r', 't', 'e', 'r'] = _ at importerRead
  simp [IdentityScan.condition, expression, expressionWith_equation, oldLimit, locals, bindings,
    IdentityScan.counter, IdentityScan.flag, importerRead]

theorem old_comparison_in_extended_environment (layout : SpaceLayout)
    (environment : ReadExpressions.Environment) (reader source : Ptr)
    (index : UInt32) (seen : Bool)
    (importerRead : environment "importer".toList = some (.ptr (some reader)))
    (sourceRead : environment "dependency".toList = some (.ptr (some source))) :
    expression (fields layout) (locals environment index seen)
        (.binary .eq (.index oldArray (.identifier IdentityScan.counter)) needle) =
      expression (fields layout) (locals (bindings reader source) index seen)
        (.binary .eq (.index oldArray (.identifier IdentityScan.counter)) needle) := by
  change environment ['i', 'm', 'p', 'o', 'r', 't', 'e', 'r'] = _ at importerRead
  change environment ['d', 'e', 'p', 'e', 'n', 'd', 'e', 'n', 'c', 'y'] = _ at sourceRead
  simp [expression, expressionWith_equation, oldArray, needle, locals, bindings,
    IdentityScan.counter, IdentityScan.flag, importerRead, sourceRead]

theorem input_expression_is_physical_load (layout : ReadExpressions.Layout)
    (environment : ReadExpressions.Environment) (array : Ptr) (index : UInt32)
    (arrayRead : environment "dependencies".toList = some (.ptr (some array)))
    (indexRead : environment "i".toList = some (.u32 index)) :
    expression layout environment inputExpression =
      (CProg.loadPtr (array + index.toNat) >>= fun item => pure (.ptr item)) := by
  change environment ['d', 'e', 'p', 'e', 'n', 'd', 'e', 'n', 'c', 'i', 'e', 's'] = _ at arrayRead
  change environment ['i'] = _ at indexRead
  simp [inputExpression, expression, expressionWith_equation, arrayRead, indexRead, resolved, indexed, pointer, word]

theorem invalid_expression_retains_short_circuit (layout : ReadExpressions.Layout)
    (environment : ReadExpressions.Environment) (reader : Ptr) (source : Option Ptr)
    (importerRead : environment "importer".toList = some (.ptr (some reader)))
    (sourceRead : environment "dependency".toList = some (.ptr source)) :
    expression layout environment invalidCondition =
      (CProg.ptrEq source none >>= fun isNull =>
        if isNull then pure (.bool true) else
          CProg.ptrEq source (some reader) >>= fun self => pure (.bool self)) := by
  change environment ['i', 'm', 'p', 'o', 'r', 't', 'e', 'r'] = _ at importerRead
  change environment ['d', 'e', 'p', 'e', 'n', 'd', 'e', 'n', 'c', 'y'] = _ at sourceRead
  simp [invalidCondition, expression, expressionWith_equation, importerRead, sourceRead, resolved, truth, binary,
    equal, Prog.bind_assoc]

section Specifications

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]
variable {Id : Type} [DecidableEq Id] (addr : Id → Ptr)

def inputValues (inputs : List (Option Id)) : List CVal :=
  inputs.map (fun value => .ptr (value.map addr))

def InputState (layout : SpaceLayout) (D : List Id) (H : SplitHeap Id)
    (array : Ptr) (capacity : Nat) (inputs : List (Option Id)) (F : Heap L → Prop) :
    Heap L → Prop :=
  StoreState addr layout D H (DynArray (some array) capacity (inputValues addr inputs) ∗ F)

theorem extended_scan_operands (layout : SpaceLayout) {D : List Id} (H : SplitHeap Id)
    {reader source : Id} (readerIn : reader ∈ D) (sourceIn : source ∈ D)
    (closed : ∀ identity ∈ (H.forward reader).active, identity ∈ D)
    (environment : ReadExpressions.Environment)
    (importerRead : environment "importer".toList = some (.ptr (some (addr reader))))
    (sourceRead : environment "dependency".toList = some (.ptr (some (addr source))))
    (F : Heap L → Prop) :
    DependencyReadScan.Operands (StoreState addr layout D H F) (fields layout) environment
      oldArray oldLimit needle (H.forward reader).active (H.forward reader).count source := by
  constructor
  · intro index seen
    rw [old_condition_in_extended_environment layout environment (addr reader) (addr source)
      index seen importerRead]
    exact old_condition_refines_current_count addr layout H readerIn source index seen F
  · intro index seen inside
    rw [old_comparison_in_extended_environment layout environment (addr reader) (addr source)
      index seen importerRead sourceRead]
    exact old_comparison_refines_current_identity addr layout H readerIn sourceIn index inside
      closed seen F

omit [DecidableEq Id] in
theorem initialized_input_load (layout : SpaceLayout) {D : List Id} (H : SplitHeap Id)
    (array : Ptr) (capacity : Nat) (inputs : List (Option Id)) (index : UInt32)
    (inside : index.toNat < inputs.length) (F : Heap L → Prop) :
    CTriple (InputState addr layout D H array capacity inputs F)
      (CProg.loadPtr (array + index.toNat))
      (fun result σ => result = (inputs[index.toNat]).map addr ∧
        InputState addr layout D H array capacity inputs F σ) := by
  apply loadPtr_rule
  intro σ holds
  have arrayHolds : (DynArray (some array) capacity (inputValues addr inputs) ∗
      (StoreRep addr layout D H ∗ F)) σ := by
    simpa only [sepConj_left_comm] using holds.2
  have mappedInside : index.toNat < (inputValues addr inputs).length := by
    simpa [inputValues] using inside
  simpa only [inputValues, List.getElem_map] using read_dynArray mappedInside arrayHolds

omit [DecidableEq Id] in
theorem input_expression_refines_nullable_identity (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) (array : Ptr) (capacity : Nat) (inputs : List (Option Id))
    (environment : ReadExpressions.Environment) (index : UInt32) (inside : index.toNat < inputs.length)
    (arrayRead : environment "dependencies".toList = some (.ptr (some array)))
    (indexRead : environment "i".toList = some (.u32 index)) (F : Heap L → Prop) :
    CTriple (InputState addr layout D H array capacity inputs F)
      (expression (fields layout) environment inputExpression)
      (fun result σ => result = .ptr ((inputs[index.toNat]).map addr) ∧
        InputState addr layout D H array capacity inputs F σ) := by
  rw [input_expression_is_physical_load _ _ array index arrayRead indexRead]
  refine triple_bind _ (initialized_input_load addr layout H array capacity inputs index inside F)
    fun value => ?_
  apply triple_pure
  intro same
  subst value
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩) (triple_ret _ _ _)

theorem nullable_pointer_is_valid (layout : SpaceLayout) {D : List Id} (H : SplitHeap Id)
    (value : Option Id) (closed : ∀ identity, value = some identity → identity ∈ D)
    {F : Heap L → Prop} {σ : Heap L} (holds : StoreState addr layout D H F σ) :
    ValidOpt σ (value.map addr) := by
  cases value with
  | none => trivial
  | some identity =>
    exact represented_address_is_valid addr layout H (closed identity rfl) holds.1 holds.2

theorem invalid_expression_refines_null_or_self (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {reader : Id} (readerIn : reader ∈ D)
    (source : Option Id) (closed : ∀ identity, source = some identity → identity ∈ D)
    (environment : ReadExpressions.Environment)
    (importerRead : environment "importer".toList = some (.ptr (some (addr reader))))
    (sourceRead : environment "dependency".toList = some (.ptr (source.map addr)))
    (F : Heap L → Prop) :
    CTriple (StoreState addr layout D H F)
      (expression (fields layout) environment invalidCondition)
      (fun result σ => result = .bool (decide (source = none ∨ source = some reader)) ∧
        StoreState addr layout D H F σ) := by
  rw [invalid_expression_retains_short_circuit _ _ (addr reader) (source.map addr)
    importerRead sourceRead]
  have nullTest : CTriple (StoreState addr layout D H F)
      (CProg.ptrEq (source.map addr) none)
      (fun result σ => result = decide (source.map addr = none) ∧
        StoreState addr layout D H F σ) :=
    ptrEq_rule (fun _ holds => ⟨nullable_pointer_is_valid addr layout H source closed holds, trivial⟩)
  refine triple_bind _ nullTest fun isNull => ?_
  apply triple_pure
  intro same
  subst isNull
  cases source with
  | none =>
    simp only [Option.map_none, decide_true, ↓reduceIte]
    exact triple_pre _ (fun _ held => ⟨rfl, held⟩) (triple_ret _ _ _)
  | some identity =>
    simp only [Option.map_some, reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte]
    refine triple_bind _ (module_pointer_comparison_refines_identity addr layout H
      (closed identity rfl) readerIn F) fun equal => ?_
    apply triple_pure
    intro same
    subst equal
    exact triple_pre _ (fun _ held => ⟨by simp, held⟩) (triple_ret _ _ _)

end Specifications

end Mettapedia.Machines.CMemory.DependencyValidationOperands
