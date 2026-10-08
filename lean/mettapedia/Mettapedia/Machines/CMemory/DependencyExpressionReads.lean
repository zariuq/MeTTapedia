import Mettapedia.Machines.CMemory.ReadExpressions
import Mettapedia.Machines.CMemory.DependencyReads
import Mettapedia.Machines.OrderedDependencyCPreparationScan

/-!
# Retained preparation expressions over block memory

The existing-dependency loop's count, indexed identity and comparison are
executed by the physical scalar-expression reader. Its field descriptors name
actual cell offsets. The initialized prefix and represented module domain
justify loads and pointer comparisons; capacities are not scan bounds.

Module address injectivity comes from separate owned fields. Validity comes
from those fields and the well-formed full heap, rather than an assumed inverse
address map or an unrestricted pointer comparison. The complete surrounding
preparation, native byte ABI and concurrent currency are not proved here.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Machines.CMemory.DependencyExpressionReads

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open CMemory.Lift CMemory.DependencyReads CMemory.ReadExpressions
open OrderedDependencyCPreparationScan
open CellPermission

universe u

def fields (layout : SpaceLayout) : ReadExpressions.Layout := fun name =>
  if name = "deps".toList then some ⟨layout.deps, .pointer⟩
  else if name = "dep_count".toList then some ⟨layout.depCount, .word⟩
  else if name = "dep_cap".toList then some ⟨layout.depCap, .word⟩
  else if name = "importers".toList then some ⟨layout.importers, .pointer⟩
  else if name = "importer_count".toList then some ⟨layout.importerCount, .word⟩
  else if name = "importer_cap".toList then some ⟨layout.importerCap, .word⟩
  else none

def bindings (reader source : Ptr) : ReadExpressions.Environment := fun name =>
  if name = "importer".toList then some (.ptr (some reader))
  else if name = "dependency".toList then some (.ptr (some source)) else none

def locals (base : ReadExpressions.Environment) (index : UInt32) (seen : Bool) :
    ReadExpressions.Environment := fun name =>
  if name = IdentityScan.counter then some (.u32 index)
  else if name = IdentityScan.flag then some (.bool seen) else base name

def sourceCondition? : Option CStatement → Option CExpr
  | some (.forLoop _ _ _ condition _ _) => some condition
  | _ => none

def sourceComparison? : Option CStatement → Option CExpr
  | some (.forLoop _ _ _ _ _ [.assign (.identifier _) comparison]) => some comparison
  | _ => none

theorem quoted_condition_is_retained :
    sourceCondition? (quotedScan 10 3) = some (IdentityScan.condition oldLimit) := by
  rw [quoted_existing_node_is_actual, existing_node_is_retained]
  rfl

theorem quoted_comparison_is_retained :
    sourceComparison? (quotedScan 10 3) =
      some (.binary .eq (.index oldArray (.identifier IdentityScan.counter)) needle) := by
  rw [quoted_existing_node_is_actual, existing_node_is_retained]
  rfl

theorem old_limit_loads_current_cell (layout : SpaceLayout) (reader source : Ptr)
    (index : UInt32) (seen : Bool) :
    ReadExpressions.expression (fields layout) (locals (bindings reader source) index seen)
      oldLimit = (CProg.loadU32 (reader + layout.depCount) >>= fun count =>
        pure (.u32 count)) := by
  simp [ReadExpressions.expression, ReadExpressions.expressionWith_equation, ReadExpressions.field, ReadExpressions.pointer,
    ReadExpressions.resolved, oldLimit, locals, bindings, fields,
    IdentityScan.counter, IdentityScan.flag]

theorem old_item_follows_stored_array_pointer (layout : SpaceLayout) (reader source : Ptr)
    (index : UInt32) (seen : Bool) :
    ReadExpressions.expression (fields layout) (locals (bindings reader source) index seen)
      (.index oldArray (.identifier IdentityScan.counter)) =
      (loadItem (reader + layout.deps) index >>= fun item => pure (.ptr item)) := by
  simp [ReadExpressions.expression, ReadExpressions.expressionWith_equation, ReadExpressions.field, ReadExpressions.pointer,
    ReadExpressions.word, ReadExpressions.indexed, ReadExpressions.resolved,
    oldArray, locals, bindings, fields, IdentityScan.counter, IdentityScan.flag,
    loadItem, Prog.bind_assoc]
  congr 1
  funext array
  cases array with
  | none => exact (undefined_bind _).symm
  | some array => rfl

theorem old_condition_executes_bound_before_flag (layout : SpaceLayout) (reader source : Ptr)
    (index : UInt32) (seen : Bool) :
    ReadExpressions.expression (fields layout) (locals (bindings reader source) index seen)
      (IdentityScan.condition oldLimit) =
      (CProg.loadU32 (reader + layout.depCount) >>= fun count =>
        pure (.bool (decide (index < count) && !seen))) := by
  simp [IdentityScan.condition, ReadExpressions.expression, ReadExpressions.expressionWith_equation, ReadExpressions.field,
    ReadExpressions.binary, ReadExpressions.word, ReadExpressions.truth,
    ReadExpressions.pointer, ReadExpressions.resolved, oldLimit, locals, bindings,
    fields, IdentityScan.counter, IdentityScan.flag, Prog.bind_assoc]
  congr 1
  funext count
  split <;> simp_all

theorem old_comparison_executes_typed_load_and_pointer_equality
    (layout : SpaceLayout) (reader source : Ptr) (index : UInt32) (seen : Bool) :
    ReadExpressions.expression (fields layout) (locals (bindings reader source) index seen)
      (.binary .eq (.index oldArray (.identifier IdentityScan.counter)) needle) =
      (loadItem (reader + layout.deps) index >>= fun item =>
        CProg.ptrEq item (some source) >>= fun equal => pure (.bool equal)) := by
  change (ReadExpressions.expression (fields layout) (locals (bindings reader source) index seen)
    (.index oldArray (.identifier IdentityScan.counter)) >>= fun first =>
      ReadExpressions.expression (fields layout) (locals (bindings reader source) index seen)
        needle >>= fun second => ReadExpressions.binary .eq first second) = _
  rw [old_item_follows_stored_array_pointer]
  simp [ReadExpressions.expression, ReadExpressions.expressionWith_equation, ReadExpressions.resolved, ReadExpressions.binary,
    ReadExpressions.equal, needle, locals, bindings, IdentityScan.counter,
    IdentityScan.flag, Prog.bind_assoc]

section Specifications

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]
variable {Id : Type} [DecidableEq Id] (addr : Id → Ptr)

/-- Holding a represented field in a well-formed full heap supplies a live
block for the struct's base, even when the owned field has nonzero offset. -/
theorem represented_address_is_valid (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {owner : Id} (member : owner ∈ D) {F : Heap L → Prop}
    {σ : Heap L} (wellFormed : WellFormed σ) (holds : (StoreRep addr layout D H ∗ F) σ) :
    Valid σ (addr owner) := by
  obtain ⟨rest, split⟩ := store_array_split (L := L) addr layout H member .forward
  rw [split, sepConj_assoc] at holds
  obtain ⟨array, wholeField⟩ := counted_pointer_field_is_whole addr holds
  change (σ (addr owner + layout.deps).block).2 (addr owner + layout.deps).offset =
    whole (some (CVal.ptr array)) at wholeField
  have nonzero : (σ (addr owner + layout.deps).block).2
      (addr owner + layout.deps).offset ≠ 0 := by
    rw [wholeField]
    exact whole_ne_zero _
  obtain ⟨extent, header, inside⟩ := wellFormed.live nonzero
  refine Or.inl ⟨extent, header, ?_⟩
  simp only [Ptr.add_offset] at inside
  omega

theorem physical_identity_equality_iff (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {left right : Id} (leftIn : left ∈ D) (rightIn : right ∈ D)
    {F : Heap L → Prop} {σ : Heap L} (holds : (StoreRep addr layout D H ∗ F) σ) :
    some (addr left) = some (addr right) ↔ left = right := by
  constructor
  · intro same
    by_contra different
    have distinct : addr left ≠ addr right := fact_of_sepConj_left holds fun τ store =>
      represented_module_addresses_are_distinct addr layout H leftIn rightIn different store
    exact distinct (Option.some.inj same)
  · rintro rfl
    rfl

def StoreState (layout : SpaceLayout) (D : List Id) (H : SplitHeap Id)
    (F : Heap L → Prop) : Heap L → Prop :=
  fun σ => WellFormed σ ∧ (StoreRep addr layout D H ∗ F) σ

theorem module_pointer_comparison_refines_identity (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {left right : Id} (leftIn : left ∈ D) (rightIn : right ∈ D)
    (F : Heap L → Prop) :
    CTriple (StoreState addr layout D H F) (CProg.ptrEq (some (addr left)) (some (addr right)))
      (fun result σ => result = decide (left = right) ∧ StoreState addr layout D H F σ) := by
  refine triple_post _ (ptrEq_rule fun σ holds =>
    ⟨represented_address_is_valid addr layout H leftIn holds.1 holds.2,
      represented_address_is_valid addr layout H rightIn holds.1 holds.2⟩) ?_
  rintro result σ ⟨rfl, holds⟩
  refine ⟨?_, holds⟩
  simp only [physical_identity_equality_iff addr layout H leftIn rightIn holds.2]

theorem load_item_readOnly (items : Ptr) (index : UInt32) :
    ReadOnly (L := L) (loadItem items index) := by
  apply bind_readOnly _ _ (load_pointer_readOnly items)
  intro array
  cases array with
  | none => exact undefined_readOnly
  | some array => exact load_pointer_readOnly _

theorem old_condition_refines_current_count (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {reader : Id} (readerIn : reader ∈ D) (source : Id)
    (index : UInt32) (seen : Bool) (F : Heap L → Prop) :
    CTriple (StoreState addr layout D H F)
      (ReadExpressions.expression (fields layout)
        (locals (bindings (addr reader) (addr source)) index seen)
        (IdentityScan.condition oldLimit))
      (fun result σ => result = .bool (decide (index < (H.forward reader).count) && !seen) ∧
        StoreState addr layout D H F σ) := by
  rw [old_condition_executes_bound_before_flag]
  have countSpec := triple_preserves_predicate (R := WellFormed)
    (load_word_readOnly (L := L) _) (store_count_load addr layout H readerIn .forward F)
  have retained : CTriple (StoreState addr layout D H F)
      (CProg.loadU32 (addr reader + layout.depCount))
      (fun count σ => count = (H.forward reader).count ∧ StoreState addr layout D H F σ) :=
    triple_post _ countSpec (fun _ _ held => ⟨held.2.1, held.1, held.2.2⟩)
  refine triple_bind _ retained fun count => ?_
  apply triple_pure
  intro same
  subst count
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩)
    (triple_ret _ _ _)

theorem old_comparison_refines_current_identity (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {reader source : Id} (readerIn : reader ∈ D) (sourceIn : source ∈ D)
    (index : UInt32) (inside : index.toNat < (H.forward reader).active.length)
    (closed : ∀ identity ∈ (H.forward reader).active, identity ∈ D)
    (seen : Bool) (F : Heap L → Prop) :
    CTriple (StoreState addr layout D H F)
      (ReadExpressions.expression (fields layout)
        (locals (bindings (addr reader) (addr source)) index seen)
        (.binary .eq (.index oldArray (.identifier IdentityScan.counter)) needle))
      (fun result σ => result = .bool (decide ((H.forward reader).active[index.toNat] = source)) ∧
        StoreState addr layout D H F σ) := by
  rw [old_comparison_executes_typed_load_and_pointer_equality]
  have itemSpec := triple_preserves_predicate (R := WellFormed)
    (load_item_readOnly (L := L) _ index) (store_item_load addr layout H readerIn .forward
      index inside F)
  have retained : CTriple (StoreState addr layout D H F)
      (loadItem (addr reader + layout.deps) index)
      (fun item σ => item = some (addr (H.forward reader).active[index.toNat]) ∧
        StoreState addr layout D H F σ) :=
    triple_post _ itemSpec (fun _ _ held => ⟨held.2.1, held.1, held.2.2⟩)
  refine triple_bind _ retained fun item => ?_
  apply triple_pure
  intro same
  subst item
  have member : (H.forward reader).active[index.toNat] ∈ D :=
    closed _ (List.getElem_mem inside)
  refine triple_bind _
    (module_pointer_comparison_refines_identity addr layout H member sourceIn F) fun equal => ?_
  apply triple_pure
  intro same
  subst equal
  exact triple_pre _ (fun σ holds => ⟨rfl, holds⟩) (triple_ret _ _ _)

end Specifications

end Mettapedia.Machines.CMemory.DependencyExpressionReads
