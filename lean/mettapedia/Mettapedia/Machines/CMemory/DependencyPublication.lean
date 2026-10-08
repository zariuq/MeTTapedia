import Mettapedia.Machines.CMemory.DependencyReads

/-!
# Source-linked publication through reservation and pending-array loads

The retained C AST is lowered to an indexed pointer-load declaration followed
by its actual sequence of post-index stores. The loop reads `added` at every
condition and `pending` at every iteration. Omitting a store, changing its RHS,
or changing its field is not repaired by recognition.

Proof fuel has a distinct exhaustion result. It is not an allocation failure,
an undefined memory access, or successful empty publication. The refinement
below supplies enough fuel using the loaded UInt32 extent.

This uses the existing cell-memory framework. Its layout/effective-type
contracts, and the remaining preparation and concurrency obligations, are not
replaced by a claim about a native C compiler.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Mettapedia.Machines.CMemory.DependencyPublication

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.Lift
open Mettapedia.Machines.CMemory.DependencyReads
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open PostIndex (Array32 StoreSyntax)
open CellPermission

universe u

structure ReservationLayout where
  pending : Nat
  added : Nat

structure MemoryStore where
  owner : Name
  direction : OrderedDependencyCSource.ArrayField
  value : Name

structure BodyCode where
  localName : Name
  stores : List MemoryStore

/-- Lower only the supported typed array/count pairing, retaining both
identifier operands from the supplied statement. -/
def lowerStore? (statement : CStatement) : Option MemoryStore := do
  let site ← PostIndex.storeSyntax? statement
  let direction ← OrderedDependencyCSource.spaceArrayField? site.arrayField site.countField
  some ⟨site.owner, direction, site.value⟩

/-- The continuation is lowered as supplied; it is never compared with the
two-store successful-publisher template. -/
def lowerBody? : List CStatement → Option BodyCode
  | .declare type name (.index (.field (.identifier reservation) field true)
      (.identifier index)) :: rest =>
    if type = ⟨"Space".toList, 1⟩ ∧ reservation = "reservation".toList ∧
        field = "pending".toList ∧ index = "i".toList then do
      let stores ← rest.mapM lowerStore?
      some ⟨name, stores⟩
    else none
  | _ => none

def lowerFunction? (function : CQualifiedFunction) : Option BodyCode :=
  (OrderedDependencyCSource.publisherLoopBody? function).bind lowerBody?

def lowerText? (source : String) : Option BodyCode :=
  (qualifiedFunctionText? OrderedDependencyCSource.publisherTypeNames source.toList).bind
    lowerFunction?

/-- Independently authored expected IR, checked against the parsed source. -/
def publisherCode : BodyCode :=
  ⟨"dependency".toList,
    [⟨"importer".toList, .forward, "dependency".toList⟩,
      ⟨"dependency".toList, .reverse, "importer".toList⟩]⟩

theorem source_lowers_to_memory_publisher :
    lowerText? OrderedDependencyCSource.publisherSource = some publisherCode := by
  rw [lowerText?, OrderedDependencyCSource.complete_source_admitted]
  rfl

abbrev PointerEnvironment := Name → Option (Option Ptr)

/-- A store dereferences its owner but may store a null RHS. Missing bindings
do not grant pointer values or silently manufacture callable authority. -/
def storeProg (layout : SpaceLayout) (environment : PointerEnvironment)
    (site : MemoryStore) : CProg CVal Unit :=
  match environment site.owner, environment site.value with
  | some (some owner), some value =>
      let offsets := arrayOffsets layout site.direction
      postIndexStore (owner + offsets.1) (owner + offsets.2.1) (.ptr value)
  | _, _ => CProg.undefined

def storesProg (layout : SpaceLayout) (environment : PointerEnvironment) :
    List MemoryStore → CProg CVal Unit
  | [] => pure ()
  | site :: rest => do
      storeProg layout environment site
      storesProg layout environment rest

def arguments (reader reservation : Ptr) : PointerEnvironment :=
  fun name => if name = "importer".toList then some (some reader)
    else if name = "reservation".toList then some (some reservation) else none

def bodyProg (layout : SpaceLayout) (reservationLayout : ReservationLayout)
    (code : BodyCode) (reader reservation : Ptr) (index : UInt32) : CProg CVal Unit := do
  let source ← loadItem (reservation + reservationLayout.pending) index
  storesProg layout (Function.update (arguments reader reservation) code.localName (some source))
    code.stores

theorem unit_bind_ret (c : CProg CVal Unit) : c.bind (fun _ => Prog.ret ()) = c := by
  have identity : (fun _ : Unit => (Prog.ret () : CProg CVal Unit)) = Prog.ret := by
    funext value
    cases value
    rfl
  rw [identity, Prog.bind_ret]

theorem publisher_stores_use_loaded_pointer {Id : Type} (addr : Id → Ptr)
    (layout : SpaceLayout) (reader source : Id) (reservation : Ptr) :
    storesProg layout
      (Function.update (arguments (addr reader) reservation) publisherCode.localName
        (some (some (addr source)))) publisherCode.stores =
      writeLinkProg addr layout reader source := by
  change (postIndexStore (addr reader + layout.deps) (addr reader + layout.depCount)
      (spacePtr (addr source)) >>= fun _ =>
    postIndexStore (addr source + layout.importers) (addr source + layout.importerCount)
      (spacePtr (addr reader)) >>= fun _ => pure ()) = _
  simp only [Prog.bind_eq, Prog.pure_eq, unit_bind_ret]
  rfl

inductive Completion where
  | finished
  | exhausted
  deriving DecidableEq, Repr

/-- Each condition is a memory load. UInt32 increments use the machine
operation; the refinement proves that the admitted extent prevents wrapping. -/
def run (layout : SpaceLayout) (reservationLayout : ReservationLayout) (code : BodyCode)
    (reader reservation : Ptr) (fuel : Nat) (index : UInt32) : CProg CVal Completion := do
  let limit ← CProg.loadU32 (reservation + reservationLayout.added)
  if index < limit then
    match fuel with
    | 0 => pure .exhausted
    | fuel + 1 => do
        bodyProg layout reservationLayout code reader reservation index
        run layout reservationLayout code reader reservation fuel (index + 1)
  else pure .finished

def runText (layout : SpaceLayout) (reservationLayout : ReservationLayout)
    (source : String) (reader reservation : Ptr) (fuel : Nat) :
    Option (CProg CVal Completion) :=
  (lowerText? source).map fun code => run layout reservationLayout code reader reservation fuel 0

theorem quoted_source_executes_memory_program (layout : SpaceLayout)
    (reservationLayout : ReservationLayout) (reader reservation : Ptr) (fuel : Nat) :
    runText layout reservationLayout OrderedDependencyCSource.publisherSource
      reader reservation fuel =
      some (run layout reservationLayout publisherCode reader reservation fuel 0) := by
  rw [runText, source_lowers_to_memory_publisher]
  rfl

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]
variable {Id : Type} (addr : Id → Ptr)

/-- The reservation owns its pointer and count fields and the actual pending
storage, including spare capacity. An empty reservation may have a null pointer. -/
def ReservationFields (layout : ReservationLayout) (reservation : Ptr) (array : Option Ptr)
    (capacity : Nat) (added : UInt32) (pending : List Id) : Heap L → Prop :=
  PointsTo (reservation + layout.pending) (.ptr array) ∗
    (PointsTo (reservation + layout.added) (.u32 added) ∗
      DynArray array capacity (pending.map (spacePtr ∘ addr)))

theorem reservation_count_read {layout : ReservationLayout} {reservation : Ptr}
    {array : Option Ptr} {capacity : Nat} {added : UInt32} {pending : List Id}
    {F : Heap L → Prop} {σ : Heap L}
    (holds : (F ∗ ReservationFields addr layout reservation array capacity added pending) σ) :
    read ((σ (reservation + layout.added).block).2 (reservation + layout.added).offset) =
      some (some (.u32 added)) := by
  exact read_framed_right holds fun _ fields =>
    read_framed_right fields fun _ rest => read_of_pointsTo rest

theorem reservation_item_load (layout : ReservationLayout) (reservation : Ptr)
    (array : Option Ptr) (capacity : Nat) (added : UInt32) (pending : List Id)
    (index : UInt32) (inside : index.toNat < pending.length) (F : Heap L → Prop) :
    CTriple (F ∗ ReservationFields addr layout reservation array capacity added pending)
      (loadItem (reservation + layout.pending) index)
      (fun r σ => r = some (addr pending[index.toNat]) ∧
        (F ∗ ReservationFields addr layout reservation array capacity added pending) σ) := by
  unfold loadItem
  simp only [Prog.bind_eq]
  refine triple_bind _ (loadPtr_rule (q := array) fun σ holds =>
    read_framed_right holds fun _ fields => read_of_pointsTo fields) fun p => ?_
  apply triple_pure
  intro same
  subst p
  cases array with
  | none =>
    refine triple_pre _ (fun σ holds => ?_) (triple_false _ _ _)
    have empty := fact_of_sepConj_right holds fun τ fields =>
      fact_of_sepConj_right fields fun τ rest =>
        fact_of_sepConj_right rest fun τ array => array.2.1
    have length : (pending.map (spacePtr ∘ addr)).length = 0 := by rw [empty]; rfl
    rw [List.length_map] at length
    omega
  | some p =>
    apply loadPtr_rule
    intro σ holds
    exact read_framed_right holds fun _ fields =>
      read_framed_right fields fun _ rest =>
        read_framed_right rest fun τ array => by
          have arrayFramed : (DynArray (some p) capacity (pending.map (spacePtr ∘ addr)) ∗
              emp) τ := by rw [sepConj_emp]; exact array
          have mappedInside : index.toNat < (pending.map (spacePtr ∘ addr)).length := by
            simpa using inside
          have element : (pending.map (spacePtr ∘ addr))[index.toNat]'mappedInside =
              spacePtr (addr pending[index.toNat]) := by rw [List.getElem_map]; rfl
          simpa only [element, spacePtr] using read_dynArray mappedInside arrayFramed

/-- One two-way link updates the whole represented store, framing all other
modules. This reuses the existing block-store proof rather than a second
ownership or array implementation. -/
theorem write_store_refines [DecidableEq Id] (layout : SpaceLayout) {D : List Id}
    (distinct : D.Nodup) {reader source : Id} (readerIn : reader ∈ D) (sourceIn : source ∈ D)
    (different : reader ≠ source) (H : SplitHeap Id)
    (ready : OrderedDependencyCArray.Ready H reader [source]) :
    CTriple (L := L) (StoreRep addr layout D H) (writeLinkProg addr layout reader source)
      (fun _ σ => ∃ H', OrderedDependencyCArray.writeLink H reader source = some H' ∧
        StoreRep addr layout D H' σ) := by
  have one := publish_refines (L := L) addr layout distinct readerIn [source] H
    (by simpa using sourceIn) (by simpa using different) ready
  simpa only [publishProg, Prog.foldList, unit_bind_ret, Prog.bind_ret,
    OrderedDependencyCArray.writeBatch,
    Option.bind_some, Option.bind_fun_some] using one

/-- The physical loop realizes the remaining ordered batch. The original
pending block is retained throughout; every iteration reads the actual slot.
The final guard is checked even when no body fuel remains. -/
theorem run_refines_remaining [DecidableEq Id] (layout : SpaceLayout)
    (reservationLayout : ReservationLayout) {D : List Id} (distinct : D.Nodup)
    {reader : Id} (readerIn : reader ∈ D) (reservation : Ptr) (array : Option Ptr)
    (capacity : Nat) (added : UInt32) (remaining : List Id) :
    ∀ (prior : List Id) (index : UInt32) (fuel : Nat) (H : SplitHeap Id),
      index.toNat = prior.length → added.toNat = (prior ++ remaining).length →
      remaining.length ≤ fuel → (∀ s ∈ remaining, s ∈ D) → reader ∉ remaining →
      OrderedDependencyCArray.Ready H reader remaining →
      CTriple (L := L)
        (StoreRep addr layout D H ∗
          ReservationFields addr reservationLayout reservation array capacity added
            (prior ++ remaining))
        (run layout reservationLayout publisherCode (addr reader) reservation fuel index)
        (fun r σ => r = .finished ∧ ∃ H',
          OrderedDependencyCArray.writeBatch H reader remaining = some H' ∧
          (StoreRep addr layout D H' ∗
            ReservationFields addr reservationLayout reservation array capacity added
              (prior ++ remaining)) σ) := by
  induction remaining with
  | nil =>
    intro prior index fuel H position extent _ _ _ _
    have stopped : ¬ index < added := by
      rw [UInt32.lt_iff_toNat_lt]
      simp only [List.append_nil] at extent
      omega
    rw [run.eq_def]
    simp only [Prog.bind_eq]
    refine triple_bind _ (loadU32_rule (n := added) fun σ holds =>
      reservation_count_read addr holds) fun limit => ?_
    apply triple_pure
    intro same
    subst limit
    rw [if_neg stopped]
    refine triple_pre _ (fun σ holds => ?_) (triple_ret _ Completion.finished _)
    exact ⟨rfl, H, rfl, holds⟩
  | cons source rest ih =>
    intro prior index fuel H position extent enough pendingIn notSelf ready
    have selected : index < added := by
      rw [UInt32.lt_iff_toNat_lt]
      simp only [List.length_append, List.length_cons] at extent
      omega
    have increment : (index + 1).toNat = index.toNat + 1 := by
      rw [UInt32.toNat_add]
      apply Nat.mod_eq_of_lt
      have upper := added.toNat_lt
      have before := UInt32.lt_iff_toNat_lt.mp selected
      change index.toNat + 1 < 2 ^ 32
      omega
    have inside : index.toNat < (prior ++ source :: rest).length := by
      simp only [List.length_append, List.length_cons]
      omega
    have loaded : (prior ++ source :: rest)[index.toNat]'inside = source := by
      rw [List.getElem_append_right (by omega)]
      simp [position]
    have sourceIn := pendingIn source List.mem_cons_self
    have different : reader ≠ source := fun same => notSelf (same ▸ List.mem_cons_self)
    have oneReady : OrderedDependencyCArray.Ready H reader [source] := by
      refine ⟨ready.1, by simp, ?_, ?_⟩
      · have room := ready.2.2.1
        simp only [List.length_cons, List.length_nil] at room ⊢
        omega
      · simpa using ready.2.2.2 source List.mem_cons_self
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      rw [run.eq_def]
      simp only [Prog.bind_eq]
      refine triple_bind _ (loadU32_rule (n := added) fun σ holds =>
        reservation_count_read addr holds) fun limit => ?_
      apply triple_pure
      intro same
      subst limit
      rw [if_pos selected]
      unfold bodyProg
      simp only [Prog.bind_eq, Prog.bind_assoc]
      have loadSpec := reservation_item_load (L := L) addr reservationLayout reservation
        array capacity added (prior ++ source :: rest) index inside (StoreRep addr layout D H)
      rw [loaded] at loadSpec
      refine triple_bind _ loadSpec fun pointer => ?_
      apply triple_pure
      intro same
      subst pointer
      rw [publisher_stores_use_loaded_pointer]
      refine triple_bind _ (frame (write_store_refines addr layout distinct readerIn sourceIn
        different H oneReady) _) fun _ => ?_
      refine triple_pre _ (P := fun σ => ∃ H',
          OrderedDependencyCArray.writeLink H reader source = some H' ∧
          (StoreRep addr layout D H' ∗
            ReservationFields addr reservationLayout reservation array capacity added
              (prior ++ source :: rest)) σ) (fun σ holds => ?_) ?_
      · obtain ⟨x, y, separate, rfl, ⟨H', linked, store⟩, fields⟩ := holds
        exact ⟨H', linked, x, y, separate, rfl, store, fields⟩
      apply triple_exists
      intro H'
      apply triple_pure
      intro linked
      have nextPosition : (index + 1).toNat = (prior ++ [source]).length := by
        simp [increment, position]
      have nextExtent : added.toNat = ((prior ++ [source]) ++ rest).length := by
        simpa [List.append_assoc] using extent
      have following := ih (prior ++ [source]) (index + 1) fuel H' nextPosition nextExtent
        (by simpa using enough) (fun s member => pendingIn s (List.mem_cons_of_mem _ member))
        (fun member => notSelf (List.mem_cons_of_mem _ member))
        (OrderedDependencyCArray.ready_after_first ready linked)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at following
      refine triple_post _ following ?_
      rintro r σ ⟨finished, H'', batch, holds⟩
      exact ⟨finished, H'', by simp [OrderedDependencyCArray.writeBatch, linked, batch], holds⟩

theorem loaded_publisher_refines_batch [DecidableEq Id] (layout : SpaceLayout)
    (reservationLayout : ReservationLayout) {D : List Id} (distinct : D.Nodup)
    {reader : Id} (readerIn : reader ∈ D) (reservation : Ptr) (array : Option Ptr)
    (capacity : Nat) (added : UInt32) (pending : List Id) (H : SplitHeap Id)
    (extent : added.toNat = pending.length) (pendingIn : ∀ s ∈ pending, s ∈ D)
    (notSelf : reader ∉ pending) (ready : OrderedDependencyCArray.Ready H reader pending) :
    CTriple (L := L)
      (StoreRep addr layout D H ∗
        ReservationFields addr reservationLayout reservation array capacity added pending)
      (run layout reservationLayout publisherCode (addr reader) reservation pending.length 0)
      (fun r σ => r = .finished ∧ ∃ H',
        OrderedDependencyCArray.writeBatch H reader pending = some H' ∧
        (StoreRep addr layout D H' ∗
          ReservationFields addr reservationLayout reservation array capacity added pending) σ) := by
  simpa using run_refines_remaining addr layout reservationLayout distinct readerIn reservation
    array capacity added pending [] 0 pending.length H rfl extent (Nat.le_refl _)
    pendingIn notSelf ready

/-- The complete retained source, parsed and lowered, publishes the abstract
store through real block loads and stores. Preparation readiness, the current
representation and the cell-layout contract remain explicit premises. -/
theorem parsed_publication_realizes_store {Entry : Type*} {size : Nat}
    (addr : Fin size → Ptr) (layout : SpaceLayout) (reservationLayout : ReservationLayout)
    (state : OrderedDependencyStore.Store Entry size) (H : SplitHeap (Fin size))
    (reader : Fin size) (sources : List (Fin size)) (reservation : Ptr) (array : Option Ptr)
    (capacity : Nat) (added : UInt32)
    (represented : OrderedDependencyCArray.Represents H state)
    (observers : OrderedDependencyStore.ObserverInvariant state)
    (ready : OrderedDependencyCArray.Ready H reader
      (OrderedDependencyBatch.collectMissing (state.members reader).deps [] sources))
    (notSelf : reader ∉
      OrderedDependencyBatch.collectMissing (state.members reader).deps [] sources)
    (extent : added.toNat =
      (OrderedDependencyBatch.collectMissing (state.members reader).deps [] sources).length) :
    ∃ program, runText layout reservationLayout OrderedDependencyCSource.publisherSource
        (addr reader) reservation added.toNat = some program ∧
      CTriple (L := L)
        (StoreRep addr layout (List.finRange size) H ∗
          ReservationFields addr reservationLayout reservation array capacity added
            (OrderedDependencyBatch.collectMissing (state.members reader).deps [] sources))
        program
        (fun r σ => r = .finished ∧ ∃ H',
          OrderedDependencyCArray.Represents H' (OrderedDependencyBatch.publish state reader sources) ∧
          (StoreRep addr layout (List.finRange size) H' ∗
            ReservationFields addr reservationLayout reservation array capacity added
              (OrderedDependencyBatch.collectMissing (state.members reader).deps [] sources)) σ) := by
  refine ⟨run layout reservationLayout publisherCode (addr reader) reservation added.toNat 0,
    quoted_source_executes_memory_program layout reservationLayout _ _ _, ?_⟩
  obtain ⟨after, batch, representsAfter⟩ :=
    OrderedDependencyCArray.prepared_publication_represents_topology state H reader sources
      represented observers ready
  rw [extent]
  refine triple_post _ (loaded_publisher_refines_batch addr layout reservationLayout
    (List.nodup_finRange size) (List.mem_finRange reader) reservation array capacity added _ H
    extent (fun s _ => List.mem_finRange s) notSelf ready) ?_
  rintro r σ ⟨finished, H', written, holds⟩
  rw [batch] at written
  cases written
  exact ⟨finished, after, representsAfter, holds⟩

namespace Controls

/-- Altering the actual continuation changes the generated store list. -/
theorem omitted_reverse_is_not_restored :
    lowerFunction? OrderedDependencyCSource.Controls.withoutReverse =
      some ⟨"dependency".toList, [⟨"importer".toList, .forward, "dependency".toList⟩]⟩ := rfl

theorem altered_rhs_is_retained :
    lowerStore? (⟨"importer".toList, "deps".toList, "dep_count".toList,
      "importer".toList⟩ : StoreSyntax).statement =
      some ⟨"importer".toList, .forward, "importer".toList⟩ := rfl

theorem wrong_counter_field_is_not_lowered :
    lowerStore? (⟨"importer".toList, "deps".toList, "importer_count".toList,
      "dependency".toList⟩ : StoreSyntax).statement = none := rfl

theorem mismatched_counter_owner_is_not_lowered :
    lowerStore? (.assign (.index (.field (.identifier "importer".toList) "deps".toList true)
        (.postIncrement (.field (.identifier "dependency".toList) "dep_count".toList true)))
      (.identifier "dependency".toList)) = none := rfl

/-- An empty continuation really performs no stores. The pending load is
still in the declaration; it is not elided by a successful-template test. -/
theorem empty_store_continuation_is_retained :
    lowerBody? (OrderedDependencyCSource.iterationBody.take 1) =
      some ⟨"dependency".toList, []⟩ := rfl

/-- A held null pointer field does not make an indexed dereference safe. -/
theorem null_pending_pointer_is_undefined (items : Ptr) (index : UInt32) (σ : Heap L)
    (nullRead : read ((σ items.block).2 items.offset) = some (some (.ptr none))) :
    ¬ (loadItem items index).Safe act σ := by
  intro safe
  rw [loadItem, Prog.bind_eq, Prog.safe_bind] at safe
  have loadRun : (CProg.loadPtr items).Runs act σ none σ :=
    ⟨CVal.ptr none, σ, ⟨nullRead, rfl⟩, rfl, rfl⟩
  exact (safe.2 _ _ loadRun).1

/-- Exhaustion checks the guard but performs no pending load or publication.
Thus its result is distinct from both a completed loop and undefined access. -/
theorem no_body_fuel_is_exhaustion (layout : SpaceLayout)
    (reservationLayout : ReservationLayout) (code : BodyCode) (reader reservation : Ptr)
    (index added : UInt32) (selected : index < added) (F : Heap L → Prop) :
    CTriple (PointsTo (reservation + reservationLayout.added) (.u32 added) ∗ F)
      (run layout reservationLayout code reader reservation 0 index)
      (fun r σ => r = .exhausted ∧
        (PointsTo (reservation + reservationLayout.added) (.u32 added) ∗ F) σ) := by
  rw [run.eq_def]
  simp only [Prog.bind_eq]
  refine triple_bind _ (loadU32_rule (n := added) fun σ holds => read_of_pointsTo holds)
    fun limit => ?_
  apply triple_pure
  intro same
  subst limit
  rw [if_pos selected]
  exact triple_pre _ (fun _ holds => ⟨rfl, holds⟩) (triple_ret _ Completion.exhausted _)

/-- A zero extent needs no pending storage or pending-pointer field at all.
This is actual guard execution, not an assumption that a null dereference works. -/
theorem empty_extent_does_not_read_pending (layout : SpaceLayout)
    (reservationLayout : ReservationLayout) (code : BodyCode) (reader reservation : Ptr)
    (fuel : Nat) (F : Heap L → Prop) :
    CTriple (PointsTo (reservation + reservationLayout.added) (.u32 0) ∗ F)
      (run layout reservationLayout code reader reservation fuel 0)
      (fun r σ => r = .finished ∧
        (PointsTo (reservation + reservationLayout.added) (.u32 0) ∗ F) σ) := by
  rw [run.eq_def]
  simp only [Prog.bind_eq]
  refine triple_bind _ (loadU32_rule (n := 0) fun σ holds => read_of_pointsTo holds)
    fun limit => ?_
  apply triple_pure
  intro same
  subst limit
  rw [if_neg (show ¬ (0 : UInt32) < 0 by decide)]
  exact triple_pre _ (fun _ holds => ⟨rfl, holds⟩) (triple_ret _ Completion.finished _)

/-- A live, typed array pointer is insufficient when its selected cell was
never initialized. The second load has no defined value. -/
theorem indeterminate_pending_slot_is_undefined (items p : Ptr) (index : UInt32) (σ : Heap L)
    (pointerRead : read ((σ items.block).2 items.offset) = some (some (.ptr (some p))))
    (indeterminate : read ((σ (p + index.toNat).block).2 (p + index.toNat).offset) = some none) :
    ¬ (loadItem items index).Safe act σ := by
  intro safe
  rw [loadItem, Prog.bind_eq, Prog.safe_bind] at safe
  have loadRun : (CProg.loadPtr items).Runs act σ (some p) σ :=
    ⟨CVal.ptr (some p), σ, ⟨pointerRead, rfl⟩, rfl, rfl⟩
  have next := safe.2 _ _ loadRun
  obtain ⟨v, valueRead⟩ := next.1
  rw [indeterminate] at valueRead
  cases valueRead

theorem unreadable_pending_slot_is_undefined (items p : Ptr) (index : UInt32) (σ : Heap L)
    (pointerRead : read ((σ items.block).2 items.offset) = some (some (.ptr (some p))))
    (unreadable : read ((σ (p + index.toNat).block).2 (p + index.toNat).offset) = none) :
    ¬ (loadItem items index).Safe act σ := by
  intro safe
  rw [loadItem, Prog.bind_eq, Prog.safe_bind] at safe
  have loadRun : (CProg.loadPtr items).Runs act σ (some p) σ :=
    ⟨CVal.ptr (some p), σ, ⟨pointerRead, rfl⟩, rfl, rfl⟩
  have next := safe.2 _ _ loadRun
  obtain ⟨v, valueRead⟩ := next.1
  rw [unreadable] at valueRead
  cases valueRead

/-- A pointer field may stay readable while its indexed offset is outside the
live array. The whole-memory invariant excludes a permission at that offset. -/
theorem out_of_bounds_pending_slot_is_undefined (items p : Ptr) (index : UInt32)
    (capacity : Nat) (σ : Heap L) (wellFormed : WellFormed σ)
    (pointerRead : read ((σ items.block).2 items.offset) = some (some (.ptr (some p))))
    (header : (σ p.block).1 = .own ⟨capacity, true⟩)
    (outside : capacity ≤ p.offset + index.toNat) : ¬ (loadItem items index).Safe act σ := by
  apply unreadable_pending_slot_is_undefined items p index σ pointerRead
  have empty : (σ p.block).2 (p.offset + index.toNat) = 0 := by
    by_contra held
    obtain ⟨size, actualHeader, inside⟩ := wellFormed p.block _ held
    rw [header] at actualHeader
    cases actualHeader
    omega
  simp only [Ptr.add_block, Ptr.add_offset, empty, read_zero]

/-- Merely retaining a non-null pointer does not keep its storage alive. -/
theorem dead_pending_storage_is_undefined (items p : Ptr) (index : UInt32)
    (capacity : Nat) (σ : Heap L) (wellFormed : WellFormed σ)
    (pointerRead : read ((σ items.block).2 items.offset) = some (some (.ptr (some p))))
    (dead : (σ p.block).1 = .own ⟨capacity, false⟩) : ¬ (loadItem items index).Safe act σ := by
  apply unreadable_pending_slot_is_undefined items p index σ pointerRead
  have empty : (σ p.block).2 (p.offset + index.toNat) = 0 := by
    by_contra held
    obtain ⟨size, actualHeader, -⟩ := wellFormed p.block _ held
    rw [dead] at actualHeader
    cases actualHeader
  simp only [Ptr.add_block, Ptr.add_offset, empty, read_zero]

/-- An initialized integer is still not a `Space *`. The continuation must
not accept a differently typed pending slot just because it is readable. -/
theorem wrong_pending_slot_type_is_undefined (items p : Ptr) (index value : UInt32)
    (σ : Heap L)
    (pointerRead : read ((σ items.block).2 items.offset) = some (some (.ptr (some p))))
    (integerRead : read ((σ (p + index.toNat).block).2 (p + index.toNat).offset) =
      some (some (.u32 value))) : ¬ (loadItem items index).Safe act σ := by
  intro safe
  rw [loadItem, Prog.bind_eq, Prog.safe_bind] at safe
  have loadRun : (CProg.loadPtr items).Runs act σ (some p) σ :=
    ⟨CVal.ptr (some p), σ, ⟨pointerRead, rfl⟩, rfl, rfl⟩
  have next := safe.2 _ _ loadRun
  change (CProg.loadPtr (p + index.toNat)).Safe act σ at next
  rw [CProg.loadPtr, Prog.bind_eq, Prog.safe_bind] at next
  have slotRun : (CProg.load (V := CVal) (p + index.toNat)).Runs act σ (.u32 value) σ :=
    ⟨CVal.u32 value, σ, ⟨integerRead, rfl⟩, rfl, rfl⟩
  exact (next.2 _ _ slotRun).1

end Controls

end Mettapedia.Machines.CMemory.DependencyPublication
