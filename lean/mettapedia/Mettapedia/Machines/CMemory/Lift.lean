import Mettapedia.Machines.CMemory.Array
import Mettapedia.Machines.OrderedDependencyCArray
import Mettapedia.Machines.OrderedDependencyCReserve

/-!
# Layer 2: from block memory to Co5's split heaps

Co5's proofs of CeTTa's module-link functions run over split heaps: one
abstract counted array per owner and direction
(`OrderedDependencyCArray.Heap Id`, with `forward` and `reverse` of type
`Id → Array32 Id`).  This module relates block memory to those split heaps and
proves the publisher's refinements through the relation.

Identities stay abstract: `addr : Id → Ptr` gives the address of each `Space`
struct, and arrays store the addresses of the spaces they name.  With
`Id = Fin size`, Co5's own store theorems apply unchanged.

**The representation.**

* `CountedArray addr items count capacity A`: three fields of a C struct (the
  array pointer, the counter and the capacity) and the array they describe
  represent Co5's counted array `A`.  The array holds exactly the addresses of
  `A.active`; its capacity is `A.slots.length`.  Co5's spare slots carry values
  that no observation reads, and the representation forgets them, so it is a
  relation rather than a function.
* `SpaceLayout`: the cell offsets of the six dependency fields inside a
  `Space` struct.  Distinct offsets are not assumed: a layout whose fields
  overlap makes the representation unsatisfiable
  (`overlapping_fields_unsatisfiable`).
* `SpaceRep layout addr i fwd rev`: the forward and reverse counted arrays of
  the `Space` with identity `i`.
* `StoreRep layout addr D H`: the representations of every `Space` in the list
  `D`, side by side.  This is the invariant the lock of layer 3 owns.

**What is proved.**

* `postIndexStore_refines`: the C statement `a[n++] = v`, executed on block
  memory, refines Co5's `PostIndex.store`.  In memory, a full array has no
  safe execution (`full_array_undefined`).
* `writeLink_refines`: the two stores of one published link,

  ```c
  importer->deps[importer->dep_count++] = dependency;
  dependency->importers[dependency->importer_count++] = importer;
  ```

  executed on block memory from the representations of two different spaces,
  refine Co5's `OrderedDependencyCArray.writeLink`.  The two stores cannot
  interfere because the representations are separate: that disjointness is
  what Co5's split heap supplied by construction.
* `publish_refines`: the publisher loop over the pending identities, from the
  representation of a whole store, refines Co5's `writeBatch`.
* `publication_realizes_store`: composed with Co5's
  `prepared_publication_represents_topology`, the publisher on block memory
  realizes the abstract store's `publish`.
* `shared_block_unsatisfiable`: two spaces never share a `deps` block (the
  negative control of the B1 plan).
* `nextCapacity_eq_chosenCapacity`: the capacity the block-level `reserve`
  requests is Co5's `OrderedDependencyCReserve.chosenCapacity`.

The publisher loop here iterates over the pending identities as values; it
does not yet load them from the reservation's `pending` array.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.Lift

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open PostIndex (Array32)
open CellPermission

universe u

/-- Co5's split heap over identities `Id`. -/
abbrev SplitHeap (Id : Type) := Mettapedia.Machines.OrderedDependencyCArray.Heap Id

/-- A `Space *` stored in a cell. -/
def spacePtr (s : Ptr) : CVal := .ptr (some s)

section Representation

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]
variable {Id : Type} (addr : Id → Ptr)

/-- The three fields and the array, for a given array pointer `a`. -/
def CountedFields (items count capacity : Ptr) (a : Option Ptr) (A : Array32 Id) :
    Heap L → Prop :=
  PointsTo items (.ptr a) ∗ (PointsTo count (.u32 A.count) ∗
    (PointsTo capacity (.u32 (UInt32.ofNat A.slots.length)) ∗
      DynArray a A.slots.length (A.active.map (spacePtr ∘ addr))))

/-- **A counted array**: three fields of a C struct and the array they describe
represent Co5's `Array32`. -/
def CountedArray (items count capacity : Ptr) (A : Array32 Id) : Heap L → Prop :=
  fun σ => A.count.toNat ≤ A.slots.length ∧ ∃ a, CountedFields addr items count capacity a A σ

/-- `a[n++] = v`, with the array pointer in field `items` and the counter in
field `count`. -/
def postIndexStore (items count : Ptr) (v : CVal) : CProg CVal Unit := do
  let a ← CProg.loadPtr items
  let n ← CProg.loadU32 count
  CProg.store count (.u32 (n + 1))
  match a with
  | none => CProg.undefined
  | some a => CProg.store (a + n.toNat) v

omit addr in
theorem active_length (f : Id → CVal) {A : Array32 Id} (within : A.count.toNat ≤ A.slots.length) :
    (A.active.map f).length = A.count.toNat := by
  simp only [List.length_map, Array32.active, List.length_take]
  omega

/-- **The post-index store refines Co5's `PostIndex.store`.** -/
theorem postIndexStore_refines (items count capacity : Ptr) (A : Array32 Id) (v : Id)
    (sized : A.Sized) (room : A.Room) :
    CTriple (L := L) (CountedArray addr items count capacity A)
      (postIndexStore items count (spacePtr (addr v)))
      (fun _ σ => ∃ A', PostIndex.store A v = some A' ∧
        CountedArray addr items count capacity A' σ) := by
  refine triple_pre _ (P := fun σ => A.count.toNat ≤ A.slots.length ∧
      ∃ a, CountedFields addr items count capacity a A σ) (fun _ holds => holds) ?_
  apply triple_pure
  intro within
  apply triple_exists
  intro a
  unfold postIndexStore
  simp only [Prog.bind_eq]
  refine triple_bind _ (loadPtr_rule (q := a) fun σ holds => read_of_pointsTo holds)
    fun a' => ?_
  apply triple_pure
  intro same
  subst a'
  refine triple_bind _ (loadU32_rule (n := A.count) fun σ holds => ?_) fun n => ?_
  · rw [CountedFields, sepConj_left_comm] at holds
    exact read_of_pointsTo holds
  apply triple_pure
  intro same
  subst n
  refine triple_bind _ (triple_pre _ (fun σ holds => ?_)
    (frame (store_spec count (CVal.u32 (A.count + 1)))
      (PointsTo items (.ptr a) ∗ (PointsTo capacity (.u32 (UInt32.ofNat A.slots.length)) ∗
        DynArray a A.slots.length (A.active.map (spacePtr ∘ addr)))))) fun _ => ?_
  · rw [CountedFields, sepConj_left_comm] at holds
    exact sepConj_mono (pointsTo_le_any count _) le_rfl σ holds
  cases a with
  | none =>
    refine triple_pre _ (fun σ holds => ?_) (triple_false _ _ _)
    refine fact_of_sepConj_right holds fun τ rest => ?_
    refine fact_of_sepConj_right rest fun τ rest => ?_
    refine fact_of_sepConj_right rest fun τ array => ?_
    have empty := array.1
    change A.count.toNat < A.slots.length at room
    omega
  | some p =>
    have length := active_length (spacePtr ∘ addr) within
    have appended := store_append (L := L) p A.slots.length (A.active.map (spacePtr ∘ addr))
      (spacePtr (addr v)) (by rw [length]; exact room)
    rw [length] at appended
    refine triple_post _ (frame_left (frame_left (frame_left appended _) _) _) ?_
    intro _ σ holds
    have exact := PostIndex.increment_is_exact A sized room
    refine ⟨⟨A.slots.set A.count.toNat v, A.count + 1⟩, PostIndex.store_defined A v room, ?_,
      some p, ?_⟩
    · change (A.count + 1).toNat ≤ (A.slots.set A.count.toNat v).length
      rw [exact, List.length_set]
      exact room
    · have stored := PostIndex.store_realizes_append sized (PostIndex.store_defined A v room)
      rw [CountedFields, sepConj_left_comm]
      simp only [List.length_set, stored.1, List.map_append, List.map_cons, List.map_nil,
        Function.comp_apply]
      exact holds

/-- **Negative control**: in memory, `a[n++] = v` on a full array writes past the
end of its block, and has no safe execution. -/
theorem full_array_undefined (items count capacity : Ptr) (A : Array32 Id) (v : Ptr)
    (full : ¬ A.Room) (σ : Heap L) (wellFormed : WellFormed σ)
    (holds : CountedArray addr items count capacity A σ) :
    ¬ (postIndexStore items count (spacePtr v)).Safe act σ := by
  obtain ⟨within, a, fields⟩ := holds
  have equal : A.count.toNat = A.slots.length := by
    change ¬ A.count.toNat < A.slots.length at full
    omega
  unfold postIndexStore
  simp only [Prog.bind_eq]
  refine not_safe_of_triple_wf (loadPtr_rule (q := a)
    (P := CountedFields addr items count capacity a A) fun τ held => read_of_pointsTo held)
    fields wellFormed ?_
  rintro a' τ ⟨same, fields⟩ wellFormed
  subst a'
  refine not_safe_of_triple_wf (loadU32_rule (n := A.count)
    (P := CountedFields addr items count capacity a A) fun τ held => by
      rw [CountedFields, sepConj_left_comm] at held
      exact read_of_pointsTo held) fields wellFormed ?_
  rintro n τ ⟨rfl, fields⟩ wellFormed
  rw [CountedFields, sepConj_left_comm] at fields
  refine not_safe_of_triple_wf (frame (store_spec count (CVal.u32 (A.count + 1))) _)
    (sepConj_mono (pointsTo_le_any count _) le_rfl τ fields) wellFormed ?_
  rintro _ τ' after wellFormed'
  cases a with
  | none => exact fun safe => safe.1
  | some p =>
    rintro ⟨⟨c, whole_at⟩, -⟩
    have base : p.offset = 0 :=
      fact_of_sepConj_right after fun _ rest => fact_of_sepConj_right rest fun _ rest =>
        fact_of_sepConj_right rest fun _ array => array.1
    have header : (τ' p.block).1 = .own ⟨A.slots.length, true⟩ :=
      header_of_sepConj_right after fun _ rest => header_of_sepConj_right rest fun _ rest =>
        header_of_sepConj_right rest fun _ array => header_of_dynArray array
    have held : (τ' p.block).2 (p.offset + A.count.toNat) ≠ 0 := by
      simp only [Ptr.add_block, Ptr.add_offset] at whole_at
      rw [whole_at]
      exact whole_ne_zero c
    obtain ⟨n', header', inside⟩ := wellFormed' p.block _ held
    rw [header] at header'
    cases header'
    omega

/-! ## Spaces -/

/-- The cell offsets of the dependency fields inside a `Space` struct. -/
structure SpaceLayout where
  deps : ℕ
  depCount : ℕ
  depCap : ℕ
  importers : ℕ
  importerCount : ℕ
  importerCap : ℕ

/-- **The representation of one `Space`**: its forward and reverse counted
arrays. -/
def SpaceRep (layout : SpaceLayout) (i : Id) (forward reverse : Array32 Id) :
    Heap L → Prop :=
  CountedArray addr (addr i + layout.deps) (addr i + layout.depCount) (addr i + layout.depCap)
      forward ∗
    CountedArray addr (addr i + layout.importers) (addr i + layout.importerCount)
      (addr i + layout.importerCap) reverse

/-- **The representation of a store of spaces**: every `Space` of `D`, side by
side, represents its forward and reverse arrays in `H`. -/
def StoreRep (layout : SpaceLayout) (D : List Id) (H : SplitHeap Id) : Heap L → Prop :=
  bigSep (D.map fun i => SpaceRep addr layout i (H.forward i) (H.reverse i))

/-- The two stores that publish one link. -/
def writeLinkProg (layout : SpaceLayout) (reader source : Id) : CProg CVal Unit := do
  postIndexStore (addr reader + layout.deps) (addr reader + layout.depCount)
    (spacePtr (addr source))
  postIndexStore (addr source + layout.importers) (addr source + layout.importerCount)
    (spacePtr (addr reader))

/-- **Publishing one link on block memory refines Co5's `writeLink`.**  The
reader's forward array and the source's reverse array each take one append;
nothing else changes. -/
theorem writeLink_refines [DecidableEq Id] (layout : SpaceLayout) (H : SplitHeap Id)
    (reader source : Id) (different : reader ≠ source) (sized : H.Sized)
    (forwardRoom : (H.forward reader).Room) (reverseRoom : (H.reverse source).Room) :
    CTriple (L := L)
      (SpaceRep addr layout reader (H.forward reader) (H.reverse reader) ∗
        SpaceRep addr layout source (H.forward source) (H.reverse source))
      (writeLinkProg addr layout reader source)
      (fun _ σ => ∃ H', OrderedDependencyCArray.writeLink H reader source = some H' ∧
        (SpaceRep addr layout reader (H'.forward reader) (H'.reverse reader) ∗
          SpaceRep addr layout source (H'.forward source) (H'.reverse source)) σ) := by
  unfold writeLinkProg
  simp only [Prog.bind_eq]
  set readerReverse := CountedArray (L := L) addr (addr reader + layout.importers)
    (addr reader + layout.importerCount) (addr reader + layout.importerCap) (H.reverse reader)
  set sourceForward := CountedArray (L := L) addr (addr source + layout.deps)
    (addr source + layout.depCount) (addr source + layout.depCap) (H.forward source)
  set sourceReverse := CountedArray (L := L) addr (addr source + layout.importers)
    (addr source + layout.importerCount) (addr source + layout.importerCap) (H.reverse source)
  have first := frame (postIndexStore_refines (L := L) addr (addr reader + layout.deps)
    (addr reader + layout.depCount) (addr reader + layout.depCap) (H.forward reader) source
    (sized.1 reader) forwardRoom) (readerReverse ∗ (sourceForward ∗ sourceReverse))
  refine triple_bind _ (triple_pre _ (fun σ holds => ?_) first) fun _ => ?_
  · rwa [SpaceRep, SpaceRep, sepConj_assoc] at holds
  refine triple_pre _ (P := fun σ => ∃ A', PostIndex.store (H.forward reader) source = some A' ∧
      (CountedArray addr (addr reader + layout.deps) (addr reader + layout.depCount)
        (addr reader + layout.depCap) A' ∗ (readerReverse ∗ (sourceForward ∗ sourceReverse))) σ)
    (fun σ holds => ?_) ?_
  · obtain ⟨x, y, separate, rfl, ⟨A', stored, holdsX⟩, holdsY⟩ := holds
    exact ⟨A', stored, x, y, separate, rfl, holdsX, holdsY⟩
  apply triple_exists
  intro A'
  apply triple_pure
  intro storedForward
  have second := frame_left (frame_left (frame_left (postIndexStore_refines (L := L) addr
    (addr source + layout.importers) (addr source + layout.importerCount)
    (addr source + layout.importerCap) (H.reverse source) reader (sized.2 source) reverseRoom)
    sourceForward) readerReverse)
    (CountedArray addr (addr reader + layout.deps) (addr reader + layout.depCount)
      (addr reader + layout.depCap) A')
  refine triple_post _ second ?_
  rintro _ σ ⟨x₁, y₁, separate₁, rfl, holds₁, x₂, y₂, separate₂, rfl, holds₂, x₃, y₃,
    separate₃, rfl, holds₃, A'', storedReverse, holds₄⟩
  refine ⟨⟨Function.update H.forward reader A', Function.update H.reverse source A''⟩, ?_, ?_⟩
  · simp [OrderedDependencyCArray.writeLink, storedForward, storedReverse]
  · simp only [Function.update_self, Function.update_of_ne different,
      Function.update_of_ne (Ne.symm different)]
    rw [SpaceRep, SpaceRep, sepConj_assoc]
    exact ⟨x₁, _, separate₁, rfl, holds₁, x₂, _, separate₂, rfl, holds₂, x₃, y₃, separate₃,
      rfl, holds₃, holds₄⟩

/-! ## The publisher loop -/

/-- The publisher loop, over the pending identities. -/
def publishProg (layout : SpaceLayout) (reader : Id) (pending : List Id) : CProg CVal Unit :=
  Prog.foldList (fun _ source => writeLinkProg addr layout reader source) pending ()

/-- Two members of a store, taken out of its representation. -/
theorem storeRep_split [DecidableEq Id] (layout : SpaceLayout) {D : List Id} (H : SplitHeap Id)
    {reader source : Id} (readerIn : reader ∈ D) (sourceIn : source ∈ D)
    (different : reader ≠ source) :
    StoreRep (L := L) addr layout D H =
      ((SpaceRep addr layout reader (H.forward reader) (H.reverse reader) ∗
        SpaceRep addr layout source (H.forward source) (H.reverse source)) ∗
          StoreRep addr layout ((D.erase reader).erase source) H) := by
  have perm : D.Perm (reader :: source :: (D.erase reader).erase source) :=
    (List.perm_cons_erase readerIn).trans (List.Perm.cons _
      (List.perm_cons_erase ((List.mem_erase_of_ne (Ne.symm different)).mpr sourceIn)))
  rw [StoreRep, bigSep_perm (perm.map _), List.map_cons, List.map_cons, bigSep_cons, bigSep_cons,
    ← sepConj_assoc]
  rfl

/-- The representation of a store depends only on its members' arrays. -/
theorem storeRep_congr (layout : SpaceLayout) {D : List Id} {H H' : SplitHeap Id}
    (same : ∀ i ∈ D, H'.forward i = H.forward i ∧ H'.reverse i = H.reverse i) :
    StoreRep (L := L) addr layout D H' = StoreRep addr layout D H := by
  unfold StoreRep
  congr 1
  exact List.map_congr_left fun i member => by rw [(same i member).1, (same i member).2]

/-- **The publisher loop on block memory refines Co5's `writeBatch`.**  The
reader and the pending identities are members of the store, the reader is not
pending (the C preparation rejects `dependency == importer`), and the split
heap is `Ready`. -/
theorem publish_refines [DecidableEq Id] (layout : SpaceLayout) {D : List Id}
    (distinct : D.Nodup) {reader : Id} (readerIn : reader ∈ D) :
    ∀ (pending : List Id) (H : SplitHeap Id), (∀ s ∈ pending, s ∈ D) → reader ∉ pending →
      OrderedDependencyCArray.Ready H reader pending →
      CTriple (L := L) (StoreRep addr layout D H) (publishProg addr layout reader pending)
        (fun _ σ => ∃ H', OrderedDependencyCArray.writeBatch H reader pending = some H' ∧
          StoreRep addr layout D H' σ) := by
  intro pending
  induction pending with
  | nil =>
    intro H _ _ _
    refine triple_pre _ ?_ (triple_ret _ () _)
    intro σ holds
    exact ⟨H, rfl, holds⟩
  | cons source rest ih =>
    intro H pendingIn notSelf ready
    have sourceIn := pendingIn source List.mem_cons_self
    have different : reader ≠ source := fun same => notSelf (same ▸ List.mem_cons_self)
    have forwardRoom : (H.forward reader).Room := by
      have capacity := ready.2.2.1
      simp only [List.length_cons] at capacity
      change (H.forward reader).count.toNat < (H.forward reader).slots.length
      omega
    have reverseRoom := ready.2.2.2 source List.mem_cons_self
    unfold publishProg
    rw [Prog.foldList, storeRep_split addr layout H readerIn sourceIn different]
    refine triple_bind _ (frame (writeLink_refines addr layout H reader source different
      ready.1 forwardRoom reverseRoom) _) fun _ => ?_
    refine triple_pre _ (P := fun σ => ∃ H', OrderedDependencyCArray.writeLink H reader source =
        some H' ∧ StoreRep addr layout D H' σ) (fun σ holds => ?_) ?_
    · obtain ⟨x, y, separate, rfl, ⟨H', linked, holdsX⟩, holdsY⟩ := holds
      refine ⟨H', linked, ?_⟩
      obtain ⟨forward, reverse, -, -, rfl⟩ := OrderedDependencyCArray.writeLink_fields linked
      rw [storeRep_split addr layout _ readerIn sourceIn different,
        storeRep_congr addr layout (H := H)]
      · exact ⟨x, y, separate, rfl, holdsX, holdsY⟩
      · intro i member
        rw [(List.Nodup.erase reader distinct).mem_erase_iff, distinct.mem_erase_iff] at member
        exact ⟨Function.update_of_ne member.2.1 _ _, Function.update_of_ne member.1 _ _⟩
    apply triple_exists
    intro H'
    apply triple_pure
    intro linked
    refine triple_post _ (ih H' (fun s member => pendingIn s (List.mem_cons_of_mem _ member))
      (fun member => notSelf (List.mem_cons_of_mem _ member))
      (OrderedDependencyCArray.ready_after_first ready linked)) ?_
    rintro _ σ ⟨H'', batch, holds⟩
    exact ⟨H'', by simp [OrderedDependencyCArray.writeBatch, linked, batch], holds⟩

/-! ## Negative controls for the representation -/

/-- **Negative control**: two counted arrays whose pointer fields hold one
block cannot be represented separately; in particular two spaces never share a
`deps` block. -/
theorem shared_block_unsatisfiable (items count capacity items' count' capacity' p : Ptr)
    (A A' : Array32 Id) (σ : Heap L) :
    ¬ (CountedFields addr items count capacity (some p) A ∗
        CountedFields addr items' count' capacity' (some p) A') σ := by
  rintro ⟨x, y, separate, -, first, second⟩
  have headerX : (x p.block).1 = .own ⟨A.slots.length, true⟩ :=
    header_of_sepConj_right first fun _ rest => header_of_sepConj_right rest fun _ rest =>
      header_of_sepConj_right rest fun _ array => header_of_dynArray array
  have headerY : (y p.block).1 = .own ⟨A'.slots.length, true⟩ :=
    header_of_sepConj_right second fun _ rest => header_of_sepConj_right rest fun _ rest =>
      header_of_sepConj_right rest fun _ array => header_of_dynArray array
  have headers := (separate p.block).1
  rw [headerX, headerY] at headers
  exact Excl.not_separate_own _ _ headers

/-- **Negative control**: a layout whose array pointer and counter overlap has
no representation.  Distinct members of a struct do not overlap (C11
6.7.2.1p15), and the representation enforces it. -/
theorem overlapping_fields_unsatisfiable (layout : SpaceLayout)
    (overlap : layout.deps = layout.depCount) (i : Id) (forward reverse : Array32 Id)
    (σ : Heap L) : ¬ SpaceRep addr layout i forward reverse σ := by
  intro holds
  refine fact_of_sepConj_left holds fun τ counted => ?_
  obtain ⟨-, a, fields⟩ := counted
  rw [CountedFields, ← sepConj_assoc, overlap] at fields
  exact fact_of_sepConj_left fields fun τ both => pointsTo_sepConj_self_false _ _ _ τ both

end Representation

/-- **Co5's store theorem through the lift.**  From the representation of a
store whose split heap represents Co5's abstract store and is ready for the
prepared batch, the publisher on block memory ends in the representation of a
split heap that represents the published store. -/
theorem publication_realizes_store {L : Type u} [Zero L] [Add L] [SepAlgebra L]
    [CellPermission L (Option CVal)] {Entry : Type*} {size : ℕ} (addr : Fin size → Ptr)
    (layout : SpaceLayout) (state : OrderedDependencyStore.Store Entry size)
    (H : SplitHeap (Fin size)) (reader : Fin size) (sources : List (Fin size))
    (represented : OrderedDependencyCArray.Represents H state)
    (observers : OrderedDependencyStore.ObserverInvariant state)
    (ready : OrderedDependencyCArray.Ready H reader
      (OrderedDependencyBatch.collectMissing (state.members reader).deps [] sources))
    (notSelf : reader ∉
      OrderedDependencyBatch.collectMissing (state.members reader).deps [] sources) :
    CTriple (L := L) (StoreRep addr layout (List.finRange size) H)
      (publishProg addr layout reader
        (OrderedDependencyBatch.collectMissing (state.members reader).deps [] sources))
      (fun _ σ => ∃ H', OrderedDependencyCArray.Represents H'
          (OrderedDependencyBatch.publish state reader sources) ∧
        StoreRep addr layout (List.finRange size) H' σ) := by
  obtain ⟨after, batch, representsAfter⟩ :=
    OrderedDependencyCArray.prepared_publication_represents_topology state H reader sources
      represented observers ready
  refine triple_post _ (publish_refines addr layout (List.nodup_finRange size)
    (List.mem_finRange reader) _ H (fun s _ => List.mem_finRange s) notSelf ready) ?_
  rintro _ σ ⟨H', batch', holds⟩
  rw [batch] at batch'
  cases batch'
  exact ⟨after, representsAfter, holds⟩

/-- **The capacity `reserve` requests is Co5's `chosenCapacity`.** -/
theorem nextCapacity_eq_chosenCapacity {Value : Type} (required cap : UInt32)
    (before : Array32 Value) (capacity : before.slots.length = cap.toNat) :
    nextCapacity required cap = OrderedDependencyCReserve.chosenCapacity before required := by
  simp only [nextCapacity, OrderedDependencyCReserve.chosenCapacity, capacity]

end Mettapedia.Machines.CMemory.Lift
