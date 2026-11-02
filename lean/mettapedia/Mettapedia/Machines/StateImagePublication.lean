import Mettapedia.Machines.ResourceOwnership
import Mathlib.Tactic

/-!
Stable mutable cells publish independently owned immutable value/type images.
Publication allocates a fresh image and replaces the cell's current-image
edge. An old image remains observable through an explicit reader root, even
after publication and collection; an unreachable old image is reclaimable.

This is a sequential graph contract after private preparation. Native root
discovery, synchronization, allocation failure handling and correspondence
between payload references and the complete native graph remain obligations
of the runtime implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.StateImagePublication

open ResourceOwnership

inductive Address where
  | cell (identity : Nat)
  | image (identity : Nat)
  deriving DecidableEq

inductive Payload (Value TypeInfo : Type) where
  | state (current : Nat)
  | image (value : Value) (typeInfo : TypeInfo)
  deriving DecidableEq

structure Image (Value TypeInfo : Type) where
  value : Value
  typeInfo : TypeInfo
  references : Finset Address
  bytes : Nat
  deriving DecidableEq

abbrev StateHeap (Value TypeInfo : Type) := Heap Address (Payload Value TypeInfo)

variable {Value TypeInfo : Type}

def cellObject (current bytes : Nat) : Cell Address (Payload Value TypeInfo) :=
  ⟨.state current, {.image current}, bytes⟩

def imageObject (image : Image Value TypeInfo) : Cell Address (Payload Value TypeInfo) :=
  ⟨.image image.value image.typeInfo, image.references, image.bytes⟩

/-- Preparation owns complete payload data; its outgoing graph is explicit. -/
structure Prepared (heap : StateHeap Value TypeInfo) (fresh : Nat) where
  image : Image Value TypeInfo
  closed : image.references ⊆ insert (.image fresh) heap.allocated

/-- Replace a real current edge while adding its fresh destination object. -/
def publish (heap : StateHeap Value TypeInfo) (cell old fresh bytes : Nat)
    (found : heap.lookup (.cell cell) = some (cellObject old bytes))
    (_unused : Address.image fresh ∉ heap.allocated)
    (prepared : Prepared heap fresh) : StateHeap Value TypeInfo where
  lookup address :=
    if address = .image fresh then some (imageObject prepared.image)
    else if address = .cell cell then some (cellObject fresh bytes)
    else heap.lookup address
  allocated := insert (.image fresh) heap.allocated
  allocated_iff address := by
    by_cases image : address = .image fresh
    · simp [image]
    · by_cases target : address = .cell cell
      · subst address
        have allocated := (heap.allocated_iff (.cell cell)).mpr ⟨_, found⟩
        simp [allocated]
      · simpa [image, target] using heap.allocated_iff address
  closed address object present next reference := by
    by_cases image : address = .image fresh
    · simp only [image, if_pos, Option.some.injEq] at present
      subst object
      exact prepared.closed reference
    · by_cases target : address = .cell cell
      · simp [target] at present
        subst object
        have same : next = .image fresh := Finset.mem_singleton.mp reference
        exact same ▸ Finset.mem_insert_self _ _
      · simp only [image, if_false, target] at present
        exact Finset.mem_insert_of_mem (heap.closed address object present next reference)

@[simp] theorem publish_current (heap : StateHeap Value TypeInfo)
    (cell old fresh bytes : Nat) (found) (unused) (prepared : Prepared heap fresh) :
    (publish heap cell old fresh bytes found unused prepared).lookup (.cell cell) =
      some (cellObject fresh bytes) := by
  simp [publish]

@[simp] theorem publish_image (heap : StateHeap Value TypeInfo)
    (cell old fresh bytes : Nat) (found) (unused) (prepared : Prepared heap fresh) :
    (publish heap cell old fresh bytes found unused prepared).lookup (.image fresh) =
      some (imageObject prepared.image) := by
  simp [publish]

theorem publish_other (heap : StateHeap Value TypeInfo)
    (cell old fresh bytes : Nat) (found) (unused) (prepared : Prepared heap fresh)
    (address : Address) (notFresh : address ≠ .image fresh)
    (notCell : address ≠ .cell cell) :
    (publish heap cell old fresh bytes found unused prepared).lookup address =
      heap.lookup address := by
  simp [publish, notFresh, notCell]

theorem publication_allocates_one_image (heap : StateHeap Value TypeInfo)
    (cell old fresh bytes : Nat) (found) (unused) (prepared : Prepared heap fresh) :
    (publish heap cell old fresh bytes found unused prepared).allocated.card =
      heap.allocated.card + 1 := by
  simp [publish, unused]

theorem stable_cell_identities (heap : StateHeap Value TypeInfo)
    (cell old fresh bytes : Nat) (found) (unused) (prepared : Prepared heap fresh)
    (identity : Nat) :
    Address.cell identity ∈
        (publish heap cell old fresh bytes found unused prepared).allocated ↔
      Address.cell identity ∈ heap.allocated := by
  simp [publish]

def readImage (heap : StateHeap Value TypeInfo) (image : Nat) :
    Option (Value × TypeInfo) := do
  let object ← heap.lookup (.image image)
  match object.value with
  | .state _ => none
  | .image value typeInfo => some (value, typeInfo)

def readState (heap : StateHeap Value TypeInfo) (cell : Nat) :
    Option (Value × TypeInfo) := do
  let object ← heap.lookup (.cell cell)
  match object.value with
  | .state current => readImage heap current
  | .image _ _ => none

@[simp] theorem readState_publish (heap : StateHeap Value TypeInfo)
    (cell old fresh bytes : Nat) (found) (unused) (prepared : Prepared heap fresh) :
    readState (publish heap cell old fresh bytes found unused prepared) cell =
      some (prepared.image.value, prepared.image.typeInfo) := by
  simp [readState, readImage, cellObject, imageObject]

def attempt (heap : StateHeap Value TypeInfo) (cell old fresh bytes : Nat)
    (found : heap.lookup (.cell cell) = some (cellObject old bytes))
    (unused : Address.image fresh ∉ heap.allocated)
    (prepared : Option (Prepared heap fresh)) : StateHeap Value TypeInfo :=
  match prepared with
  | none => heap
  | some image => publish heap cell old fresh bytes found unused image

@[simp] theorem preparation_failure (heap : StateHeap Value TypeInfo)
    (cell old fresh bytes : Nat) (found) (unused) :
    attempt heap cell old fresh bytes found unused none = heap := rfl

theorem old_image_allocated (heap : StateHeap Value TypeInfo)
    (cell old bytes : Nat)
    (found : heap.lookup (.cell cell) = some (cellObject old bytes)) :
    Address.image old ∈ heap.allocated :=
  heap.closed _ _ found _ (Finset.mem_singleton_self _)

theorem fresh_ne_old (heap : StateHeap Value TypeInfo)
    (cell old fresh bytes : Nat)
    (found : heap.lookup (.cell cell) = some (cellObject old bytes))
    (unused : Address.image fresh ∉ heap.allocated) : fresh ≠ old := by
  intro same
  subst fresh
  exact unused (old_image_allocated heap cell old bytes found)

theorem old_image_unchanged (heap : StateHeap Value TypeInfo)
    (cell old fresh bytes : Nat) (found) (unused) (prepared : Prepared heap fresh) :
    (publish heap cell old fresh bytes found unused prepared).lookup (.image old) =
      heap.lookup (.image old) := by
  apply publish_other
  · exact fun same => fresh_ne_old heap cell old fresh bytes found unused
      (Address.image.inj same).symm
  · simp

/-- Readers may retain versions older than the cell's immediately previous
image. Every already allocated image has the same protection law. -/
theorem retained_image_unchanged (heap : StateHeap Value TypeInfo)
    (cell old fresh bytes : Nat) (found) (unused) (prepared : Prepared heap fresh)
    (image : Nat) (allocated : Address.image image ∈ heap.allocated) :
    (publish heap cell old fresh bytes found unused prepared).lookup (.image image) =
      heap.lookup (.image image) := by
  apply publish_other
  · intro same
    exact unused (same ▸ allocated)
  · simp

theorem retained_image_observation (heap : StateHeap Value TypeInfo)
    (cell old fresh bytes : Nat) (found) (unused) (prepared : Prepared heap fresh)
    (image : Nat) (allocated : Address.image image ∈ heap.allocated)
    (roots : Roots Nat Address) (reader : Nat)
    (retained : (reader, Address.image image) ∈ roots) :
    readImage (collect (publish heap cell old fresh bytes found unused prepared) roots)
      image = readImage heap image := by
  have live := live_of_root
    (publish heap cell old fresh bytes found unused prepared) roots retained
    (Finset.mem_insert_of_mem allocated)
  unfold readImage
  rw [lookup_collect_of_live _ roots live,
    retained_image_unchanged heap cell old fresh bytes found unused prepared image allocated]

theorem reader_preserves_old_image (heap : StateHeap Value TypeInfo)
    (cell old fresh bytes : Nat) (found) (unused) (prepared : Prepared heap fresh)
    (roots : Roots Nat Address) (reader : Nat)
    (retained : (reader, Address.image old) ∈ roots) :
    (collect (publish heap cell old fresh bytes found unused prepared) roots).lookup
      (.image old) = heap.lookup (.image old) := by
  rw [lookup_collect_of_live]
  · exact old_image_unchanged heap cell old fresh bytes found unused prepared
  · exact live_of_root _ roots retained
      (Finset.mem_insert_of_mem (old_image_allocated heap cell old bytes found))

theorem reader_observation_preserved (heap : StateHeap Value TypeInfo)
    (cell old fresh bytes : Nat) (found) (unused) (prepared : Prepared heap fresh)
    (roots : Roots Nat Address) (reader : Nat)
    (retained : (reader, Address.image old) ∈ roots) :
    readImage (collect (publish heap cell old fresh bytes found unused prepared) roots)
      old = readImage heap old := by
  simp only [readImage,
    reader_preserves_old_image heap cell old fresh bytes found unused prepared roots reader retained]

theorem rooted_current_observation (heap : StateHeap Value TypeInfo)
    (cell old fresh bytes : Nat) (found) (unused) (prepared : Prepared heap fresh)
    (roots : Roots Nat Address) (owner : Nat)
    (retained : (owner, Address.cell cell) ∈ roots) :
    readState (collect (publish heap cell old fresh bytes found unused prepared) roots)
      cell = some (prepared.image.value, prepared.image.typeInfo) := by
  let updated := publish heap cell old fresh bytes found unused prepared
  have liveCell : Live updated roots (.cell cell) :=
    live_of_root updated roots retained
      (Finset.mem_insert_of_mem ((heap.allocated_iff _).mpr ⟨_, found⟩))
  have liveImage : Live updated roots (.image fresh) :=
    live_step updated roots liveCell
      (publish_current heap cell old fresh bytes found unused prepared)
      (Finset.mem_singleton_self _)
  have cellLookup : (collect updated roots).lookup (.cell cell) =
      some (cellObject fresh bytes) :=
    (lookup_collect_of_live updated roots liveCell).trans
      (publish_current heap cell old fresh bytes found unused prepared)
  have imageLookup : (collect updated roots).lookup (.image fresh) =
      some (imageObject prepared.image) :=
    (lookup_collect_of_live updated roots liveImage).trans
      (publish_image heap cell old fresh bytes found unused prepared)
  change readState (collect updated roots) cell = _
  simp [readState, cellLookup, readImage, imageLookup, cellObject, imageObject]

theorem unreachable_old_image_reclaimed (heap : StateHeap Value TypeInfo)
    (cell old fresh bytes : Nat) (found) (unused) (prepared : Prepared heap fresh)
    (roots : Roots Nat Address)
    (unreachable : ¬ Live (publish heap cell old fresh bytes found unused prepared)
      roots (.image old)) :
    (collect (publish heap cell old fresh bytes found unused prepared) roots).lookup
      (.image old) = none :=
  lookup_collect_of_not_live _ roots unreachable

namespace Controls

def original : StateHeap Nat Nat where
  lookup address :=
    if address = .cell 0 then some (cellObject 0 32)
    else if address = .image 0 then some (imageObject ⟨17, 1, ∅, 80⟩)
    else none
  allocated := {.cell 0, .image 0}
  allocated_iff address := by
    by_cases cell : address = .cell 0
    · simp [cell]
    · by_cases image : address = .image 0
      · simp [image]
      · simp [cell, image]
  closed address object present next reference := by
    split at present
    · cases Option.some.inj present
      have same : next = .image 0 := Finset.mem_singleton.mp reference
      subst next
      simp
    · split at present
      · cases Option.some.inj present
        simp [imageObject] at reference
      · cases present

def freshValue : Prepared original 1 :=
  ⟨⟨23, 1, ∅, 120⟩, by simp⟩

def updated : StateHeap Nat Nat :=
  publish original 0 0 1 32 rfl (by decide) freshValue

def cellRoot : Roots Nat Address := {(0, .cell 0)}

def withReader : Roots Nat Address := cellRoot ∪ {(1, .image 0)}

theorem cellRoot_valid (heap : StateHeap Nat Nat)
    (allocated : Address.cell 0 ∈ heap.allocated) : ValidRoots heap cellRoot := by
  intro pair member
  have same : pair = (0, Address.cell 0) := by simpa [cellRoot] using member
  subst pair
  exact allocated

example : readState original 0 = some (17, 1) ∧
    readState updated 0 = some (23, 1) ∧
    updated.lookup (.image 0) = original.lookup (.image 0) := by decide

example : updated.allocated.card = original.allocated.card + 1 := by decide

theorem without_reader_old_is_garbage : ¬ Live updated cellRoot (.image 0) := by
  intro live
  have absent : Address.image 0 ∉ census updated cellRoot := by decide
  exact absent ((mem_census_iff_live updated cellRoot
    (cellRoot_valid updated (by decide)) _).mpr live)

theorem without_reader_old_is_removed :
    (collect updated cellRoot).lookup (.image 0) = none :=
  lookup_collect_of_not_live updated cellRoot without_reader_old_is_garbage

example : readState (collect updated cellRoot) 0 = some (23, 1) := by
  exact rooted_current_observation original 0 0 1 32 rfl (by decide)
    freshValue cellRoot 0 (by decide)

theorem retained_reader_sees_old_snapshot :
    readImage (collect updated withReader) 0 = some (17, 1) := by
  calc
    readImage (collect updated withReader) 0 = readImage original 0 :=
      reader_observation_preserved original 0 0 1 32 rfl (by decide)
        freshValue withReader 1 (by decide)
    _ = some (17, 1) := rfl

example : readState (collect updated withReader) 0 = some (23, 1) := by
  exact rooted_current_observation original 0 0 1 32 rfl (by decide)
    freshValue withReader 0 (by decide)

/-- A value may itself retain the previous image: absence of a reader alone
does not make that image unreachable. -/
def retainingValue : Prepared original 1 :=
  ⟨⟨23, 1, {.image 0}, 120⟩, by decide⟩

def retainingUpdate : StateHeap Nat Nat :=
  publish original 0 0 1 32 rfl (by decide) retainingValue

example : readImage (collect retainingUpdate cellRoot) 0 = some (17, 1) := by
  have live : Live retainingUpdate cellRoot (.image 0) :=
    (mem_census_iff_live retainingUpdate cellRoot
      (cellRoot_valid retainingUpdate (by decide)) _).mp (by decide)
  unfold readImage
  rw [lookup_collect_of_live retainingUpdate cellRoot live]
  rfl

/-- Reusing the old image as mutable storage changes a retained reader's
answer, despite preserving the cell's address and current-image edge. -/
def overwriteOldImage : StateHeap Nat Nat :=
  original.writePayload (.image 0) (.image 23 1)

example : readImage overwriteOldImage 0 = some (23, 1) ∧
    readImage overwriteOldImage 0 ≠ readImage original 0 := by decide

example : readState (attempt original 0 0 1 32 rfl (by decide) none) 0 =
    some (17, 1) := by decide

end Controls

#print axioms publication_allocates_one_image
#print axioms stable_cell_identities
#print axioms readState_publish
#print axioms reader_observation_preserved
#print axioms retained_image_observation
#print axioms rooted_current_observation
#print axioms preparation_failure
#print axioms unreachable_old_image_reclaimed
#print axioms Controls.without_reader_old_is_removed
#print axioms Controls.retained_reader_sees_old_snapshot

end Mettapedia.Machines.StateImagePublication
