import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic
import Mettapedia.GSLT.Core.BindingStoreCapabilityAlgebra
import Mettapedia.Languages.MeTTa.SubstitutionAlgebra

/-!
# Versioned MeTTa bindings and copy-on-escape

This module supplies one concrete realization of the strategy-independent
binding-store interfaces in `BindingStoreCapabilityAlgebra`.

The authoritative object is a logical substitution.  Two physical forms
refine it:

* `Version` is an immutable parent-plus-update graph.  Equal parents may be
  shared, so independently live branches need not copy their common prefix.
* `ExclusiveRegion` holds one checkpoint and a chronological local delta.  It
  is useful while one continuation has exclusive ownership.  `freeze` promotes
  it to a `Version` exactly when the continuation escapes to a shared frontier
  or another worker.
* `CowSnapshot` is an ownership-state model for one bounded flat-array
  candidate: a first capture may share, and a write or later capture pays for
  detachment.  It proves the denotational boundary and exposes an abstract
  work equation; it neither asserts runtime admission nor gives a byte-level
  refinement proof of a C implementation.

No traversal order appears in these definitions.  A depth-first controller may
keep an exclusive region for a long quantum; FIFO, fair, learned, and parallel
controllers may promote earlier.  The same denotation laws govern both.

Disjunctive answers remain distinct versions.  `combineIndependent` is
provided only for an explicit conjunction or reconciliation boundary whose
substitutions have been proved independent; bag-valued choice does not require
or imply a merge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.BindingVersions

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra
open Mettapedia.GSLT.Core.BindingStoreCapabilityAlgebra
open Mettapedia.GSLT.Core.BranchCaptureAlgebra

/-! ## Logical updates -/

/-- One authored binding update. -/
@[ext] structure BindingUpdate where
  key : Var
  value : Atom

/-- The logical meaning of one update.  Newer bindings shadow older ones. -/
def logicalWrite (environment : Subst) (update : BindingUpdate) : Subst :=
  Function.update environment update.key (some update.value)

@[simp] theorem logicalWrite_same (environment : Subst)
    (update : BindingUpdate) :
    logicalWrite environment update update.key = some update.value := by
  simp [logicalWrite]

theorem logicalWrite_other (environment : Subst) (update : BindingUpdate)
    (key : Var) (different : key ≠ update.key) :
    logicalWrite environment update key = environment key := by
  simp [logicalWrite, different]

/-! ## Immutable parent-plus-update versions -/

/-- A persistent binding version.  The constructor stores only the new edge;
the parent may be physically shared by arbitrarily many descendants. -/
inductive Version where
  | root (base : Subst)
  | extend (parent : Version) (update : BindingUpdate)

namespace Version

/-- Authoritative substitution denoted by a version. -/
def denote : Version → Subst
  | .root base => base
  | .extend parent update => logicalWrite parent.denote update

@[simp] theorem denote_root (base : Subst) :
    denote (.root base) = base := rfl

@[simp] theorem denote_extend (parent : Version) (update : BindingUpdate) :
    denote (.extend parent update) = logicalWrite parent.denote update := rfl

end Version

/-- The immutable version graph is a physical realization of logical writes. -/
def versionStore : BindingStore Subst Version BindingUpdate where
  denote := Version.denote
  logicalWrite := logicalWrite
  write := Version.extend
  write_exact _ _ := rfl

/-- Logical update paths compose by concatenation. -/
theorem logicalWriteMany_append
    (store : BindingStore Subst Version BindingUpdate)
    (environment : Subst) (first second : List BindingUpdate) :
    store.logicalWriteMany environment (first ++ second) =
      store.logicalWriteMany
        (store.logicalWriteMany environment first) second := by
  induction first generalizing environment with
  | nil => rfl
  | cons update rest inductionHypothesis =>
      simp only [List.cons_append, BindingStore.logicalWriteMany]
      exact inductionHypothesis (store.logicalWrite environment update)

/-- Forking an immutable version shares the parent.  Subsequent writes create
distinct child nodes, so both returned handles remain independently usable. -/
def versionForkable : ForkableStore Subst Version Unit BindingUpdate where
  toBindingStore := versionStore
  fork version _ := (version, version)
  fork_left_exact _ _ := rfl
  fork_right_exact _ _ := rfl

/-- Updating one fork changes its denotation while the sibling retains the
fork-point denotation. -/
theorem fork_write_left_keep_right_exact
    (version : Version) (update : BindingUpdate) :
    versionForkable.denote
        (versionForkable.write (versionForkable.fork version ()).1 update) =
        logicalWrite (Version.denote version) update ∧
      versionForkable.denote (versionForkable.fork version ()).2 =
        Version.denote version :=
  versionForkable.write_left_keep_right_exact version () update

/-! ## One exclusive region and promotion on escape -/

/-- A continuation-local binding region.  `pending` is chronological: it
records exactly the writes after `checkpoint`. -/
structure ExclusiveRegion where
  checkpoint : Version
  pending : List BindingUpdate

namespace ExclusiveRegion

/-- The logical meaning of a local region, without constructing its frozen
version graph. -/
def denote (region : ExclusiveRegion) : Subst :=
  versionStore.logicalWriteMany region.checkpoint.denote region.pending

/-- Record one local update.  This reference list uses append to expose the
chronological law; a production region may use a reverse log or chunked tail. -/
def write (region : ExclusiveRegion) (update : BindingUpdate) : ExclusiveRegion :=
  { region with pending := region.pending ++ [update] }

theorem denote_write (region : ExclusiveRegion) (update : BindingUpdate) :
    denote (write region update) = logicalWrite (denote region) update := by
  rw [denote, write, logicalWriteMany_append]
  rfl

/-- Materialize the pending path as immutable version edges when ownership
escapes the current continuation. -/
def freeze (region : ExclusiveRegion) : Version :=
  versionStore.writeMany region.checkpoint region.pending

/-- Promotion preserves the authoritative logical substitution exactly. -/
theorem freeze_exact (region : ExclusiveRegion) :
    Version.denote region.freeze = region.denote := by
  exact versionStore.writeMany_exact region.checkpoint region.pending

/-- Enter a new exclusive quantum at an already shared version. -/
def thaw (version : Version) : ExclusiveRegion :=
  { checkpoint := version, pending := [] }

@[simp] theorem denote_thaw (version : Version) :
    (thaw version).denote = version.denote := rfl

@[simp] theorem freeze_thaw (version : Version) :
    (thaw version).freeze = version := rfl

/-- Local regions themselves satisfy the generic binding-store refinement
law. -/
def store : BindingStore Subst ExclusiveRegion BindingUpdate where
  denote := denote
  logicalWrite := logicalWrite
  write := write
  write_exact := denote_write

end ExclusiveRegion

/-! ## A provider image that promotes only when required -/

/-- Physical binding state carried by a continuation provider. -/
inductive Image where
  /-- One continuation owns this region exclusively. -/
  | exclusive (region : ExclusiveRegion)
  /-- The image may coexist with independently live siblings. -/
  | shared (version : Version)

namespace Image

def denote : Image → Subst
  | .exclusive region => region.denote
  | .shared version => version.denote

def write : Image → BindingUpdate → Image
  | .exclusive region, update => .exclusive (region.write update)
  | .shared version, update => .shared (.extend version update)

/-- Promote an exclusive local region before it enters an owned multi-shot
frontier.  Shared images require no further conversion. -/
def escape : Image → Image
  | .exclusive region => .shared region.freeze
  | image@(.shared _) => image

/-- Storage capability belongs to the current image, not to a traversal
policy. -/
def capacity : Image → CaptureCapacity
  | .exclusive _ => .oneShot
  | .shared _ => .multiShot

end Image

/-- Both image forms refine the same logical binding store. -/
def imageStore : BindingStore Subst Image BindingUpdate where
  denote := Image.denote
  logicalWrite := logicalWrite
  write := Image.write
  write_exact := by
    intro image update
    cases image with
    | exclusive region => exact region.denote_write update
    | shared version => rfl

/-- Escape changes ownership representation but never logical bindings. -/
theorem escape_exact (image : Image) :
    Image.denote image.escape = Image.denote image := by
  cases image with
  | exclusive region => exact region.freeze_exact
  | shared _ => rfl

/-- Promotion is idempotent, so repeated scheduler or worker boundaries do
not rebuild an already shared image. -/
@[simp] theorem escape_idempotent (image : Image) :
    image.escape.escape = image.escape := by
  cases image <;> rfl

/-- Updating after promotion has the same logical result as updating before
promotion.  The theorem deliberately claims denotational, not physical,
equality. -/
theorem escape_write_exact (image : Image) (update : BindingUpdate) :
    Image.denote (Image.write image.escape update) =
      Image.denote (Image.write image update) := by
  change imageStore.denote (imageStore.write image.escape update) =
    imageStore.denote (imageStore.write image update)
  calc
    _ = imageStore.logicalWrite (imageStore.denote image.escape) update :=
      imageStore.write_exact image.escape update
    _ = imageStore.logicalWrite (imageStore.denote image) update := by
      rw [show imageStore.denote image.escape = imageStore.denote image by
        exact escape_exact image]
    _ = _ := (imageStore.write_exact image update).symm

/-- An exclusive image supplies exactly the one-shot capacity required by an
exclusive continuation quantum. -/
theorem exclusive_admits_oneShot (region : ExclusiveRegion) :
    Admitted (Image.capacity (.exclusive region)) .exclusiveOneShot := by
  change Admitted .oneShot .exclusiveOneShot
  decide

/-- The same image cannot be published directly as an owned multi-shot
frontier entry. -/
theorem exclusive_rejects_multiShot (region : ExclusiveRegion) :
    ¬ Admitted (Image.capacity (.exclusive region)) .ownedMultiShot := by
  change ¬ Admitted .oneShot .ownedMultiShot
  decide

/-- Escaping an exclusive image supplies the multi-shot capacity required by
the common continuation frontier. -/
theorem escape_admits_multiShot (image : Image) :
    Admitted (Image.capacity image.escape) .ownedMultiShot := by
  cases image <;> change Admitted .multiShot .ownedMultiShot <;> decide

/-! ## Direct observation and explicit combination -/

/-- Variable lookup can inspect a version directly and return the same
physical image; it need not materialize a substituted term. -/
def lookupObservation :
    BindingObservation imageStore Var (Option Atom) where
  observeLogical environment key := environment key
  observe image key := (Image.denote image key, image)
  result_exact _ _ := rfl
  state_preserved _ _ := rfl

theorem lookup_after_writes_exact
    (image : Image) (updates : List BindingUpdate) (key : Var) :
    (lookupObservation.observe
      (imageStore.writeMany image updates) key).1 =
      imageStore.logicalWriteMany (Image.denote image) updates key :=
  lookupObservation.observe_writeMany_result_exact image updates key

/-! ## Bounded copy-on-write snapshots

`Version` above is the fully persistent reference realization.  A flat runtime
can instead share one immutable snapshot with one captured image, detach on a
write, and copy a later capture when the source snapshot is already paired.
The following model states that realization separately, so its favorable
capture cost is not confused with the parent-edge cost of `Version`.
-/

/-- Whether a flat snapshot has an exclusive array or shares it with one
independently live image. -/
inductive CowOwnership where
  | unique
  | paired
deriving DecidableEq, Repr

/-- An abstract flat binding array.  `checkpoint` represents the array prefix
and `pending` the updates accumulated since that prefix was established. -/
structure CowSnapshot where
  checkpoint : Subst
  pending : List BindingUpdate
  ownership : CowOwnership

namespace CowSnapshot

/-- Logical substitution represented by a flat snapshot. -/
def denote (snapshot : CowSnapshot) : Subst :=
  versionStore.logicalWriteMany snapshot.checkpoint snapshot.pending

/-- Copy-on-write update.  An exclusive array extends locally; a paired array
first establishes the current denotation as its new private checkpoint. -/
def write (snapshot : CowSnapshot) (update : BindingUpdate) : CowSnapshot :=
  match snapshot.ownership with
  | .unique => { snapshot with pending := snapshot.pending ++ [update] }
  | .paired =>
      { checkpoint := snapshot.denote
        pending := [update]
        ownership := .unique }

/-- Capture returns the still-live source image and an independently writable
child.  The first capture pairs the physical array.  A later capture from an
already paired source is represented by a private copied child. -/
def capture (snapshot : CowSnapshot) : CowSnapshot × CowSnapshot :=
  match snapshot.ownership with
  | .unique =>
      ({ snapshot with ownership := .paired },
       { snapshot with ownership := .paired })
  | .paired =>
      (snapshot, { snapshot with ownership := .unique })

theorem denote_write (snapshot : CowSnapshot) (update : BindingUpdate) :
    (write snapshot update).denote =
      logicalWrite snapshot.denote update := by
  cases snapshot with
  | mk checkpoint pending ownership =>
      cases ownership with
      | unique =>
          simp only [write, denote]
          rw [logicalWriteMany_append]
          rfl
      | paired => rfl

theorem capture_left_exact (snapshot : CowSnapshot) :
    snapshot.capture.1.denote = snapshot.denote := by
  cases snapshot with
  | mk checkpoint pending ownership => cases ownership <;> rfl

theorem capture_right_exact (snapshot : CowSnapshot) :
    snapshot.capture.2.denote = snapshot.denote := by
  cases snapshot with
  | mk checkpoint pending ownership => cases ownership <;> rfl

end CowSnapshot

/-- The copy-on-write snapshot implements the same binding-store interface as
the persistent version graph. -/
def cowStore : BindingStore Subst CowSnapshot BindingUpdate where
  denote := CowSnapshot.denote
  logicalWrite := logicalWrite
  write := CowSnapshot.write
  write_exact := CowSnapshot.denote_write

/-- Copy-on-write capture is a forkable store even though the two physical
routes differ: sharing when unique, copying when already paired. -/
def cowForkable : ForkableStore Subst CowSnapshot Unit BindingUpdate where
  toBindingStore := cowStore
  fork snapshot _ := snapshot.capture
  fork_left_exact snapshot _ := snapshot.capture_left_exact
  fork_right_exact snapshot _ := snapshot.capture_right_exact

theorem cow_fork_write_left_keep_right_exact
    (snapshot : CowSnapshot) (update : BindingUpdate) :
    cowForkable.denote
        (cowForkable.write (cowForkable.fork snapshot ()).1 update) =
        logicalWrite snapshot.denote update ∧
      cowForkable.denote (cowForkable.fork snapshot ()).2 =
        snapshot.denote :=
  cowForkable.write_left_keep_right_exact snapshot () update

/-! ### Honest abstract work bounds

The input `footprint` denotes the number of flat slots that a full snapshot
copy would visit.  These abstract work units deliberately expose both sides of
copy-on-write: the first capture is constant work, while a write through a
paired image must copy the footprint before applying its update.  A native
receipt bridge is still required before equating these units with operations
or time in a concrete runtime.
-/

def cowCaptureWork (footprint : Nat) (ownership : CowOwnership) : Nat :=
  match ownership with
  | .unique => 1
  | .paired => footprint

def cowWriteWork (footprint : Nat) (ownership : CowOwnership) : Nat :=
  match ownership with
  | .unique => 1
  | .paired => footprint + 1

def eagerCaptureWork (footprint : Nat) : Nat := footprint

theorem unique_capture_lt_eager (footprint : Nat) (nontrivial : 1 < footprint) :
    cowCaptureWork footprint .unique < eagerCaptureWork footprint := by
  simpa [cowCaptureWork, eagerCaptureWork]

theorem paired_capture_eq_eager (footprint : Nat) :
    cowCaptureWork footprint .paired = eagerCaptureWork footprint := rfl

theorem paired_write_cost_eq_detach_then_write (footprint : Nat) :
    cowWriteWork footprint .paired = eagerCaptureWork footprint + 1 := rfl

theorem unique_write_lt_paired_write (footprint : Nat) (positive : 0 < footprint) :
    cowWriteWork footprint .unique < cowWriteWork footprint .paired := by
  simp [cowWriteWork, positive]

/-- Explicitly combine independent substitutions.  This operation belongs to
a conjunction or reconciliation boundary; ordinary choice retains both
arguments as separate answers. -/
def combineIndependent (left right : Subst) : Subst := comp left right

theorem combineIndependent_comm (left right : Subst)
    (independent : Independent left right) :
    combineIndependent left right = combineIndependent right left :=
  comp_comm_of_disjoint left right independent

/-! ## A small, explicit promotion cost model -/

/-- Work charged to publishing only the local delta. -/
def deltaPromotionWork (region : ExclusiveRegion) : Nat :=
  region.pending.length

/-- Reference work for eagerly copying a complete binding image at the same
boundary.  `sharedFootprint` is a measured input, not inferred by this model. -/
def eagerSnapshotWork (sharedFootprint : Nat)
    (region : ExclusiveRegion) : Nat :=
  sharedFootprint + region.pending.length

theorem deltaPromotionWork_le_eagerSnapshotWork
    (sharedFootprint : Nat) (region : ExclusiveRegion) :
    deltaPromotionWork region ≤ eagerSnapshotWork sharedFootprint region := by
  simp [deltaPromotionWork, eagerSnapshotWork]

theorem deltaPromotionWork_lt_eagerSnapshotWork
    (sharedFootprint : Nat) (region : ExclusiveRegion)
    (positive : 0 < sharedFootprint) :
    deltaPromotionWork region < eagerSnapshotWork sharedFootprint region := by
  simp [deltaPromotionWork, eagerSnapshotWork, positive]

/-! ## Positive and negative controls -/

namespace Canaries

def emptyVersion : Version :=
  .root Mettapedia.Languages.MeTTa.SubstitutionAlgebra.empty

def bindX : BindingUpdate :=
  { key := "x", value := .symbol "left" }

def bindY : BindingUpdate :=
  { key := "y", value := .symbol "right" }

def localTwo : ExclusiveRegion :=
  (ExclusiveRegion.thaw emptyVersion).write bindX |>.write bindY

/-- Positive: publishing a two-edge local delta preserves both bindings. -/
theorem freeze_two_exact :
    localTwo.freeze.denote "x" = some (.symbol "left") ∧
      localTwo.freeze.denote "y" = some (.symbol "right") := by
  rw [ExclusiveRegion.freeze_exact]
  simp [localTwo, bindX, bindY, ExclusiveRegion.denote,
    ExclusiveRegion.write, ExclusiveRegion.thaw, emptyVersion,
    versionStore, BindingStore.logicalWriteMany, logicalWrite]

/-- Positive: a forked sibling remains at the shared parent when the other
sibling receives a write. -/
theorem forked_sibling_is_unchanged :
    let forks := versionForkable.fork emptyVersion ()
    Version.denote (versionForkable.write forks.1 bindX) "x" =
        some (.symbol "left") ∧
      Version.denote forks.2 "x" = none := by
  simp [versionForkable, emptyVersion, bindX, versionStore,
    Version.denote, logicalWrite,
    Mettapedia.Languages.MeTTa.SubstitutionAlgebra.empty]

/-- Positive: direct observation after promotion sees the same logical value
as observation before promotion. -/
theorem lookup_survives_escape :
    (lookupObservation.observe (Image.exclusive localTwo) "y").1 =
      (lookupObservation.observe
        (Image.escape (Image.exclusive localTwo)) "y").1 := by
  change Image.denote (Image.exclusive localTwo) "y" =
    Image.denote (Image.escape (Image.exclusive localTwo)) "y"
  rw [escape_exact]

/-- Negative: the two branch endpoints are not one merged answer. -/
theorem distinct_branches_remain_distinct :
    Version.denote (.extend emptyVersion bindX) "x" ≠
      Version.denote (.extend emptyVersion bindY) "x" := by
  simp [emptyVersion, bindX, bindY, Version.denote, logicalWrite,
    Mettapedia.Languages.MeTTa.SubstitutionAlgebra.empty]

def emptyCow : CowSnapshot :=
  { checkpoint := Mettapedia.Languages.MeTTa.SubstitutionAlgebra.empty
    pending := []
    ownership := .unique }

/-- Positive: the copy-on-write realization can capture and then mutate one
image without changing the sibling's logical substitution. -/
theorem cow_capture_write_keeps_sibling :
    let images := emptyCow.capture
    (CowSnapshot.write images.1 bindX).denote "x" =
        some (.symbol "left") ∧
      images.2.denote "x" = none := by
  simp [emptyCow, CowSnapshot.capture, CowSnapshot.write,
    CowSnapshot.denote, bindX, versionStore,
    BindingStore.logicalWriteMany, logicalWrite,
    Mettapedia.Languages.MeTTa.SubstitutionAlgebra.empty]

/-- An intentionally invalid aliased write changes both handles.  This
negative control witnesses why a paired flat image must detach before write. -/
def aliasedWritePair (snapshot : CowSnapshot) (update : BindingUpdate) :
    CowSnapshot × CowSnapshot :=
  let changed := CowSnapshot.write snapshot update
  (changed, changed)

theorem aliased_write_does_not_preserve_sibling :
    (aliasedWritePair emptyCow bindX).2.denote "x" ≠
      emptyCow.denote "x" := by
  simp [aliasedWritePair, emptyCow, CowSnapshot.write,
    CowSnapshot.denote, bindX, versionStore,
    BindingStore.logicalWriteMany, logicalWrite,
    Mettapedia.Languages.MeTTa.SubstitutionAlgebra.empty]

end Canaries

#print axioms Version.denote_extend
#print axioms fork_write_left_keep_right_exact
#print axioms ExclusiveRegion.freeze_exact
#print axioms escape_exact
#print axioms escape_write_exact
#print axioms exclusive_rejects_multiShot
#print axioms escape_admits_multiShot
#print axioms lookup_after_writes_exact
#print axioms CowSnapshot.denote_write
#print axioms CowSnapshot.capture_left_exact
#print axioms CowSnapshot.capture_right_exact
#print axioms cow_fork_write_left_keep_right_exact
#print axioms unique_capture_lt_eager
#print axioms paired_write_cost_eq_detach_then_write
#print axioms combineIndependent_comm
#print axioms deltaPromotionWork_lt_eagerSnapshotWork
#print axioms Canaries.freeze_two_exact
#print axioms Canaries.forked_sibling_is_unchanged
#print axioms Canaries.lookup_survives_escape
#print axioms Canaries.distinct_branches_remain_distinct
#print axioms Canaries.cow_capture_write_keeps_sibling
#print axioms Canaries.aliased_write_does_not_preserve_sibling

end Mettapedia.Languages.MeTTa.BindingVersions
