import Mettapedia.GSLT.LanguageDef.PettaOrderedLibraryResolution

/-!
# Atomic publication of prepared PeTTa library roots

External providers may clone, validate, build, or otherwise prepare a library.
Those physical operations are not the language's library algebra.  At the
semantic boundary they produce either a refused preparation or one prepared
root carrying provider provenance.

Publishing a prepared root updates two views together:

* the keyed mount index is replaced or appended;
* the ordered root-occurrence word is extended on the left.

The mount index is a cache/provenance view.  The occurrence word remains the
authority for PeTTa's nondeterministic `library` relation, so repeated imports
retain repeated root occurrences even when they update the same mount key.
Refusal acts as the identity on both views.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.PettaLibraryImportPublication

open PettaOrderedLibraryResolution

universe uKey uRoot uOrigin uRevision uRefusal uMember uPath

/-- Revision provenance after provider-side validation.  The `exactCommit`
case receives an already validated commit identity; parsing hexadecimal text
belongs to a concrete provider realization, not this algebra. -/
inductive RevisionPolicy (Revision : Type uRevision) where
  | defaultBranch
  | exactCommit (revision : Revision)
deriving DecidableEq, Repr

/-- One provider-prepared root ready for atomic language publication. -/
structure PreparedImport
    (Key : Type uKey) (Root : Type uRoot)
    (Origin : Type uOrigin) (Revision : Type uRevision) where
  key : Key
  root : Root
  origin : Origin
  revision : RevisionPolicy Revision
deriving DecidableEq, Repr

/-- Preparation is partial and proof-relevant: refusal is not an empty root
family and cannot be reinterpreted as successful publication. -/
inductive Preparation
    (Key : Type uKey) (Root : Type uRoot)
    (Origin : Type uOrigin) (Revision : Type uRevision)
    (Refusal : Type uRefusal) where
  | prepared (value : PreparedImport Key Root Origin Revision)
  | refused (reason : Refusal)
deriving DecidableEq, Repr

/-- A keyed physical/provenance view of one prepared root. -/
structure Mount
    (Key : Type uKey) (Root : Type uRoot)
    (Origin : Type uOrigin) (Revision : Type uRevision) where
  key : Key
  root : Root
  origin : Origin
  revision : RevisionPolicy Revision
deriving DecidableEq, Repr

def PreparedImport.toMount
    {Key : Type uKey} {Root : Type uRoot}
    {Origin : Type uOrigin} {Revision : Type uRevision}
    (prepared : PreparedImport Key Root Origin Revision) :
    Mount Key Root Origin Revision where
  key := prepared.key
  root := prepared.root
  origin := prepared.origin
  revision := prepared.revision

/-- Replace the first mount with the same key, preserving its position, or
append a new key.  This is an index update, not the root-occurrence algebra. -/
def upsertMount
    {Key : Type uKey} [DecidableEq Key]
    {Root : Type uRoot} {Origin : Type uOrigin}
    {Revision : Type uRevision}
    (mount : Mount Key Root Origin Revision) :
    List (Mount Key Root Origin Revision) →
      List (Mount Key Root Origin Revision)
  | [] => [mount]
  | current :: rest =>
      if current.key = mount.key then
        mount :: rest
      else
        current :: upsertMount mount rest

def findMount
    {Key : Type uKey} [DecidableEq Key]
    {Root : Type uRoot} {Origin : Type uOrigin}
    {Revision : Type uRevision}
    (key : Key) : List (Mount Key Root Origin Revision) →
      Option (Mount Key Root Origin Revision)
  | [] => none
  | current :: rest =>
      if current.key = key then some current else findMount key rest

theorem findMount_upsert_self
    {Key : Type uKey} [DecidableEq Key]
    {Root : Type uRoot} {Origin : Type uOrigin}
    {Revision : Type uRevision}
    (mount : Mount Key Root Origin Revision)
    (mounts : List (Mount Key Root Origin Revision)) :
    findMount mount.key (upsertMount mount mounts) = some mount := by
  induction mounts with
  | nil => simp [upsertMount, findMount]
  | cons current rest ih =>
      by_cases same : current.key = mount.key
      · simp [upsertMount, findMount, same]
      · simp [upsertMount, findMount, same, ih]

/-- The complete language-visible publication state.  `roots` is an ordered
free word of occurrences; `mounts` is a keyed derived index. -/
structure LibraryIndex
    (Key : Type uKey) (Root : Type uRoot)
    (Origin : Type uOrigin) (Revision : Type uRevision) where
  roots : List Root
  mounts : List (Mount Key Root Origin Revision)
deriving DecidableEq, Repr

/-- Commit both observable views of one successful preparation. -/
def publishPrepared
    {Key : Type uKey} [DecidableEq Key]
    {Root : Type uRoot} {Origin : Type uOrigin}
    {Revision : Type uRevision}
    (prepared : PreparedImport Key Root Origin Revision)
    (state : LibraryIndex Key Root Origin Revision) :
    LibraryIndex Key Root Origin Revision where
  roots := prepared.root :: state.roots
  mounts := upsertMount prepared.toMount state.mounts

inductive PublicationObservation (Refusal : Type uRefusal) where
  | committed
  | refused (reason : Refusal)
deriving DecidableEq, Repr

/-- Provider preparation followed by atomic language publication.  A refused
preparation is the identity transition on the complete publication state. -/
def applyPreparation
    {Key : Type uKey} [DecidableEq Key]
    {Root : Type uRoot} {Origin : Type uOrigin}
    {Revision : Type uRevision} {Refusal : Type uRefusal}
    (preparation : Preparation Key Root Origin Revision Refusal)
    (state : LibraryIndex Key Root Origin Revision) :
    LibraryIndex Key Root Origin Revision ×
      PublicationObservation Refusal :=
  match preparation with
  | .prepared value => (publishPrepared value state, .committed)
  | .refused reason => (state, .refused reason)

@[simp] theorem refusal_preserves_complete_index
    {Key : Type uKey} [DecidableEq Key]
    {Root : Type uRoot} {Origin : Type uOrigin}
    {Revision : Type uRevision} {Refusal : Type uRefusal}
    (reason : Refusal)
    (state : LibraryIndex Key Root Origin Revision) :
    applyPreparation
        (.refused reason : Preparation Key Root Origin Revision Refusal)
        state = (state, .refused reason) := rfl

@[simp] theorem success_prepends_exact_root_occurrence
    {Key : Type uKey} [DecidableEq Key]
    {Root : Type uRoot} {Origin : Type uOrigin}
    {Revision : Type uRevision} {Refusal : Type uRefusal}
    (prepared : PreparedImport Key Root Origin Revision)
    (state : LibraryIndex Key Root Origin Revision) :
    (applyPreparation
        (.prepared prepared : Preparation Key Root Origin Revision Refusal)
        state).1.roots = prepared.root :: state.roots := rfl

@[simp] theorem success_mount_channel_exact
    {Key : Type uKey} [DecidableEq Key]
    {Root : Type uRoot} {Origin : Type uOrigin}
    {Revision : Type uRevision} {Refusal : Type uRefusal}
    (prepared : PreparedImport Key Root Origin Revision)
    (state : LibraryIndex Key Root Origin Revision) :
    findMount prepared.key
        (applyPreparation
          (.prepared prepared : Preparation Key Root Origin Revision Refusal)
          state).1.mounts = some prepared.toMount := by
  exact findMount_upsert_self prepared.toMount state.mounts

/-- Publication commutes with rooted resolution by the free-monoid prepend
law: one successful import contributes exactly its matching candidate prefix. -/
theorem rootedCandidates_after_successful_publication
    {Key : Type uKey} [DecidableEq Key]
    {Root : Type uRoot} {Member : Type uMember}
    {Path : Type uPath} [DecidableEq Path]
    {Origin : Type uOrigin} {Revision : Type uRevision}
    {Refusal : Type uRefusal}
    (presentation : Presentation Root Member Path Refusal)
    (root : Root) (member : Member)
    (prepared : PreparedImport Key Path Origin Revision)
    (state : LibraryIndex Key Path Origin Revision) :
    rootedCandidates presentation root member
        (applyPreparation
          (.prepared prepared : Preparation Key Path Origin Revision Refusal)
          state).1.roots =
      (if presentation.rootMatches root prepared.root then
        [presentation.join prepared.root member]
       else []) ++
        rootedCandidates presentation root member state.roots := by
  simpa [applyPreparation, publishPrepared, applyRootEdit] using
    rootedCandidates_after_prepend
      presentation root member prepared.root state.roots

/-- Repeating a successful import retains two root occurrences even though
the keyed mount view contains the latest value for that key. -/
theorem repeated_success_retains_root_multiplicity
    {Key : Type uKey} [DecidableEq Key]
    {Root : Type uRoot} {Origin : Type uOrigin}
    {Revision : Type uRevision}
    (prepared : PreparedImport Key Root Origin Revision)
    (state : LibraryIndex Key Root Origin Revision) :
    (publishPrepared prepared (publishPrepared prepared state)).roots =
      prepared.root :: prepared.root :: state.roots := rfl

/-- A pinned request produces exact-commit provenance after the external
provider has validated the full commit identity. -/
def pinnedPrepared
    {Key : Type uKey} {Root : Type uRoot}
    {Origin : Type uOrigin} {Revision : Type uRevision}
    (key : Key) (root : Root) (origin : Origin) (commit : Revision) :
    PreparedImport Key Root Origin Revision where
  key := key
  root := root
  origin := origin
  revision := .exactCommit commit

@[simp] theorem pinnedPrepared_has_exact_revision
    {Key : Type uKey} {Root : Type uRoot}
    {Origin : Type uOrigin} {Revision : Type uRevision}
    (key : Key) (root : Root) (origin : Origin) (commit : Revision) :
    (pinnedPrepared key root origin commit).revision =
      RevisionPolicy.exactCommit commit := rfl

/-! ## Executable positive and negative canaries -/

private def initial : LibraryIndex Nat Nat Nat Nat where
  roots := [1, 2]
  mounts := []

private def pinned : PreparedImport Nat Nat Nat Nat :=
  pinnedPrepared 9 7 42 1001

example : (publishPrepared pinned initial).roots = [7, 1, 2] := by
  decide

example :
    (publishPrepared pinned (publishPrepared pinned initial)).roots =
      [7, 7, 1, 2] := by
  decide

example :
    (publishPrepared pinned (publishPrepared pinned initial)).mounts =
      [pinned.toMount] := by
  decide

example :
    applyPreparation
        (.refused "origin mismatch" : Preparation Nat Nat Nat Nat String)
        initial = (initial, .refused "origin mismatch") := by
  decide

#print axioms findMount_upsert_self
#print axioms refusal_preserves_complete_index
#print axioms success_mount_channel_exact
#print axioms rootedCandidates_after_successful_publication
#print axioms repeated_success_retains_root_multiplicity

end Mettapedia.GSLT.LanguageDef.PettaLibraryImportPublication
