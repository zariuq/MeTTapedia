import Mettapedia.GSLT.Dynamics.RevisionBoundProgramView

/-!
# Staged callability with live definition observation

An evaluator may classify an expression head at one stage while observing the
current ordered definition occurrences only when that already-classified call
is entered.  These are independent coordinates:

* a stage records which heads have a callable interpretation;
* a live store records the current ordered occurrence fibre of each head.

The resulting observer is an idempotent, append-preserving projection onto an
admitted head fibre.  It is natural under occurrence-presentation maps that
preserve head classification.  Consequently, mutations of an admitted
definition remain visible without making a newly introduced head callable in
the middle of the same stage.

The negative controls distinguish this product from both common
over-approximations: freezing the complete occurrence family hides live
changes to an admitted definition, while consulting the unrestricted live
family makes newly introduced heads executable too early.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.StagedDefinitionObservation

open StableOccurrenceIdentityIndex
open RevisionBoundProgramView

universe uHead uId uRow uId' uRow'
universe uStage uAuthority uRevision

variable {Head : Type uHead} {Id : Type uId} {Row : Type uRow}
variable {Id' : Type uId'} {Row' : Type uRow'}
variable {StageId : Type uStage} {Authority : Type uAuthority}
variable {Revision : Type uRevision}

/-- The stage-local set of heads whose occurrences have a callable
interpretation.  The list retains first-admission order as presentation
evidence; semantic admission is membership. -/
structure Stage (Head : Type uHead) where
  admittedHeads : List Head
deriving DecidableEq, Repr

@[ext] theorem Stage.ext {left right : Stage Head}
    (admittedHeads : left.admittedHeads = right.admittedHeads) :
    left = right := by
  cases left
  cases right
  cases admittedHeads
  rfl

/-- Capture the first-occurrence order of the heads present in an authored
occurrence family. -/
def capture [DecidableEq Head]
    (headOf : Row → Head) (occurrences : List (Occurrence Id Row)) :
    Stage Head where
  admittedHeads :=
    (occurrences.map (fun occurrence => headOf occurrence.payload)).eraseDups

/-- The current ordered occurrence fibre of one head.  Duplicate payloads and
duplicate heads remain separate occurrences. -/
def fibre [DecidableEq Head]
    (headOf : Row → Head) (head : Head)
    (occurrences : List (Occurrence Id Row)) : List (Occurrence Id Row) :=
  occurrences.filter (fun occurrence => headOf occurrence.payload == head)

/-- Observe the live occurrence fibre exactly when the stage admitted the
head.  An unadmitted head remains data even if a later store mutation adds an
occurrence for it. -/
def observe [DecidableEq Head]
    (stage : Stage Head) (headOf : Row → Head)
    (occurrences : List (Occurrence Id Row)) (head : Head) :
    List (Occurrence Id Row) :=
  if head ∈ stage.admittedHeads then fibre headOf head occurrences else []

@[simp] theorem observe_of_admitted [DecidableEq Head]
    (stage : Stage Head) (headOf : Row → Head)
    (occurrences : List (Occurrence Id Row)) (head : Head)
    (admitted : head ∈ stage.admittedHeads) :
    observe stage headOf occurrences head = fibre headOf head occurrences := by
  simp [observe, admitted]

@[simp] theorem observe_of_unadmitted [DecidableEq Head]
    (stage : Stage Head) (headOf : Row → Head)
    (occurrences : List (Occurrence Id Row)) (head : Head)
    (unadmitted : head ∉ stage.admittedHeads) :
    observe stage headOf occurrences head = [] := by
  simp [observe, unadmitted]

/-- Observation distributes over chronological concatenation. -/
theorem observe_append [DecidableEq Head]
    (stage : Stage Head) (headOf : Row → Head)
    (left right : List (Occurrence Id Row)) (head : Head) :
    observe stage headOf (left ++ right) head =
      observe stage headOf left head ++ observe stage headOf right head := by
  by_cases admitted : head ∈ stage.admittedHeads <;>
    simp [observe, admitted, fibre, List.filter_append]

/-- Re-observing an already projected fibre changes nothing. -/
theorem observe_idempotent [DecidableEq Head]
    (stage : Stage Head) (headOf : Row → Head)
    (occurrences : List (Occurrence Id Row)) (head : Head) :
    observe stage headOf (observe stage headOf occurrences head) head =
      observe stage headOf occurrences head := by
  by_cases admitted : head ∈ stage.admittedHeads <;>
    simp [observe, admitted, fibre, List.filter_filter]

/-- Appending an occurrence to an admitted head is visible at the next
observation of that head. -/
theorem observe_append_admitted [DecidableEq Head]
    (stage : Stage Head) (headOf : Row → Head)
    (occurrences : List (Occurrence Id Row))
    (occurrence : Occurrence Id Row) (head : Head)
    (admitted : head ∈ stage.admittedHeads)
    (sameHead : headOf occurrence.payload = head) :
    observe stage headOf (occurrences ++ [occurrence]) head =
      observe stage headOf occurrences head ++ [occurrence] := by
  simp [observe, admitted, fibre, List.filter_append, sameHead]

/-- Appending an occurrence cannot make an unadmitted head callable within
the same stage. -/
theorem observe_append_unadmitted [DecidableEq Head]
    (stage : Stage Head) (headOf : Row → Head)
    (occurrences : List (Occurrence Id Row))
    (occurrence : Occurrence Id Row)
    (unadmitted : headOf occurrence.payload ∉ stage.admittedHeads) :
    observe stage headOf (occurrences ++ [occurrence])
        (headOf occurrence.payload) = [] := by
  simp [observe, unadmitted]

/-- Every occurrence is callable after a fresh stage is captured from a
family containing it. -/
theorem capture_admits_occurrence [DecidableEq Head]
    (headOf : Row → Head) (occurrences : List (Occurrence Id Row))
    (occurrence : Occurrence Id Row) (member : occurrence ∈ occurrences) :
    headOf occurrence.payload ∈ (capture headOf occurrences).admittedHeads := by
  simp only [capture, List.mem_eraseDups, List.mem_map]
  exact ⟨occurrence, member, rfl⟩

/-- Recapturing a stage makes every retained occurrence visible through its
own live fibre. -/
theorem mem_observe_capture [DecidableEq Head]
    (headOf : Row → Head) (occurrences : List (Occurrence Id Row))
    (occurrence : Occurrence Id Row) (member : occurrence ∈ occurrences) :
    occurrence ∈
      observe (capture headOf occurrences) headOf occurrences
        (headOf occurrence.payload) := by
  rw [observe_of_admitted _ _ _ _
    (capture_admits_occurrence headOf occurrences occurrence member)]
  simp [fibre, member]

/-! ## Presentation naturality -/

/-- Mapping occurrence identity and payload commutes with taking a head fibre
when the payload map preserves head classification. -/
theorem fibre_map
    [DecidableEq Head]
    (presentation : OccurrenceMap Id Row Id' Row')
    (sourceHead : Row → Head) (targetHead : Row' → Head)
    (commutes : ∀ row, targetHead (presentation.mapPayload row) = sourceHead row)
    (head : Head) (occurrences : List (Occurrence Id Row)) :
    fibre targetHead head
        (occurrences.map presentation.mapOccurrence) =
      (fibre sourceHead head occurrences).map presentation.mapOccurrence := by
  induction occurrences with
  | nil => rfl
  | cons occurrence occurrences inductionHypothesis =>
      have tailEquality :
          List.filter (fun item => targetHead item.payload == head)
              (occurrences.map presentation.mapOccurrence) =
            (List.filter (fun item => sourceHead item.payload == head)
              occurrences).map presentation.mapOccurrence := by
        simpa [fibre] using inductionHypothesis
      simp only [List.map_cons, fibre, List.filter_cons,
        OccurrenceMap.mapOccurrence]
      rw [show targetHead (presentation.mapPayload occurrence.payload) =
        sourceHead occurrence.payload from commutes occurrence.payload]
      by_cases sameHead : sourceHead occurrence.payload = head <;>
        simp [sameHead, tailEquality, OccurrenceMap.mapOccurrence]

/-- The staged live observer is natural under every occurrence-presentation
map that preserves head classification. -/
theorem observe_map
    [DecidableEq Head]
    (stage : Stage Head)
    (presentation : OccurrenceMap Id Row Id' Row')
    (sourceHead : Row → Head) (targetHead : Row' → Head)
    (commutes : ∀ row, targetHead (presentation.mapPayload row) = sourceHead row)
    (head : Head) (occurrences : List (Occurrence Id Row)) :
    observe stage targetHead
        (occurrences.map presentation.mapOccurrence) head =
      (observe stage sourceHead occurrences head).map
        presentation.mapOccurrence := by
  by_cases admitted : head ∈ stage.admittedHeads
  · simp [observe, admitted,
      fibre_map presentation sourceHead targetHead commutes]
  · simp [observe, admitted]

/-- Capturing callability itself is natural under a head-preserving
presentation map. -/
theorem capture_map
    [DecidableEq Head]
    (presentation : OccurrenceMap Id Row Id' Row')
    (sourceHead : Row → Head) (targetHead : Row' → Head)
    (commutes : ∀ row, targetHead (presentation.mapPayload row) = sourceHead row)
    (occurrences : List (Occurrence Id Row)) :
    capture targetHead (occurrences.map presentation.mapOccurrence) =
      capture sourceHead occurrences := by
  apply Stage.ext
  simp [capture, OccurrenceMap.mapOccurrence, Function.comp_def, commutes]

/-! ## Translation events and generation-stable calls

`Stage` records only the extensional callability classification.  An actual
translation event additionally remembers when and against which definition
authority that classification was produced.  Calls may enter later revisions
of the same authority, but a call snapshots its ordered occurrence fibre at
entry.  Continuing that call therefore cannot observe a subsequent mutation;
a later call can.
-/

/-- One revision of an authored definition authority.  `authority` is its
lifetime identity; `revision` orders observations within that lifetime. -/
structure DefinitionStore
    (Authority : Type uAuthority) (Revision : Type uRevision)
    (Id : Type uId) (Row : Type uRow) where
  authority : Authority
  revision : Revision
  occurrences : List (Occurrence Id Row)
deriving DecidableEq, Repr

/-- A concrete translation event.  Equal callability classifications can
still arise at different events and revisions. -/
structure TranslationStage
    (StageId : Type uStage) (Authority : Type uAuthority)
    (Revision : Type uRevision) (Head : Type uHead) where
  event : StageId
  authority : Authority
  sourceRevision : Revision
  callability : Stage Head
deriving DecidableEq, Repr

/-- Translate the current definition store into a stage-local callability
classification. -/
def translate [DecidableEq Head]
    (event : StageId) (headOf : Row → Head)
    (store : DefinitionStore Authority Revision Id Row) :
    TranslationStage StageId Authority Revision Head where
  event := event
  authority := store.authority
  sourceRevision := store.revision
  callability := capture headOf store.occurrences

/-- The owned semantic payload of one entered call.  The occurrence list is
copied into the value of the lease; the authority and entry revision are
receipts tying it to the store lifetime and observation event. -/
structure CallSnapshot
    (StageId : Type uStage) (Authority : Type uAuthority)
    (Revision : Type uRevision) (Head : Type uHead)
    (Id : Type uId) (Row : Type uRow) where
  translationEvent : StageId
  authority : Authority
  translationRevision : Revision
  entryRevision : Revision
  head : Head
  visible : List (Occurrence Id Row)
deriving DecidableEq, Repr

/-- Enter a call at the current store revision.  A translation stage can be
used only with the same lifetime authority, and only for a head classified as
callable by that translation event. -/
def enterCall [DecidableEq Authority] [DecidableEq Head]
    (stage : TranslationStage StageId Authority Revision Head)
    (headOf : Row → Head)
    (store : DefinitionStore Authority Revision Id Row) (head : Head) :
    Option (CallSnapshot StageId Authority Revision Head Id Row) :=
  if store.authority = stage.authority ∧
      head ∈ stage.callability.admittedHeads then
    some {
      translationEvent := stage.event
      authority := store.authority
      translationRevision := stage.sourceRevision
      entryRevision := store.revision
      head := head
      visible := fibre headOf head store.occurrences
    }
  else
    none

/-- Continue enumerating an entered call.  The later store is explicit so the
non-observation of later mutations is part of the interface rather than an
ambient convention. -/
def enumerateCall
    (snapshot : CallSnapshot StageId Authority Revision Head Id Row)
    (_laterStore : DefinitionStore Authority Revision Id Row) :
    List (Occurrence Id Row) :=
  snapshot.visible

@[simp] theorem enterCall_of_admitted
    [DecidableEq Authority] [DecidableEq Head]
    (stage : TranslationStage StageId Authority Revision Head)
    (headOf : Row → Head)
    (store : DefinitionStore Authority Revision Id Row) (head : Head)
    (sameAuthority : store.authority = stage.authority)
    (admitted : head ∈ stage.callability.admittedHeads) :
    enterCall stage headOf store head = some {
      translationEvent := stage.event
      authority := store.authority
      translationRevision := stage.sourceRevision
      entryRevision := store.revision
      head := head
      visible := fibre headOf head store.occurrences
    } := by
  simp [enterCall, sameAuthority, admitted]

@[simp] theorem enterCall_of_unadmitted
    [DecidableEq Authority] [DecidableEq Head]
    (stage : TranslationStage StageId Authority Revision Head)
    (headOf : Row → Head)
    (store : DefinitionStore Authority Revision Id Row) (head : Head)
    (unadmitted : head ∉ stage.callability.admittedHeads) :
    enterCall stage headOf store head = none := by
  simp [enterCall, unadmitted]

@[simp] theorem enterCall_of_authority_mismatch
    [DecidableEq Authority] [DecidableEq Head]
    (stage : TranslationStage StageId Authority Revision Head)
    (headOf : Row → Head)
    (store : DefinitionStore Authority Revision Id Row) (head : Head)
    (mismatch : store.authority ≠ stage.authority) :
    enterCall stage headOf store head = none := by
  simp [enterCall, mismatch]

/-- The visible occurrences in a successful lease are exactly the ordered
fibre at call entry. -/
theorem enterCall_visible_exact
    [DecidableEq Authority] [DecidableEq Head]
    (stage : TranslationStage StageId Authority Revision Head)
    (headOf : Row → Head)
    (store : DefinitionStore Authority Revision Id Row) (head : Head)
    (snapshot : CallSnapshot StageId Authority Revision Head Id Row)
    (entered : enterCall stage headOf store head = some snapshot) :
    snapshot.visible = fibre headOf head store.occurrences := by
  simp only [enterCall] at entered
  split at entered
  · injection entered with equality
    rw [← equality]
  · contradiction

/-- Successful call entry certifies both authority continuity and the
translation-stage callability decision. -/
theorem enterCall_authorized
    [DecidableEq Authority] [DecidableEq Head]
    (stage : TranslationStage StageId Authority Revision Head)
    (headOf : Row → Head)
    (store : DefinitionStore Authority Revision Id Row) (head : Head)
    (snapshot : CallSnapshot StageId Authority Revision Head Id Row)
    (entered : enterCall stage headOf store head = some snapshot) :
    store.authority = stage.authority ∧
      head ∈ stage.callability.admittedHeads := by
  simp only [enterCall] at entered
  split at entered
  · assumption
  · contradiction

/-- Successful call entry refines the staged live observer exactly. -/
theorem enterCall_visible_eq_observe
    [DecidableEq Authority] [DecidableEq Head]
    (stage : TranslationStage StageId Authority Revision Head)
    (headOf : Row → Head)
    (store : DefinitionStore Authority Revision Id Row) (head : Head)
    (snapshot : CallSnapshot StageId Authority Revision Head Id Row)
    (entered : enterCall stage headOf store head = some snapshot) :
    snapshot.visible =
      observe stage.callability headOf store.occurrences head := by
  rw [observe_of_admitted _ _ _ _
    (enterCall_authorized stage headOf store head snapshot entered).2]
  exact enterCall_visible_exact stage headOf store head snapshot entered

/-- Later store mutations cannot alter an already-entered call. -/
theorem enumerateCall_entered_frozen
    [DecidableEq Authority] [DecidableEq Head]
    (stage : TranslationStage StageId Authority Revision Head)
    (headOf : Row → Head)
    (entryStore laterStore : DefinitionStore Authority Revision Id Row)
    (head : Head)
    (snapshot : CallSnapshot StageId Authority Revision Head Id Row)
    (entered : enterCall stage headOf entryStore head = some snapshot) :
    enumerateCall snapshot laterStore =
      fibre headOf head entryStore.occurrences := by
  exact enterCall_visible_exact stage headOf entryStore head snapshot entered

/-- A later call through the same translation event observes the current
fibre of an admitted head. -/
theorem later_enterCall_observes_current
    [DecidableEq Authority] [DecidableEq Head]
    (stage : TranslationStage StageId Authority Revision Head)
    (headOf : Row → Head)
    (laterStore : DefinitionStore Authority Revision Id Row) (head : Head)
    (sameAuthority : laterStore.authority = stage.authority)
    (admitted : head ∈ stage.callability.admittedHeads) :
    enterCall stage headOf laterStore head = some {
      translationEvent := stage.event
      authority := laterStore.authority
      translationRevision := stage.sourceRevision
      entryRevision := laterStore.revision
      head := head
      visible := fibre headOf head laterStore.occurrences
    } :=
  enterCall_of_admitted stage headOf laterStore head sameAuthority admitted

/-- Map a store through an occurrence presentation without changing its
authority or revision. -/
def DefinitionStore.map
    (store : DefinitionStore Authority Revision Id Row)
    (presentation : OccurrenceMap Id Row Id' Row') :
    DefinitionStore Authority Revision Id' Row' where
  authority := store.authority
  revision := store.revision
  occurrences := store.occurrences.map presentation.mapOccurrence

/-- Map the occurrence presentation carried by a call snapshot. -/
def CallSnapshot.map
    (snapshot : CallSnapshot StageId Authority Revision Head Id Row)
    (presentation : OccurrenceMap Id Row Id' Row') :
    CallSnapshot StageId Authority Revision Head Id' Row' where
  translationEvent := snapshot.translationEvent
  authority := snapshot.authority
  translationRevision := snapshot.translationRevision
  entryRevision := snapshot.entryRevision
  head := snapshot.head
  visible := snapshot.visible.map presentation.mapOccurrence

/-- Entering a call is natural under every presentation map that preserves
head classification. -/
theorem enterCall_map
    [DecidableEq Authority] [DecidableEq Head]
    (stage : TranslationStage StageId Authority Revision Head)
    (presentation : OccurrenceMap Id Row Id' Row')
    (sourceHead : Row → Head) (targetHead : Row' → Head)
    (commutes : ∀ row,
      targetHead (presentation.mapPayload row) = sourceHead row)
    (store : DefinitionStore Authority Revision Id Row) (head : Head) :
    enterCall stage targetHead (store.map presentation) head =
      (enterCall stage sourceHead store head).map
        (fun snapshot => snapshot.map presentation) := by
  by_cases allowed :
      store.authority = stage.authority ∧
        head ∈ stage.callability.admittedHeads
  · simp [enterCall, allowed, DefinitionStore.map, CallSnapshot.map,
      fibre_map presentation sourceHead targetHead commutes]
  · simp [enterCall, allowed, DefinitionStore.map]

/-- Capturing a translation event is natural under head-preserving
occurrence presentation. -/
theorem translate_map
    [DecidableEq Head]
    (event : StageId)
    (presentation : OccurrenceMap Id Row Id' Row')
    (sourceHead : Row → Head) (targetHead : Row' → Head)
    (commutes : ∀ row,
      targetHead (presentation.mapPayload row) = sourceHead row)
    (store : DefinitionStore Authority Revision Id Row) :
    translate event targetHead (store.map presentation) =
      translate event sourceHead store := by
  cases store
  simp [translate, DefinitionStore.map,
    capture_map presentation sourceHead targetHead commutes]

/-! ## Positive and negative executable controls -/

namespace Canary

inductive CanaryHead where
  | known
  | fresh
deriving DecidableEq, Repr

inductive CanaryId where
  | old
  | added
  | fresh
deriving DecidableEq, Repr

def oldOccurrence : Occurrence CanaryId CanaryHead := ⟨.old, .known⟩
def addedOccurrence : Occurrence CanaryId CanaryHead := ⟨.added, .known⟩
def freshOccurrence : Occurrence CanaryId CanaryHead := ⟨.fresh, .fresh⟩

def initial : List (Occurrence CanaryId CanaryHead) := [oldOccurrence]
def initialStage : Stage CanaryHead := capture _root_.id initial

/-- A mutation of an admitted definition is visible and retains authored
multiplicity and order. -/
example :
    observe initialStage _root_.id
      (initial ++ [addedOccurrence]) .known =
      [oldOccurrence, addedOccurrence] := by
  decide

/-- A new head remains non-callable during the old stage. -/
example :
    observe initialStage _root_.id
      (initial ++ [freshOccurrence]) .fresh = [] := by
  decide

/-- A subsequent stage capture admits the new head. -/
example :
    observe (capture _root_.id (initial ++ [freshOccurrence])) _root_.id
      (initial ++ [freshOccurrence]) .fresh = [freshOccurrence] := by
  decide

/-- Freezing the complete occurrence family is not equivalent to staged
callability plus live observation for an admitted head. -/
example :
    observe initialStage _root_.id initial .known ≠
      observe initialStage _root_.id
        (initial ++ [addedOccurrence]) .known := by
  decide

/-- Unrestricted live selection is not equivalent to staged observation for a
newly introduced head. -/
example :
    fibre _root_.id .fresh (initial ++ [freshOccurrence]) ≠
      observe initialStage _root_.id
        (initial ++ [freshOccurrence]) .fresh := by
  decide

def store0 : DefinitionStore Bool Nat CanaryId CanaryHead :=
  ⟨false, 0, initial⟩

def storeAdded : DefinitionStore Bool Nat CanaryId CanaryHead :=
  ⟨false, 1, initial ++ [addedOccurrence]⟩

def storeRemoved : DefinitionStore Bool Nat CanaryId CanaryHead :=
  ⟨false, 2, []⟩

def storeFresh : DefinitionStore Bool Nat CanaryId CanaryHead :=
  ⟨false, 3, initial ++ [freshOccurrence]⟩

def foreignStore : DefinitionStore Bool Nat CanaryId CanaryHead :=
  ⟨true, 0, initial⟩

def literalTranslation :
    TranslationStage Nat Bool Nat CanaryHead :=
  translate 0 _root_.id store0

def initialCall :
    CallSnapshot Nat Bool Nat CanaryHead CanaryId CanaryHead :=
  ⟨0, false, 0, 0, .known, [oldOccurrence]⟩

def addedCall :
    CallSnapshot Nat Bool Nat CanaryHead CanaryId CanaryHead :=
  ⟨0, false, 0, 1, .known, [oldOccurrence, addedOccurrence]⟩

def removedCall :
    CallSnapshot Nat Bool Nat CanaryHead CanaryId CanaryHead :=
  ⟨0, false, 0, 2, .known, []⟩

/-- Entering the literal translation stage snapshots the original ordered
occurrence fibre. -/
example :
    enterCall literalTranslation _root_.id store0 .known =
      some initialCall := by
  decide

/-- Adding an occurrence after entry cannot change the alternatives of the
already-entered call. -/
example :
    enumerateCall initialCall storeAdded = [oldOccurrence] := by
  decide

/-- A later call through the same translation event sees the added
occurrence, with order and multiplicity intact. -/
example :
    enterCall literalTranslation _root_.id storeAdded .known =
      some addedCall := by
  decide

/-- Removal after entry likewise leaves the old call stable. -/
example :
    enumerateCall initialCall storeRemoved = [oldOccurrence] := by
  decide

/-- A call entered after that removal sees the empty current fibre while the
head remains callable. -/
example :
    enterCall literalTranslation _root_.id storeRemoved .known =
      some removedCall := by
  decide

/-- Introducing a fresh head does not retroactively alter an earlier
translation event. -/
example :
    enterCall literalTranslation _root_.id storeFresh .fresh = none := by
  decide

/-- A later explicit translation event admits that fresh head. -/
example :
    (enterCall (translate 1 _root_.id storeFresh) _root_.id
      storeFresh .fresh).map (fun snapshot => snapshot.visible) =
      some [freshOccurrence] := by
  decide

/-- Translation evidence from another authority lifetime cannot be reused. -/
example :
    enterCall literalTranslation _root_.id foreignStore .known = none := by
  decide

end Canary

#print axioms observe_append
#print axioms observe_idempotent
#print axioms observe_append_admitted
#print axioms observe_append_unadmitted
#print axioms mem_observe_capture
#print axioms observe_map
#print axioms capture_map
#print axioms enterCall_visible_exact
#print axioms enterCall_authorized
#print axioms enterCall_visible_eq_observe
#print axioms enumerateCall_entered_frozen
#print axioms later_enterCall_observes_current
#print axioms enterCall_map
#print axioms translate_map

end Mettapedia.GSLT.Dynamics.StagedDefinitionObservation
