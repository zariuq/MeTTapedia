import Mettapedia.GSLT.Dynamics.ProofRelevantNeedOwnership
import Mettapedia.TypeTheory.DisplayedEvidenceNeed

/-!
# Pullback of indexed evidence and evaluator ownership for call-by-need

Displayed exact evidence and evaluator ownership refine the ordinary
proof-relevant Need protocol along independent axes.  This module combines
them by the strict pullback of their state and event maps into that common
protocol.

The pullback admits exactly those pairs whose ordinary Need images agree.
Consequently a cached witness must inhabit the fibre selected by the cell's
raw origin, while an evaluating state and every commit retain the evaluator
which owns it.  Forgetting either coordinate is an explicit projection.

The construction excludes two different malformed cases:

* a packed witness whose internal raw index differs from the cell origin; and
* a commit performed by an evaluator other than the current owner.

It also proves that every live transition and trace preserves the complete
raw origin.  Taking the raw origin to contain a revision therefore makes
in-place revision change impossible; resampling at a new revision requires a
fresh cell.

No evaluator, scheduler, revision order, forcing policy, or object language is
selected here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.IndexedEvidenceNeedPullback

open Mettapedia.GSLT.Dynamics
open Mettapedia.TypeTheory.DisplayedEvidence

namespace Indexed

export Mettapedia.TypeTheory.DisplayedEvidenceNeed
  (CellState Event Step PackedEvidence PackedRefutation toNeedState)

namespace Event

export Mettapedia.TypeTheory.DisplayedEvidenceNeed.Event (toNeed)

end Event

namespace Step

export Mettapedia.TypeTheory.DisplayedEvidenceNeed.Step (toNeed)

end Step

end Indexed

namespace Owned

export Mettapedia.GSLT.Dynamics.ProofRelevantNeed.Ownership
  (CellState Event Step Trace eraseState eraseEvent)

end Owned

namespace Need

export Mettapedia.GSLT.Dynamics.ProofRelevantNeed (CellState Event Step)

end Need

universe uRaw uExact uReason uCell uOwner uRetryable

variable (family : Family.{uRaw, uExact}) (Reason : Type uReason)
variable (Cell : Type uCell) (Owner : Type uOwner)
variable (RetryableFault : Type uRetryable)

/-! ## Strict pullbacks of states and events -/

/-- The explicit pullback of two functions with one common codomain. -/
abbrev StrictPullback
    {Left : Type*} {Right : Type*} {Base : Type*}
    (left : Left -> Base) (right : Right -> Base) : Type _ :=
  { pair : Left × Right // left pair.1 = right pair.2 }

namespace StrictPullback

/-- The mediating map from any compatible cone of functions. -/
def lift
    {Left Right Base Source : Type*}
    {left : Left -> Base} {right : Right -> Base}
    (toLeft : Source -> Left) (toRight : Source -> Right)
    (commutes : ∀ source, left (toLeft source) = right (toRight source)) :
    Source -> StrictPullback left right :=
  fun source => ⟨(toLeft source, toRight source), commutes source⟩

@[simp] theorem lift_left
    {Left Right Base Source : Type*}
    {left : Left -> Base} {right : Right -> Base}
    (toLeft : Source -> Left) (toRight : Source -> Right)
    (commutes : ∀ source, left (toLeft source) = right (toRight source))
    (source : Source) :
    (lift toLeft toRight commutes source).1.1 = toLeft source :=
  rfl

@[simp] theorem lift_right
    {Left Right Base Source : Type*}
    {left : Left -> Base} {right : Right -> Base}
    (toLeft : Source -> Left) (toRight : Source -> Right)
    (commutes : ∀ source, left (toLeft source) = right (toRight source))
    (source : Source) :
    (lift toLeft toRight commutes source).1.2 = toRight source :=
  rfl

/-- The mediating map is unique from its two pullback projections. -/
theorem lift_unique
    {Left Right Base Source : Type*}
    {left : Left -> Base} {right : Right -> Base}
    (toLeft : Source -> Left) (toRight : Source -> Right)
    (commutes : ∀ source, left (toLeft source) = right (toRight source))
    (candidate : Source -> StrictPullback left right)
    (candidateLeft : ∀ source, (candidate source).1.1 = toLeft source)
    (candidateRight : ∀ source, (candidate source).1.2 = toRight source) :
    candidate = lift toLeft toRight commutes := by
  funext source
  apply Subtype.ext
  exact Prod.ext (candidateLeft source) (candidateRight source)

end StrictPullback

/-- States carrying both indexed exact evidence and evaluator ownership,
identified precisely over their common ordinary Need state. -/
abbrev State : Type _ :=
  StrictPullback
    (Indexed.toNeedState family Reason)
    (Owned.eraseState :
      Owned.CellState Owner family.Raw (Indexed.PackedEvidence family)
        (Indexed.PackedRefutation family Reason) ->
      Need.CellState family.Raw (Indexed.PackedEvidence family)
        (Indexed.PackedRefutation family Reason))

/-- Events carrying both the indexed-evidence and owner-sensitive views,
identified precisely over their common ordinary Need event. -/
abbrev Event : Type _ :=
  StrictPullback
    (Indexed.Event.toNeed (family := family) (Reason := Reason) :
      Indexed.Event family Reason Cell RetryableFault ->
        Need.Event Cell family.Raw (Indexed.PackedEvidence family)
          (Indexed.PackedRefutation family Reason) RetryableFault)
    (Owned.eraseEvent :
      Owned.Event Cell Owner family.Raw (Indexed.PackedEvidence family)
        (Indexed.PackedRefutation family Reason) RetryableFault ->
      Need.Event Cell family.Raw (Indexed.PackedEvidence family)
        (Indexed.PackedRefutation family Reason) RetryableFault)

namespace State

/-- Indexed-evidence projection of the strict pullback. -/
def indexed (state : State family Reason Owner) :
    Indexed.CellState family Reason :=
  state.1.1

/-- Owner-sensitive projection of the strict pullback. -/
def owned (state : State family Reason Owner) :
    Owned.CellState Owner family.Raw (Indexed.PackedEvidence family)
      (Indexed.PackedRefutation family Reason) :=
  state.1.2

/-- The two projections have exactly the same ordinary Need image. -/
theorem agreement (state : State family Reason Owner) :
    Indexed.toNeedState family Reason state.indexed =
      Owned.eraseState state.owned :=
  state.2

/-- Construct a state from compatible indexed and owner-sensitive views. -/
def mk
    (indexed : Indexed.CellState family Reason)
    (owned : Owned.CellState Owner family.Raw
      (Indexed.PackedEvidence family)
      (Indexed.PackedRefutation family Reason))
    (agreement : Indexed.toNeedState family Reason indexed =
      Owned.eraseState owned) :
    State family Reason Owner :=
  ⟨(indexed, owned), agreement⟩

@[simp] theorem indexed_mk
    (indexed : Indexed.CellState family Reason)
    (owned : Owned.CellState Owner family.Raw
      (Indexed.PackedEvidence family)
      (Indexed.PackedRefutation family Reason))
    (agreement : Indexed.toNeedState family Reason indexed =
      Owned.eraseState owned) :
    (mk family Reason Owner indexed owned agreement).indexed = indexed :=
  rfl

@[simp] theorem owned_mk
    (indexed : Indexed.CellState family Reason)
    (owned : Owned.CellState Owner family.Raw
      (Indexed.PackedEvidence family)
      (Indexed.PackedRefutation family Reason))
    (agreement : Indexed.toNeedState family Reason indexed =
      Owned.eraseState owned) :
    (mk family Reason Owner indexed owned agreement).owned = owned :=
  rfl

/-- The strict pullback is determined by its two projections. -/
theorem ext {left right : State family Reason Owner}
    (indexed : left.indexed = right.indexed)
    (owned : left.owned = right.owned) : left = right := by
  apply Subtype.ext
  exact Prod.ext indexed owned

end State

namespace Event

/-- Indexed-evidence projection of a joint event. -/
def indexed (event : Event family Reason Cell Owner RetryableFault) :
    Indexed.Event family Reason Cell RetryableFault :=
  event.1.1

/-- Owner-sensitive projection of a joint event. -/
def owned (event : Event family Reason Cell Owner RetryableFault) :
    Owned.Event Cell Owner family.Raw (Indexed.PackedEvidence family)
      (Indexed.PackedRefutation family Reason) RetryableFault :=
  event.1.2

/-- The two event projections have exactly the same ordinary Need image. -/
theorem agreement
    (event : Event family Reason Cell Owner RetryableFault) :
    event.indexed.toNeed = Owned.eraseEvent event.owned :=
  event.2

/-- Construct a joint event from compatible views. -/
def mk
    (indexed : Indexed.Event family Reason Cell RetryableFault)
    (owned : Owned.Event Cell Owner family.Raw
      (Indexed.PackedEvidence family)
      (Indexed.PackedRefutation family Reason) RetryableFault)
    (agreement : indexed.toNeed = Owned.eraseEvent owned) :
    Event family Reason Cell Owner RetryableFault :=
  ⟨(indexed, owned), agreement⟩

@[simp] theorem indexed_mk
    (indexed : Indexed.Event family Reason Cell RetryableFault)
    (owned : Owned.Event Cell Owner family.Raw
      (Indexed.PackedEvidence family)
      (Indexed.PackedRefutation family Reason) RetryableFault)
    (agreement : indexed.toNeed = Owned.eraseEvent owned) :
    (mk family Reason Cell Owner RetryableFault indexed owned agreement).indexed =
      indexed :=
  rfl

@[simp] theorem owned_mk
    (indexed : Indexed.Event family Reason Cell RetryableFault)
    (owned : Owned.Event Cell Owner family.Raw
      (Indexed.PackedEvidence family)
      (Indexed.PackedRefutation family Reason) RetryableFault)
    (agreement : indexed.toNeed = Owned.eraseEvent owned) :
    (mk family Reason Cell Owner RetryableFault indexed owned agreement).owned =
      owned :=
  rfl

end Event

/-! ## Joint transitions and traces -/

/-- A joint transition is exactly a transition in both refinements between
the corresponding pullback components. -/
structure Step (cell : Cell)
    (source : State family Reason Owner)
    (event : Event family Reason Cell Owner RetryableFault)
    (target : State family Reason Owner) : Type _ where
  indexed : Indexed.Step family Reason Cell RetryableFault cell
    source.indexed event.indexed target.indexed
  owned : Owned.Step RetryableFault cell
    source.owned event.owned target.owned

namespace Step

/-- Forget evaluator ownership while retaining the indexed evidence step. -/
def forgetOwnership
    {cell : Cell} {source target : State family Reason Owner}
    {event : Event family Reason Cell Owner RetryableFault}
    (step : Step family Reason Cell Owner RetryableFault cell source event target) :
    Indexed.Step family Reason Cell RetryableFault cell
      source.indexed event.indexed target.indexed :=
  step.indexed

/-- Forget dependent indexing while retaining the owner-sensitive step. -/
def forgetIndexing
    {cell : Cell} {source target : State family Reason Owner}
    {event : Event family Reason Cell Owner RetryableFault}
    (step : Step family Reason Cell Owner RetryableFault cell source event target) :
    Owned.Step RetryableFault cell source.owned event.owned target.owned :=
  step.owned

/-- Every joint transition has the common ordinary Need transition supplied
by its indexed projection. -/
def toNeed
    {cell : Cell} {source target : State family Reason Owner}
    {event : Event family Reason Cell Owner RetryableFault}
    (step : Step family Reason Cell Owner RetryableFault cell source event target) :
    Need.Step RetryableFault cell
      (Indexed.toNeedState family Reason source.indexed)
      event.indexed.toNeed
      (Indexed.toNeedState family Reason target.indexed) :=
  step.indexed.toNeed

end Step

/-- A chronological trace retaining indexed evidence but not evaluator
ownership. -/
inductive IndexedTrace (cell : Cell) :
    Indexed.CellState family Reason -> Indexed.CellState family Reason ->
      Type _ where
  | refl (state : Indexed.CellState family Reason) :
      IndexedTrace cell state state
  | tail {source middle target : Indexed.CellState family Reason}
      (event : Indexed.Event family Reason Cell RetryableFault)
      (step : Indexed.Step family Reason Cell RetryableFault
        cell source event middle)
      (rest : IndexedTrace cell middle target) :
      IndexedTrace cell source target

/-- A chronological trace in the joint protocol. -/
inductive Trace (cell : Cell) :
    State family Reason Owner -> State family Reason Owner -> Type _ where
  | refl (state : State family Reason Owner) : Trace cell state state
  | tail {source middle target : State family Reason Owner}
      (event : Event family Reason Cell Owner RetryableFault)
      (step : Step family Reason Cell Owner RetryableFault
        cell source event middle)
      (rest : Trace cell middle target) :
      Trace cell source target

namespace Trace

/-- Retain the exact joint event history. -/
def events {cell : Cell} :
    {source target : State family Reason Owner} ->
    Trace family Reason Cell Owner RetryableFault cell source target ->
      List (Event family Reason Cell Owner RetryableFault)
  | _, _, .refl _ => []
  | _, _, .tail event _ rest => event :: rest.events

/-- Forget ownership from every transition in a joint trace. -/
def forgetOwnership {cell : Cell} :
    {source target : State family Reason Owner} ->
    Trace family Reason Cell Owner RetryableFault cell source target ->
      IndexedTrace family Reason Cell RetryableFault cell
        source.indexed target.indexed
  | _, _, .refl state => .refl state.indexed
  | _, _, .tail event step rest =>
      .tail event.indexed step.indexed rest.forgetOwnership

/-- Forget indexing from every transition while retaining ownership. -/
def forgetIndexing {cell : Cell} :
    {source target : State family Reason Owner} ->
    Trace family Reason Cell Owner RetryableFault cell source target ->
      Owned.Trace RetryableFault cell source.owned target.owned
  | _, _, .refl state => .refl state.owned
  | _, _, .tail event step rest =>
      .tail event.owned step.owned rest.forgetIndexing

end Trace

/-! ## Immutable raw origins and revisions -/

/-- Partial raw-origin observation of an indexed cell. -/
def rawOrigin? : Indexed.CellState family Reason -> Option family.Raw
  | .absent => none
  | .suspended raw => some raw
  | .evaluating raw => some raw
  | .cachedEvidence raw _ => some raw
  | .cachedRefutation raw _ => some raw

/-- A live indexed state retains one exact raw origin. -/
def LiveAt (raw : family.Raw) (state : Indexed.CellState family Reason) : Prop :=
  rawOrigin? family Reason state = some raw

/-- Every transition from a live indexed state preserves its complete raw
origin. -/
theorem indexedStep_preservesRawOrigin
    {cell : Cell}
    {source target : Indexed.CellState family Reason}
    {event : Indexed.Event family Reason Cell RetryableFault}
    (step : Indexed.Step family Reason Cell RetryableFault
      cell source event target)
    {raw : family.Raw} (live : LiveAt family Reason raw source) :
    LiveAt family Reason raw target := by
  cases step <;> simp_all [LiveAt, rawOrigin?]

/-- Raw-origin preservation lifts through the indexed/owned pullback. -/
theorem Step.preservesRawOrigin
    {cell : Cell} {source target : State family Reason Owner}
    {event : Event family Reason Cell Owner RetryableFault}
    (step : Step family Reason Cell Owner RetryableFault cell source event target)
    {raw : family.Raw} (live : LiveAt family Reason raw source.indexed) :
    LiveAt family Reason raw target.indexed := by
  exact indexedStep_preservesRawOrigin family Reason Cell RetryableFault
    step.indexed live

/-- Raw-origin preservation extends to every chronological joint trace. -/
theorem Trace.preservesRawOrigin
    {cell : Cell} {source target : State family Reason Owner}
    (trace : Trace family Reason Cell Owner RetryableFault cell source target)
    {raw : family.Raw} (live : LiveAt family Reason raw source.indexed) :
    LiveAt family Reason raw target.indexed := by
  induction trace with
  | refl => exact live
  | tail event step rest inductionHypothesis =>
      exact inductionHypothesis
        (indexedStep_preservesRawOrigin family Reason Cell RetryableFault
          step.indexed live)

/-- Revision and ordinary origin are independent coordinates of a cell's
immutable raw origin. -/
structure RevisionOrigin (Revision Origin : Type*) where
  revision : Revision
  origin : Origin
deriving DecidableEq, Repr

/-- Every coordinate computed from the immutable raw origin is preserved by a
joint trace.  Revision preservation is the instance where `coordinate` reads
the revision field. -/
theorem trace_preserves_origin_coordinate
    {Coordinate : Type*} (coordinate : family.Raw -> Coordinate)
    {cell : Cell}
    {source target : State family Reason Owner}
    (trace : Trace family Reason Cell Owner RetryableFault
      cell source target)
    {sourceRaw targetRaw : family.Raw}
    (sourceLive : LiveAt family Reason sourceRaw source.indexed)
    (targetLive : LiveAt family Reason targetRaw target.indexed) :
    coordinate sourceRaw = coordinate targetRaw := by
  have targetAtSource := Trace.preservesRawOrigin
    (family := family) (Reason := Reason) (Cell := Cell)
    (Owner := Owner) (RetryableFault := RetryableFault) trace sourceLive
  have rawEquality : sourceRaw = targetRaw := by
    rw [LiveAt, targetLive] at targetAtSource
    exact Option.some.inj targetAtSource.symm
  exact congrArg coordinate rawEquality

/-! ## Positive and adversarial controls -/

namespace Canary

open Mettapedia.TypeTheory.DisplayedEvidenceNeed.Canary

abbrev IndexedState := State booleanUnit Empty Bool
abbrev JointEvent := Event booleanUnit Empty Unit Bool Empty

def evaluating (owner : Bool) : IndexedState :=
  State.mk booleanUnit Empty Bool
    (.evaluating false)
    (.evaluating false owner)
    rfl

def cachedMatching : IndexedState :=
  State.mk booleanUnit Empty Bool
    (.cachedEvidence false PUnit.unit)
    (.cachedValue false matchingPacked)
    rfl

def commitEvent (owner : Bool) : JointEvent :=
  Event.mk booleanUnit Empty Unit Bool Empty
    (.commitEvidence () false PUnit.unit)
    (.commitValue () false owner matchingPacked)
    rfl

/-- Matching evidence and the current evaluator jointly authorize commit. -/
def matchingCommit :
    Step booleanUnit Empty Unit Bool Empty ()
      (evaluating true) (commitEvent true) cachedMatching where
  indexed := by
    change Indexed.Step booleanUnit Empty Unit Empty ()
      (.evaluating false) (.commitEvidence () false PUnit.unit)
      (.cachedEvidence false PUnit.unit)
    exact
      @Mettapedia.TypeTheory.DisplayedEvidenceNeed.Step.commitEvidence
        booleanUnit Empty Unit Empty () false PUnit.unit
  owned := .commitValue false true matchingPacked

/-- The same evidence cannot be committed by a different evaluator. -/
theorem wrong_owner_commit_empty :
    IsEmpty
      (Step booleanUnit Empty Unit Bool Empty ()
        (evaluating true) (commitEvent false) cachedMatching) :=
  ⟨by
    intro impossible
    cases impossible.owned⟩

/-- An owner-sensitive state with a mismatched packed evidence index cannot
appear in the pullback. -/
theorem mismatched_index_excluded :
    Not (Exists fun state : IndexedState =>
      state.owned =
        (.cachedValue false mismatchedPacked :
          Owned.CellState Bool Bool PackedBooleanEvidence
            PackedBooleanRefutation)) := by
  rintro ⟨state, ownedEquality⟩
  apply mismatchedNeedState_not_in_image
  refine ⟨state.indexed, ?_⟩
  rw [state.agreement, ownedEquality]
  rfl

/-- Ownership is a genuine additional coordinate: projecting to indexed
evidence states is not injective. -/
theorem indexed_projection_not_injective :
    Not (Function.Injective
      (State.indexed (family := booleanUnit) (Reason := Empty)
        (Owner := Bool))) := by
  intro injective
  have equalJoint : evaluating false = evaluating true :=
    injective rfl
  have equalOwned := congrArg
    (State.owned (family := booleanUnit) (Reason := Empty) (Owner := Bool))
    equalJoint
  cases equalOwned

def revisionFamily : Family where
  Raw := RevisionOrigin Bool Unit
  Exact := fun raw => if raw.revision then PUnit else Bool

def revisionSourceRaw : revisionFamily.Raw := ⟨false, ()⟩
def revisionTargetRaw : revisionFamily.Raw := ⟨true, ()⟩

def revisionSource : State revisionFamily Empty Bool :=
  State.mk revisionFamily Empty Bool
    (.suspended revisionSourceRaw)
    (.suspended revisionSourceRaw)
    rfl

def revisionTarget : State revisionFamily Empty Bool :=
  State.mk revisionFamily Empty Bool
    (.suspended revisionTargetRaw)
    (.suspended revisionTargetRaw)
    rfl

/-- A live joint trace cannot retag a suspension from one revision to another
inside the same cell. -/
theorem revision_change_requires_fresh_cell :
    IsEmpty
      (Trace revisionFamily Empty Unit Bool Empty ()
        revisionSource revisionTarget) := by
  constructor
  intro trace
  have sourceLive :
      LiveAt revisionFamily Empty revisionSourceRaw revisionSource.indexed :=
    rfl
  have preserved := Trace.preservesRawOrigin
    (family := revisionFamily) (Reason := Empty) (Cell := Unit)
    (Owner := Bool) (RetryableFault := Empty) trace sourceLive
  change rawOrigin? revisionFamily Empty revisionTarget.indexed =
    some revisionSourceRaw at preserved
  have equalRaw : revisionTargetRaw = revisionSourceRaw :=
    Option.some.inj preserved
  have equalRevision := congrArg RevisionOrigin.revision equalRaw
  exact Bool.false_ne_true equalRevision.symm

/-- Paired discriminator: one matching joint commit exists, while wrong-owner,
mismatched-index, and in-place revision-change cases are all excluded. -/
theorem indexed_owned_need_boundary :
    Nonempty
        (Step booleanUnit Empty Unit Bool Empty ()
          (evaluating true) (commitEvent true) cachedMatching) /\
      IsEmpty
        (Step booleanUnit Empty Unit Bool Empty ()
          (evaluating true) (commitEvent false) cachedMatching) /\
      Not (Exists fun state : IndexedState =>
        state.owned =
          (.cachedValue false mismatchedPacked :
            Owned.CellState Bool Bool PackedBooleanEvidence
              PackedBooleanRefutation)) /\
      IsEmpty
        (Trace revisionFamily Empty Unit Bool Empty ()
          revisionSource revisionTarget) :=
  ⟨⟨matchingCommit⟩, wrong_owner_commit_empty,
    mismatched_index_excluded, revision_change_requires_fresh_cell⟩

end Canary

#print axioms State.ext
#print axioms StrictPullback.lift_unique
#print axioms Step.toNeed
#print axioms indexedStep_preservesRawOrigin
#print axioms Step.preservesRawOrigin
#print axioms Trace.preservesRawOrigin
#print axioms trace_preserves_origin_coordinate
#print axioms Canary.wrong_owner_commit_empty
#print axioms Canary.mismatched_index_excluded
#print axioms Canary.indexed_projection_not_injective
#print axioms Canary.revision_change_requires_fresh_cell
#print axioms Canary.indexed_owned_need_boundary

end Mettapedia.GSLT.Dynamics.IndexedEvidenceNeedPullback
