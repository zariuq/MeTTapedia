import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.LanguageDef.CompiledPlanOpenActivationViewCompilation

/-!
# Ownership-closed materialization

Materializing a semantic value does not require rebuilding every physical
subgraph.  A runtime result may contain three kinds of component:

* an already-normalized subgraph retained transitively by some owner;
* a constructor whose children still have to be materialized;
* a representation boundary which must be normalized before publication.

This module makes that partition explicit.  A destination-aware compiler
reuses a resident subgraph exactly when its transitive owner is the
destination, copies a foreign resident, recursively builds constructors, and
normalizes every boundary.  The resulting artifact has the same complete
term observation as eager rebuilding and is rooted entirely at the
destination.

The owner coordinate is a physical lifetime certificate, not part of term
meaning.  A concrete runtime must establish it compositionally for the whole
subgraph; shallow ownership of only the root is insufficient.

Lifetime compatibility does not by itself authorize memoized reuse.  Rooting
answers whether an immutable graph may remain referenced; a reuse key must
separately prove that equal keys imply equal observations of the requests it
serves.  The MeTTa term-view specialization states that observer law with an
explicit binding-version coordinate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.OwnershipClosedMaterialization

open Mettapedia.GSLT
open CompiledPlanOpenActivationViewCompilation

universe uOwner uBoundary

variable {Owner : Type uOwner} {Boundary : Type uBoundary}

mutual

/-- A physical term graph before publication.  `resident` certifies a
completely normalized, transitively retained subgraph.  `boundary` names a
carrier whose language-specific normalizer supplies its public meaning. -/
inductive Source (Owner : Type uOwner) (Boundary : Type uBoundary) where
  | resident (owner : Owner) (value : OpenTerm)
  | construct (head : List UInt8) (children : Sources Owner Boundary)
  | boundary (carrier : Boundary)

/-- Authored child order for a physical source graph. -/
inductive Sources (Owner : Type uOwner) (Boundary : Type uBoundary) where
  | nil
  | cons (head : Source Owner Boundary) (tail : Sources Owner Boundary)

end

mutual

/-- A materialized graph records whether an immutable subgraph was retained,
copied, or newly constructed.  The owner remains evidence for lifetime
checking and is erased by semantic observation. -/
inductive Artifact (Owner : Type uOwner) where
  | shared (owner : Owner) (value : OpenTerm)
  | copied (owner : Owner) (value : OpenTerm)
  | constructed (owner : Owner) (head : List UInt8)
      (children : Artifacts Owner)

/-- Authored child order in a materialized graph. -/
inductive Artifacts (Owner : Type uOwner) where
  | nil
  | cons (head : Artifact Owner) (tail : Artifacts Owner)

end


mutual

/-- Complete semantic observation of a physical source graph. -/
def Source.denote (normalize : Boundary -> OpenTerm) :
    Source Owner Boundary -> OpenTerm
  | .resident _ value => value
  | .construct head children => .application head (children.denote normalize)
  | .boundary carrier => normalize carrier

/-- Complete semantic observations of source children. -/
def Sources.denote (normalize : Boundary -> OpenTerm) :
    Sources Owner Boundary -> OpenTerms
  | .nil => .nil
  | .cons head tail => .cons (head.denote normalize) (tail.denote normalize)

end

mutual

/-- Forget physical reuse and observe the published term. -/
def Artifact.denote : Artifact Owner -> OpenTerm
  | .shared _ value => value
  | .copied _ value => value
  | .constructed _ head children => .application head children.denote

/-- Forget physical reuse in an authored child sequence. -/
def Artifacts.denote : Artifacts Owner -> OpenTerms
  | .nil => .nil
  | .cons head tail => .cons head.denote tail.denote

end


mutual

/-- Every pointer retained by an artifact is transitively rooted at the
publication destination. -/
def Artifact.RootedAt (destination : Owner) : Artifact Owner -> Prop
  | .shared owner _ => owner = destination
  | .copied owner _ => owner = destination
  | .constructed owner _ children =>
      owner = destination /\ children.RootedAt destination

/-- Rooting for every child in a materialized sequence. -/
def Artifacts.RootedAt (destination : Owner) : Artifacts Owner -> Prop
  | .nil => True
  | .cons head tail =>
      head.RootedAt destination /\ tail.RootedAt destination

end


mutual

/-- Materialize into one destination.  Equality of owners is the only route
to a `shared` artifact; foreign residents and normalization boundaries become
destination-owned copies. -/
def materialize [DecidableEq Owner]
    (destination : Owner) (normalize : Boundary -> OpenTerm) :
    Source Owner Boundary -> Artifact Owner
  | .resident owner value =>
      if owner = destination then .shared owner value
      else .copied destination value
  | .construct head children =>
      .constructed destination head
        (materializeSources destination normalize children)
  | .boundary carrier => .copied destination (normalize carrier)

/-- Materialize an authored child sequence. -/
def materializeSources [DecidableEq Owner]
    (destination : Owner) (normalize : Boundary -> OpenTerm) :
    Sources Owner Boundary -> Artifacts Owner
  | .nil => .nil
  | .cons head tail =>
      .cons (materialize destination normalize head)
        (materializeSources destination normalize tail)

end

mutual

/-- Destination-aware materialization preserves complete term observation. -/
theorem materialize_exact [DecidableEq Owner]
    (destination : Owner) (normalize : Boundary -> OpenTerm)
    (source : Source Owner Boundary) :
    (materialize destination normalize source).denote =
      source.denote normalize := by
  cases source with
  | resident owner value =>
      by_cases same : owner = destination <;>
        simp [materialize, same, Artifact.denote, Source.denote]
  | construct head children =>
      simp [materialize, Artifact.denote, Source.denote,
        materializeSources_exact destination normalize children]
  | boundary carrier => rfl

/-- Child-sequence form of complete observation preservation. -/
theorem materializeSources_exact [DecidableEq Owner]
    (destination : Owner) (normalize : Boundary -> OpenTerm)
    (sources : Sources Owner Boundary) :
    (materializeSources destination normalize sources).denote =
      sources.denote normalize := by
  cases sources with
  | nil => rfl
  | cons head tail =>
      simp [materializeSources, Artifacts.denote,
        Sources.denote, materialize_exact destination normalize head,
        materializeSources_exact destination normalize tail]

end

mutual

/-- Every compiled graph is transitively rooted at its destination. -/
theorem materialize_rooted [DecidableEq Owner]
    (destination : Owner) (normalize : Boundary -> OpenTerm)
    (source : Source Owner Boundary) :
    (materialize destination normalize source).RootedAt destination := by
  cases source with
  | resident owner value =>
      by_cases same : owner = destination <;>
        simp [materialize, same, Artifact.RootedAt]
  | construct head children =>
      simp [materialize, Artifact.RootedAt,
        materializeSources_rooted destination normalize children]
  | boundary carrier => simp [materialize, Artifact.RootedAt]

/-- Child-sequence form of destination rooting. -/
theorem materializeSources_rooted [DecidableEq Owner]
    (destination : Owner) (normalize : Boundary -> OpenTerm)
    (sources : Sources Owner Boundary) :
    (materializeSources destination normalize sources).RootedAt destination := by
  cases sources with
  | nil => simp [materializeSources, Artifacts.RootedAt]
  | cons head tail =>
      simp [materializeSources, Artifacts.RootedAt,
        materialize_rooted destination normalize head,
        materializeSources_rooted destination normalize tail]

end


/-- Ownership-closed materialization is a certified GSLT realization under
complete term observation. -/
def realization [DecidableEq Owner]
    (destination : Owner) (normalize : Boundary -> OpenTerm) :
    SimpleRealization (Source Owner Boundary) (Artifact Owner) OpenTerm where
  compile := fun _ source => materialize destination normalize source
  observeSource := fun _ source => source.denote normalize
  observeArtifact := fun _ artifact => artifact.denote
  adequate := fun _ source => materialize_exact destination normalize source


/-! ## Structural work refinement -/

mutual

/-- Constructor count of a completely materialized open term. -/
def openTermNodeCount : OpenTerm -> Nat
  | .symbol _ => 1
  | .variable _ => 1
  | .string _ => 1
  | .integer _ => 1
  | .application _ children => 1 + openTermsNodeCount children

/-- Constructor count of a sequence of open terms. -/
def openTermsNodeCount : OpenTerms -> Nat
  | .nil => 0
  | .cons head tail => openTermNodeCount head + openTermsNodeCount tail

end


mutual

/-- Structural construction work of rebuilding every source component. -/
def Source.eagerWork (normalize : Boundary -> OpenTerm) :
    Source Owner Boundary -> Nat
  | .resident _ value => openTermNodeCount value
  | .construct _ children => 1 + children.eagerWork normalize
  | .boundary carrier => openTermNodeCount (normalize carrier)

/-- Eager work over source children. -/
def Sources.eagerWork (normalize : Boundary -> OpenTerm) :
    Sources Owner Boundary -> Nat
  | .nil => 0
  | .cons head tail => head.eagerWork normalize + tail.eagerWork normalize

end


mutual

/-- Structural construction work performed by a materialized artifact.
Retaining an already-rooted immutable subgraph constructs no node. -/
def Artifact.work : Artifact Owner -> Nat
  | .shared _ _ => 0
  | .copied _ value => openTermNodeCount value
  | .constructed _ _ children => 1 + children.work

/-- Construction work over materialized children. -/
def Artifacts.work : Artifacts Owner -> Nat
  | .nil => 0
  | .cons head tail => head.work + tail.work

end


mutual

/-- Destination-aware materialization never performs more structural
construction work than rebuilding every source component. -/
theorem materialize_work_le [DecidableEq Owner]
    (destination : Owner) (normalize : Boundary -> OpenTerm)
    (source : Source Owner Boundary) :
    (materialize destination normalize source).work <=
      source.eagerWork normalize := by
  cases source with
  | resident owner value =>
      by_cases same : owner = destination <;>
        simp [materialize, same, Artifact.work, Source.eagerWork]
  | construct head children =>
      simpa [materialize, Artifact.work, Source.eagerWork] using
        Nat.add_le_add_left
          (materializeSources_work_le destination normalize children) 1
  | boundary carrier => rfl

/-- Child-sequence form of the structural work refinement. -/
theorem materializeSources_work_le [DecidableEq Owner]
    (destination : Owner) (normalize : Boundary -> OpenTerm)
    (sources : Sources Owner Boundary) :
    (materializeSources destination normalize sources).work <=
      sources.eagerWork normalize := by
  cases sources with
  | nil => simp [materializeSources, Artifacts.work,
      Sources.eagerWork]
  | cons head tail =>
      simpa [materializeSources, Artifacts.work,
        Sources.eagerWork] using
        Nat.add_le_add
          (materialize_work_le destination normalize head)
          (materializeSources_work_le destination normalize tail)

end


theorem openTermNodeCount_positive (value : OpenTerm) :
    0 < openTermNodeCount value := by
  cases value <;> simp [openTermNodeCount]

/-- A destination-resident closed subgraph is retained with zero construction
work, strictly less than rebuilding its nonempty semantic tree. -/
theorem resident_reuse_strict [DecidableEq Owner]
    (destination : Owner) (normalize : Boundary -> OpenTerm)
    (value : OpenTerm) :
    (materialize destination normalize
        (.resident destination value)).work <
      (Source.resident destination value).eagerWork normalize := by
  simp [materialize, Artifact.work, Source.eagerWork,
    openTermNodeCount_positive]


/-! ## Construction/publication fusion -/

mutual

/-- The first half of an eager two-region pipeline: rebuild the complete
source graph in a temporary owner, even when a resident child was already
rooted somewhere longer-lived. -/
def stage (temporary : Owner) (normalize : Boundary -> OpenTerm) :
    Source Owner Boundary -> Artifact Owner
  | .resident _ value => .copied temporary value
  | .construct head children =>
      .constructed temporary head (stageSources temporary normalize children)
  | .boundary carrier => .copied temporary (normalize carrier)

/-- Eager temporary construction over an authored child sequence. -/
def stageSources (temporary : Owner) (normalize : Boundary -> OpenTerm) :
    Sources Owner Boundary -> Artifacts Owner
  | .nil => .nil
  | .cons head tail =>
      .cons (stage temporary normalize head)
        (stageSources temporary normalize tail)

end

mutual

/-- Temporary construction preserves the complete source observation. -/
theorem stage_exact
    (temporary : Owner) (normalize : Boundary -> OpenTerm)
    (source : Source Owner Boundary) :
    (stage temporary normalize source).denote = source.denote normalize := by
  cases source with
  | resident owner value => rfl
  | construct head children =>
      simp [stage, Artifact.denote, Source.denote,
        stageSources_exact temporary normalize children]
  | boundary carrier => rfl

/-- Child-sequence form of temporary observation preservation. -/
theorem stageSources_exact
    (temporary : Owner) (normalize : Boundary -> OpenTerm)
    (sources : Sources Owner Boundary) :
    (stageSources temporary normalize sources).denote =
      sources.denote normalize := by
  cases sources with
  | nil => rfl
  | cons head tail =>
      simp [stageSources, Artifacts.denote, Sources.denote,
        stage_exact temporary normalize head,
        stageSources_exact temporary normalize tail]

end


mutual

/-- The temporary stage owns every ordinary pointer it creates. -/
theorem stage_rooted
    (temporary : Owner) (normalize : Boundary -> OpenTerm)
    (source : Source Owner Boundary) :
    (stage temporary normalize source).RootedAt temporary := by
  cases source with
  | resident owner value => simp [stage, Artifact.RootedAt]
  | construct head children =>
      simp [stage, Artifact.RootedAt,
        stageSources_rooted temporary normalize children]
  | boundary carrier => simp [stage, Artifact.RootedAt]

/-- Child-sequence form of temporary rooting. -/
theorem stageSources_rooted
    (temporary : Owner) (normalize : Boundary -> OpenTerm)
    (sources : Sources Owner Boundary) :
    (stageSources temporary normalize sources).RootedAt temporary := by
  cases sources with
  | nil => simp [stageSources, Artifacts.RootedAt]
  | cons head tail =>
      simp [stageSources, Artifacts.RootedAt,
        stage_rooted temporary normalize head,
        stageSources_rooted temporary normalize tail]

end


mutual

/-- Eager temporary construction performs exactly the structural work of
rebuilding every source component. -/
theorem stage_work_eq
    (temporary : Owner) (normalize : Boundary -> OpenTerm)
    (source : Source Owner Boundary) :
    (stage temporary normalize source).work = source.eagerWork normalize := by
  cases source with
  | resident owner value => rfl
  | construct head children =>
      simp [stage, Artifact.work, Source.eagerWork,
        stageSources_work_eq temporary normalize children]
  | boundary carrier => rfl

/-- Child-sequence form of the exact temporary work equation. -/
theorem stageSources_work_eq
    (temporary : Owner) (normalize : Boundary -> OpenTerm)
    (sources : Sources Owner Boundary) :
    (stageSources temporary normalize sources).work =
      sources.eagerWork normalize := by
  cases sources with
  | nil => rfl
  | cons head tail =>
      simp [stageSources, Artifacts.work, Sources.eagerWork,
        stage_work_eq temporary normalize head,
        stageSources_work_eq temporary normalize tail]

end


/-- Physical evidence for the unfused implementation: first construct a
temporary artifact, then copy its complete denotation into the publication
owner. -/
structure StagedPublication (Owner : Type uOwner) where
  temporary : Artifact Owner
  published : Artifact Owner

/-- Complete public observation of a staged publication. -/
def StagedPublication.denote (pipeline : StagedPublication Owner) : OpenTerm :=
  pipeline.published.denote

/-- Total structural construction work across both regions. -/
def StagedPublication.work (pipeline : StagedPublication Owner) : Nat :=
  pipeline.temporary.work + pipeline.published.work

/-- The ordinary construct-then-copy pipeline. -/
def eagerPipeline
    (destination temporary : Owner) (normalize : Boundary -> OpenTerm)
    (source : Source Owner Boundary) : StagedPublication Owner :=
  { temporary := stage temporary normalize source
    published := .copied destination (source.denote normalize) }

/-- The two-region pipeline preserves complete term observation. -/
@[simp] theorem eagerPipeline_exact
    (destination temporary : Owner) (normalize : Boundary -> OpenTerm)
    (source : Source Owner Boundary) :
    (eagerPipeline destination temporary normalize source).denote =
      source.denote normalize :=
  rfl

/-- The published half of the two-region pipeline is rooted at its requested
destination. -/
theorem eagerPipeline_rooted
    (destination temporary : Owner) (normalize : Boundary -> OpenTerm)
    (source : Source Owner Boundary) :
    (eagerPipeline destination temporary normalize source).published.RootedAt
      destination := by
  simp [eagerPipeline, Artifact.RootedAt]

/-- Fusing result-spine construction with publication never performs more
structural construction work than building the same result in a temporary
region and then copying it. -/
theorem fused_work_le_pipeline [DecidableEq Owner]
    (destination temporary : Owner) (normalize : Boundary -> OpenTerm)
    (source : Source Owner Boundary) :
    (materialize destination normalize source).work <=
      (eagerPipeline destination temporary normalize source).work := by
  have fused_le := materialize_work_le destination normalize source
  have staged_eq := stage_work_eq temporary normalize source
  simp only [StagedPublication.work, eagerPipeline, Artifact.work]
  omega

/-- A constructor around a destination-resident nonempty value is a strict
fusion win: direct publication builds only the new constructor, whereas the
two-stage pipeline rebuilds the resident value and copies the whole result. -/
theorem fused_constructor_resident_strict [DecidableEq Owner]
    (destination temporary : Owner) (normalize : Boundary -> OpenTerm)
    (head : List UInt8) (value : OpenTerm) :
    (materialize destination normalize
        (.construct head
          (.cons (.resident destination value) .nil))).work <
      (eagerPipeline destination temporary normalize
        (.construct head
          (.cons (.resident destination value) .nil))).work := by
  simp [materialize, materializeSources, Artifact.work,
    eagerPipeline, StagedPublication.work, stage, stageSources,
    Source.denote, Sources.denote, Artifacts.work, openTermNodeCount,
    openTermsNodeCount]
  omega


/-! ## Allocation reachability at publication

Semantic exactness and destination ownership do not say that every allocation
made in the destination is reachable from the published root.  The distinction
matters for region allocators: unreachable destination-owned intermediates
cannot be reclaimed by releasing a temporary region.

`unreachable` is ghost evidence supplied by a concrete allocation trace.  An
implementation refinement must justify that classification from its pointer
graph; this model does not infer it from the root owner.
-/

/-- A publication together with the destination-owned artifacts allocated by
the same run but not reachable from the published root. -/
structure PublicationTrace (Owner : Type uOwner) where
  published : Artifact Owner
  unreachable : Artifacts Owner

/-- Only the published root contributes to the language observation. -/
def PublicationTrace.denote (trace : PublicationTrace Owner) : OpenTerm :=
  trace.published.denote

/-- Every retained allocation has a lifetime compatible with the destination.
This is intentionally weaker than output reachability. -/
def PublicationTrace.RootedAt
    (destination : Owner) (trace : PublicationTrace Owner) : Prop :=
  trace.published.RootedAt destination /\
    trace.unreachable.RootedAt destination

/-- No allocation made by the run remains outside the published result graph. -/
def PublicationTrace.OutputClosed (trace : PublicationTrace Owner) : Prop :=
  trace.unreachable = .nil

/-- Total construction work includes both observable and unreachable work. -/
def PublicationTrace.work (trace : PublicationTrace Owner) : Nat :=
  trace.published.work + trace.unreachable.work

/-- The output-only realization records precisely the materialized result and
no unreachable destination allocation. -/
def outputOnlyTrace [DecidableEq Owner]
    (destination : Owner) (normalize : Boundary -> OpenTerm)
    (source : Source Owner Boundary) : PublicationTrace Owner where
  published := materialize destination normalize source
  unreachable := .nil

/-- A broad destination realization models the failed shape: an eager
intermediate is allocated directly in the publication region, then an exact
result is independently published. -/
def retainedIntermediateTrace [DecidableEq Owner]
    (destination : Owner) (normalize : Boundary -> OpenTerm)
    (source : Source Owner Boundary) : PublicationTrace Owner where
  published := materialize destination normalize source
  unreachable := .cons (stage destination normalize source) .nil

@[simp] theorem outputOnlyTrace_exact [DecidableEq Owner]
    (destination : Owner) (normalize : Boundary -> OpenTerm)
    (source : Source Owner Boundary) :
    (outputOnlyTrace destination normalize source).denote =
      source.denote normalize :=
  materialize_exact destination normalize source

theorem outputOnlyTrace_rooted [DecidableEq Owner]
    (destination : Owner) (normalize : Boundary -> OpenTerm)
    (source : Source Owner Boundary) :
    (outputOnlyTrace destination normalize source).RootedAt destination := by
  simp [outputOnlyTrace, PublicationTrace.RootedAt, Artifacts.RootedAt,
    materialize_rooted]

@[simp] theorem outputOnlyTrace_outputClosed [DecidableEq Owner]
    (destination : Owner) (normalize : Boundary -> OpenTerm)
    (source : Source Owner Boundary) :
    (outputOnlyTrace destination normalize source).OutputClosed :=
  rfl

@[simp] theorem outputOnlyTrace_work [DecidableEq Owner]
    (destination : Owner) (normalize : Boundary -> OpenTerm)
    (source : Source Owner Boundary) :
    (outputOnlyTrace destination normalize source).work =
      (materialize destination normalize source).work := by
  simp [outputOnlyTrace, PublicationTrace.work, Artifacts.work]

@[simp] theorem retainedIntermediateTrace_exact [DecidableEq Owner]
    (destination : Owner) (normalize : Boundary -> OpenTerm)
    (source : Source Owner Boundary) :
    (retainedIntermediateTrace destination normalize source).denote =
      source.denote normalize :=
  materialize_exact destination normalize source

theorem retainedIntermediateTrace_rooted [DecidableEq Owner]
    (destination : Owner) (normalize : Boundary -> OpenTerm)
    (source : Source Owner Boundary) :
    (retainedIntermediateTrace destination normalize source).RootedAt
      destination := by
  simp [retainedIntermediateTrace, PublicationTrace.RootedAt,
    Artifacts.RootedAt, materialize_rooted, stage_rooted]

theorem retainedIntermediateTrace_not_outputClosed [DecidableEq Owner]
    (destination : Owner) (normalize : Boundary -> OpenTerm)
    (source : Source Owner Boundary) :
    ¬ (retainedIntermediateTrace destination normalize source).OutputClosed := by
  simp [retainedIntermediateTrace, PublicationTrace.OutputClosed]

/-- Every source forces at least one semantic node under eager rebuilding. -/
theorem Source.eagerWork_positive
    (normalize : Boundary -> OpenTerm)
    (source : Source Owner Boundary) :
    0 < source.eagerWork normalize := by
  cases source with
  | resident owner value =>
      simpa [Source.eagerWork] using openTermNodeCount_positive value
  | construct head children => simp [Source.eagerWork]
  | boundary carrier =>
      simpa [Source.eagerWork] using
        openTermNodeCount_positive (normalize carrier)

/-- Retaining an eager intermediate in the destination performs strictly more
work than publishing only the selected result. -/
theorem retainedIntermediateTrace_work_gt_outputOnly [DecidableEq Owner]
    (destination : Owner) (normalize : Boundary -> OpenTerm)
    (source : Source Owner Boundary) :
    (outputOnlyTrace destination normalize source).work <
      (retainedIntermediateTrace destination normalize source).work := by
  rw [outputOnlyTrace_work]
  simp only [retainedIntermediateTrace, PublicationTrace.work,
    Artifacts.work]
  rw [stage_work_eq]
  exact Nat.lt_add_of_pos_right (Source.eagerWork_positive normalize source)

/-- Complete semantic agreement plus destination-compatible lifetimes cannot
establish allocation reachability. -/
theorem exact_and_rooted_do_not_imply_outputClosed [DecidableEq Owner]
    (destination : Owner) (normalize : Boundary -> OpenTerm)
    (source : Source Owner Boundary) :
    ∃ trace : PublicationTrace Owner,
      trace.denote = source.denote normalize /\
      trace.RootedAt destination /\
      ¬ trace.OutputClosed := by
  exact ⟨retainedIntermediateTrace destination normalize source,
    retainedIntermediateTrace_exact destination normalize source,
    retainedIntermediateTrace_rooted destination normalize source,
    retainedIntermediateTrace_not_outputClosed destination normalize source⟩


/-! ## Positive and negative controls -/

namespace Canaries

inductive CanaryOwner
  | destination
  | foreign
deriving DecidableEq, Repr

def sampleValue : OpenTerm :=
  .application [1] (.cons (.symbol [2]) (.cons (.integer 3) .nil))

def mixedSource : Source CanaryOwner OpenTerm :=
  .construct [9]
    (.cons (.resident .destination sampleValue)
      (.cons (.resident .foreign (.symbol [4]))
        (.cons (.boundary (.symbol [5])) .nil)))

/-- A destination-resident subgraph is retained by pointer identity. -/
example :
    materialize CanaryOwner.destination id
        (Source.resident CanaryOwner.destination sampleValue) =
      Artifact.shared CanaryOwner.destination sampleValue := by
  rfl

/-- A foreign resident is copied into the destination rather than retained. -/
example :
    materialize CanaryOwner.destination id
        (Source.resident CanaryOwner.foreign sampleValue) =
      Artifact.copied CanaryOwner.destination sampleValue := by
  rfl

/-- A normalization boundary is copied even when its semantic value is
already an ordinary term. -/
example :
    materialize CanaryOwner.destination id (Source.boundary sampleValue) =
      Artifact.copied CanaryOwner.destination sampleValue := by
  rfl

/-- The mixed graph preserves its complete public value. -/
theorem mixedSource_exact :
    (materialize CanaryOwner.destination id mixedSource).denote =
      mixedSource.denote id :=
  materialize_exact CanaryOwner.destination id mixedSource

/-- The mixed graph is rooted entirely at the publication destination. -/
theorem mixedSource_rooted :
    (materialize CanaryOwner.destination id mixedSource).RootedAt
      CanaryOwner.destination :=
  materialize_rooted CanaryOwner.destination id mixedSource

/-- Negative: retaining a foreign resident directly violates the lifetime
contract even though its term denotation would be unchanged. -/
theorem foreign_sharing_is_not_rooted :
    ¬ ((Artifact.shared CanaryOwner.foreign sampleValue).RootedAt
      CanaryOwner.destination) := by
  simp [Artifact.RootedAt]

end Canaries


#print axioms materialize_exact
#print axioms materialize_rooted
#print axioms materialize_work_le
#print axioms resident_reuse_strict
#print axioms stage_exact
#print axioms stage_rooted
#print axioms stage_work_eq
#print axioms eagerPipeline_exact
#print axioms eagerPipeline_rooted
#print axioms fused_work_le_pipeline
#print axioms fused_constructor_resident_strict
#print axioms outputOnlyTrace_exact
#print axioms outputOnlyTrace_rooted
#print axioms retainedIntermediateTrace_exact
#print axioms retainedIntermediateTrace_rooted
#print axioms retainedIntermediateTrace_not_outputClosed
#print axioms retainedIntermediateTrace_work_gt_outputOnly
#print axioms exact_and_rooted_do_not_imply_outputClosed
#print axioms Canaries.foreign_sharing_is_not_rooted

end Mettapedia.GSLT.LanguageDef.OwnershipClosedMaterialization
