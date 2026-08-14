import Mathlib.Data.Finset.Basic
import Mettapedia.GSLT.Core.IndexedOperational
import Mettapedia.GSLT.Dynamics.AnswerEffect
import Mettapedia.GSLT.Dynamics.ProofRelevantNeed

/-!
# Modular profiles for proof-relevant need

The cell protocol supplies a maximal vocabulary of exact events.  A language
does not acquire that whole vocabulary by importing it.  Instead it may choose
independently:

* an executable operator fragment;
* a demand-right algebra and a held set of rights;
* an exact decomposition of guest outcomes into cached values, cached stable
  faults, and retryable faults;
* an event valuation such as cost, provenance, evidence, or priority.

These axes are deliberately not bundled into a distinguished `Prime` object.
Operator inclusion gives forward operational translations between fragment
GSLTs.  Rights attenuate fail-closed.  Outcome decompositions are lossless
isomorphisms rather than unproved classifiers.
-/

namespace Mettapedia.GSLT.Dynamics.ProofRelevantNeed

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Dynamics.OccurrenceSemantics

universe uCell uOrigin uValue uStableFault uRetryableFault uRight uGuest
  uSpace uRequest uAnswer uKey uCause

/-! ## Revision decoration of occurrence sources -/

variable {Space : Type uSpace} {Request : Type uRequest}
  {Answer : Type uAnswer}

/-- Revision identity is independent of occurrence enumeration.  A key may
depend on both the space and the exact request. -/
structure RevisionKeying (Space : Type uSpace) (Request : Type uRequest) where
  Key : Type uKey
  key : Space → Request → Key

/-- Occurrence terms decorated with an explicit revision/cache key. -/
inductive RevisionedOccurrenceTerm
    (source : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying Space Request) where
  | request (space : Space) (request : Request)
  | answer (space : Space) (request : Request) (key : keying.Key)
      (occurrence : Nat) (answer : Answer)

/-- Revision decoration changes term identity but not occurrence admission:
every generated answer carries the canonical key of its request. -/
inductive RevisionedOccurrenceStep [DecidableEq Answer]
    (source : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying Space Request) :
    RevisionedOccurrenceTerm source keying →
      RevisionedOccurrenceTerm source keying → Prop where
  | found {space request occurrence answer}
      (copy : occurrence < Multiset.count answer
        (source.occurrences space request)) :
      RevisionedOccurrenceStep source keying (.request space request)
        (.answer space request (keying.key space request) occurrence answer)

/-- The revision-decorated occurrence GSLT. -/
def revisionedOccurrenceGSLT [DecidableEq Answer]
    (source : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying Space Request) : GSLT where
  Term := RevisionedOccurrenceTerm source keying
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := RevisionedOccurrenceStep source keying
  rewrites_resp_left := by
    intro sourceTerm sourceTerm' target equal step
    subst sourceTerm'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro sourceTerm target target' step equal
    subst target'
    exact step

@[simp] theorem revisionedOccurrenceGSLT_step_iff [DecidableEq Answer]
    (source : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying Space Request)
    (space : Space) (request : Request) (answer : Answer)
    (occurrence : Nat) :
    (revisionedOccurrenceGSLT source keying).Step
        (.request space request)
        (.answer space request (keying.key space request) occurrence answer) ↔
      occurrence < Multiset.count answer
        (source.occurrences space request) := by
  constructor
  · intro step
    cases step
    assumption
  · exact RevisionedOccurrenceStep.found

/-- Add the canonical revision key to every unkeyed occurrence term. -/
def decorateRevision
    (source : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying Space Request) :
    OccurrenceTerm source → RevisionedOccurrenceTerm source keying
  | .request space request => .request space request
  | .answer space request occurrence answer =>
      .answer space request (keying.key space request) occurrence answer

/-- Forget only the revision key while retaining request and occurrence
identity. -/
def forgetRevision
    (source : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying Space Request) :
    RevisionedOccurrenceTerm source keying → OccurrenceTerm source
  | .request space request => .request space request
  | .answer space request _ occurrence answer =>
      .answer space request occurrence answer

/-- Revision decoration retains the complete answer-bag meaning and changes
only artifact identity. -/
def revisionedOccurrenceMeaning
    (source : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying Space Request) :
    RevisionedOccurrenceTerm source keying → Multiset Answer :=
  occurrenceMeaning source ∘ forgetRevision source keying

/-- Revision-decorated occurrence selection preserves its underlying answer
bag. -/
def revisionedOccurrenceElaboration [DecidableEq Answer]
    (source : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying Space Request) :
    GSLT.Elaboration (revisionedOccurrenceGSLT source keying)
      (Multiset Answer) where
  elaborate := fun term => some (revisionedOccurrenceMeaning source keying term)
  equation := by
    intro first second equal
    cases equal
    rfl
  rewrite := by
    intro first second step
    cases step
    rfl

@[simp] theorem forgetRevision_decorateRevision
    (source : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying Space Request)
    (term : OccurrenceTerm source) :
    forgetRevision source keying (decorateRevision source keying term) = term := by
  cases term <;> rfl

theorem decorateRevision_injective
    (source : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying Space Request) :
    Function.Injective (decorateRevision source keying) := by
  intro first second equal
  have forgotten := congrArg (forgetRevision source keying) equal
  simpa using forgotten

/-- Revision decoration is a faithful structural embedding: it changes
identity carried by answer artifacts without adding or removing occurrence
steps between decorated source terms. -/
def revisionDecorationEmbedding [DecidableEq Answer]
    (source : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying Space Request) :
    GSLT.Embedding (occurrenceGSLT source)
      (revisionedOccurrenceGSLT source keying) where
  toFun := decorateRevision source keying
  injective := decorateRevision_injective source keying
  equiv_iff := by
    intro first second
    change decorateRevision source keying first =
        decorateRevision source keying second ↔ first = second
    exact ⟨fun equal => decorateRevision_injective source keying equal,
      congrArg _⟩
  step_iff := by
    intro first second
    cases first with
    | request firstSpace firstRequest =>
        cases second with
        | request secondSpace secondRequest =>
            constructor <;> intro step <;> cases step
        | answer secondSpace secondRequest occurrence answer =>
            constructor
            · intro step
              cases step with
              | found copy => exact OccurrenceStep.found copy
            · intro step
              cases step with
              | found copy => exact RevisionedOccurrenceStep.found copy
    | answer firstSpace firstRequest firstOccurrence firstAnswer =>
        cases second with
        | request secondSpace secondRequest =>
            constructor <;> intro step <;> cases step
        | answer secondSpace secondRequest secondOccurrence secondAnswer =>
            constructor <;> intro step <;> cases step

/-- The exact observation of revision decoration forgets the key and nothing
else. -/
def revisionDecorationObserved [DecidableEq Answer]
    (source : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying Space Request) :
    GSLT.Embedding.Observed (occurrenceGSLT source)
      (revisionedOccurrenceGSLT source keying) (OccurrenceTerm source) where
  toEmbedding := revisionDecorationEmbedding source keying
  observeSource := id
  observeTarget := forgetRevision source keying
  preserves := forgetRevision_decorateRevision source keying

/-- At the semantic observation, revision decoration preserves the entire
answer bag. This is weaker than the exact artifact observation above and is
named separately to keep those two claims distinct. -/
def revisionDecorationBagObserved [DecidableEq Answer]
    (source : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying Space Request) :
    GSLT.Embedding.Observed (occurrenceGSLT source)
      (revisionedOccurrenceGSLT source keying) (Multiset Answer) where
  toEmbedding := revisionDecorationEmbedding source keying
  observeSource := occurrenceMeaning source
  observeTarget := revisionedOccurrenceMeaning source keying
  preserves := by
    intro term
    cases term <;> rfl

/-- A noncanonical keyed answer is outside the image of revision decoration.
The target carrier may represent such artifacts even though the generated
step relation only produces canonical keys. -/
theorem noncanonical_answer_not_in_decoration_image
    (source : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying Space Request)
    (space : Space) (request : Request) (key : keying.Key)
    (occurrence : Nat) (answer : Answer)
    (noncanonical : key ≠ keying.key space request) :
    ∀ term,
      decorateRevision source keying term ≠
        RevisionedOccurrenceTerm.answer space request key occurrence answer := by
  intro term equal
  cases term with
  | request => cases equal
  | answer =>
      cases equal
      exact noncanonical rfl

/-- A stronger, independent layer supplies sound and complete explanations
for admitted answer values. Enumeration alone does not choose this family or
its evidence vocabulary. -/
structure CausalOccurrenceSource [DecidableEq Answer]
    (source : OccurrenceSource Space Request Answer) where
  Cause : Space → Request → Answer → Type uCause
  sound : ∀ {space request answer}, Cause space request answer →
    answer ∈ source.occurrences space request
  complete : ∀ space request answer,
    answer ∈ source.occurrences space request →
      Nonempty (Cause space request answer)

/-- A sound causal layer cannot explain an answer absent from the selected
occurrence bag. -/
theorem CausalOccurrenceSource.no_cause_of_not_mem [DecidableEq Answer]
    {source : OccurrenceSource Space Request Answer}
    (causal : CausalOccurrenceSource source)
    {space : Space} {request : Request} {answer : Answer}
    (absent : answer ∉ source.occurrences space request) :
    ¬ Nonempty (causal.Cause space request answer) := by
  rintro ⟨cause⟩
  exact absent (causal.sound cause)

/-! ## Revisioned operational specification regions -/

end Mettapedia.GSLT.Dynamics.ProofRelevantNeed

namespace Mettapedia.GSLT.Dynamics.OperationalRegion

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Dynamics.OccurrenceSemantics
open Mettapedia.GSLT.Dynamics.ProofRelevantNeed

/-- A revision layer is selected over an operational point, not baked into
the definition of that point or its answer source. -/
structure RevisionLayer {Request Answer : Type} [DecidableEq Answer]
    (base : OccurrencePoint Request Answer) where
  keying : RevisionKeying base.Space Request
  keyDecidableEq : DecidableEq keying.Key

attribute [instance] RevisionLayer.keyDecidableEq

/-- A Prime-shaped operational point: an occurrence host, a selected revision
decoration, and a total theory faithfully hosting both.  Reflection, causal
evidence, presentation, and runtime realization remain independent layers. -/
structure RevisionedPoint (Request Answer : Type) [DecidableEq Answer] where
  base : OccurrencePoint Request Answer
  revision : RevisionLayer base
  total : GSLT
  baseEmbedding : GSLT.Embedding base.host total
  revisionEmbedding : GSLT.Embedding
    (revisionedOccurrenceGSLT base.source revision.keying) total

namespace RevisionedPoint

/-- A typed arrow between revisioned points.  Besides the base square, it
retains the revision and total-theory translations and both hosting squares. -/
structure Hom {Request Answer : Type} [DecidableEq Answer]
    (first second : RevisionedPoint Request Answer) where
  base : OccurrencePoint.Hom first.base second.base
  revision : OperationalTranslation
    (revisionedOccurrenceGSLT first.base.source first.revision.keying)
    (revisionedOccurrenceGSLT second.base.source second.revision.keying)
  total : OperationalTranslation first.total second.total
  decoration_commutes : ∀ term,
    revision.mapTerm
        (decorateRevision first.base.source first.revision.keying term) =
      decorateRevision second.base.source second.revision.keying
        (base.occurrence.mapTerm term)
  base_commutes : ∀ term,
    total.mapTerm (first.baseEmbedding.toFun term) =
      second.baseEmbedding.toFun (base.host.mapTerm term)
  revision_commutes : ∀ term,
    total.mapTerm (first.revisionEmbedding.toFun term) =
      second.revisionEmbedding.toFun (revision.mapTerm term)

namespace Hom

@[ext]
theorem ext {Request Answer : Type} [DecidableEq Answer]
    {first second : RevisionedPoint Request Answer}
    {left right : Hom first second}
    (base : left.base = right.base)
    (revision : left.revision = right.revision)
    (total : left.total = right.total) : left = right := by
  cases left
  cases right
  cases base
  cases revision
  cases total
  rfl

/-- Identity preserves every selected layer and commuting square. -/
def id {Request Answer : Type} [DecidableEq Answer]
    (point : RevisionedPoint Request Answer) : Hom point point where
  base := OccurrencePoint.Hom.id point.base
  revision := OperationalTranslation.id _
  total := OperationalTranslation.id _
  decoration_commutes := by intro; rfl
  base_commutes := by intro; rfl
  revision_commutes := by intro; rfl

/-- Revisioned operational arrows compose without discarding their layer
squares. -/
def comp {Request Answer : Type} [DecidableEq Answer]
    {first middle last : RevisionedPoint Request Answer}
    (earlier : Hom first middle) (later : Hom middle last) :
    Hom first last where
  base := earlier.base.comp later.base
  revision := earlier.revision.comp later.revision
  total := earlier.total.comp later.total
  decoration_commutes := by
    intro term
    change later.revision.mapTerm
        (earlier.revision.mapTerm
          (decorateRevision first.base.source first.revision.keying term)) =
      decorateRevision last.base.source last.revision.keying
        (later.base.occurrence.mapTerm
          (earlier.base.occurrence.mapTerm term))
    rw [earlier.decoration_commutes, later.decoration_commutes]
  base_commutes := by
    intro term
    change later.total.mapTerm
        (earlier.total.mapTerm (first.baseEmbedding.toFun term)) =
      last.baseEmbedding.toFun
        (later.base.host.mapTerm (earlier.base.host.mapTerm term))
    rw [earlier.base_commutes, later.base_commutes]
  revision_commutes := by
    intro term
    change later.total.mapTerm
        (earlier.total.mapTerm (first.revisionEmbedding.toFun term)) =
      last.revisionEmbedding.toFun
        (later.revision.mapTerm (earlier.revision.mapTerm term))
    rw [earlier.revision_commutes, later.revision_commutes]

end Hom

instance {Request Answer : Type} [DecidableEq Answer] :
    CategoryTheory.Category (RevisionedPoint Request Answer) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp morphism := by
    apply Hom.ext
    · apply OccurrencePoint.Hom.ext <;>
        apply OperationalTranslation.ext <;> rfl
    · apply OperationalTranslation.ext; rfl
    · apply OperationalTranslation.ext; rfl
  comp_id morphism := by
    apply Hom.ext
    · apply OccurrencePoint.Hom.ext <;>
        apply OperationalTranslation.ext <;> rfl
    · apply OperationalTranslation.ext; rfl
    · apply OperationalTranslation.ext; rfl
  assoc first second third := by
    apply Hom.ext
    · apply OccurrencePoint.Hom.ext <;>
        apply OperationalTranslation.ext <;> rfl
    · apply OperationalTranslation.ext; rfl
    · apply OperationalTranslation.ext; rfl

/-- Forgetting the selected revision and total host is a functor to the base
operational region.  This is the proved relationship; no lifting universal
property is asserted. -/
def forgetBase {Request Answer : Type} [DecidableEq Answer] :
    CategoryTheory.Functor (RevisionedPoint Request Answer)
      (OccurrencePoint Request Answer) where
  obj point := point.base
  map morphism := morphism.base
  map_id _ := rfl
  map_comp _ _ := rfl

end RevisionedPoint

end Mettapedia.GSLT.Dynamics.OperationalRegion

namespace Mettapedia.GSLT.Dynamics.ProofRelevantNeed

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Dynamics.OccurrenceSemantics

variable {Space : Type uSpace} {Request : Type uRequest}
  {Answer : Type uAnswer}

/-! ## Hosting a revision layer over a selected operational point -/

/-- A host term demands revisioned evaluation exactly when it is equivalent
to an embedded occurrence request and the runtime target is equivalent to the
corresponding embedded revisioned request. Equivalence closure makes this
usable with nontrivial host equations. -/
def HostedRevisionDemand [DecidableEq Answer]
    (source : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying Space Request)
    {host runtime : GSLT}
    (hostOccurrence : GSLT.Embedding (occurrenceGSLT source) host)
    (runtimeRevision : GSLT.Embedding
      (revisionedOccurrenceGSLT source keying) runtime) :
    host.Term → runtime.Term → Prop :=
  fun hostTerm runtimeTerm =>
    ∃ space request,
      host.Equiv hostTerm
          (hostOccurrence.toFun (.request space request)) ∧
        runtime.Equiv runtimeTerm
          (runtimeRevision.toFun (.request space request))

/-- A revisioned answer returns to a host exactly at the underlying embedded
occurrence answer. The key is canonical for the selected request. -/
def HostedRevisionReturn [DecidableEq Answer]
    (source : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying Space Request)
    {host runtime : GSLT}
    (hostOccurrence : GSLT.Embedding (occurrenceGSLT source) host)
    (runtimeRevision : GSLT.Embedding
      (revisionedOccurrenceGSLT source keying) runtime) :
    runtime.Term → host.Term → Prop :=
  fun runtimeTerm hostTerm =>
    ∃ space request occurrence answer,
      runtime.Equiv runtimeTerm
          (runtimeRevision.toFun
            (.answer space request (keying.key space request)
              occurrence answer)) ∧
        host.Equiv hostTerm
          (hostOccurrence.toFun
            (.answer space request occurrence answer))

/-- Generic assembly seam between a selected occurrence-hosting theory and a
runtime that hosts its revision decoration. No language name or evaluator
backend occurs in this construction. -/
def hostedRevisionInteraction [DecidableEq Answer]
    (source : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying Space Request)
    {host runtime : GSLT}
    (hostOccurrence : GSLT.Embedding (occurrenceGSLT source) host)
    (runtimeRevision : GSLT.Embedding
      (revisionedOccurrenceGSLT source keying) runtime) :
    GSLT.Interaction host runtime where
  leftToRight := HostedRevisionDemand source keying
    hostOccurrence runtimeRevision
  rightToLeft := HostedRevisionReturn source keying
    hostOccurrence runtimeRevision
  leftToRight_resp_left := by
    intro first second target equivalent crossing
    rcases crossing with ⟨space, request, firstRequest, targetRequest⟩
    refine ⟨target, ⟨space, request, ?_, targetRequest⟩,
      runtime.equations.refl target⟩
    exact host.equations.trans (host.equations.symm equivalent) firstRequest
  leftToRight_resp_right := by
    intro first target target' crossing equivalent
    rcases crossing with ⟨space, request, firstRequest, targetRequest⟩
    exact ⟨space, request, firstRequest,
      runtime.equations.trans (runtime.equations.symm equivalent)
        targetRequest⟩
  rightToLeft_resp_left := by
    intro first second target equivalent crossing
    rcases crossing with
      ⟨space, request, occurrence, answer, firstAnswer, targetAnswer⟩
    refine ⟨target,
      ⟨space, request, occurrence, answer, ?_, targetAnswer⟩,
      host.equations.refl target⟩
    exact runtime.equations.trans (runtime.equations.symm equivalent) firstAnswer
  rightToLeft_resp_right := by
    intro first target target' crossing equivalent
    rcases crossing with
      ⟨space, request, occurrence, answer, firstAnswer, targetAnswer⟩
    exact ⟨space, request, occurrence, answer, firstAnswer,
      host.equations.trans (host.equations.symm equivalent) targetAnswer⟩

/-- Every embedded occurrence request has the generic demand crossing. -/
theorem hostedRevisionInteraction_demand [DecidableEq Answer]
    (source : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying Space Request)
    {host runtime : GSLT}
    (hostOccurrence : GSLT.Embedding (occurrenceGSLT source) host)
    (runtimeRevision : GSLT.Embedding
      (revisionedOccurrenceGSLT source keying) runtime)
    (space : Space) (request : Request) :
    (hostedRevisionInteraction source keying hostOccurrence runtimeRevision).leftToRight
      (hostOccurrence.toFun (.request space request))
      (runtimeRevision.toFun (.request space request)) :=
  ⟨space, request, host.equations.refl _, runtime.equations.refl _⟩

/-- Every canonical revisioned answer has the generic return crossing. -/
theorem hostedRevisionInteraction_return [DecidableEq Answer]
    (source : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying Space Request)
    {host runtime : GSLT}
    (hostOccurrence : GSLT.Embedding (occurrenceGSLT source) host)
    (runtimeRevision : GSLT.Embedding
      (revisionedOccurrenceGSLT source keying) runtime)
    (space : Space) (request : Request) (occurrence : Nat)
    (answer : Answer) :
    (hostedRevisionInteraction source keying hostOccurrence runtimeRevision).rightToLeft
      (runtimeRevision.toFun
        (.answer space request (keying.key space request) occurrence answer))
      (hostOccurrence.toFun (.answer space request occurrence answer)) :=
  ⟨space, request, occurrence, answer,
    runtime.equations.refl _, host.equations.refl _⟩

/-- Negative boundary: a host term outside every embedded request-equivalence
class cannot enter the revision runtime through this seam. -/
theorem no_hostedRevisionDemand_of_no_request [DecidableEq Answer]
    (source : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying Space Request)
    {host runtime : GSLT}
    (hostOccurrence : GSLT.Embedding (occurrenceGSLT source) host)
    (runtimeRevision : GSLT.Embedding
      (revisionedOccurrenceGSLT source keying) runtime)
    (hostTerm : host.Term)
    (notRequest : ∀ space request,
      ¬ host.Equiv hostTerm
        (hostOccurrence.toFun (.request space request))) :
    ¬ ∃ runtimeTerm,
      (hostedRevisionInteraction source keying
        hostOccurrence runtimeRevision).leftToRight hostTerm runtimeTerm := by
  rintro ⟨runtimeTerm, space, request, equivalent, targetEquivalent⟩
  exact notRequest space request equivalent

/-! ## Exact operator fragments -/

/-- The finite event vocabulary of the generic protocol. -/
inductive Operation where
  | allocate
  | resample
  | beginEvaluation
  | commitValue
  | commitStableFault
  | retry
  | observeValue
  | observeStableFault
  | inspectOrigin
deriving DecidableEq, Repr, Fintype

namespace Event

/-- Forget payload and occurrence identity while retaining the exact protocol
operator used by an event. -/
def operation
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    {RetryableFault : Type uRetryableFault} :
    Event Cell Origin Value StableFault RetryableFault -> Operation
  | .allocate _ _ => .allocate
  | .resample _ _ _ => .resample
  | .beginEvaluation _ _ => .beginEvaluation
  | .commitValue _ _ _ => .commitValue
  | .commitStableFault _ _ _ => .commitStableFault
  | .retry _ _ _ => .retry
  | .observeValue _ _ _ => .observeValue
  | .observeStableFault _ _ _ => .observeStableFault
  | .inspectOrigin _ _ => .inspectOrigin

end Event

abbrev OperatorSet := Finset Operation

/-- An exact event whose operator was selected by a language fragment. -/
abbrev AdmittedEvent
    (operators : OperatorSet)
    (Cell : Type uCell) (Origin : Type uOrigin) (Value : Type uValue)
    (StableFault : Type uStableFault)
    (RetryableFault : Type uRetryableFault) :=
  { event : Event Cell Origin Value StableFault RetryableFault //
    event.operation ∈ operators }

/-- Restrict the generic protocol to a selected finite operator vocabulary.
The state carrier is unchanged; only exact event sites are admitted. -/
def fragmentTheory
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    (operators : OperatorSet) (RetryableFault : Type uRetryableFault)
    (cell : Cell) : GSLT where
  Term := CellState Origin Value StableFault
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target =>
    Nonempty (Σ site : AdmittedEvent operators Cell Origin Value StableFault
      RetryableFault, Step RetryableFault cell source site.1 target)
  rewrites_resp_left := by
    intro source source' target equal edge
    subst source'
    exact ⟨target, edge, rfl⟩
  rewrites_resp_right := by
    intro source target target' edge equal
    subst target'
    exact edge

/-- Proof-relevant sites for an exact operator fragment. -/
def fragmentPresentation
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    (operators : OperatorSet) (RetryableFault : Type uRetryableFault)
    (cell : Cell) : InteractionPresentation
      (fragmentTheory (Origin := Origin) (Value := Value)
        (StableFault := StableFault) operators RetryableFault cell) where
  Site := AdmittedEvent operators Cell Origin Value StableFault RetryableFault
  Event := fun site source target =>
    Step RetryableFault cell source site.1 target
  sound := fun evidence => ⟨⟨_, evidence⟩⟩

theorem fragmentPresentation_complete
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    (operators : OperatorSet) (RetryableFault : Type uRetryableFault)
    (cell : Cell) :
    (fragmentPresentation (Origin := Origin) (Value := Value)
      (StableFault := StableFault) operators RetryableFault cell).Complete := by
  intro source target edge
  rcases edge with ⟨⟨site, evidence⟩⟩
  exact ⟨⟨site, evidence⟩⟩

/-- Adding operators preserves every old equation and exact protocol step.
This is the forward, non-reflecting arrow appropriate to an open extension. -/
def fragmentInclusion
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    {smaller larger : OperatorSet} (included : smaller ⊆ larger)
    (RetryableFault : Type uRetryableFault) (cell : Cell) :
    OperationalTranslation
      (fragmentTheory (Origin := Origin) (Value := Value)
        (StableFault := StableFault) smaller RetryableFault cell)
      (fragmentTheory (Origin := Origin) (Value := Value)
        (StableFault := StableFault) larger RetryableFault cell) where
  mapTerm := id
  mapEquiv := fun equivalent => equivalent
  mapStep := by
    intro source target edge
    rcases edge with ⟨⟨site, evidence⟩⟩
    exact ⟨⟨⟨site.1, included site.2⟩, evidence⟩⟩

theorem fragmentInclusion_refl
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault} (operators : OperatorSet)
    (RetryableFault : Type uRetryableFault) (cell : Cell) :
    fragmentInclusion (Origin := Origin) (Value := Value)
      (StableFault := StableFault) (fun _ member => member)
      RetryableFault cell =
    OperationalTranslation.id
      (fragmentTheory (Origin := Origin) (Value := Value)
        (StableFault := StableFault) operators RetryableFault cell) := by
  apply OperationalTranslation.ext
  rfl

theorem fragmentInclusion_trans
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    {first middle last : OperatorSet}
    (firstMiddle : first ⊆ middle) (middleLast : middle ⊆ last)
    (RetryableFault : Type uRetryableFault) (cell : Cell) :
    fragmentInclusion (Origin := Origin) (Value := Value)
      (StableFault := StableFault)
      (fun _ member => middleLast (firstMiddle member)) RetryableFault cell =
    OperationalTranslation.comp
      (fragmentInclusion (Origin := Origin) (Value := Value)
        (StableFault := StableFault) firstMiddle RetryableFault cell)
      (fragmentInclusion (Origin := Origin) (Value := Value)
        (StableFault := StableFault) middleLast RetryableFault cell) := by
  apply OperationalTranslation.ext
  rfl

/-- Pure call-by-need: cache successful values and permit origin inspection,
but expose neither fault class. -/
def pureNeedOperators : OperatorSet :=
  {.allocate, .resample, .beginEvaluation, .commitValue,
    .observeValue, .inspectOrigin}

/-- Add stable-fault memoization without adding retry. -/
def stableFaultNeedOperators : OperatorSet :=
  pureNeedOperators ∪ {.commitStableFault, .observeStableFault}

/-- The maximal protocol vocabulary.  A concrete language may select any
smaller fragment. -/
def allNeedOperators : OperatorSet := Finset.univ

theorem pureNeedOperators_subset_stableFault :
    pureNeedOperators ⊆ stableFaultNeedOperators := by
  intro operation member
  simp [stableFaultNeedOperators, member]

theorem stableFaultNeedOperators_subset_all :
    stableFaultNeedOperators ⊆ allNeedOperators := by
  intro operation member
  simp [allNeedOperators]

/-! ## Demand boundaries are an independent axis -/

/-- A demand algebra assigns a finite set of rights required to invoke each
public protocol operation.  It does not choose which operations exist. -/
structure DemandBoundary where
  Right : Type uRight
  decEq : DecidableEq Right
  required : Operation -> Finset Right

namespace DemandBoundary

/-- Executable form of permission checking. -/
def permits (boundary : DemandBoundary.{uRight})
    (held : Finset boundary.Right) (operation : Operation) : Bool := by
  letI := boundary.decEq
  exact decide (boundary.required operation ⊆ held)

/-- A held set permits an operation exactly when it contains every declared
right required by that operation. -/
def Permits (boundary : DemandBoundary.{uRight})
    (held : Finset boundary.Right) (operation : Operation) : Prop :=
  boundary.permits held operation = true

theorem permits_iff (boundary : DemandBoundary.{uRight})
    (held : Finset boundary.Right) (operation : Operation) :
    boundary.Permits held operation ↔
      boundary.required operation ⊆ held := by
  letI := boundary.decEq
  simp [Permits, permits]

/-- Attenuation is fail-closed: it returns precisely the requested subset or
rejects the escalation. -/
def restrict? (boundary : DemandBoundary.{uRight})
    (current requested : Finset boundary.Right) :
    Option (Finset boundary.Right) := by
  letI := boundary.decEq
  exact if requested ⊆ current then some requested else none

theorem restrict_some_subset (boundary : DemandBoundary.{uRight})
    {current requested granted : Finset boundary.Right}
    (restricted : boundary.restrict? current requested = some granted) :
    granted ⊆ current := by
  letI := boundary.decEq
  unfold restrict? at restricted
  split at restricted <;> simp_all

theorem restrict_some_eq_requested (boundary : DemandBoundary.{uRight})
    {current requested granted : Finset boundary.Right}
    (restricted : boundary.restrict? current requested = some granted) :
    granted = requested := by
  letI := boundary.decEq
  unfold restrict? at restricted
  split at restricted <;> simp_all

theorem restrict_escalation_fails (boundary : DemandBoundary.{uRight})
    {current requested : Finset boundary.Right}
    (escalates : ¬ requested ⊆ current) :
    boundary.restrict? current requested = none := by
  letI := boundary.decEq
  simp [restrict?, escalates]

/-- Apply a demand boundary to a separately chosen operator vocabulary. -/
def publicOperators (boundary : DemandBoundary.{uRight})
    (operators : OperatorSet) (held : Finset boundary.Right) : OperatorSet := by
  exact operators.filter fun operation =>
    boundary.permits held operation = true

theorem publicOperators_mono_rights (boundary : DemandBoundary.{uRight})
    (operators : OperatorSet) {smaller larger : Finset boundary.Right}
    (included : smaller ⊆ larger) :
    boundary.publicOperators operators smaller ⊆
      boundary.publicOperators operators larger := by
  letI := boundary.decEq
  intro operation member
  simp only [publicOperators, Finset.mem_filter] at member ⊢
  refine ⟨member.1, ?_⟩
  change boundary.Permits larger operation
  apply (boundary.permits_iff larger operation).2
  have permittedSmaller : boundary.Permits smaller operation := member.2
  have requiredSmaller :=
    (boundary.permits_iff smaller operation).1 permittedSmaller
  exact fun right required => included (requiredSmaller required)

theorem publicOperators_mono_vocabulary
    (boundary : DemandBoundary.{uRight})
    {smaller larger : OperatorSet} (held : Finset boundary.Right)
    (included : smaller ⊆ larger) :
    boundary.publicOperators smaller held ⊆
      boundary.publicOperators larger held := by
  letI := boundary.decEq
  intro operation member
  simp only [publicOperators, Finset.mem_filter] at member ⊢
  exact ⟨included member.1, member.2⟩

end DemandBoundary

/-- One useful demand vocabulary; it is an instance, not part of the generic
cell protocol. -/
inductive StandardRight where
  | force
  | inspect
  | resample
deriving DecidableEq, Repr

/-- A conventional boundary in which allocation is internal, forcing covers
evaluation/commit/observation, inspection is separate, and resampling is a
separate capability. -/
def standardDemandBoundary : DemandBoundary where
  Right := StandardRight
  decEq := inferInstance
  required
    | .allocate => ∅
    | .resample => {.resample}
    | .beginEvaluation => {.force}
    | .commitValue => {.force}
    | .commitStableFault => {.force}
    | .retry => {.force}
    | .observeValue => {.force}
    | .observeStableFault => {.force}
    | .inspectOrigin => {.inspect}

/-! ## Exact guest-outcome decompositions -/

/-- A language chooses its Need outcome algebra by giving an exact
decomposition, not merely a one-way classifier. -/
structure OutcomeAlgebra (GuestOutcome : Type uGuest) where
  Value : Type uValue
  StableFault : Type uStableFault
  RetryableFault : Type uRetryableFault
  encode : GuestOutcome -> Outcome Value StableFault RetryableFault
  decode : Outcome Value StableFault RetryableFault -> GuestOutcome
  decode_encode : ∀ outcome, decode (encode outcome) = outcome
  encode_decode : ∀ outcome, encode (decode outcome) = outcome

namespace OutcomeAlgebra

/-- The already-polarized outcome sum is its own exact algebra. -/
def identity (Value : Type uValue) (StableFault : Type uStableFault)
    (RetryableFault : Type uRetryableFault) :
    OutcomeAlgebra (Outcome Value StableFault RetryableFault) where
  Value := Value
  StableFault := StableFault
  RetryableFault := RetryableFault
  encode := id
  decode := id
  decode_encode := fun _ => rfl
  encode_decode := fun _ => rfl

/-- A pure guest has successful values and no fault constructors. -/
def pure (Value : Type uValue) : OutcomeAlgebra Value where
  Value := Value
  StableFault := Empty
  RetryableFault := Empty
  encode := .value
  decode
    | .value value => value
    | .stableFault impossible => nomatch impossible
    | .retryableFault impossible => nomatch impossible
  decode_encode := fun _ => rfl
  encode_decode := by
    intro outcome
    cases outcome with
    | value => rfl
    | stableFault impossible => exact nomatch impossible
    | retryableFault impossible => exact nomatch impossible

/-- A guest with memoized faults but no retryable fault class. -/
def stableFault (Value : Type uValue) (StableFault : Type uStableFault) :
    OutcomeAlgebra (Sum Value StableFault) where
  Value := Value
  StableFault := StableFault
  RetryableFault := Empty
  encode
    | .inl value => .value value
    | .inr fault => .stableFault fault
  decode
    | .value value => .inl value
    | .stableFault fault => .inr fault
    | .retryableFault impossible => nomatch impossible
  decode_encode := by intro outcome; cases outcome <;> rfl
  encode_decode := by
    intro outcome
    cases outcome with
    | value => rfl
    | stableFault => rfl
    | retryableFault impossible => exact nomatch impossible

end OutcomeAlgebra

/-! ## Separating canaries -/

namespace ProfileCanary

abbrev DemoState := CellState Nat Nat Nat

theorem evaluating_to_suspended_is_retry
    {event : Event Nat Nat Nat Nat Nat}
    (evidence : Step Nat 0 (.evaluating 7) event (.suspended 7)) :
    event.operation = .retry := by
  cases evidence
  rfl

def retryStepInAll :
    (fragmentTheory (Origin := Nat) (Value := Nat) (StableFault := Nat)
      allNeedOperators Nat 0).Step (.evaluating 7) (.suspended 7) :=
  ⟨⟨⟨.retry 0 7 99, by simp [allNeedOperators]⟩, .retry 7 99⟩⟩

/-- Negative canary: the pure fragment genuinely omits retry. -/
theorem retryStepNotInPure :
    ¬ (fragmentTheory (Origin := Nat) (Value := Nat) (StableFault := Nat)
      pureNeedOperators Nat 0).Step (.evaluating 7) (.suspended 7) := by
  rintro ⟨⟨site, evidence⟩⟩
  have retryOperator := evaluating_to_suspended_is_retry evidence
  have admitted := site.property
  rw [retryOperator] at admitted
  simp [pureNeedOperators] at admitted

/-- Therefore no identity-on-states forward translation can erase the retry
operator from the maximal fragment into the pure fragment. -/
theorem no_identity_translation_all_to_pure :
    ¬ ∃ translation : OperationalTranslation
      (fragmentTheory (Origin := Nat) (Value := Nat) (StableFault := Nat)
        allNeedOperators Nat 0)
      (fragmentTheory (Origin := Nat) (Value := Nat) (StableFault := Nat)
        pureNeedOperators Nat 0),
      translation.mapTerm = id := by
  rintro ⟨translation, identityMap⟩
  have mapped := translation.mapStep retryStepInAll
  simp only [identityMap, id_eq] at mapped
  exact retryStepNotInPure mapped

def inspectRights : Finset StandardRight := {.inspect}
def forceInspectRights : Finset StandardRight := {.force, .inspect}

theorem inspect_only_exposes_inspection :
    Operation.inspectOrigin ∈
      standardDemandBoundary.publicOperators allNeedOperators inspectRights ∧
    Operation.beginEvaluation ∉
      standardDemandBoundary.publicOperators allNeedOperators inspectRights := by
  decide

theorem adding_force_exposes_evaluation :
    Operation.beginEvaluation ∈
      standardDemandBoundary.publicOperators allNeedOperators
        forceInspectRights := by
  decide

theorem force_cannot_be_minted_from_inspection :
    standardDemandBoundary.restrict? inspectRights forceInspectRights = none := by
  decide

theorem pureOutcome_is_value (value : Nat) :
    (OutcomeAlgebra.pure Nat).encode value = Outcome.value value :=
  rfl

end ProfileCanary

end Mettapedia.GSLT.Dynamics.ProofRelevantNeed
