import Mettapedia.GSLT.Core.CertifiedPlanning
import Mettapedia.GSLT.LanguageDef.AuthoredGSLTHosting

/-!
# Presentation-sensitive source-to-target transformation

A compiler may be handwritten, but its output must be determined by the
authored source and target presentations that it receives.  This module gives
the existing `PartialRealization` interface the source-first `transform?`
surface used by language-to-language compilers and proves the basic semantic
sensitivity law forced by adequacy.

The source and target parameters are intended to be finite, inspectable
presentations equipped elsewhere with proofs that they denote their authored
GSLTs.  A bare semantic `GSLT` is not inspectable in general: its rewrite field
is a proposition-valued relation.  Keeping presentation data explicit avoids
replacing compilation by a filename, digest, or fixed-callback dispatch.
-/

namespace Mettapedia.GSLT.LanguageDef.PresentationSensitiveTransformation

open Mettapedia.GSLT

universe uSource uTarget uArtifact uObservation

/-- A conditionally defined transformation indexed by the supplied target
presentation.  `compile target source` is the existing certified realization
order; `transform? source target` below exposes the conventional compiler
order. -/
abbrev Transformation
    (Source : Type uSource) (Target : Type uTarget)
    (Artifact : Target -> Type uArtifact)
    (Observation : Target -> Type uObservation) :=
  PartialRealization (Base := Target) (fun _ => Source) Artifact Observation

namespace Transformation

variable {Source : Type uSource} {Target : Type uTarget}
variable {Artifact : Target -> Type uArtifact}
variable {Observation : Target -> Type uObservation}

/-- Run a presentation-sensitive transformation in source-first order.
Unsupported source/target pairs fail explicitly. -/
def transform? (transformation : Transformation Source Target Artifact Observation)
    (source : Source) (target : Target) : Option (Artifact target) :=
  if accepted : transformation.accepts target source = true then
    some (transformation.compile target source accepted)
  else
    none

theorem transform?_eq_some
    (transformation : Transformation Source Target Artifact Observation)
    (source : Source) (target : Target)
    (accepted : transformation.accepts target source = true) :
    transformation.transform? source target =
      some (transformation.compile target source accepted) := by
  simp [transform?, accepted]

theorem transform?_eq_none
    (transformation : Transformation Source Target Artifact Observation)
    (source : Source) (target : Target)
    (rejected : transformation.accepts target source ≠ true) :
    transformation.transform? source target = none := by
  simp [transform?, rejected]

/-- A successful result retains the exact observation of the supplied source
under the supplied target presentation. -/
theorem transform?_adequate
    (transformation : Transformation Source Target Artifact Observation)
    (source : Source) (target : Target) (artifact : Artifact target)
    (result : transformation.transform? source target = some artifact) :
    transformation.observeArtifact target artifact =
      transformation.observeSource target source := by
  unfold transform? at result
  split at result
  next accepted =>
    cases Option.some.inj result
    exact transformation.adequate target source accepted
  next rejected =>
    simp at result

/-- If two source presentations have different declared observations, an
adequate transformation cannot produce the same artifact for both. -/
theorem compile_ne_of_source_observation_ne
    (transformation : Transformation Source Target Artifact Observation)
    (target : Target) (left right : Source)
    (leftAccepted : transformation.accepts target left = true)
    (rightAccepted : transformation.accepts target right = true)
    (different : transformation.observeSource target left ≠
      transformation.observeSource target right) :
    transformation.compile target left leftAccepted ≠
      transformation.compile target right rightAccepted := by
  intro artifactsEqual
  apply different
  calc
    transformation.observeSource target left =
        transformation.observeArtifact target
          (transformation.compile target left leftAccepted) :=
      (transformation.adequate target left leftAccepted).symm
    _ = transformation.observeArtifact target
          (transformation.compile target right rightAccepted) := by
      rw [artifactsEqual]
    _ = transformation.observeSource target right :=
      transformation.adequate target right rightAccepted

end Transformation

/-! ## Operationally two-sided transformations

Equality of one selected observation is the useful `Realization` floor above,
but hosting a language requires more: every source observation must survive
and every target observation reachable from a compiled state must come from
the source.  The following interface packages that stronger contract while
keeping the authored source presentation and target presentation as ordinary
function inputs.
-/

open Mettapedia.GSLT.LanguageDef.AuthoredGSLTHosting
open Mettapedia.GSLT.LanguageDef.NIKObservedRefinement

universe uValue uIntermediate uLowered

/-- A source- and target-presentation-sensitive compiler whose successful
result already carries two-sided behavioral hosting.  The source semantics is
a parameter rather than a field so that successive stages can share their
middle semantics definitionally. -/
structure BehavioralTransformation
    (Source : Type uSource)
    (sourceSemantics : Source → ObservedOperationalObject.{uValue} Value)
    (Target : Type uTarget) (Artifact : Target → Type uArtifact) where
  accepts : Source → Target → Bool
  compile : ∀ source target, accepts source target = true → Artifact target
  targetSemantics : ∀ target, Artifact target →
    ObservedOperationalObject.{uValue} Value
  hosts : ∀ source target accepted,
    BehavioralHosting (sourceSemantics source)
      (targetSemantics target (compile source target accepted))

/-- A compiled artifact bundled with its source-to-target hosting theorem.
This is the semantic result of a successful transformation, not a receipt
manufactured after running an unrelated implementation. -/
structure CompiledResult
    (source : ObservedOperationalObject.{uValue} Value)
    (Artifact : Type uArtifact)
    (targetSemantics : Artifact → ObservedOperationalObject.{uValue} Value) where
  artifact : Artifact
  hosting : BehavioralHosting source (targetSemantics artifact)

namespace BehavioralTransformation

variable {Value : Type uValue} {Source : Type uSource}
variable {sourceSemantics : Source → ObservedOperationalObject Value}
variable {Target : Type uTarget} {Artifact : Target → Type uArtifact}

/-- The fully proved result at one supplied source/target pair. -/
abbrev Result
    (transformation :
      BehavioralTransformation Source sourceSemantics Target Artifact)
    (source : Source) (target : Target) :=
  CompiledResult (sourceSemantics source) (Artifact target)
    (transformation.targetSemantics target)

/-- Run the actual compiler on its supplied presentations.  Rejection is an
explicit `none`; there is no identity-dispatch fallback hidden in this seam. -/
def transform?
    (transformation :
      BehavioralTransformation Source sourceSemantics Target Artifact)
    (source : Source) (target : Target) :
    Option (transformation.Result source target) :=
  if accepted : transformation.accepts source target = true then
    some
      { artifact := transformation.compile source target accepted
        hosting := transformation.hosts source target accepted }
  else
    none

theorem transform?_eq_none
    (transformation :
      BehavioralTransformation Source sourceSemantics Target Artifact)
    (source : Source) (target : Target)
    (rejected : transformation.accepts source target ≠ true) :
    transformation.transform? source target = none := by
  simp [transform?, rejected]

theorem transform?_eq_some
    (transformation :
      BehavioralTransformation Source sourceSemantics Target Artifact)
    (source : Source) (target : Target)
    (accepted : transformation.accepts source target = true) :
    transformation.transform? source target = some
      { artifact := transformation.compile source target accepted
        hosting := transformation.hosts source target accepted } := by
  simp [transform?, accepted]

end BehavioralTransformation

namespace CompiledResult

variable {Value : Type uValue}
variable {SourceObject : ObservedOperationalObject Value}
variable {Intermediate : Type uIntermediate}
variable {intermediateSemantics : Intermediate → ObservedOperationalObject Value}

/-- Continue a successful transformation through a second transformation
whose source semantics is exactly the first stage's target semantics.  The
resulting compiler pipeline inherits two-sided hosting by composition; neither
stage may repair missing no-invention evidence in the other. -/
def stage
    (earlier :
      CompiledResult SourceObject Intermediate intermediateSemantics)
    {Target : Type uTarget} {Artifact : Target → Type uLowered}
    (later : BehavioralTransformation Intermediate intermediateSemantics
      Target Artifact)
    (target : Target) (accepted : later.accepts earlier.artifact target = true) :
    CompiledResult SourceObject (Artifact target)
      (later.targetSemantics target) where
  artifact := later.compile earlier.artifact target accepted
  hosting := earlier.hosting.comp
    (later.hosts earlier.artifact target accepted)

/-- Staging retains exact public behavior from the original source. -/
theorem stage_produces_iff
    (earlier :
      CompiledResult SourceObject Intermediate intermediateSemantics)
    {Target : Type uTarget} {Artifact : Target → Type uLowered}
    (later : BehavioralTransformation Intermediate intermediateSemantics
      Target Artifact)
    (target : Target) (accepted : later.accepts earlier.artifact target = true)
    (initial : SourceObject.operational.theory.Term) (value : Value) :
    ProducesObservation
        (later.targetSemantics target
          (later.compile earlier.artifact target accepted))
        ((earlier.stage later target accepted).hosting.compile initial) value ↔
      ProducesObservation SourceObject initial value :=
  (earlier.stage later target accepted).hosting.produces_iff initial value

end CompiledResult

/-! ## Adversarial identity-only canary -/

namespace IdentityOnlyCanary

/-- The identity field deliberately fails to determine semantic meaning. -/
structure SourcePresentation where
  identity : Nat
  meaning : Bool
deriving DecidableEq

def positiveSource : SourcePresentation :=
  { identity := 7, meaning := true }

def negativeSource : SourcePresentation :=
  { identity := 7, meaning := false }

/-- A real transformation reads semantic presentation content, not merely its
identity. -/
def semanticTransformation :
    Transformation SourcePresentation Unit (fun _ => Bool) (fun _ => Bool) where
  accepts := fun _ _ => true
  compile := fun _ source _ => source.meaning
  observeSource := fun _ source => source.meaning
  observeArtifact := fun _ artifact => artifact
  adequate := by
    intro target source accepted
    rfl

theorem semanticTransformation_positive :
    semanticTransformation.transform? positiveSource () = some true := by
  rfl

theorem semanticTransformation_negative :
    semanticTransformation.transform? negativeSource () = some false := by
  rfl

/-- A transformation is identity-only when accepted sources with the same
identity always yield the same artifact. -/
def IdentityOnly
    (transformation :
      Transformation SourcePresentation Unit (fun _ => Bool) (fun _ => Bool)) :
    Prop :=
  forall left right
      (leftAccepted : transformation.accepts () left = true)
      (rightAccepted : transformation.accepts () right = true),
    left.identity = right.identity ->
      transformation.compile () left leftAccepted =
        transformation.compile () right rightAccepted

/-- No adequate transformation that observes authored meaning and accepts both
can be identity-only.  A filename/digest dispatcher therefore cannot pass as a
compiler when the same admitted identity is paired with changed semantics. -/
theorem no_adequate_identity_only_transformation
    (transformation :
      Transformation SourcePresentation Unit (fun _ => Bool) (fun _ => Bool))
    (observesMeaning : forall source,
      transformation.observeSource () source = source.meaning)
    (positiveAccepted : transformation.accepts () positiveSource = true)
    (negativeAccepted : transformation.accepts () negativeSource = true) :
    Not (IdentityOnly transformation) := by
  intro identityOnly
  have different :
      transformation.observeSource () positiveSource ≠
        transformation.observeSource () negativeSource := by
    rw [observesMeaning, observesMeaning]
    decide
  exact
    (transformation.compile_ne_of_source_observation_ne ()
      positiveSource negativeSource positiveAccepted negativeAccepted different)
      (identityOnly positiveSource negativeSource positiveAccepted
        negativeAccepted rfl)

end IdentityOnlyCanary

#print axioms Transformation.compile_ne_of_source_observation_ne
#print axioms CompiledResult.stage_produces_iff
#print axioms IdentityOnlyCanary.no_adequate_identity_only_transformation

end Mettapedia.GSLT.LanguageDef.PresentationSensitiveTransformation
