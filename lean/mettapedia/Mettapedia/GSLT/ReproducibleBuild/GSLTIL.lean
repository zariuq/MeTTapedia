import Mettapedia.GSLT.LanguageDef.RelationPresentationRoutes
import Mettapedia.GSLT.ReproducibleBuild.Composition
import Mettapedia.GSLT.Dynamics.RevisionedOccurrenceExactImage

/-!
# Relational GSLT-IL builds and their exact functional boundary

Revisioned-occurrence relations and GSLT-IL typed routes use the same
proof-relevant loose-relation equipment as relational builds.  This module
makes the shared abstraction load-bearing for reproducibility:

* every semantic relation is a build without requiring a compiler function;
* relational chaining is build composition and retains the intermediate value
  and both witnesses;
* representability earns a functional companion and hence ordinary functional
  reproducibility;
* the generic returned-fibre theorem transports reproducibility exactly on its
  proved image, while the existing pending-command witnesses remain outside
  that image.

No loose route is functionalized by this bridge.  A `Representation` or typed
route licence remains the only authority for exposing a compiled function.
-/


set_option autoImplicit false

namespace Mettapedia.GSLT.ReproducibleBuild.GSLTIL

open Mettapedia.GSLT.Core.ReproducibleBuild
open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.ReproducibleBuild.Composition
open Mettapedia.GSLT.IndexedOperational

open Mettapedia.GSLT.RelationPresentation
open Mettapedia.GSLT.Dynamics.RevisionedOccurrenceExactImage
open Mettapedia.GSLT.Dynamics.OccurrenceSemantics
open Mettapedia.GSLT.Dynamics.ProofRelevantNeed
open Mettapedia.GSLT.Dynamics.RevisionedOccurrenceProofFlow
open Mettapedia.GSLT.Dynamics.RevisionedOccurrenceReturnedFibre

universe u uDeclared uMiddleObserved uFinalObserved

/-! ## The ambient relational result -/

/-- A semantic GSLT-IL relation is already a proof-relevant relational build;
the bridge retains its evidence family definitionally. -/
def relationBuild {Source Artifact : Type u}
    (relation : Mettapedia.GSLT.RelationPresentation.Rel Source Artifact) :
    RelationalBuild Source Artifact :=
  relation.toLoose

@[simp] theorem relationBuild_evidence
    {Source Artifact : Type u}
    (relation : Mettapedia.GSLT.RelationPresentation.Rel Source Artifact)
    (source : Source) (artifact : Artifact) :
    relationBuild relation source artifact =
      relation.evidence source artifact :=
  rfl

/-- Relational Chain and build composition are the same proof family, not just
the same endpoint support. -/
def chainBuild_fibrewise
    {First Middle Last : Type u}
    (earlier : Mettapedia.GSLT.RelationPresentation.Rel First Middle)
    (later : Mettapedia.GSLT.RelationPresentation.Rel Middle Last) :
    FibrewiseEquivalent
      (relationBuild (Mettapedia.GSLT.RelationPresentation.Rel.Chain earlier later))
      (comp (relationBuild earlier) (relationBuild later)) :=
  fun _ _ => Equiv.refl _

/-- The generic reproducible-build composition theorem applies directly to
relational GSLT-IL chaining. -/
theorem chain_declaredViewReproducible
    {First Middle Last : Type u}
    {earlier : Mettapedia.GSLT.RelationPresentation.Rel First Middle}
    {later : Mettapedia.GSLT.RelationPresentation.Rel Middle Last}
    (sourceView : InputView.{u, uDeclared} First)
    (middleObservation :
      ArtifactObservation.{u, uMiddleObserved} Middle)
    (finalObservation : ArtifactObservation.{u, uFinalObserved} Last)
    (earlierReproducible :
      DeclaredViewReproducible (relationBuild earlier) sourceView
        middleObservation)
    (laterReproducible :
      DeclaredViewReproducible (relationBuild later)
        (observationInputView middleObservation) finalObservation) :
    DeclaredViewReproducible
      (relationBuild (Mettapedia.GSLT.RelationPresentation.Rel.Chain earlier later))
      sourceView finalObservation := by
  apply (chainBuild_fibrewise earlier later).declaredViewReproducible_iff
    sourceView finalObservation |>.mpr
  exact declaredViewReproducible_comp sourceView middleObservation
    finalObservation earlierReproducible laterReproducible

/-! ## Representability earns the functional specialization -/

/-- A represented relational GSLT-IL build is reproducible at every explicit
artifact observation. -/
theorem represented_reproducible
    {Source Artifact : Type u}
    {relation : Mettapedia.GSLT.RelationPresentation.Rel Source Artifact}
    (representation : Mettapedia.GSLT.RelationPresentation.Rel.Representation relation)
    (observation : ArtifactObservation.{u, uFinalObserved} Artifact) :
    Reproducible (relationBuild relation) observation :=
  reproducible_of_representation representation observation

/-- The functional companion is recovered fibrewise only from the explicit
representation witness. -/
def represented_fibrewise_companion
    {Source Artifact : Type u}
    {relation : Mettapedia.GSLT.RelationPresentation.Rel Source Artifact}
    (representation : Mettapedia.GSLT.RelationPresentation.Rel.Representation relation) :
    FibrewiseEquivalent (relationBuild relation)
      (companion representation.map) :=
  representation_fibrewise_companion representation

/-- A licensed typed GSLT-IL route is reproducible at every selected target
observation; the licence, not route syntax alone, supplies representability. -/
theorem licensedRoute_reproducible
    {program : Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax.Program}
    {route : Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax.RouteDecl}
    {profile :
      Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment.TypedRouteProfile
        program route}
    (license : profile.License)
    (observation :
      ArtifactObservation.{0, uFinalObserved} profile.Target) :
    Reproducible
      (relationBuild (Mettapedia.GSLT.RelationPresentation.AuthoredRoute.internalizeTyped profile))
      observation :=
  represented_reproducible
    ((Mettapedia.GSLT.RelationPresentation.AuthoredRoute.licenseEquiv profile) license)
    observation

/-- Executability without a licence remains relational.  The existing choice
relation executes both outputs but cannot expose a representing compiler. -/
theorem executable_relation_need_not_be_functional :
    (Nonempty (Mettapedia.GSLT.RelationPresentation.Canary.choice.evidence () false) /\
      Nonempty (Mettapedia.GSLT.RelationPresentation.Canary.choice.evidence () true)) /\
      Not (Nonempty
        (Mettapedia.GSLT.RelationPresentation.Rel.Representation Mettapedia.GSLT.RelationPresentation.Canary.choice)) :=
  ⟨Mettapedia.GSLT.RelationPresentation.Canary.choice_executes_both,
    Mettapedia.GSLT.RelationPresentation.Canary.choice_not_representable⟩

/-! ## The exact revisioned-occurrence returned image -/

section RevisionedOccurrence

universe uSpace uRequest uAnswer uKey

variable {Space : Type uSpace} {Request : Type uRequest}
  {Answer : Type uAnswer} [DecidableEq Answer]

/-- Retained revisioned-occurrence evidence as a relational build. -/
def occurrenceStepBuild (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request) :
    RelationalBuild (Claim occurrences keying) (Claim occurrences keying) :=
  relationBuild (occurrenceStepRel occurrences keying)

/-- The returned-fibre one-step evidence as a relational build. -/
def returnedStepBuild (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request) :
    RelationalBuild (Claim occurrences keying) (Claim occurrences keying) :=
  relationBuild (returnedStepRel occurrences keying)

/-- The existing returned-image theorem is exact at every one-step build
fibre. -/
def occurrenceReturnedStep_fibrewise (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request) :
    FibrewiseEquivalent (occurrenceStepBuild occurrences keying) (returnedStepBuild occurrences keying) :=
  stepEvidenceEquiv occurrences keying

/-- Any declared-view reproducibility theorem for revisioned-occurrence evidence
transports iff to the returned fibre, and conversely. -/
theorem occurrenceReturnedStep_declaredViewReproducible_iff
    (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    (view : InputView.{max uSpace uRequest uAnswer uKey, uDeclared}
      (Claim occurrences keying))
    (observation :
      ArtifactObservation.{max uSpace uRequest uAnswer uKey, uFinalObserved}
        (Claim occurrences keying)) :
    DeclaredViewReproducible (occurrenceStepBuild occurrences keying) view observation <->
      DeclaredViewReproducible (returnedStepBuild occurrences keying) view observation :=
  (occurrenceReturnedStep_fibrewise occurrences keying).declaredViewReproducible_iff
    view observation

/-- The exact returned-fibre transport cannot be promoted to the whole command
language: pending commands are concrete counterexamples outside the image. -/
theorem returnedFibre_exact_and_fullCommand_strict
    (occurrences : OccurrenceSource Space Request Answer)
    (keying : RevisionKeying.{uSpace, uRequest, uKey} Space Request)
    (claim : Claim occurrences keying) :
    InReturnedImage occurrences keying (encodeClaim occurrences keying claim) /\
      Not (InReturnedImage occurrences keying (pendingClaim occurrences keying claim)) /\
      Not (∃ decode : Command (diagram occurrences keying) → Claim occurrences keying,
        ∀ command, encodeClaim occurrences keying (decode command) = command) :=
  ⟨encodeClaim_inReturnedImage occurrences keying claim,
    pendingClaim_outsideReturnedImage occurrences keying claim,
    returned_fragment_has_no_full_command_decode occurrences keying claim⟩

end RevisionedOccurrence

#print axioms chainBuild_fibrewise
#print axioms chain_declaredViewReproducible
#print axioms represented_reproducible
#print axioms licensedRoute_reproducible
#print axioms executable_relation_need_not_be_functional
#print axioms occurrenceReturnedStep_declaredViewReproducible_iff
#print axioms returnedFibre_exact_and_fullCommand_strict

end Mettapedia.GSLT.ReproducibleBuild.GSLTIL
