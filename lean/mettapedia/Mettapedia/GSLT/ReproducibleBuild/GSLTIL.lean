import Mettapedia.GSLT.ReproducibleBuild.Composition
import Mettapedia.Languages.MeTTa.PureKernel.Universe.GSLTILExactImage

/-!
# Relational GSLT-IL builds and their exact functional boundary

Prime's semantic relations and GSLT-IL typed routes already use the same
proof-relevant loose-relation equipment as relational builds.  This module
makes the shared abstraction load-bearing for reproducibility:

* every semantic relation is a build without requiring a compiler function;
* relational chaining is build composition and retains the intermediate value
  and both witnesses;
* representability earns a functional companion and hence ordinary functional
  reproducibility;
* Prime's returned-fibre theorem transports reproducibility exactly on its
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

open Mettapedia.Languages.MeTTa.PureKernel.Universe.RelationalInternalLanguage
open Mettapedia.Languages.MeTTa.PureKernel.Universe.GSLTILExactImage
open Mettapedia.Languages.MeTTa.NativeTypeTheory
open Mettapedia.Languages.MeTTa.NativeTypeTheory.PrimeNeedProofFlow
open Mettapedia.Languages.MeTTa.NativeTypeTheory.PrimeGSLTILReturnedFibre

universe u uDeclared uMiddleObserved uFinalObserved

/-! ## The ambient relational result -/

/-- A semantic GSLT-IL relation is already a proof-relevant relational build;
the bridge retains its evidence family definitionally. -/
def relationBuild {Source Artifact : Type u}
    (relation : Semantic.Rel Source Artifact) :
    RelationalBuild Source Artifact :=
  relation.toLoose

@[simp] theorem relationBuild_evidence
    {Source Artifact : Type u}
    (relation : Semantic.Rel Source Artifact)
    (source : Source) (artifact : Artifact) :
    relationBuild relation source artifact =
      relation.evidence source artifact :=
  rfl

/-- Relational Chain and build composition are the same proof family, not just
the same endpoint support. -/
def chainBuild_fibrewise
    {First Middle Last : Type u}
    (earlier : Semantic.Rel First Middle)
    (later : Semantic.Rel Middle Last) :
    FibrewiseEquivalent
      (relationBuild (Semantic.Rel.Chain earlier later))
      (comp (relationBuild earlier) (relationBuild later)) :=
  fun _ _ => Equiv.refl _

/-- The generic reproducible-build composition theorem applies directly to
relational GSLT-IL chaining. -/
theorem chain_declaredViewReproducible
    {First Middle Last : Type u}
    {earlier : Semantic.Rel First Middle}
    {later : Semantic.Rel Middle Last}
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
      (relationBuild (Semantic.Rel.Chain earlier later))
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
    {relation : Semantic.Rel Source Artifact}
    (representation : Semantic.Rel.Representation relation)
    (observation : ArtifactObservation.{u, uFinalObserved} Artifact) :
    Reproducible (relationBuild relation) observation :=
  reproducible_of_representation representation observation

/-- The functional companion is recovered fibrewise only from the explicit
representation witness. -/
def represented_fibrewise_companion
    {Source Artifact : Type u}
    {relation : Semantic.Rel Source Artifact}
    (representation : Semantic.Rel.Representation relation) :
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
      (relationBuild (Semantic.AuthoredRoute.internalizeTyped profile))
      observation :=
  represented_reproducible
    ((Semantic.AuthoredRoute.licenseEquiv profile) license)
    observation

/-- Executability without a licence remains relational.  The existing choice
relation executes both outputs but cannot expose a representing compiler. -/
theorem executable_relation_need_not_be_functional :
    (Nonempty (Semantic.Canary.choice.evidence () false) /\
      Nonempty (Semantic.Canary.choice.evidence () true)) /\
      Not (Nonempty
        (Semantic.Rel.Representation Semantic.Canary.choice)) :=
  ⟨Semantic.Canary.choice_executes_both,
    Semantic.Canary.choice_not_representable⟩

/-! ## Prime's exact returned image -/

/-- Prime's retained one-step evidence as a relational build. -/
def primeStepBuild (model : PrimeModel) :
    RelationalBuild (Claim model) (Claim model) :=
  relationBuild (primeStepRel model)

/-- The returned-fibre one-step evidence as a relational build. -/
def returnedStepBuild (model : PrimeModel) :
    RelationalBuild (Claim model) (Claim model) :=
  relationBuild (returnedStepRel model)

/-- The existing returned-image theorem is exact at every one-step build
fibre. -/
def primeReturnedStep_fibrewise (model : PrimeModel) :
    FibrewiseEquivalent (primeStepBuild model) (returnedStepBuild model) :=
  stepEvidenceEquiv model

/-- Any declared-view reproducibility theorem for Prime one-step evidence
transports iff to the returned fibre, and conversely. -/
theorem primeReturnedStep_declaredViewReproducible_iff
    (model : PrimeModel)
    (view : InputView.{0, uDeclared} (Claim model))
    (observation :
      ArtifactObservation.{0, uFinalObserved} (Claim model)) :
    DeclaredViewReproducible (primeStepBuild model) view observation <->
      DeclaredViewReproducible (returnedStepBuild model) view observation :=
  (primeReturnedStep_fibrewise model).declaredViewReproducible_iff
    view observation

/-- The exact returned-fibre transport cannot be promoted to the whole command
language: pending commands are concrete counterexamples outside the image. -/
theorem returnedFibre_exact_and_fullCommand_strict
    (model : PrimeModel) (claim : Claim model) :
    InReturnedImage model (encodeClaim model claim) /\
      Not (InReturnedImage model (pendingClaim model claim)) /\
      Not (∃ decode : Command (diagram model) → Claim model,
        ∀ command, encodeClaim model (decode command) = command) :=
  ⟨encodeClaim_inReturnedImage model claim,
    pendingClaim_outsideReturnedImage model claim,
    current_fragment_has_no_full_command_decode model claim⟩

#print axioms chainBuild_fibrewise
#print axioms chain_declaredViewReproducible
#print axioms represented_reproducible
#print axioms licensedRoute_reproducible
#print axioms executable_relation_need_not_be_functional
#print axioms primeReturnedStep_declaredViewReproducible_iff
#print axioms returnedFibre_exact_and_fullCommand_strict

end Mettapedia.GSLT.ReproducibleBuild.GSLTIL
