import Mettapedia.GSLT.Core.ReproducibleBuild
import Mettapedia.OSLF.Framework.LanguageMorphism

/-!
# Reproducibility transport earned by OSLF language morphisms

An OSLF `LanguageMorphism` supplies forward and backward operational
simulation, but it does not choose a build observation.  This module adds the
minimal missing law explicitly: source and target endpoint observations must
commute with the term translation.  Only then does operational correspondence
transport result-level reproducibility and declared-input sufficiency.

The live OSLF multi-step relation is `Prop`-valued.  Its build presentation
therefore retains endpoint reachability but not distinct path proofs.  The
theorems below intentionally make no replay or proof-fibre claim; those require
a proof-relevant operational interface in addition to `LanguageMorphism`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ReproducibleBuild.OSLF

open Mettapedia.GSLT.Core.ReproducibleBuild
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.LangMorphism

universe uObserved uDeclared

/-- The extra observation law required to turn OSLF operational
correspondence into reproducibility transport. -/
structure ObservedLanguageMorphism
    (source target : LanguageDef) (Observed : Type uObserved) where
  morphism : LanguageMorphism source target Eq
  observeSource : Pattern → Observed
  observeTarget : Pattern → Observed
  commutes : ∀ term,
    observeTarget (morphism.mapTerm term) = observeSource term

namespace ObservedLanguageMorphism

variable {source target : LanguageDef} {Observed : Type uObserved}

/-- Source multi-step reachability as a result-level relational build. -/
def sourcePathBuild
    (_morphism : ObservedLanguageMorphism source target Observed) :
    RelationalBuild Pattern Pattern :=
  fun initial final => PLift (LangReducesStar source initial final)

/-- Target multi-step reachability pulled back along the source-term map. -/
def targetPathBuild
    (morphism : ObservedLanguageMorphism source target Observed) :
    RelationalBuild Pattern Pattern :=
  fun initial final =>
    PLift (LangReducesStar target (morphism.morphism.mapTerm initial) final)

/-- Source endpoint observation. -/
def sourceArtifactObservation
    (morphism : ObservedLanguageMorphism source target Observed) :
    ArtifactObservation Pattern where
  Observed := Observed
  observe := morphism.observeSource

/-- Target endpoint observation. -/
def targetArtifactObservation
    (morphism : ObservedLanguageMorphism source target Observed) :
    ArtifactObservation Pattern where
  Observed := Observed
  observe := morphism.observeTarget

theorem source_rebuildable
    (morphism : ObservedLanguageMorphism source target Observed) :
    Rebuildable morphism.sourcePathBuild := by
  intro initial
  exact ⟨⟨initial, ⟨LangReducesStar.refl initial⟩⟩⟩

theorem target_rebuildable
    (morphism : ObservedLanguageMorphism source target Observed) :
    Rebuildable morphism.targetPathBuild := by
  intro initial
  exact ⟨⟨morphism.morphism.mapTerm initial,
    ⟨LangReducesStar.refl _⟩⟩⟩

/-- Forward and backward operational simulation transport consistency exactly
at the explicitly commuting endpoint observation. -/
theorem observationConsistent_iff
    (morphism : ObservedLanguageMorphism source target Observed) :
    ObservationConsistent morphism.sourcePathBuild
        morphism.sourceArtifactObservation <->
      ObservationConsistent morphism.targetPathBuild
        morphism.targetArtifactObservation := by
  constructor
  · intro sourceConsistent initial left right leftPath rightPath
    obtain ⟨leftSourceFinal, leftSourcePath, leftEndpoint⟩ :=
      morphism.morphism.backward_multi_eq leftPath.down
    obtain ⟨rightSourceFinal, rightSourcePath, rightEndpoint⟩ :=
      morphism.morphism.backward_multi_eq rightPath.down
    have sourceAgreement := sourceConsistent initial
      ⟨leftSourcePath⟩ ⟨rightSourcePath⟩
    calc
      morphism.observeTarget left =
          morphism.observeTarget
            (morphism.morphism.mapTerm leftSourceFinal) :=
        congrArg morphism.observeTarget leftEndpoint
      _ = morphism.observeSource leftSourceFinal :=
        morphism.commutes leftSourceFinal
      _ = morphism.observeSource rightSourceFinal := sourceAgreement
      _ = morphism.observeTarget
          (morphism.morphism.mapTerm rightSourceFinal) :=
        (morphism.commutes rightSourceFinal).symm
      _ = morphism.observeTarget right :=
        congrArg morphism.observeTarget rightEndpoint.symm
  · intro targetConsistent initial left right leftPath rightPath
    obtain ⟨leftTarget, leftTargetPath, leftEndpoint⟩ :=
      morphism.morphism.forward_multi_eq leftPath.down
    obtain ⟨rightTarget, rightTargetPath, rightEndpoint⟩ :=
      morphism.morphism.forward_multi_eq rightPath.down
    have targetAgreement := targetConsistent initial
      ⟨leftTargetPath⟩ ⟨rightTargetPath⟩
    calc
      morphism.observeSource left =
          morphism.observeTarget (morphism.morphism.mapTerm left) :=
        (morphism.commutes left).symm
      _ = morphism.observeTarget leftTarget :=
        congrArg morphism.observeTarget leftEndpoint.symm
      _ = morphism.observeTarget rightTarget := targetAgreement
      _ = morphism.observeTarget (morphism.morphism.mapTerm right) :=
        congrArg morphism.observeTarget rightEndpoint
      _ = morphism.observeSource right := morphism.commutes right

/-- Result-level reproducibility transports in both directions. -/
theorem reproducible_iff
    (morphism : ObservedLanguageMorphism source target Observed) :
    Reproducible morphism.sourcePathBuild
        morphism.sourceArtifactObservation <->
      Reproducible morphism.targetPathBuild
        morphism.targetArtifactObservation := by
  constructor
  · intro sourceReproducible
    exact ⟨morphism.target_rebuildable,
      morphism.observationConsistent_iff.mp sourceReproducible.2⟩
  · intro targetReproducible
    exact ⟨morphism.source_rebuildable,
      morphism.observationConsistent_iff.mpr targetReproducible.2⟩

/-- Cross-source declared-input sufficiency also transports through the same
operational correspondence and observation law. -/
theorem declarationSufficient_iff
    (morphism : ObservedLanguageMorphism source target Observed)
    (view : InputView.{0, uDeclared} Pattern) :
    DeclarationSufficient morphism.sourcePathBuild view
        morphism.sourceArtifactObservation <->
      DeclarationSufficient morphism.targetPathBuild view
        morphism.targetArtifactObservation := by
  constructor
  · intro sourceSufficient
    rintro ⟨leftInitial, left, leftPath⟩
      ⟨rightInitial, right, rightPath⟩ sameDeclaration
    obtain ⟨leftSourceFinal, leftSourcePath, leftEndpoint⟩ :=
      morphism.morphism.backward_multi_eq leftPath.down
    obtain ⟨rightSourceFinal, rightSourcePath, rightEndpoint⟩ :=
      morphism.morphism.backward_multi_eq rightPath.down
    have sourceAgreement := sourceSufficient
      (a := ⟨leftInitial, leftSourceFinal, ⟨leftSourcePath⟩⟩)
      (b := ⟨rightInitial, rightSourceFinal, ⟨rightSourcePath⟩⟩)
      sameDeclaration
    calc
      morphism.observeTarget left =
          morphism.observeTarget
            (morphism.morphism.mapTerm leftSourceFinal) :=
        congrArg morphism.observeTarget leftEndpoint
      _ = morphism.observeSource leftSourceFinal :=
        morphism.commutes leftSourceFinal
      _ = morphism.observeSource rightSourceFinal := sourceAgreement
      _ = morphism.observeTarget
          (morphism.morphism.mapTerm rightSourceFinal) :=
        (morphism.commutes rightSourceFinal).symm
      _ = morphism.observeTarget right :=
        congrArg morphism.observeTarget rightEndpoint.symm
  · intro targetSufficient
    rintro ⟨leftInitial, left, leftPath⟩
      ⟨rightInitial, right, rightPath⟩ sameDeclaration
    obtain ⟨leftTarget, leftTargetPath, leftEndpoint⟩ :=
      morphism.morphism.forward_multi_eq leftPath.down
    obtain ⟨rightTarget, rightTargetPath, rightEndpoint⟩ :=
      morphism.morphism.forward_multi_eq rightPath.down
    have targetAgreement := targetSufficient
      (a := ⟨leftInitial, leftTarget, ⟨leftTargetPath⟩⟩)
      (b := ⟨rightInitial, rightTarget, ⟨rightTargetPath⟩⟩)
      sameDeclaration
    calc
      morphism.observeSource left =
          morphism.observeTarget (morphism.morphism.mapTerm left) :=
        (morphism.commutes left).symm
      _ = morphism.observeTarget leftTarget :=
        congrArg morphism.observeTarget leftEndpoint.symm
      _ = morphism.observeTarget rightTarget := targetAgreement
      _ = morphism.observeTarget (morphism.morphism.mapTerm right) :=
        congrArg morphism.observeTarget rightEndpoint
      _ = morphism.observeSource right := morphism.commutes right

/-- Declared-view reproducibility transports through OSLF only after both
operational correspondence and endpoint-observation compatibility are present. -/
theorem declaredViewReproducible_iff
    (morphism : ObservedLanguageMorphism source target Observed)
    (view : InputView.{0, uDeclared} Pattern) :
    DeclaredViewReproducible morphism.sourcePathBuild view
        morphism.sourceArtifactObservation <->
      DeclaredViewReproducible morphism.targetPathBuild view
        morphism.targetArtifactObservation := by
  constructor
  · intro sourceReproducible
    exact ⟨morphism.target_rebuildable,
      (morphism.declarationSufficient_iff view).mp sourceReproducible.2⟩
  · intro targetReproducible
    exact ⟨morphism.source_rebuildable,
      (morphism.declarationSufficient_iff view).mpr targetReproducible.2⟩

/-- The current OSLF path carrier is proof-irrelevant.  It therefore cannot by
itself establish replay- or path-identity fidelity. -/
theorem sourcePathBuild_fibre_subsingleton
    (morphism : ObservedLanguageMorphism source target Observed)
    (initial final : Pattern) :
    Subsingleton (morphism.sourcePathBuild initial final) := by
  constructor
  rintro ⟨left⟩ ⟨right⟩
  congr

/-- Identity translation with exact endpoint observation is a substantive
satisfying instance of the additional observation law. -/
def identity (language : LanguageDef) :
    ObservedLanguageMorphism language language Pattern where
  morphism := idLanguageMorphism language
  observeSource := id
  observeTarget := id
  commutes := by intro term; rfl

end ObservedLanguageMorphism

/-! ## Compatibility failure control -/

namespace Canary

def language : LanguageDef := LanguageDef.empty "observation-canary"

def badTargetObservation : Pattern → Pattern :=
  fun _ => .fvar "fixed"

/-- A syntactically valid identity language morphism cannot transport an
observation that replaces every target endpoint by one fixed term. -/
theorem identity_morphism_incompatible_with_constant_target_observation :
    Not (∀ term,
      badTargetObservation ((idLanguageMorphism language).mapTerm term) =
        (id : Pattern → Pattern) term) := by
  intro compatible
  have impossible := compatible (.fvar "different")
  change Pattern.fvar "fixed" = Pattern.fvar "different" at impossible
  have fixedEqDifferent := Pattern.fvar.inj impossible
  exact (by decide : "fixed" ≠ "different") fixedEqDifferent

end Canary

#print axioms ObservedLanguageMorphism.reproducible_iff
#print axioms ObservedLanguageMorphism.declarationSufficient_iff
#print axioms ObservedLanguageMorphism.declaredViewReproducible_iff
#print axioms ObservedLanguageMorphism.sourcePathBuild_fibre_subsingleton
#print axioms Canary.identity_morphism_incompatible_with_constant_target_observation

end Mettapedia.GSLT.ReproducibleBuild.OSLF
