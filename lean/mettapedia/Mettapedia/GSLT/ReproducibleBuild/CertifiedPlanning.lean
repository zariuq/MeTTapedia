import Mettapedia.GSLT.Core.CertifiedPlanning
import Mettapedia.GSLT.ReproducibleBuild.Composition

/-!
# Reproducible-build view of certified realization plans

The existing `Realization` interface is functional and observation-indexed: a
compiler maps source objects to artifacts, and `adequate` proves equality at a
named observation.  This module recovers it as a represented special case of
the relational reproducible-build theory.

Every certified realization is declared-view reproducible when its declared
input is the source observation named by the realization.  Staged realization
composition agrees, proof-fibre by proof-fibre, with relational build
composition.  Existing `ObservationCell` composition therefore remains the
two-dimensional comparison between implementation routes; it is not replaced
by build reproducibility.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ReproducibleBuild.CertifiedPlanning

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.ReproducibleBuild
open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.ReproducibleBuild.Composition

universe uBase u uObservation

variable {Base : Type uBase}
  {Source Artifact Intermediate : Base → Type u}
  {Observation : Base → Type uObservation}

/-- The functional build relation selected by one certified realization at an
index. -/
def realizationBuild
    (realization : Realization Source Artifact Observation)
    (base : Base) : RelationalBuild (Source base) (Artifact base) :=
  companion (realization.compile base)

/-- The source observation named by a realization is its canonical declared
input view. -/
def sourceInputView
    (realization : Realization Source Artifact Observation)
    (base : Base) : InputView.{u, uObservation} (Source base) where
  View := Observation base
  project := realization.observeSource base

/-- The realization's artifact observation as an explicit reproducible-build
observation. -/
def artifactObservation
    (realization : Realization Source Artifact Observation)
    (base : Base) : ArtifactObservation.{u, uObservation} (Artifact base) where
  Observed := Observation base
  observe := realization.observeArtifact base

/-- Adequacy is exactly the factorization needed for declared-view
reproducibility of the realization's companion build. -/
theorem realization_declaredViewReproducible
    (realization : Realization Source Artifact Observation)
    (base : Base) :
    DeclaredViewReproducible (realizationBuild realization base)
      (sourceInputView realization base)
      (artifactObservation realization base) := by
  constructor
  · exact (companion_reproducible (realization.compile base)
      (artifactObservation realization base)).1
  · change DeclarationSufficient (companion (realization.compile base))
      (sourceInputView realization base)
      (artifactObservation realization base)
    rw [companion_declarationSufficient_iff]
    intro left right sameSourceObservation
    calc
      realization.observeArtifact base (realization.compile base left) =
          realization.observeSource base left :=
        realization.adequate base left
      _ = realization.observeSource base right := sameSourceObservation
      _ = realization.observeArtifact base (realization.compile base right) :=
        (realization.adequate base right).symm

/-- Relational composition of two certified stages retains exactly the same
proof fibres as the companion build of their staged compiler. -/
def stagedBuild_fibrewise
    (first : Realization Source Intermediate Observation)
    (second : Realization Intermediate Artifact Observation)
    (middleAgreement : ∀ base intermediate,
      second.observeSource base intermediate =
        first.observeArtifact base intermediate)
    (base : Base) :
    FibrewiseEquivalent
      (comp (realizationBuild first base) (realizationBuild second base))
      (realizationBuild (first.trans second middleAgreement) base) := by
  change FibrewiseEquivalent
    (comp (companion (first.compile base))
      (companion (second.compile base)))
    (companion (second.compile base ∘ first.compile base))
  exact companionComp_fibrewise (first.compile base) (second.compile base)

/-- Reproducibility of staged functional realizations is invariant under the
proof-fibre reassociation from relational composition to ordinary compiler
composition. -/
theorem stagedBuild_declaredViewReproducible_iff
    (first : Realization Source Intermediate Observation)
    (second : Realization Intermediate Artifact Observation)
    (middleAgreement : ∀ base intermediate,
      second.observeSource base intermediate =
        first.observeArtifact base intermediate)
    (base : Base)
    (view : InputView.{u, uObservation} (Source base))
    (observation :
      ArtifactObservation.{u, uObservation} (Artifact base)) :
    DeclaredViewReproducible
        (comp (realizationBuild first base) (realizationBuild second base))
        view observation <->
      DeclaredViewReproducible
        (realizationBuild (first.trans second middleAgreement) base)
        view observation :=
  (stagedBuild_fibrewise first second middleAgreement base)
    |>.declaredViewReproducible_iff view observation

namespace ObservationCell

/-- An observation cell says exactly that the two companion builds selected by
its realizations produce the same named compiled observation.  This bridge
does not identify their artifact or certificate fibres. -/
theorem compiled_build_observations_agree
    {LeftArtifact RightArtifact : Base → Type u}
    {left : Realization Source LeftArtifact Observation}
    {right : Realization Source RightArtifact Observation}
    (cell : Mettapedia.GSLT.ObservationCell left right)
    (base : Base) (source : Source base) :
    (artifactObservation left base).observe (left.compile base source) =
      (artifactObservation right base).observe
        (right.compile base source) :=
  cell.compiled base source

/-- Existing vertical composition of observation cells is respected by the
reproducible-build readout: agreement through an intermediate route yields
agreement of the endpoint compiled observations. -/
theorem trans_compiled_build_observations_agree
    {LeftArtifact MiddleArtifact RightArtifact : Base → Type u}
    {left : Realization Source LeftArtifact Observation}
    {middle : Realization Source MiddleArtifact Observation}
    {right : Realization Source RightArtifact Observation}
    (first : Mettapedia.GSLT.ObservationCell left middle)
    (second : Mettapedia.GSLT.ObservationCell middle right)
    (base : Base) (source : Source base) :
    (artifactObservation left base).observe (left.compile base source) =
      (artifactObservation right base).observe
        (right.compile base source) :=
  (first.trans second).compiled base source

end ObservationCell

#print axioms realization_declaredViewReproducible
#print axioms stagedBuild_fibrewise
#print axioms stagedBuild_declaredViewReproducible_iff
#print axioms ObservationCell.trans_compiled_build_observations_agree

end Mettapedia.GSLT.ReproducibleBuild.CertifiedPlanning
