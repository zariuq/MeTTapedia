import Mettapedia.GSLT.Core.ReproducibleBuild

/-!
# Composition laws for relational reproducible builds

Build composition retains the intermediate artifact and both execution
witnesses through the existing proof-relevant loose-relation composition.
Rebuildability composes whenever both stages are total.  Declared-view
reproducibility additionally requires an observation of the intermediate
artifact that is sufficient both for the upstream declaration and for the
downstream result.

This compatibility premise is essential.  Two stages can each be reproducible
at their own declared observations while their composite is not reproducible
at a finer final observation: the downstream stage may inspect a distinction
that the upstream observation deliberately erased.  The negative control below
exhibits exactly that hidden-intermediate-input failure.

The task/build separation and proof-relevant relational composition follow the
framework of Mokhov, Mitchell, and Peyton Jones, *Build Systems a la Carte*
(2020).  The complete-input interpretation is aligned with Dolstra's closure
model and Hatta's AGI-oriented complete-input requirement; the composition
theorems and controls here are our formal extensions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ReproducibleBuild.Composition

open Mettapedia.GSLT.Core.ReproducibleBuild
open Mettapedia.GSLT.LooseRelationEquipment

universe u uDeclared uMiddleObserved uFinalObserved

variable {Source Middle Artifact : Type u}

/-! ## Invariance under exact proof-fibre equivalence -/

/-- Two build relations are fibrewise equivalent when they have exactly the
same execution evidence for every fixed source and artifact. -/
def FibrewiseEquivalent
    {Source Artifact : Type u}
    (left right : RelationalBuild Source Artifact) : Type u :=
  forall source artifact, left source artifact ≃ right source artifact

namespace FibrewiseEquivalent

variable {left right : RelationalBuild Source Artifact}

/-- Exact proof-fibre equivalence preserves and reflects rebuildability. -/
theorem rebuildable_iff (equivalent : FibrewiseEquivalent left right) :
    Rebuildable left <-> Rebuildable right := by
  constructor
  · intro leftRebuildable source
    obtain ⟨⟨artifact, witness⟩⟩ := leftRebuildable source
    exact ⟨⟨artifact, equivalent source artifact witness⟩⟩
  · intro rightRebuildable source
    obtain ⟨⟨artifact, witness⟩⟩ := rightRebuildable source
    exact ⟨⟨artifact, (equivalent source artifact).symm witness⟩⟩

/-- Exact proof-fibre equivalence preserves and reflects consistency at every
artifact observation. -/
theorem observationConsistent_iff
    (equivalent : FibrewiseEquivalent left right)
    (observation : ArtifactObservation.{u, uFinalObserved} Artifact) :
    ObservationConsistent left observation <->
      ObservationConsistent right observation := by
  constructor
  · intro leftConsistent source first second firstWitness secondWitness
    exact leftConsistent source
      ((equivalent source first).symm firstWitness)
      ((equivalent source second).symm secondWitness)
  · intro rightConsistent source first second firstWitness secondWitness
    exact rightConsistent source
      (equivalent source first firstWitness)
      (equivalent source second secondWitness)

/-- Exact proof-fibre equivalence preserves and reflects per-source
reproducibility. -/
theorem reproducible_iff
    (equivalent : FibrewiseEquivalent left right)
    (observation : ArtifactObservation.{u, uFinalObserved} Artifact) :
    Reproducible left observation <-> Reproducible right observation := by
  rw [Reproducible, Reproducible, equivalent.rebuildable_iff,
    equivalent.observationConsistent_iff observation]

/-- Exact proof-fibre equivalence preserves and reflects declared-input
sufficiency. -/
theorem declarationSufficient_iff
    (equivalent : FibrewiseEquivalent left right)
    (view : InputView.{u, uDeclared} Source)
    (observation : ArtifactObservation.{u, uFinalObserved} Artifact) :
    DeclarationSufficient left view observation <->
      DeclarationSufficient right view observation := by
  constructor
  · intro leftSufficient
    rintro ⟨leftSource, leftArtifact, leftWitness⟩
      ⟨rightSource, rightArtifact, rightWitness⟩ sameDeclaration
    exact leftSufficient
      (a := ⟨leftSource, leftArtifact,
        (equivalent leftSource leftArtifact).symm leftWitness⟩)
      (b := ⟨rightSource, rightArtifact,
        (equivalent rightSource rightArtifact).symm rightWitness⟩)
      sameDeclaration
  · intro rightSufficient
    rintro ⟨leftSource, leftArtifact, leftWitness⟩
      ⟨rightSource, rightArtifact, rightWitness⟩ sameDeclaration
    exact rightSufficient
      (a := ⟨leftSource, leftArtifact,
        equivalent leftSource leftArtifact leftWitness⟩)
      (b := ⟨rightSource, rightArtifact,
        equivalent rightSource rightArtifact rightWitness⟩)
      sameDeclaration

/-- Exact proof-fibre equivalence preserves the complete declared-view
reproducibility contract in both directions. -/
theorem declaredViewReproducible_iff
    (equivalent : FibrewiseEquivalent left right)
    (view : InputView.{u, uDeclared} Source)
    (observation : ArtifactObservation.{u, uFinalObserved} Artifact) :
    DeclaredViewReproducible left view observation <->
      DeclaredViewReproducible right view observation := by
  rw [DeclaredViewReproducible, DeclaredViewReproducible,
    equivalent.rebuildable_iff,
    equivalent.declarationSufficient_iff view observation]

end FibrewiseEquivalent

/-- Left identity is exact at every retained execution fibre. -/
def compIdentityLeft_fibrewise
    (build : RelationalBuild Source Artifact) :
    FibrewiseEquivalent (comp identity build) build :=
  compIdentityLeft build

/-- Right identity is exact at every retained execution fibre. -/
def compIdentityRight_fibrewise
    (build : RelationalBuild Source Artifact) :
    FibrewiseEquivalent (comp build identity) build :=
  compIdentityRight build

/-- Associativity changes only the bracketing of retained intermediate
artifacts and witnesses. -/
def compAssoc_fibrewise
    {A B C D : Type u}
    (first : RelationalBuild A B) (second : RelationalBuild B C)
    (third : RelationalBuild C D) :
    FibrewiseEquivalent (comp (comp first second) third)
      (comp first (comp second third)) :=
  compAssoc first second third

/-- A represented relation is exactly its representing functional companion at
every proof fibre. -/
def representation_fibrewise_companion
    {build : RelationalBuild Source Artifact}
    (representation : Representation build) :
    FibrewiseEquivalent build (companion representation.map) :=
  representation.exact

/-- Composition of two functional companion builds is proof-fibre equivalent
to the companion of ordinary function composition. -/
def companionComp_fibrewise
    (earlier : Source → Middle) (later : Middle → Artifact) :
    FibrewiseEquivalent (comp (companion earlier) (companion later))
      (companion (later ∘ earlier)) :=
  representation_fibrewise_companion
    (Representation.horizontalComp
      (Representation.companionSelf earlier)
      (Representation.companionSelf later))

/-- Regard an observation of intermediate artifacts as the input declaration
available to the downstream build. -/
def observationInputView
    (observation : ArtifactObservation.{u, uMiddleObserved} Middle) :
    InputView.{u, uMiddleObserved} Middle where
  View := observation.Observed
  project := observation.observe

/-- Total relational builds compose without choosing or erasing the retained
intermediate artifact. -/
theorem rebuildable_comp
    {earlier : RelationalBuild Source Middle}
    {later : RelationalBuild Middle Artifact}
    (earlierRebuildable : Rebuildable earlier)
    (laterRebuildable : Rebuildable later) :
    Rebuildable (comp earlier later) := by
  intro source
  obtain ⟨⟨middle, earlierWitness⟩⟩ := earlierRebuildable source
  obtain ⟨⟨artifact, laterWitness⟩⟩ := laterRebuildable middle
  exact ⟨⟨artifact, middle, earlierWitness, laterWitness⟩⟩

/-- Sufficient upstream and downstream declarations compose.  The shared
intermediate observation is the explicit compatibility interface between the
two stages. -/
theorem declarationSufficient_comp
    {earlier : RelationalBuild Source Middle}
    {later : RelationalBuild Middle Artifact}
    (sourceView : InputView.{u, uDeclared} Source)
    (middleObservation :
      ArtifactObservation.{u, uMiddleObserved} Middle)
    (finalObservation :
      ArtifactObservation.{u, uFinalObserved} Artifact)
    (earlierSufficient :
      DeclarationSufficient earlier sourceView middleObservation)
    (laterSufficient :
      DeclarationSufficient later
        (observationInputView middleObservation) finalObservation) :
    DeclarationSufficient (comp earlier later) sourceView finalObservation := by
  rintro ⟨leftSource, leftArtifact, leftMiddle, leftEarlier, leftLater⟩
    ⟨rightSource, rightArtifact, rightMiddle, rightEarlier, rightLater⟩
    sameSourceView
  let leftEarlierOccurrence : Occurrence earlier :=
    ⟨leftSource, leftMiddle, leftEarlier⟩
  let rightEarlierOccurrence : Occurrence earlier :=
    ⟨rightSource, rightMiddle, rightEarlier⟩
  have sameMiddleObservation :
      middleObservation.observe leftMiddle =
        middleObservation.observe rightMiddle :=
    earlierSufficient
      (a := leftEarlierOccurrence) (b := rightEarlierOccurrence)
      sameSourceView
  let leftLaterOccurrence : Occurrence later :=
    ⟨leftMiddle, leftArtifact, leftLater⟩
  let rightLaterOccurrence : Occurrence later :=
    ⟨rightMiddle, rightArtifact, rightLater⟩
  exact laterSufficient
    (a := leftLaterOccurrence) (b := rightLaterOccurrence)
    sameMiddleObservation

/-- Declared-view reproducibility composes exactly when the selected
intermediate observation is an adequate interface for the downstream stage. -/
theorem declaredViewReproducible_comp
    {earlier : RelationalBuild Source Middle}
    {later : RelationalBuild Middle Artifact}
    (sourceView : InputView.{u, uDeclared} Source)
    (middleObservation :
      ArtifactObservation.{u, uMiddleObserved} Middle)
    (finalObservation :
      ArtifactObservation.{u, uFinalObserved} Artifact)
    (earlierReproducible :
      DeclaredViewReproducible earlier sourceView middleObservation)
    (laterReproducible :
      DeclaredViewReproducible later
        (observationInputView middleObservation) finalObservation) :
    DeclaredViewReproducible (comp earlier later) sourceView
      finalObservation :=
  ⟨rebuildable_comp earlierReproducible.1 laterReproducible.1,
    declarationSufficient_comp sourceView middleObservation finalObservation
      earlierReproducible.2 laterReproducible.2⟩

/-! ## Positive and negative controls -/

namespace Canary

/-- The complete source declaration for the one-point source. -/
def unitSourceView : InputView Unit where
  View := Unit
  project := id

/-- A downstream identity build reads the intermediate Boolean exactly. -/
def inspectIntermediate : RelationalBuild Bool Bool :=
  companion id

/-- Branching followed by exact inspection retains the hidden intermediate
Boolean as the final artifact. -/
def hiddenIntermediateComposite : RelationalBuild Unit Bool :=
  comp Mettapedia.GSLT.Core.ReproducibleBuild.Canary.branching
    inspectIntermediate

theorem inspectIntermediate_exact_reproducible :
    Reproducible inspectIntermediate
      (ArtifactObservation.identity Bool) :=
  companion_reproducible id (ArtifactObservation.identity Bool)

/-- Although the branching stage is reproducible at the collapsed Boolean
observation, the downstream identity build cannot factor its exact result
through that erased observation. -/
theorem collapsedMiddle_not_sufficient_for_inspection :
    Not (DeclarationSufficient inspectIntermediate
      (observationInputView
        Mettapedia.GSLT.Core.ReproducibleBuild.Canary.collapsedBoolObservation)
      (ArtifactObservation.identity Bool)) := by
  intro sufficient
  let falseOccurrence : Occurrence inspectIntermediate :=
    ⟨false, false, ⟨⟨rfl⟩⟩⟩
  let trueOccurrence : Occurrence inspectIntermediate :=
    ⟨true, true, ⟨⟨rfl⟩⟩⟩
  have falseEqTrue := sufficient
    (a := falseOccurrence) (b := trueOccurrence) rfl
  exact Bool.false_ne_true falseEqTrue

/-- Per-stage reproducibility at mismatched observations does not imply
reproducibility of the composite at the final exact observation. -/
theorem hiddenIntermediateComposite_not_exact_reproducible :
    Not (Reproducible hiddenIntermediateComposite
      (ArtifactObservation.identity Bool)) := by
  intro reproducible
  have falseWitness : hiddenIntermediateComposite () false :=
    ⟨false, (), ⟨⟨rfl⟩⟩⟩
  have trueWitness : hiddenIntermediateComposite () true :=
    ⟨true, (), ⟨⟨rfl⟩⟩⟩
  have falseEqTrue := reproducible.2 () falseWitness trueWitness
  exact Bool.false_ne_true falseEqTrue

/-- The negative control keeps both premises visible: each stage is
reproducible at its own observation, yet the composite fails because the
chosen intermediate observation is not downstream-sufficient. -/
theorem stagewise_reproducible_but_composite_not :
    Reproducible
        Mettapedia.GSLT.Core.ReproducibleBuild.Canary.branching
        Mettapedia.GSLT.Core.ReproducibleBuild.Canary.collapsedBoolObservation /\
      Reproducible inspectIntermediate
        (ArtifactObservation.identity Bool) /\
      Not (Reproducible hiddenIntermediateComposite
        (ArtifactObservation.identity Bool)) :=
  ⟨Mettapedia.GSLT.Core.ReproducibleBuild.Canary.branching_collapsed_reproducible,
    inspectIntermediate_exact_reproducible,
    hiddenIntermediateComposite_not_exact_reproducible⟩

/-- Exact intermediate observation makes the same identity downstream stage
compatible, providing the positive composition control. -/
theorem exactIntermediate_sufficient_for_inspection :
    DeclarationSufficient inspectIntermediate
      (observationInputView (ArtifactObservation.identity Bool))
      (ArtifactObservation.identity Bool) := by
  change DeclarationSufficient (companion id)
    (observationInputView (ArtifactObservation.identity Bool))
    (ArtifactObservation.identity Bool)
  rw [companion_declarationSufficient_iff]
  intro left right same
  exact same

end Canary

#print axioms rebuildable_comp
#print axioms FibrewiseEquivalent.declaredViewReproducible_iff
#print axioms compAssoc_fibrewise
#print axioms companionComp_fibrewise
#print axioms declarationSufficient_comp
#print axioms declaredViewReproducible_comp
#print axioms Canary.collapsedMiddle_not_sufficient_for_inspection
#print axioms Canary.stagewise_reproducible_but_composite_not

end Mettapedia.GSLT.ReproducibleBuild.Composition
