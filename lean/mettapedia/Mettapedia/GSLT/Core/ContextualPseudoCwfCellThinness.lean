import Mettapedia.GSLT.Core.ContextualPseudoCwfBasePseudofunctor

/-!
# Local thinness transfer for corrected pseudo-CwF transformations

The corrected comprehension square makes the displayed action of a
pseudo-CwF transformation uniquely determined by its natural transformation
on contexts.  Consequently, local thinness of the context-level semantic
image transfers to the corrected pseudo-CwF layer.

This separates two kinds of proof relevance.  Types and terms in a fibre may
retain many witnesses, costs, or execution receipts without creating distinct
transformations between the same pseudo-CwF morphisms.  A genuinely distinct
corrected transformation must already project to a distinct context-level
natural transformation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ContextualLadder

open CategoryTheory

universe u v w w' uObservation

variable {C D : CwfWithTerminal.{u, v, w, w'}}
variable {F G : PseudoCwfMorphism C D}

/-- If the natural transformations between the two context functors form a
subsingleton, then so do the corrected pseudo-CwF transformations. -/
theorem correctedTransformationSubsingletonOfBase
    (baseThin : Subsingleton (F.base ⟶ G.base)) :
    Subsingleton (F ⟶ G) where
  allEq first second :=
    CorrectedTransformationData.ext_of_base_eq first second
      (baseThin.elim first.base second.base)

/-- Local thinness of the projected `Cat` 2-cell fibre transfers back through
the locally faithful base pseudofunctor. -/
theorem correctedTransformationSubsingletonOfProjectedCells
    (projectedThin : Subsingleton
      (pseudoCwfBasePseudofunctor.map F ⟶
        pseudoCwfBasePseudofunctor.map G)) :
    Subsingleton (F ⟶ G) where
  allEq first second :=
    pseudoCwfBasePseudofunctor_map₂_injective first second
      (projectedThin.elim
        (pseudoCwfBasePseudofunctor.map₂ first)
        (pseudoCwfBasePseudofunctor.map₂ second))

/-- Distinct corrected pseudo-CwF transformations necessarily have distinct
natural transformations on contexts. -/
theorem base_ne_of_correctedTransformation_ne
    (first second : F ⟶ G) (different : first ≠ second) :
    first.base ≠ second.base := by
  intro baseEqual
  exact different
    (CorrectedTransformationData.ext_of_base_eq first second baseEqual)

/-- Equivalently, a distinct corrected 2-cell remains distinct after the
base pseudofunctor projects it to `Cat`. -/
theorem projectedCell_ne_of_correctedTransformation_ne
    (first second : F ⟶ G) (different : first ≠ second) :
    pseudoCwfBasePseudofunctor.map₂ first ≠
      pseudoCwfBasePseudofunctor.map₂ second := by
  intro projectedEqual
  exact different
    (pseudoCwfBasePseudofunctor_map₂_injective first second projectedEqual)

/-- Any consumer of corrected transformations is constant on a fibre of the
base projection.  Thus a consumer-visible distinction cannot be hidden solely
in the displayed family component. -/
theorem observation_eq_of_base_eq
    {Observation : Sort uObservation}
    (observe : (F ⟶ G) → Observation)
    (first second : F ⟶ G)
    (baseEqual : first.base = second.base) :
    observe first = observe second :=
  congrArg observe
    (CorrectedTransformationData.ext_of_base_eq first second baseEqual)

/-- If a consumer distinguishes two corrected transformations, then their
projected `Cat` 2-cells are also distinct.  This is the exact discriminator
required before proof-relevant mode cells are forced by dependent semantics. -/
theorem projectedCell_ne_of_observation_ne
    {Observation : Sort uObservation}
    (observe : (F ⟶ G) → Observation)
    (first second : F ⟶ G)
    (distinguished : observe first ≠ observe second) :
    pseudoCwfBasePseudofunctor.map₂ first ≠
      pseudoCwfBasePseudofunctor.map₂ second := by
  intro projectedEqual
  exact distinguished (congrArg observe
    (pseudoCwfBasePseudofunctor_map₂_injective
      first second projectedEqual))

/-- A proof-relevant corrected transformation fibre forces a proof-relevant
base-transformation fibre. -/
theorem distinctBaseTransformations_of_distinctCorrectedTransformations
    (witness : ∃ first second : F ⟶ G, first ≠ second) :
    ∃ firstBase secondBase : F.base ⟶ G.base, firstBase ≠ secondBase := by
  rcases witness with ⟨first, second, different⟩
  exact ⟨first.base, second.base,
    base_ne_of_correctedTransformation_ne first second different⟩

/-! ## Controls -/

/-- Positive control: every pseudo-CwF morphism has its canonical corrected
identity transformation. -/
theorem correctedIdentityTransformation_inhabited
    (F : PseudoCwfMorphism C D) : Nonempty (F ⟶ F) :=
  ⟨𝟙 F⟩

/-- Negative control: two corrected transformations with the same projected
context action cannot be separated by any observation of their dependent
action. -/
theorem noDisplayedOnlyTransformationDiscriminator
    {Observation : Sort uObservation}
    (observe : (F ⟶ G) → Observation)
    (first second : F ⟶ G)
    (sameProjectedCell :
      pseudoCwfBasePseudofunctor.map₂ first =
        pseudoCwfBasePseudofunctor.map₂ second) :
    ¬ observe first ≠ observe second := by
  intro distinguished
  exact projectedCell_ne_of_observation_ne observe first second distinguished
    sameProjectedCell

#print axioms correctedTransformationSubsingletonOfBase
#print axioms correctedTransformationSubsingletonOfProjectedCells
#print axioms base_ne_of_correctedTransformation_ne
#print axioms projectedCell_ne_of_correctedTransformation_ne
#print axioms observation_eq_of_base_eq
#print axioms projectedCell_ne_of_observation_ne
#print axioms distinctBaseTransformations_of_distinctCorrectedTransformations
#print axioms correctedIdentityTransformation_inhabited
#print axioms noDisplayedOnlyTransformationDiscriminator

end Mettapedia.GSLT.Core.ContextualLadder
