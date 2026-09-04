import Mettapedia.GSLT.Core.ContextualPseudoCwfMorphism
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Corrected transformations between pseudo CwF morphisms

This module begins the 2-cell layer for the bicategorical organization of
categories with families.  The central contract incorporates the missing
comprehension-coherence square identified in the erratum to the
Clairambault--Dybjer biequivalence theorem.

For pseudo CwF morphisms `F` and `G`, a base natural transformation
`alpha : F.base ⟶ G.base` sends a translated type `G(A)` back to the fibre
over `F(Gamma)` by reindexing along `alpha_Gamma`.  A displayed component
then has the form

```text
  F(A) ⟶ G(A)[alpha_Gamma].
```

The corrected square says that this displayed arrow is exactly the
factorization of `alpha_(Gamma.A)` through the selected comprehension
comparisons.  It is load-bearing: the square makes the displayed component
unique once the base transformation is fixed.

The structure below is intentionally called `CorrectedTransformationData`:
the substitution-coherence theorem and horizontal/vertical composition are
proved in the subsequent layer before this data is installed as the hom
category of a bicategory.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ContextualLadder

open CategoryTheory

universe u v w w'

/-- Corrected fibrewise data for a transformation between pseudo CwF
morphisms.  In addition to naturality in display maps, the final field is the
comprehension square omitted from the historical definition. -/
structure CorrectedTransformationData
    {C D : CwfWithTerminal.{u, v, w, w'}}
    (F G : PseudoCwfMorphism C D) where
  /-- The transformation on contexts and substitutions. -/
  base : F.base ⟶ G.base
  /-- Its displayed action on each category of types over a context. -/
  family : ∀ (Γ : C.toCwf.Ctx) (A : TypeOver C.toCwf Γ),
    F.mapTypeObject A ⟶
      TypeOver.reindexObject (base.app ⟨Γ⟩) (G.mapTypeObject A)
  /-- The displayed component is natural in maps between types over the same
  context. -/
  family_naturality : ∀ (Γ : C.toCwf.Ctx)
      {A B : TypeOver C.toCwf Γ} (arrow : A ⟶ B),
    (F.mapTypeFunctor Γ).map arrow ≫ family Γ B =
      family Γ A ≫
        (TypeOver.reindexFunctor (base.app ⟨Γ⟩)).map
          ((G.mapTypeFunctor Γ).map arrow)
  /-- Corrected comprehension coherence.  Following the displayed component
  and the selected cartesian lift is exactly the extension-context component
  of the base transformation, conjugated by the two comprehension
  comparisons. -/
  comprehension_coherence : ∀ (Γ : C.toCwf.Ctx)
      (A : TypeOver C.toCwf Γ),
    (F.comprehensionIso Γ A.val).hom ≫
        (family Γ A).substitution ≫
          TypeOver.extensionSubstitution (base.app ⟨Γ⟩)
            (G.mapType A.val) =
      base.app ⟨C.toCwf.ext Γ A.val⟩ ≫
        (G.comprehensionIso Γ A.val).hom

namespace CorrectedTransformationData

variable {C D : CwfWithTerminal.{u, v, w, w'}}
variable {F G : PseudoCwfMorphism C D}

/-- Naturality of the base transformation identifies the two staged
reindexings of a translated type.  The comparison is assembled from the
two pseudofunctorial composition comparisons and the equality induced by
the naturality square; no iterated reindexing is treated as definitionally
equal. -/
def baseNaturalityReindexIso
    (transformation : CorrectedTransformationData F G)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    (A : TypeOver C.toCwf Δ) :
    TypeOver.reindexObject (F.base.map substitution)
        (TypeOver.reindexObject (transformation.base.app ⟨Δ⟩)
          (G.mapTypeObject A)) ≅
      TypeOver.reindexObject (transformation.base.app ⟨Γ⟩)
        (TypeOver.reindexObject (G.base.map substitution)
          (G.mapTypeObject A)) :=
  (TypeOver.compositionObjectIso
      (transformation.base.app ⟨Δ⟩) (F.base.map substitution)
      (G.mapTypeObject A)).symm ≪≫
    TypeOver.substitutionEqualityObjectIso
      (transformation.base.naturality
        (show (⟨Γ⟩ : C.toCwf.base.Context) ⟶ ⟨Δ⟩ from substitution))
      (G.mapTypeObject A) ≪≫
    TypeOver.compositionObjectIso
      (G.base.map substitution) (transformation.base.app ⟨Γ⟩)
      (G.mapTypeObject A)

/-- The base-naturality comparison identifies the two staged cartesian
lifts.  This is the load-bearing equation behind the historical
substitution-coherence square. -/
theorem baseNaturalityReindexIso_hom_composedExtensionSubstitution
    (transformation : CorrectedTransformationData F G)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    (A : TypeOver C.toCwf Δ) :
    D.toCwf.compS
      (TypeOver.composedExtensionSubstitution
          (G.base.map substitution) (transformation.base.app ⟨Γ⟩)
          (G.mapTypeObject A).val)
      (transformation.baseNaturalityReindexIso substitution A).hom.substitution =
      TypeOver.composedExtensionSubstitution
        (transformation.base.app ⟨Δ⟩) (F.base.map substitution)
        (G.mapTypeObject A).val := by
  let leftComposition := TypeOver.compositionObjectIso
    (transformation.base.app ⟨Δ⟩) (F.base.map substitution)
    (G.mapTypeObject A)
  let substitutionEquality := TypeOver.substitutionEqualityObjectIso
    (transformation.base.naturality
      (show (⟨Γ⟩ : C.toCwf.base.Context) ⟶ ⟨Δ⟩ from substitution))
    (G.mapTypeObject A)
  let rightComposition := TypeOver.compositionObjectIso
    (G.base.map substitution) (transformation.base.app ⟨Γ⟩)
    (G.mapTypeObject A)
  have rightComparison := TypeOver.compositionObjectIso_hom_lift
    (G.base.map substitution) (transformation.base.app ⟨Γ⟩)
    (G.mapTypeObject A)
  have equalityComparison :=
    TypeOver.substitutionEqualityObjectIso_hom_lift
      (transformation.base.naturality
        (show (⟨Γ⟩ : C.toCwf.base.Context) ⟶ ⟨Δ⟩ from substitution))
      (G.mapTypeObject A)
  have leftComparison := TypeOver.compositionObjectIso_hom_lift
    (transformation.base.app ⟨Δ⟩) (F.base.map substitution)
    (G.mapTypeObject A)
  have comparisonExpansion :
      (transformation.baseNaturalityReindexIso substitution A).hom.substitution =
        D.toCwf.compS rightComposition.hom.substitution
          (D.toCwf.compS substitutionEquality.hom.substitution
            leftComposition.inv.substitution) := by
    simp only [baseNaturalityReindexIso, Iso.trans_hom,
      TypeOver.Hom.comp_substitution]
    exact D.toCwf.comp_assoc _ _ _
  rw [comparisonExpansion]
  change
    D.toCwf.compS
      (TypeOver.composedExtensionSubstitution
        (G.base.map substitution) (transformation.base.app ⟨Γ⟩)
        (G.mapTypeObject A).val)
      (D.toCwf.compS rightComposition.hom.substitution
        (D.toCwf.compS substitutionEquality.hom.substitution
          leftComposition.inv.substitution)) =
      TypeOver.composedExtensionSubstitution
        (transformation.base.app ⟨Δ⟩) (F.base.map substitution)
        (G.mapTypeObject A).val
  have leftCancellation :
      D.toCwf.compS leftComposition.hom.substitution
          leftComposition.inv.substitution =
        D.toCwf.idS _ := by
    exact congrArg TypeOver.Hom.substitution
      leftComposition.inv_hom_id
  change D.toCwf.compS
      (TypeOver.extensionSubstitution
        (D.toCwf.compS (G.base.map substitution)
          (transformation.base.app ⟨Γ⟩))
        (G.mapTypeObject A).val)
      substitutionEquality.hom.substitution =
    TypeOver.extensionSubstitution
      (D.toCwf.compS (transformation.base.app ⟨Δ⟩)
        (F.base.map substitution))
      (G.mapTypeObject A).val at equalityComparison
  calc
    _ = D.toCwf.compS
        (D.toCwf.compS
          (TypeOver.composedExtensionSubstitution
            (G.base.map substitution) (transformation.base.app ⟨Γ⟩)
            (G.mapTypeObject A).val)
          rightComposition.hom.substitution)
        (D.toCwf.compS substitutionEquality.hom.substitution
          leftComposition.inv.substitution) :=
      (D.toCwf.comp_assoc _ _ _).symm
    _ = D.toCwf.compS
        (TypeOver.extensionSubstitution
          (D.toCwf.compS (G.base.map substitution)
            (transformation.base.app ⟨Γ⟩))
          (G.mapTypeObject A).val)
        (D.toCwf.compS substitutionEquality.hom.substitution
          leftComposition.inv.substitution) :=
      congrArg
        (fun outer => D.toCwf.compS outer
          (D.toCwf.compS substitutionEquality.hom.substitution
            leftComposition.inv.substitution))
        rightComparison
    _ = D.toCwf.compS
        (D.toCwf.compS
          (TypeOver.extensionSubstitution
            (D.toCwf.compS (G.base.map substitution)
              (transformation.base.app ⟨Γ⟩))
            (G.mapTypeObject A).val)
          substitutionEquality.hom.substitution)
        leftComposition.inv.substitution :=
      (D.toCwf.comp_assoc _ _ _).symm
    _ = D.toCwf.compS
        (TypeOver.extensionSubstitution
          (D.toCwf.compS (transformation.base.app ⟨Δ⟩)
            (F.base.map substitution))
          (G.mapTypeObject A).val)
        leftComposition.inv.substitution :=
      congrArg
        (fun outer => D.toCwf.compS outer
          leftComposition.inv.substitution)
        equalityComparison
    _ = D.toCwf.compS
        (D.toCwf.compS
          (TypeOver.composedExtensionSubstitution
            (transformation.base.app ⟨Δ⟩) (F.base.map substitution)
            (G.mapTypeObject A).val)
          leftComposition.hom.substitution)
        leftComposition.inv.substitution :=
      congrArg
        (fun outer => D.toCwf.compS outer
          leftComposition.inv.substitution)
        leftComparison.symm
    _ = D.toCwf.compS
        (TypeOver.composedExtensionSubstitution
          (transformation.base.app ⟨Δ⟩) (F.base.map substitution)
          (G.mapTypeObject A).val)
        (D.toCwf.compS leftComposition.hom.substitution
          leftComposition.inv.substitution) :=
      D.toCwf.comp_assoc _ _ _
    _ = D.toCwf.compS
        (TypeOver.composedExtensionSubstitution
          (transformation.base.app ⟨Δ⟩) (F.base.map substitution)
          (G.mapTypeObject A).val)
        (D.toCwf.idS _) :=
      congrArg
        (fun inner => D.toCwf.compS
          (TypeOver.composedExtensionSubstitution
            (transformation.base.app ⟨Δ⟩) (F.base.map substitution)
            (G.mapTypeObject A).val)
          inner)
        leftCancellation
    _ = _ := D.toCwf.comp_id _

/-- The inverse base-naturality comparison carries the left staged lift to
the right staged lift. -/
theorem baseNaturalityReindexIso_inv_composedExtensionSubstitution
    (transformation : CorrectedTransformationData F G)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    (A : TypeOver C.toCwf Δ) :
    D.toCwf.compS
      (TypeOver.composedExtensionSubstitution
        (transformation.base.app ⟨Δ⟩) (F.base.map substitution)
        (G.mapTypeObject A).val)
      (transformation.baseNaturalityReindexIso substitution A).inv.substitution =
    TypeOver.composedExtensionSubstitution
      (G.base.map substitution) (transformation.base.app ⟨Γ⟩)
      (G.mapTypeObject A).val := by
  let comparison := transformation.baseNaturalityReindexIso substitution A
  let leftLift := TypeOver.composedExtensionSubstitution
    (transformation.base.app ⟨Δ⟩) (F.base.map substitution)
    (G.mapTypeObject A).val
  let rightLift := TypeOver.composedExtensionSubstitution
    (G.base.map substitution) (transformation.base.app ⟨Γ⟩)
    (G.mapTypeObject A).val
  have forward :=
    transformation.baseNaturalityReindexIso_hom_composedExtensionSubstitution
      substitution A
  have cancellation :
      D.toCwf.compS comparison.hom.substitution
          comparison.inv.substitution =
        D.toCwf.idS _ := by
    exact congrArg TypeOver.Hom.substitution comparison.inv_hom_id
  change D.toCwf.compS leftLift comparison.inv.substitution = rightLift
  change D.toCwf.compS rightLift comparison.hom.substitution = leftLift
    at forward
  calc
    _ = D.toCwf.compS
        (D.toCwf.compS rightLift comparison.hom.substitution)
        comparison.inv.substitution :=
      congrArg
        (fun outer => D.toCwf.compS outer comparison.inv.substitution)
        forward.symm
    _ = D.toCwf.compS rightLift
        (D.toCwf.compS comparison.hom.substitution
          comparison.inv.substitution) := D.toCwf.comp_assoc _ _ _
    _ = D.toCwf.compS rightLift (D.toCwf.idS _) :=
      congrArg (fun inner => D.toCwf.compS rightLift inner) cancellation
    _ = rightLift := D.toCwf.comp_id _

/-- The target-side comparison used to cancel the historical substitution
square.  It first reindexes the inverse of `G`'s substitution comparison and
then transports across naturality of the base transformation. -/
def historicalTargetIso
    (transformation : CorrectedTransformationData F G)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    (A : TypeOver C.toCwf Δ) :
    TypeOver.reindexObject (transformation.base.app ⟨Γ⟩)
        (G.mapTypeObject (TypeOver.reindexObject substitution A)) ≅
      TypeOver.reindexObject (F.base.map substitution)
        (TypeOver.reindexObject (transformation.base.app ⟨Δ⟩)
          (G.mapTypeObject A)) :=
  (TypeOver.reindexFunctor (transformation.base.app ⟨Γ⟩)).mapIso
      (G.substitutionIso substitution A).symm ≪≫
    (transformation.baseNaturalityReindexIso substitution A).symm

/-- Following the historical target comparison by the left staged lift is
the concrete path obtained by lifting the base transformation, applying the
inverse target substitution comparison, and lifting the translated source
substitution. -/
theorem historicalTargetIso_hom_composedExtensionSubstitution
    (transformation : CorrectedTransformationData F G)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    (A : TypeOver C.toCwf Δ) :
    D.toCwf.compS
      (TypeOver.composedExtensionSubstitution
        (transformation.base.app ⟨Δ⟩) (F.base.map substitution)
        (G.mapTypeObject A).val)
      (transformation.historicalTargetIso substitution A).hom.substitution =
    D.toCwf.compS
      (TypeOver.extensionSubstitution (G.base.map substitution)
        (G.mapTypeObject A).val)
      (D.toCwf.compS
        (G.substitutionIso substitution A).inv.substitution
        (TypeOver.extensionSubstitution
          (transformation.base.app ⟨Γ⟩)
          (G.mapTypeObject
            (TypeOver.reindexObject substitution A)).val)) := by
  let targetComparison :=
    (TypeOver.reindexFunctor (transformation.base.app ⟨Γ⟩)).mapIso
      (G.substitutionIso substitution A).symm
  let baseComparison :=
    transformation.baseNaturalityReindexIso substitution A
  let leftLift := TypeOver.composedExtensionSubstitution
    (transformation.base.app ⟨Δ⟩) (F.base.map substitution)
    (G.mapTypeObject A).val
  let rightLift := TypeOver.composedExtensionSubstitution
    (G.base.map substitution) (transformation.base.app ⟨Γ⟩)
    (G.mapTypeObject A).val
  let baseLift := TypeOver.extensionSubstitution
    (transformation.base.app ⟨Γ⟩)
    (G.mapTypeObject (TypeOver.reindexObject substitution A)).val
  let targetLift := TypeOver.extensionSubstitution
    (transformation.base.app ⟨Γ⟩)
    (TypeOver.reindexObject (G.base.map substitution)
      (G.mapTypeObject A)).val
  let substitutionLift := TypeOver.extensionSubstitution
    (G.base.map substitution) (G.mapTypeObject A).val
  have baseTransport :=
    transformation.baseNaturalityReindexIso_inv_composedExtensionSubstitution
      substitution A
  have comparisonNaturality := TypeOver.extensionSubstitution_naturality
    (transformation.base.app ⟨Γ⟩)
    (G.substitutionIso substitution A).inv
  change D.toCwf.compS targetLift targetComparison.hom.substitution =
      D.toCwf.compS (G.substitutionIso substitution A).inv.substitution
        baseLift
    at comparisonNaturality
  have targetExpansion :
      (transformation.historicalTargetIso substitution A).hom.substitution =
        D.toCwf.compS baseComparison.inv.substitution
          targetComparison.hom.substitution := by
    simp only [historicalTargetIso, Iso.trans_hom,
      TypeOver.Hom.comp_substitution]
    rfl
  rw [targetExpansion]
  change D.toCwf.compS leftLift
      (D.toCwf.compS baseComparison.inv.substitution
        targetComparison.hom.substitution) =
    D.toCwf.compS substitutionLift
      (D.toCwf.compS
        (G.substitutionIso substitution A).inv.substitution baseLift)
  change D.toCwf.compS leftLift baseComparison.inv.substitution = rightLift
    at baseTransport
  have rightLiftExpansion :
      rightLift = D.toCwf.compS substitutionLift targetLift := rfl
  calc
    _ = D.toCwf.compS
        (D.toCwf.compS leftLift baseComparison.inv.substitution)
        targetComparison.hom.substitution :=
      (D.toCwf.comp_assoc _ _ _).symm
    _ = D.toCwf.compS rightLift targetComparison.hom.substitution := by
      exact congrArg
        (fun outer => D.toCwf.compS outer targetComparison.hom.substitution)
        baseTransport
    _ = D.toCwf.compS
        (D.toCwf.compS substitutionLift targetLift)
        targetComparison.hom.substitution :=
      congrArg
        (fun outer => D.toCwf.compS outer targetComparison.hom.substitution)
        rightLiftExpansion
    _ = D.toCwf.compS substitutionLift
        (D.toCwf.compS targetLift targetComparison.hom.substitution) :=
      D.toCwf.comp_assoc _ _ _
    _ = D.toCwf.compS substitutionLift
        (D.toCwf.compS
          (G.substitutionIso substitution A).inv.substitution baseLift) := by
      exact congrArg
        (fun inner => D.toCwf.compS substitutionLift inner)
        comparisonNaturality

/-- The historical substitution-coherence square follows from the corrected
comprehension square.  The proof pastes the cartesian-lift preservation laws
of `F` and `G` around the corrected square, then cancels the canonical
two-stage target lift. -/
theorem substitution_coherence
    (transformation : CorrectedTransformationData F G)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    (A : TypeOver C.toCwf Δ) :
    (TypeOver.reindexFunctor (F.base.map substitution)).map
          (transformation.family Δ A) ≫
        (transformation.baseNaturalityReindexIso substitution A).hom ≫
    (TypeOver.reindexFunctor (transformation.base.app ⟨Γ⟩)).map
        (G.substitutionIso substitution A).hom =
    (F.substitutionIso substitution A).hom ≫
      transformation.family Γ (TypeOver.reindexObject substitution A) := by
  rcases A with ⟨type⟩
  let A : TypeOver C.toCwf Δ := ⟨type⟩
  let sourceAfter : TypeOver C.toCwf Γ :=
    ⟨C.toCwf.tySub A.val substitution⟩
  let sourceType := F.mapTypeObject A
  let targetType := G.mapTypeObject A
  let sourceSubstitution := F.base.map substitution
  let targetSubstitution := G.base.map substitution
  let alphaSource := transformation.base.app ⟨Γ⟩
  let alphaTarget := transformation.base.app ⟨Δ⟩
  let sourceComparison := F.substitutionIso substitution A
  let targetComparison := G.substitutionIso substitution A
  let targetComparisonInv :
      D.toCwf.Sub
        (D.toCwf.ext (G.base.obj ⟨Γ⟩).val
          (G.mapTypeObject sourceAfter).val)
        (D.toCwf.ext (G.base.obj ⟨Γ⟩).val
          (D.toCwf.tySub targetType.val targetSubstitution)) :=
    targetComparison.inv.substitution
  let baseComparison :=
    transformation.baseNaturalityReindexIso substitution A
  let targetTail := transformation.historicalTargetIso substitution A
  let reindexedFamily :=
    (TypeOver.reindexFunctor sourceSubstitution).map
      (transformation.family Δ A)
  let reindexedTargetComparison :=
    (TypeOver.reindexFunctor alphaSource).map targetComparison.hom
  let leftPath := reindexedFamily ≫ baseComparison.hom ≫
    reindexedTargetComparison
  let rightPath := sourceComparison.hom ≫
    transformation.family Γ sourceAfter
  change leftPath = rightPath
  have leftAfterTail : leftPath ≫ targetTail.hom = reindexedFamily := by
    have leftPathExpansion :
        leftPath = reindexedFamily ≫ targetTail.inv := by
      rfl
    rw [leftPathExpansion]
    calc
      (reindexedFamily ≫ targetTail.inv) ≫ targetTail.hom =
          reindexedFamily ≫ (targetTail.inv ≫ targetTail.hom) :=
        Category.assoc _ _ _
      _ = reindexedFamily ≫ 𝟙 _ :=
        congrArg (fun tail => reindexedFamily ≫ tail)
          targetTail.inv_hom_id
      _ = reindexedFamily := Category.comp_id _
  have pathsAfterTail :
      leftPath ≫ targetTail.hom = rightPath ≫ targetTail.hom := by
    apply TypeOver.composedExtensionSubstitution_cancel
      alphaTarget sourceSubstitution
    rw [leftAfterTail]
    let sourceLift := TypeOver.extensionSubstitution substitution A.val
    let sourceMappedLift := F.base.map sourceLift
    let targetMappedLift := G.base.map sourceLift
    let sourceTypeLift :
        (⟨D.toCwf.ext (F.base.obj ⟨Γ⟩).val
          (D.toCwf.tySub sourceType.val sourceSubstitution)⟩ :
            D.toCwf.base.Context) ⟶
          ⟨D.toCwf.ext (F.base.obj ⟨Δ⟩).val sourceType.val⟩ :=
      TypeOver.extensionSubstitution sourceSubstitution sourceType.val
    let reindexedTargetType := TypeOver.reindexObject alphaTarget targetType
    let reindexedFamilyTarget :=
      (TypeOver.reindexFunctor sourceSubstitution).obj reindexedTargetType
    let reindexedTargetTypeLift :
        D.toCwf.Sub
          (D.toCwf.ext (F.base.obj ⟨Γ⟩).val reindexedFamilyTarget.val)
          (D.toCwf.ext (F.base.obj ⟨Δ⟩).val reindexedTargetType.val) :=
      TypeOver.extensionSubstitution sourceSubstitution
        reindexedTargetType.val
    let alphaTargetLift :
        D.toCwf.Sub
          (D.toCwf.ext (F.base.obj ⟨Δ⟩).val reindexedTargetType.val)
          (D.toCwf.ext (G.base.obj ⟨Δ⟩).val targetType.val) :=
      TypeOver.extensionSubstitution alphaTarget targetType.val
    let alphaSourceLift := TypeOver.extensionSubstitution alphaSource
      (G.mapTypeObject sourceAfter).val
    let targetTypeLift :
        (⟨D.toCwf.ext (G.base.obj ⟨Γ⟩).val
          (D.toCwf.tySub targetType.val targetSubstitution)⟩ :
            D.toCwf.base.Context) ⟶
          ⟨D.toCwf.ext (G.base.obj ⟨Δ⟩).val targetType.val⟩ :=
      TypeOver.extensionSubstitution targetSubstitution targetType.val
    let rhoSourceTarget := F.comprehensionIso Δ A.val
    let rhoSourceSource := F.comprehensionIso Γ sourceAfter.val
    let rhoTargetTarget := G.comprehensionIso Δ A.val
    let rhoTargetSource := G.comprehensionIso Γ sourceAfter.val
    have reindexedFamilyNaturality :=
      TypeOver.extensionSubstitution_naturality sourceSubstitution
        (transformation.family Δ A)
    change D.toCwf.compS reindexedTargetTypeLift
        reindexedFamily.substitution =
      D.toCwf.compS (transformation.family Δ A).substitution
        sourceTypeLift
      at reindexedFamilyNaturality
    have targetTailLift :=
      transformation.historicalTargetIso_hom_composedExtensionSubstitution
        substitution A
    change D.toCwf.compS
        (TypeOver.composedExtensionSubstitution alphaTarget
          sourceSubstitution targetType.val)
        targetTail.hom.substitution =
      D.toCwf.compS targetTypeLift
        (D.toCwf.compS targetComparisonInv alphaSourceLift)
      at targetTailLift
    have coherenceTargetRaw :=
      transformation.comprehension_coherence Δ A
    have coherenceTargetAssociated := by
      simpa only [D.toCwf.base_comp_substitution] using
        coherenceTargetRaw
    have coherenceTarget :=
      (D.toCwf.comp_assoc alphaTargetLift
        (transformation.family Δ A).substitution
        rhoSourceTarget.hom).symm.trans coherenceTargetAssociated
    have coherenceSourceRaw :=
      transformation.comprehension_coherence Γ sourceAfter
    have coherenceSourceAssociated := by
      simpa only [D.toCwf.base_comp_substitution] using
        coherenceSourceRaw
    have coherenceSource :=
      (D.toCwf.comp_assoc alphaSourceLift
        (transformation.family Γ sourceAfter).substitution
        rhoSourceSource.hom).symm.trans coherenceSourceAssociated
    have baseNaturality := transformation.base.naturality
      (show
        (⟨C.toCwf.ext Γ sourceAfter.val⟩ : C.toCwf.base.Context) ⟶
          ⟨C.toCwf.ext Δ A.val⟩ from sourceLift)
    change D.toCwf.compS
        (transformation.base.app ⟨C.toCwf.ext Δ A.val⟩)
          sourceMappedLift =
      D.toCwf.compS targetMappedLift
        (transformation.base.app ⟨C.toCwf.ext Γ sourceAfter.val⟩)
      at baseNaturality
    have sourceLiftFactorization :
        sourceTypeLift =
          D.toCwf.compS rhoSourceTarget.hom
            (D.toCwf.compS sourceMappedLift
              (D.toCwf.compS rhoSourceSource.inv
                sourceComparison.hom.substitution)) := by
      simpa only [sourceTypeLift, sourceComparison, rhoSourceSource,
        sourceMappedLift, rhoSourceTarget, D.toCwf.base_comp_substitution,
        D.toCwf.comp_assoc] using
        F.extensionSubstitution_eq_comparison_comprehension substitution A
    have targetLiftFactorization := by
      simpa only [targetMappedLift, rhoTargetTarget, rhoTargetSource,
        targetComparison, targetTypeLift, D.toCwf.base_comp_substitution,
        D.toCwf.comp_assoc] using
        G.mapped_extensionSubstitution_comp_comprehension substitution A
    let sourcePrefix := D.toCwf.compS rhoSourceSource.inv
      sourceComparison.hom.substitution
    let sourceMappedPrefix :=
      D.toCwf.compS sourceMappedLift sourcePrefix
    let sourceBaseComponent :=
      transformation.base.app ⟨C.toCwf.ext Γ sourceAfter.val⟩
    let targetBaseComponent :=
      transformation.base.app ⟨C.toCwf.ext Δ A.val⟩
    let semanticSource : D.toCwf.base.Context :=
      ⟨D.toCwf.ext (F.base.obj ⟨Γ⟩).val
        (D.toCwf.tySub sourceType.val sourceSubstitution)⟩
    let semanticTarget : D.toCwf.base.Context :=
      ⟨D.toCwf.ext (G.base.obj ⟨Δ⟩).val targetType.val⟩
    let asSemantic
        (path : D.toCwf.Sub semanticSource.val semanticTarget.val) :
        semanticSource ⟶ semanticTarget := path
    let fromSemantic
        (path : semanticSource ⟶ semanticTarget) :
        D.toCwf.Sub semanticSource.val semanticTarget.val := path
    have targetFactorWithPrefix :
        asSemantic (D.toCwf.compS
            (D.toCwf.compS rhoTargetTarget.hom targetMappedLift)
            (D.toCwf.compS sourceBaseComponent sourcePrefix)) =
          asSemantic (D.toCwf.compS
              (D.toCwf.compS targetTypeLift
                (D.toCwf.compS targetComparisonInv
                  rhoTargetSource.hom))
              (D.toCwf.compS sourceBaseComponent sourcePrefix)) := by
      apply congrArg asSemantic
      exact congrArg
          (fun path => D.toCwf.compS path
            (D.toCwf.compS sourceBaseComponent sourcePrefix))
          targetLiftFactorization
    have semanticPasting :
        asSemantic (D.toCwf.compS alphaTargetLift
            (D.toCwf.compS (transformation.family Δ A).substitution
              sourceTypeLift)) =
            asSemantic (D.toCwf.compS targetTypeLift
              (D.toCwf.compS targetComparisonInv
                (D.toCwf.compS alphaSourceLift
                  (D.toCwf.compS
                    (transformation.family Γ sourceAfter).substitution
                    sourceComparison.hom.substitution)))) := by
      calc
        _ = asSemantic (D.toCwf.compS alphaTargetLift
            (D.toCwf.compS (transformation.family Δ A).substitution
              (D.toCwf.compS rhoSourceTarget.hom
                sourceMappedPrefix))) := by
          apply congrArg asSemantic
          exact congrArg
              (fun path => D.toCwf.compS alphaTargetLift
                (D.toCwf.compS
                  (transformation.family Δ A).substitution path))
              sourceLiftFactorization
        _ = asSemantic (D.toCwf.compS
            (D.toCwf.compS alphaTargetLift
              (D.toCwf.compS
                (transformation.family Δ A).substitution
                rhoSourceTarget.hom))
            sourceMappedPrefix) := by
          simp only [D.toCwf.comp_assoc]
        _ = asSemantic (D.toCwf.compS
            (D.toCwf.compS rhoTargetTarget.hom targetBaseComponent)
            sourceMappedPrefix) := by
          apply congrArg asSemantic
          exact congrArg
              (fun path => D.toCwf.compS path sourceMappedPrefix)
              coherenceTarget
        _ = asSemantic (D.toCwf.compS rhoTargetTarget.hom
              (D.toCwf.compS
                (D.toCwf.compS targetBaseComponent sourceMappedLift)
                sourcePrefix)) := by
          apply congrArg asSemantic
          dsimp only [sourceMappedPrefix]
          simp only [D.toCwf.comp_assoc]
          rfl
        _ = asSemantic (D.toCwf.compS rhoTargetTarget.hom
            (D.toCwf.compS
              (D.toCwf.compS targetMappedLift sourceBaseComponent)
              sourcePrefix)) := by
          apply congrArg asSemantic
          exact congrArg
              (fun path => D.toCwf.compS rhoTargetTarget.hom
                (D.toCwf.compS path sourcePrefix))
              baseNaturality
        _ = asSemantic (D.toCwf.compS
              (D.toCwf.compS rhoTargetTarget.hom targetMappedLift)
              (D.toCwf.compS sourceBaseComponent sourcePrefix)) := by
          simp only [D.toCwf.comp_assoc]
        _ = asSemantic (D.toCwf.compS
            (D.toCwf.compS targetTypeLift
              (D.toCwf.compS targetComparisonInv
                rhoTargetSource.hom))
            (D.toCwf.compS sourceBaseComponent sourcePrefix)) := by
          exact targetFactorWithPrefix
        _ = asSemantic (D.toCwf.compS targetTypeLift
            (D.toCwf.compS targetComparisonInv
              (D.toCwf.compS
                (D.toCwf.compS rhoTargetSource.hom sourceBaseComponent)
                sourcePrefix))) := by
          simp only [D.toCwf.comp_assoc]
        _ = asSemantic (D.toCwf.compS targetTypeLift
            (D.toCwf.compS targetComparisonInv
              (D.toCwf.compS
                (D.toCwf.compS alphaSourceLift
                  (D.toCwf.compS
                    (transformation.family Γ sourceAfter).substitution
                    rhoSourceSource.hom))
                sourcePrefix))) := by
          apply congrArg asSemantic
          exact congrArg
              (fun path => D.toCwf.compS targetTypeLift
                (D.toCwf.compS targetComparisonInv
                  (D.toCwf.compS path sourcePrefix)))
              coherenceSource.symm
        _ = asSemantic (D.toCwf.compS targetTypeLift
            (D.toCwf.compS targetComparisonInv
              (D.toCwf.compS alphaSourceLift
                (D.toCwf.compS
                  (transformation.family Γ sourceAfter).substitution
                  (D.toCwf.compS rhoSourceSource.hom sourcePrefix))))) := by
          simp only [D.toCwf.comp_assoc]
        _ = asSemantic (D.toCwf.compS targetTypeLift
            (D.toCwf.compS targetComparisonInv
              (D.toCwf.compS alphaSourceLift
                (D.toCwf.compS
                  (transformation.family Γ sourceAfter).substitution
                  sourceComparison.hom.substitution)))) := by
          apply congrArg asSemantic
          have rhoCancellation :
              D.toCwf.compS rhoSourceSource.hom rhoSourceSource.inv =
                D.toCwf.idS _ := by
            simpa only [D.toCwf.base_comp_substitution,
              D.toCwf.base_id_substitution] using
              rhoSourceSource.inv_hom_id
          dsimp only [sourcePrefix]
          have sourceCancellationWithPrefix :
              D.toCwf.compS rhoSourceSource.hom
                  (D.toCwf.compS rhoSourceSource.inv
                    sourceComparison.hom.substitution) =
                sourceComparison.hom.substitution := by
            calc
              _ = D.toCwf.compS
                  (D.toCwf.compS rhoSourceSource.hom
                    rhoSourceSource.inv)
                  sourceComparison.hom.substitution :=
                (D.toCwf.comp_assoc _ _ _).symm
              _ = D.toCwf.compS (D.toCwf.idS _)
                  sourceComparison.hom.substitution :=
                congrArg
                  (fun path => D.toCwf.compS path
                    sourceComparison.hom.substitution)
                  rhoCancellation
              _ = sourceComparison.hom.substitution :=
                D.toCwf.id_comp _
          exact congrArg
            (fun suffix => D.toCwf.compS targetTypeLift
              (D.toCwf.compS targetComparisonInv
                (D.toCwf.compS alphaSourceLift
                  (D.toCwf.compS
                    (transformation.family Γ sourceAfter).substitution
                    suffix))))
            sourceCancellationWithPrefix
    let composedLift := TypeOver.composedExtensionSubstitution alphaTarget
      sourceSubstitution targetType.val
    have composedLiftExpansion :
        composedLift =
          D.toCwf.compS alphaTargetLift reindexedTargetTypeLift := by
      rfl
    have rightPathExpansion :
        rightPath.substitution =
          D.toCwf.compS
            (transformation.family Γ sourceAfter).substitution
            sourceComparison.hom.substitution := by
      simp only [rightPath, TypeOver.Hom.comp_substitution]
      rfl
    change D.toCwf.compS composedLift reindexedFamily.substitution =
      D.toCwf.compS composedLift
        (rightPath ≫ targetTail.hom).substitution
    have finalSemantic :
        asSemantic (D.toCwf.compS composedLift
          reindexedFamily.substitution) =
        asSemantic (D.toCwf.compS composedLift
          (rightPath ≫ targetTail.hom).substitution) := by
      calc
        asSemantic (D.toCwf.compS composedLift
            reindexedFamily.substitution) =
            asSemantic (D.toCwf.compS alphaTargetLift
              (D.toCwf.compS reindexedTargetTypeLift
                reindexedFamily.substitution)) := by
          apply congrArg asSemantic
          rw [composedLiftExpansion]
          exact D.toCwf.comp_assoc _ _ _
        _ = asSemantic (D.toCwf.compS alphaTargetLift
            (D.toCwf.compS
              (transformation.family Δ A).substitution
              sourceTypeLift)) := by
          apply congrArg asSemantic
          exact congrArg
            (fun inner => D.toCwf.compS alphaTargetLift inner)
            reindexedFamilyNaturality
        _ = asSemantic (D.toCwf.compS targetTypeLift
            (D.toCwf.compS targetComparisonInv
              (D.toCwf.compS alphaSourceLift
                (D.toCwf.compS
                  (transformation.family Γ sourceAfter).substitution
                  sourceComparison.hom.substitution)))) := semanticPasting
        _ = asSemantic (D.toCwf.compS
            (D.toCwf.compS targetTypeLift
              (D.toCwf.compS targetComparisonInv alphaSourceLift))
            rightPath.substitution) := by
          apply congrArg asSemantic
          rw [rightPathExpansion]
          simp only [D.toCwf.comp_assoc]
          rfl
        _ = asSemantic (D.toCwf.compS
            (D.toCwf.compS composedLift targetTail.hom.substitution)
            rightPath.substitution) := by
          apply congrArg asSemantic
          exact congrArg (fun outer =>
            D.toCwf.compS outer rightPath.substitution)
            targetTailLift.symm
        _ = asSemantic (D.toCwf.compS composedLift
            (D.toCwf.compS targetTail.hom.substitution
              rightPath.substitution)) := by
          apply congrArg asSemantic
          exact D.toCwf.comp_assoc _ _ _
        _ = asSemantic (D.toCwf.compS composedLift
            (rightPath ≫ targetTail.hom).substitution) := by
          apply congrArg asSemantic
          change _ = D.toCwf.compS composedLift
            (D.toCwf.compS targetTail.hom.substitution
              rightPath.substitution)
          rfl
    exact congrArg fromSemantic finalSemantic
  exact (cancel_mono targetTail.hom).mp pathsAfterTail

/-- The corrected comprehension square determines the displayed component
uniquely.  This is the formal content of the erratum's observation that the
old independent `psi` component becomes redundant once the missing square is
required. -/
theorem family_unique
    (base : F.base ⟶ G.base)
    (Γ : C.toCwf.Ctx) (A : TypeOver C.toCwf Γ)
    (left right : F.mapTypeObject A ⟶
      TypeOver.reindexObject (base.app ⟨Γ⟩) (G.mapTypeObject A))
    (leftCoherence :
      (F.comprehensionIso Γ A.val).hom ≫
          left.substitution ≫
            TypeOver.extensionSubstitution (base.app ⟨Γ⟩)
              (G.mapType A.val) =
        base.app ⟨C.toCwf.ext Γ A.val⟩ ≫
          (G.comprehensionIso Γ A.val).hom)
    (rightCoherence :
      (F.comprehensionIso Γ A.val).hom ≫
          right.substitution ≫
            TypeOver.extensionSubstitution (base.app ⟨Γ⟩)
              (G.mapType A.val) =
        base.app ⟨C.toCwf.ext Γ A.val⟩ ≫
          (G.comprehensionIso Γ A.val).hom) :
    left = right := by
  have pathsEqual :
      (F.comprehensionIso Γ A.val).hom ≫
          left.substitution ≫
            TypeOver.extensionSubstitution (base.app ⟨Γ⟩)
              (G.mapType A.val) =
        (F.comprehensionIso Γ A.val).hom ≫
          right.substitution ≫
            TypeOver.extensionSubstitution (base.app ⟨Γ⟩)
              (G.mapType A.val) :=
    leftCoherence.trans rightCoherence.symm
  have tailsEqual := congrArg
    (fun path => (F.comprehensionIso Γ A.val).inv ≫ path)
    pathsEqual
  have liftedEqual :
      D.toCwf.compS
          (TypeOver.extensionSubstitution (base.app ⟨Γ⟩)
            (G.mapType A.val)) left.substitution =
        D.toCwf.compS
          (TypeOver.extensionSubstitution (base.app ⟨Γ⟩)
            (G.mapType A.val)) right.substitution := by
    simp only [Iso.inv_hom_id_assoc] at tailsEqual
    change
      D.toCwf.compS
          (TypeOver.extensionSubstitution (base.app ⟨Γ⟩)
            (G.mapType A.val)) left.substitution =
        D.toCwf.compS
          (TypeOver.extensionSubstitution (base.app ⟨Γ⟩)
            (G.mapType A.val)) right.substitution
      at tailsEqual
    exact tailsEqual
  exact TypeOver.extensionSubstitution_cancel (base.app ⟨Γ⟩)
    liftedEqual

/-- Any two corrected transformation-data records with the same base
component have the same displayed components pointwise. -/
theorem family_eq_of_base_eq
    (first second : CorrectedTransformationData F G)
    (baseEqual : first.base = second.base)
    (Γ : C.toCwf.Ctx) (A : TypeOver C.toCwf Γ) :
    HEq (first.family Γ A) (second.family Γ A) := by
  rcases first with ⟨firstBase, firstFamily, firstNaturality,
    firstCoherence⟩
  rcases second with ⟨secondBase, secondFamily, secondNaturality,
    secondCoherence⟩
  dsimp only at baseEqual ⊢
  subst secondBase
  exact heq_of_eq (family_unique firstBase Γ A
    (firstFamily Γ A) (secondFamily Γ A)
    (firstCoherence Γ A) (secondCoherence Γ A))

/-! ## Vertical composition -/

variable {H : PseudoCwfMorphism C D}

/-- The inverse reindexing compositor followed by the direct selected lift
is the selected two-stage lift. -/
theorem compositionObjectIso_inv_extensionSubstitution
    {Γ Δ Θ : D.toCwf.Ctx}
    (first : D.toCwf.Sub Δ Θ) (second : D.toCwf.Sub Γ Δ)
    (A : TypeOver D.toCwf Θ) :
    D.toCwf.compS
        (TypeOver.extensionSubstitution
          (D.toCwf.compS first second) A.val)
        (TypeOver.compositionObjectIso first second A).inv.substitution =
      TypeOver.composedExtensionSubstitution first second A.val := by
  let comparison := TypeOver.compositionObjectIso first second A
  let directLift := TypeOver.extensionSubstitution
    (D.toCwf.compS first second) A.val
  let stagedLift := TypeOver.composedExtensionSubstitution
    first second A.val
  have homLift := TypeOver.compositionObjectIso_hom_lift
    first second A
  have cancellation :
      D.toCwf.compS comparison.hom.substitution
          comparison.inv.substitution =
        D.toCwf.idS _ := by
    exact congrArg TypeOver.Hom.substitution comparison.inv_hom_id
  change D.toCwf.compS directLift comparison.inv.substitution = stagedLift
  change D.toCwf.compS stagedLift comparison.hom.substitution = directLift
    at homLift
  calc
    _ = D.toCwf.compS
        (D.toCwf.compS stagedLift comparison.hom.substitution)
        comparison.inv.substitution :=
      congrArg (fun outer =>
        D.toCwf.compS outer comparison.inv.substitution) homLift.symm
    _ = D.toCwf.compS stagedLift
        (D.toCwf.compS comparison.hom.substitution
          comparison.inv.substitution) := D.toCwf.comp_assoc _ _ _
    _ = D.toCwf.compS stagedLift (D.toCwf.idS _) :=
      congrArg (fun inner => D.toCwf.compS stagedLift inner)
        cancellation
    _ = stagedLift := D.toCwf.comp_id _

/-- The displayed component of a vertical composite.  The inverse
reindexing compositor is essential: two consecutive pullbacks are only
canonically isomorphic to pullback along the composite substitution. -/
def verticalFamily
    (first : CorrectedTransformationData F G)
    (second : CorrectedTransformationData G H)
    (Γ : C.toCwf.Ctx) (A : TypeOver C.toCwf Γ) :
    F.mapTypeObject A ⟶
      TypeOver.reindexObject ((first.base ≫ second.base).app ⟨Γ⟩)
        (H.mapTypeObject A) :=
  first.family Γ A ≫
    (TypeOver.reindexFunctor (first.base.app ⟨Γ⟩)).map
      (second.family Γ A) ≫
    (TypeOver.compositionObjectIso
      (second.base.app ⟨Γ⟩) (first.base.app ⟨Γ⟩)
      (H.mapTypeObject A)).inv

/-- Fibre naturality of the displayed vertical composite. -/
theorem verticalFamily_naturality
    (first : CorrectedTransformationData F G)
    (second : CorrectedTransformationData G H)
    (Γ : C.toCwf.Ctx) {A B : TypeOver C.toCwf Γ}
    (arrow : A ⟶ B) :
    (F.mapTypeFunctor Γ).map arrow ≫
        verticalFamily first second Γ B =
      verticalFamily first second Γ A ≫
        (TypeOver.reindexFunctor
          ((first.base ≫ second.base).app ⟨Γ⟩)).map
          ((H.mapTypeFunctor Γ).map arrow) := by
  let alphaPullback := TypeOver.reindexFunctor (first.base.app ⟨Γ⟩)
  let betaPullback := TypeOver.reindexFunctor (second.base.app ⟨Γ⟩)
  let compositePullback := TypeOver.reindexFunctor
    ((first.base ≫ second.base).app ⟨Γ⟩)
  let comparison := TypeOver.compositionReindexIso
    (second.base.app ⟨Γ⟩) (first.base.app ⟨Γ⟩)
  let sourceArrow := (F.mapTypeFunctor Γ).map arrow
  let middleArrow := (G.mapTypeFunctor Γ).map arrow
  let targetArrow := (H.mapTypeFunctor Γ).map arrow
  let firstA := first.family Γ A
  let firstB := first.family Γ B
  let secondA := second.family Γ A
  let secondB := second.family Γ B
  have firstNaturality :
      sourceArrow ≫ firstB =
        firstA ≫ alphaPullback.map middleArrow :=
    first.family_naturality Γ arrow
  have secondNaturality :
      middleArrow ≫ secondB =
        secondA ≫ betaPullback.map targetArrow :=
    second.family_naturality Γ arrow
  have mappedSecondNaturality :
      alphaPullback.map middleArrow ≫ alphaPullback.map secondB =
        alphaPullback.map secondA ≫
          alphaPullback.map (betaPullback.map targetArrow) := by
    calc
      _ = alphaPullback.map (middleArrow ≫ secondB) :=
        (alphaPullback.map_comp middleArrow secondB).symm
      _ = alphaPullback.map
          (secondA ≫ betaPullback.map targetArrow) :=
        congrArg alphaPullback.map secondNaturality
      _ = _ := alphaPullback.map_comp secondA
        (betaPullback.map targetArrow)
  have comparisonNaturality :
      alphaPullback.map (betaPullback.map targetArrow) ≫
          comparison.inv.app (H.mapTypeObject B) =
        comparison.inv.app (H.mapTypeObject A) ≫
          compositePullback.map targetArrow := by
    exact comparison.inv.naturality targetArrow
  let naturalitySource := F.mapTypeObject A
  let naturalityTarget := TypeOver.reindexObject
    ((first.base ≫ second.base).app ⟨Γ⟩) (H.mapTypeObject B)
  let asNaturality
      (path : naturalitySource ⟶ naturalityTarget) :
      naturalitySource ⟶ naturalityTarget := path
  change asNaturality (sourceArrow ≫
      (firstB ≫ alphaPullback.map secondB ≫
        comparison.inv.app (H.mapTypeObject B))) =
    asNaturality ((firstA ≫ alphaPullback.map secondA ≫
      comparison.inv.app (H.mapTypeObject A)) ≫
        compositePullback.map targetArrow)
  calc
    _ = asNaturality
        (((sourceArrow ≫ firstB) ≫ alphaPullback.map secondB) ≫
          comparison.inv.app (H.mapTypeObject B)) := by
      apply congrArg asNaturality
      simp only [Category.assoc]
    _ = asNaturality
        (((firstA ≫ alphaPullback.map middleArrow) ≫
          alphaPullback.map secondB) ≫
          comparison.inv.app (H.mapTypeObject B)) :=
      congrArg (fun head => asNaturality
        ((head ≫ alphaPullback.map secondB) ≫
          comparison.inv.app (H.mapTypeObject B))) firstNaturality
    _ = asNaturality
        ((firstA ≫
          (alphaPullback.map middleArrow ≫
            alphaPullback.map secondB)) ≫
          comparison.inv.app (H.mapTypeObject B)) := by
      apply congrArg asNaturality
      exact congrArg
        (fun head => head ≫ comparison.inv.app (H.mapTypeObject B))
        (Category.assoc firstA (alphaPullback.map middleArrow)
          (alphaPullback.map secondB))
    _ = asNaturality
        ((firstA ≫
          (alphaPullback.map secondA ≫
            alphaPullback.map (betaPullback.map targetArrow))) ≫
          comparison.inv.app (H.mapTypeObject B)) :=
      congrArg (fun middle => asNaturality
        ((firstA ≫ middle) ≫
          comparison.inv.app (H.mapTypeObject B)))
        mappedSecondNaturality
    _ = asNaturality
        ((firstA ≫ alphaPullback.map secondA) ≫
          (alphaPullback.map (betaPullback.map targetArrow) ≫
            comparison.inv.app (H.mapTypeObject B))) := by
      apply congrArg asNaturality
      simp only [Category.assoc]
    _ = asNaturality
        ((firstA ≫ alphaPullback.map secondA) ≫
          (comparison.inv.app (H.mapTypeObject A) ≫
            compositePullback.map targetArrow)) :=
      congrArg (fun tail => asNaturality
        ((firstA ≫ alphaPullback.map secondA) ≫ tail))
        comparisonNaturality
    _ = asNaturality
        (((firstA ≫ alphaPullback.map secondA) ≫
          comparison.inv.app (H.mapTypeObject A)) ≫
          compositePullback.map targetArrow) := by
      apply congrArg asNaturality
      simp only [Category.assoc]
    _ = asNaturality
        ((firstA ≫ (alphaPullback.map secondA ≫
          comparison.inv.app (H.mapTypeObject A))) ≫
          compositePullback.map targetArrow) := by
      apply congrArg asNaturality
      exact congrArg
        (fun head => head ≫ compositePullback.map targetArrow)
        (Category.assoc firstA (alphaPullback.map secondA)
          (comparison.inv.app (H.mapTypeObject A)))

/-- The displayed vertical composite satisfies the corrected comprehension
square by pasting the two input squares around pullback naturality. -/
theorem verticalFamily_comprehension_coherence
    (first : CorrectedTransformationData F G)
    (second : CorrectedTransformationData G H)
    (Γ : C.toCwf.Ctx) (A : TypeOver C.toCwf Γ) :
    (F.comprehensionIso Γ A.val).hom ≫
        (verticalFamily first second Γ A).substitution ≫
          TypeOver.extensionSubstitution
            ((first.base ≫ second.base).app ⟨Γ⟩)
            (H.mapType A.val) =
      (first.base ≫ second.base).app
          ⟨C.toCwf.ext Γ A.val⟩ ≫
        (H.comprehensionIso Γ A.val).hom := by
  rcases A with ⟨type⟩
  let A : TypeOver C.toCwf Γ := ⟨type⟩
  let alpha := first.base.app ⟨Γ⟩
  let beta := second.base.app ⟨Γ⟩
  let alphaExtended := first.base.app ⟨C.toCwf.ext Γ A.val⟩
  let betaExtended := second.base.app ⟨C.toCwf.ext Γ A.val⟩
  let mappedG := G.mapTypeObject A
  let mappedH := H.mapTypeObject A
  have mappedHCarrier : H.mapType A.val = mappedH.val :=
    H.mapType_val A
  cases mappedHCarrier
  let betaTarget := TypeOver.reindexObject beta mappedH
  let firstComponent := first.family Γ A
  let secondComponent := second.family Γ A
  let pulledSecond :=
    (TypeOver.reindexFunctor alpha).map secondComponent
  let comparison := TypeOver.compositionObjectIso beta alpha mappedH
  let rhoF := F.comprehensionIso Γ A.val
  let rhoG := G.comprehensionIso Γ A.val
  let rhoH := H.comprehensionIso Γ A.val
  let directLift := TypeOver.extensionSubstitution
    ((first.base ≫ second.base).app ⟨Γ⟩) (H.mapType A.val)
  let alphaMiddleLift := TypeOver.extensionSubstitution alpha mappedG.val
  let alphaTargetLift := TypeOver.extensionSubstitution alpha betaTarget.val
  let betaLift := TypeOver.extensionSubstitution beta mappedH.val
  let stagedLift := TypeOver.composedExtensionSubstitution
    beta alpha mappedH.val
  let compositeExtended :=
    (first.base ≫ second.base).app ⟨C.toCwf.ext Γ A.val⟩
  let verticalSubstitution := (verticalFamily first second Γ A).substitution
  have verticalExpansion :
      verticalSubstitution =
        D.toCwf.compS comparison.inv.substitution
          (D.toCwf.compS pulledSecond.substitution
            firstComponent.substitution) := by
    simp only [verticalSubstitution, verticalFamily,
      TypeOver.Hom.comp_substitution]
    exact D.toCwf.comp_assoc _ _ _
  have comparisonLift :
      D.toCwf.compS directLift comparison.inv.substitution =
        stagedLift := by
    dsimp only [directLift, stagedLift, comparison]
    change D.toCwf.compS
        (TypeOver.extensionSubstitution
          (D.toCwf.compS beta alpha) mappedH.val)
        (TypeOver.compositionObjectIso beta alpha mappedH).inv.substitution =
      TypeOver.composedExtensionSubstitution beta alpha mappedH.val
    exact compositionObjectIso_inv_extensionSubstitution beta alpha mappedH
  have stagedExpansion :
      stagedLift = D.toCwf.compS betaLift alphaTargetLift := by
    rfl
  have pulledNaturality :=
    TypeOver.extensionSubstitution_naturality alpha secondComponent
  change D.toCwf.compS alphaTargetLift pulledSecond.substitution =
      D.toCwf.compS secondComponent.substitution alphaMiddleLift
    at pulledNaturality
  have firstCoherenceRaw := first.comprehension_coherence Γ A
  have firstCoherenceAssociated := by
    simpa only [D.toCwf.base_comp_substitution] using firstCoherenceRaw
  have firstCoherence :
      D.toCwf.compS alphaMiddleLift
          (D.toCwf.compS firstComponent.substitution rhoF.hom) =
        D.toCwf.compS rhoG.hom alphaExtended :=
    (D.toCwf.comp_assoc alphaMiddleLift
      firstComponent.substitution rhoF.hom).symm.trans
        firstCoherenceAssociated
  have secondCoherenceRaw := second.comprehension_coherence Γ A
  have secondCoherenceAssociated := by
    simpa only [D.toCwf.base_comp_substitution] using secondCoherenceRaw
  have secondCoherence :
      D.toCwf.compS betaLift
          (D.toCwf.compS secondComponent.substitution rhoG.hom) =
        D.toCwf.compS rhoH.hom betaExtended :=
    (D.toCwf.comp_assoc betaLift
      secondComponent.substitution rhoG.hom).symm.trans
        secondCoherenceAssociated
  let semanticSource : D.toCwf.base.Context :=
    F.base.obj ⟨C.toCwf.ext Γ A.val⟩
  let semanticTarget : D.toCwf.base.Context :=
    ⟨D.toCwf.ext (H.base.obj ⟨Γ⟩).val mappedH.val⟩
  let asSemantic
      (path : semanticSource ⟶ semanticTarget) :
      semanticSource ⟶ semanticTarget := path
  change asSemantic (D.toCwf.compS
      (D.toCwf.compS directLift verticalSubstitution) rhoF.hom) =
    asSemantic (D.toCwf.compS rhoH.hom
      compositeExtended)
  calc
    _ = asSemantic (D.toCwf.compS directLift
        (D.toCwf.compS verticalSubstitution rhoF.hom)) := by
      apply congrArg asSemantic
      exact D.toCwf.comp_assoc _ _ _
    _ = asSemantic (D.toCwf.compS directLift
        (D.toCwf.compS
          (D.toCwf.compS comparison.inv.substitution
            (D.toCwf.compS pulledSecond.substitution
              firstComponent.substitution)) rhoF.hom)) := by
      apply congrArg asSemantic
      exact congrArg
        (fun middle => D.toCwf.compS directLift
          (D.toCwf.compS middle rhoF.hom)) verticalExpansion
    _ = asSemantic (D.toCwf.compS
        (D.toCwf.compS directLift comparison.inv.substitution)
        (D.toCwf.compS pulledSecond.substitution
          (D.toCwf.compS firstComponent.substitution rhoF.hom))) := by
      apply congrArg asSemantic
      simp only [D.toCwf.comp_assoc]
    _ = asSemantic (D.toCwf.compS stagedLift
        (D.toCwf.compS pulledSecond.substitution
          (D.toCwf.compS firstComponent.substitution rhoF.hom))) :=
      congrArg (fun outer => asSemantic
        (D.toCwf.compS outer
          (D.toCwf.compS pulledSecond.substitution
            (D.toCwf.compS firstComponent.substitution rhoF.hom))))
        comparisonLift
    _ = asSemantic (D.toCwf.compS
        (D.toCwf.compS betaLift alphaTargetLift)
        (D.toCwf.compS pulledSecond.substitution
          (D.toCwf.compS firstComponent.substitution rhoF.hom))) :=
      congrArg (fun outer => asSemantic
        (D.toCwf.compS outer
          (D.toCwf.compS pulledSecond.substitution
            (D.toCwf.compS firstComponent.substitution rhoF.hom))))
        stagedExpansion
    _ = asSemantic (D.toCwf.compS betaLift
        (D.toCwf.compS
          (D.toCwf.compS alphaTargetLift pulledSecond.substitution)
          (D.toCwf.compS firstComponent.substitution rhoF.hom))) := by
      apply congrArg asSemantic
      simp only [D.toCwf.comp_assoc]
    _ = asSemantic (D.toCwf.compS betaLift
        (D.toCwf.compS
          (D.toCwf.compS secondComponent.substitution alphaMiddleLift)
          (D.toCwf.compS firstComponent.substitution rhoF.hom))) :=
      congrArg (fun middle => asSemantic
        (D.toCwf.compS betaLift
          (D.toCwf.compS middle
            (D.toCwf.compS firstComponent.substitution rhoF.hom))))
        pulledNaturality
    _ = asSemantic (D.toCwf.compS betaLift
        (D.toCwf.compS secondComponent.substitution
          (D.toCwf.compS alphaMiddleLift
            (D.toCwf.compS firstComponent.substitution rhoF.hom)))) := by
      apply congrArg asSemantic
      simp only [D.toCwf.comp_assoc]
    _ = asSemantic (D.toCwf.compS betaLift
        (D.toCwf.compS secondComponent.substitution
          (D.toCwf.compS rhoG.hom alphaExtended))) :=
      congrArg (fun middle => asSemantic
        (D.toCwf.compS betaLift
          (D.toCwf.compS secondComponent.substitution middle)))
        firstCoherence
    _ = asSemantic (D.toCwf.compS
        (D.toCwf.compS betaLift
          (D.toCwf.compS secondComponent.substitution rhoG.hom))
        alphaExtended) := by
      apply congrArg asSemantic
      simp only [D.toCwf.comp_assoc]
    _ = asSemantic (D.toCwf.compS
        (D.toCwf.compS rhoH.hom betaExtended) alphaExtended) :=
      congrArg (fun outer => asSemantic
        (D.toCwf.compS outer alphaExtended)) secondCoherence
    _ = asSemantic (D.toCwf.compS rhoH.hom
        (D.toCwf.compS betaExtended alphaExtended)) := by
      apply congrArg asSemantic
      exact D.toCwf.comp_assoc _ _ _
    _ = asSemantic (D.toCwf.compS rhoH.hom compositeExtended) := by
      apply congrArg asSemantic
      rfl

/-- Vertical composition of corrected pseudo-CwF transformations. -/
def vertical
    (first : CorrectedTransformationData F G)
    (second : CorrectedTransformationData G H) :
    CorrectedTransformationData F H where
  base := first.base ≫ second.base
  family := verticalFamily first second
  family_naturality := verticalFamily_naturality first second
  comprehension_coherence :=
    verticalFamily_comprehension_coherence first second

/-- Identity corrected transformation data.  Its fibre component is the
inverse of the canonical identity-reindexing comparison because displayed
components point from the untranslated object into its reindexing. -/
def identity (F : PseudoCwfMorphism C D) :
    CorrectedTransformationData F F where
  base := 𝟙 F.base
  family := fun Γ A =>
    (TypeOver.identityObjectIso (F.mapTypeObject A)).inv
  family_naturality := by
    intro Γ A B arrow
    exact (TypeOver.identityReindexIso
      (F.base.obj ⟨Γ⟩).val).inv.naturality
        ((F.mapTypeFunctor Γ).map arrow)
  comprehension_coherence := by
    intro Γ A
    let mappedType := F.mapTypeObject A
    let identityComparison := TypeOver.identityObjectIso mappedType
    have inverseThenHom :
        identityComparison.inv.substitution ≫
            identityComparison.hom.substitution =
          𝟙
            (⟨D.toCwf.ext (F.base.obj ⟨Γ⟩).val mappedType.val⟩ :
              D.toCwf.base.Context) := by
      exact congrArg TypeOver.Hom.substitution
        identityComparison.inv_hom_id
    have liftIsHom :
        TypeOver.extensionSubstitution
            (D.toCwf.idS (F.base.obj ⟨Γ⟩).val) mappedType.val =
          identityComparison.hom.substitution :=
      (TypeOver.identityObjectIso_hom_substitution mappedType).symm
    change
      (F.comprehensionIso Γ A.val).hom ≫
          identityComparison.inv.substitution ≫
            TypeOver.extensionSubstitution
              (D.toCwf.idS (F.base.obj ⟨Γ⟩).val) mappedType.val =
        𝟙 (F.base.obj ⟨C.toCwf.ext Γ A.val⟩) ≫
          (F.comprehensionIso Γ A.val).hom
    calc
      _ = (F.comprehensionIso Γ A.val).hom ≫
          (identityComparison.inv.substitution ≫
            identityComparison.hom.substitution) := by rw [liftIsHom]
      _ = (F.comprehensionIso Γ A.val).hom ≫ 𝟙 _ :=
        congrArg
          (fun tail => (F.comprehensionIso Γ A.val).hom ≫ tail)
          inverseThenHom
      _ = (F.comprehensionIso Γ A.val).hom := Category.comp_id _
      _ = 𝟙 _ ≫ (F.comprehensionIso Γ A.val).hom :=
        (Category.id_comp _).symm

/-- Corrected transformations are determined by their base natural
transformation.  Fibre components are forced by comprehension coherence;
the remaining fields are propositions. -/
@[ext]
theorem ext_of_base_eq
    (first second : CorrectedTransformationData F G)
    (baseEqual : first.base = second.base) : first = second := by
  rcases first with
    ⟨firstBase, firstFamily, firstNaturality, firstCoherence⟩
  rcases second with
    ⟨secondBase, secondFamily, secondNaturality, secondCoherence⟩
  dsimp only at baseEqual
  subst secondBase
  have familyEqual : firstFamily = secondFamily := by
    funext Γ A
    exact family_unique firstBase Γ A
      (firstFamily Γ A) (secondFamily Γ A)
      (firstCoherence Γ A) (secondCoherence Γ A)
  subst secondFamily
  rfl

/-- Left identity for vertical composition. -/
@[simp]
theorem identity_vertical
    (transformation : CorrectedTransformationData F G) :
    vertical (identity F) transformation = transformation :=
  ext_of_base_eq _ _ (Category.id_comp transformation.base)

/-- Right identity for vertical composition. -/
@[simp]
theorem vertical_identity
    (transformation : CorrectedTransformationData F G) :
    vertical transformation (identity G) = transformation :=
  ext_of_base_eq _ _ (Category.comp_id transformation.base)

/-- Associativity of vertical composition. -/
theorem vertical_assoc
    {I : PseudoCwfMorphism C D}
    (first : CorrectedTransformationData F G)
    (second : CorrectedTransformationData G H)
    (third : CorrectedTransformationData H I) :
    vertical (vertical first second) third =
      vertical first (vertical second third) :=
  ext_of_base_eq _ _ (Category.assoc first.base second.base third.base)

/-- For fixed source and target CwFs, pseudo CwF morphisms and corrected
transformations form a category. -/
instance pseudoCwfMorphismCategory :
    Category (PseudoCwfMorphism C D) where
  Hom := CorrectedTransformationData
  id := identity
  comp := vertical
  id_comp := identity_vertical
  comp_id := vertical_identity
  assoc := vertical_assoc

/-- Forget a corrected pseudo-CwF transformation down to its natural
transformation on base categories.  The comprehension square makes this
forgetful functor faithful: the displayed component carries no independent
choice once the base transformation is fixed. -/
def baseForgetfulFunctor :
    PseudoCwfMorphism C D ⥤
      (C.toCwf.base.Context ⥤ D.toCwf.base.Context) where
  obj morphism := morphism.base
  map transformation := transformation.base
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Corrected pseudo-CwF transformations are faithfully represented by their
base natural transformations.  This deliberately does not claim fullness:
an arbitrary base transformation need not satisfy the displayed
comprehension condition needed to lift it. -/
instance baseForgetfulFunctor_faithful :
    (baseForgetfulFunctor (C := C) (D := D)).Faithful where
  map_injective equality := ext_of_base_eq _ _ equality

/-! ## Positive and negative controls -/

/-- The identity corrected transformation uses the canonical cartesian
identity comparison in every fibre. -/
@[simp]
theorem identity_family
    (F : PseudoCwfMorphism C D)
    (Γ : C.toCwf.Ctx) (A : TypeOver C.toCwf Γ) :
    (identity F).family Γ A =
      (TypeOver.identityObjectIso (F.mapTypeObject A)).inv := rfl

/-- A Boolean-negating displayed component cannot masquerade as the identity
2-cell.  Although it has the correct source and target, it violates the
corrected comprehension square. -/
theorem families_negation_not_identity_comprehension_coherent :
    let model := familiesCwfWithTerminal.{0}
    let morphism := PseudoCwfMorphism.identity model
    let base : morphism.base ⟶ morphism.base := 𝟙 morphism.base
    let A : TypeOver model.toCwf PUnit := TypeOver.unitBoolType
    let comparison := TypeOver.identityObjectIso
      (morphism.mapTypeObject A)
    let candidate : morphism.mapTypeObject A ⟶
        TypeOver.reindexObject (base.app ⟨PUnit⟩)
          (morphism.mapTypeObject A) :=
      (morphism.mapTypeFunctor PUnit).map TypeOver.boolNegationDisplay ≫
        comparison.inv
    ¬ ((morphism.comprehensionIso PUnit A.val).hom ≫
          candidate.substitution ≫
            TypeOver.extensionSubstitution (base.app ⟨PUnit⟩)
              (morphism.mapType A.val) =
        base.app ⟨model.toCwf.ext PUnit A.val⟩ ≫
          (morphism.comprehensionIso PUnit A.val).hom) := by
  dsimp only
  intro candidateCoherence
  let model := familiesCwfWithTerminal.{0}
  let morphism := PseudoCwfMorphism.identity model
  let base : morphism.base ⟶ morphism.base := 𝟙 morphism.base
  let A : TypeOver model.toCwf PUnit := TypeOver.unitBoolType
  let comparison := TypeOver.identityObjectIso
    (morphism.mapTypeObject A)
  let candidate : morphism.mapTypeObject A ⟶
      TypeOver.reindexObject (base.app ⟨PUnit⟩)
        (morphism.mapTypeObject A) :=
    (morphism.mapTypeFunctor PUnit).map TypeOver.boolNegationDisplay ≫
      comparison.inv
  have canonicalCoherence :=
    (identity morphism).comprehension_coherence PUnit A
  have candidateIsCanonical : candidate = comparison.inv :=
    family_unique base PUnit A candidate comparison.inv
      candidateCoherence canonicalCoherence
  have afterComparison := congrArg
    (fun arrow => arrow ≫ comparison.hom) candidateIsCanonical
  have negationIsIdentity :
      (morphism.mapTypeFunctor PUnit).map TypeOver.boolNegationDisplay =
        𝟙 (morphism.mapTypeObject A) := by
    let negation :=
      (morphism.mapTypeFunctor PUnit).map TypeOver.boolNegationDisplay
    change negation = 𝟙 (morphism.mapTypeObject A)
    change
      (negation ≫ comparison.inv) ≫ comparison.hom =
        comparison.inv ≫ comparison.hom
      at afterComparison
    have prefixEquality :
        negation = (negation ≫ comparison.inv) ≫ comparison.hom := by
      calc
        negation = negation ≫ 𝟙 _ := (Category.comp_id _).symm
        _ = negation ≫ (comparison.inv ≫ comparison.hom) :=
          congrArg (fun tail => negation ≫ tail)
            comparison.inv_hom_id.symm
        _ = (negation ≫ comparison.inv) ≫ comparison.hom :=
          (Category.assoc _ _ _).symm
    have suffixEquality :
        (negation ≫ comparison.inv) ≫ comparison.hom =
          𝟙 (morphism.mapTypeObject A) :=
      afterComparison.trans comparison.inv_hom_id
    exact prefixEquality.trans suffixEquality
  exact TypeOver.boolNegationDisplay_ne_identity negationIsIdentity

#print axioms CorrectedTransformationData.baseNaturalityReindexIso
#print axioms
  CorrectedTransformationData.baseNaturalityReindexIso_hom_composedExtensionSubstitution
#print axioms
  CorrectedTransformationData.baseNaturalityReindexIso_inv_composedExtensionSubstitution
#print axioms CorrectedTransformationData.historicalTargetIso
#print axioms
  CorrectedTransformationData.historicalTargetIso_hom_composedExtensionSubstitution
#print axioms CorrectedTransformationData.substitution_coherence
#print axioms
  CorrectedTransformationData.compositionObjectIso_inv_extensionSubstitution
#print axioms CorrectedTransformationData.verticalFamily
#print axioms CorrectedTransformationData.verticalFamily_naturality
#print axioms
  CorrectedTransformationData.verticalFamily_comprehension_coherence
#print axioms CorrectedTransformationData.vertical
#print axioms CorrectedTransformationData.family_unique
#print axioms CorrectedTransformationData.family_eq_of_base_eq
#print axioms CorrectedTransformationData.identity
#print axioms CorrectedTransformationData.ext_of_base_eq
#print axioms CorrectedTransformationData.identity_vertical
#print axioms CorrectedTransformationData.vertical_identity
#print axioms CorrectedTransformationData.vertical_assoc
#print axioms CorrectedTransformationData.pseudoCwfMorphismCategory
#print axioms CorrectedTransformationData.identity_family
#print axioms
  CorrectedTransformationData.families_negation_not_identity_comprehension_coherent

end CorrectedTransformationData

end Mettapedia.GSLT.Core.ContextualLadder
