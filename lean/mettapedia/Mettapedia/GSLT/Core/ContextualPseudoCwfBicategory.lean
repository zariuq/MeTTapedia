import Mettapedia.GSLT.Core.ContextualPseudoCwfTransformation
import Mathlib.CategoryTheory.Products.Basic

/-!
# Horizontal composition for corrected pseudo-CwF transformations

This module continues the bicategorical organization of categories with
families.  The hom categories and vertical composition live in
`ContextualPseudoCwfTransformation`; here we derive whiskering from the
actual substitution and comprehension comparisons of pseudo CwF morphisms.

The constructions are deliberately asymmetric.  Right whiskering must use
the outer pseudo morphism's substitution comparison, whereas left
whiskering is pointwise on the already translated type.  Their composite is
the genuine horizontal composite.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ContextualLadder

open CategoryTheory

universe u v w w'

namespace PseudoCwfMorphism

variable {C D E : CwfWithTerminal.{u, v, w, w'}}

/-- The base functor of pseudo-morphism composition is ordinary functor
composition.  Naming this projection prevents later coherence proofs from
unfolding the entire pseudo-morphism record. -/
@[simp]
theorem comp_base
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E) :
    (first.comp second).base = first.base ⋙ second.base := rfl

/-- The substitution comparison bundled as a natural isomorphism between
the two fibre functors. -/
def substitutionNatIso
    (morphism : PseudoCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ) :
    morphism.mapTypeFunctor Δ ⋙
        TypeOver.reindexFunctor (morphism.base.map substitution) ≅
      TypeOver.reindexFunctor substitution ⋙
        morphism.mapTypeFunctor Γ :=
  NatIso.ofComponents
    (fun A => morphism.substitutionIso substitution A)
    (fun arrow => morphism.substitutionIso_naturality substitution arrow)

/-- Inverse naturality for the substitution comparison.  This is the form
needed when a displayed transformation is mapped through a pseudo CwF
morphism and then transported back to the selected reindexed type. -/
theorem substitutionIso_inv_naturality
    (morphism : PseudoCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    {A B : TypeOver C.toCwf Δ} (arrow : A ⟶ B) :
    (morphism.mapTypeFunctor Γ).map
          ((TypeOver.reindexFunctor substitution).map arrow) ≫
        (morphism.substitutionIso substitution B).inv =
      (morphism.substitutionIso substitution A).inv ≫
        (TypeOver.reindexFunctor
          (morphism.base.map substitution)).map
            ((morphism.mapTypeFunctor Δ).map arrow) := by
  exact (morphism.substitutionNatIso substitution).inv.naturality arrow

end PseudoCwfMorphism

namespace CorrectedTransformationData

variable {C D E : CwfWithTerminal.{u, v, w, w'}}
variable {F G : PseudoCwfMorphism C D}
variable {H I : PseudoCwfMorphism D E}

/-- The displayed component of right whiskering.  Mapping the original
component lands in the translation of a reindexed type; the inverse
substitution comparison identifies that object with the selected reindexing
of the translated type. -/
def rightWhiskerFamily
    (transformation : CorrectedTransformationData F G)
    (outer : PseudoCwfMorphism D E)
    (Γ : C.toCwf.Ctx) (A : TypeOver C.toCwf Γ) :
    (F.comp outer).mapTypeObject A ⟶
      TypeOver.reindexObject
        ((Functor.whiskerRight transformation.base outer.base).app ⟨Γ⟩)
        ((G.comp outer).mapTypeObject A) :=
  (outer.mapTypeFunctor (F.base.obj ⟨Γ⟩).val).map
      (transformation.family Γ A) ≫
    (outer.substitutionIso (transformation.base.app ⟨Γ⟩)
      (G.mapTypeObject A)).inv

set_option backward.isDefEq.respectTransparency false in
/-- Right whiskering preserves naturality in display maps. -/
theorem rightWhiskerFamily_naturality
    (transformation : CorrectedTransformationData F G)
    (outer : PseudoCwfMorphism D E)
    (Γ : C.toCwf.Ctx) {A B : TypeOver C.toCwf Γ}
    (arrow : A ⟶ B) :
    ((F.comp outer).mapTypeFunctor Γ).map arrow ≫
        rightWhiskerFamily transformation outer Γ B =
      rightWhiskerFamily transformation outer Γ A ≫
        (TypeOver.reindexFunctor
          ((Functor.whiskerRight transformation.base outer.base).app
            ⟨Γ⟩)).map
          (((G.comp outer).mapTypeFunctor Γ).map arrow) := by
  rcases A with ⟨A⟩
  rcases B with ⟨B⟩
  let outerF := outer.mapTypeFunctor (F.base.obj ⟨Γ⟩).val
  let outerG := outer.mapTypeFunctor (G.base.obj ⟨Γ⟩).val
  have mappedNaturality := congrArg outerF.map
    (transformation.family_naturality Γ arrow)
  have inverseNaturality := outer.substitutionIso_inv_naturality
    (transformation.base.app ⟨Γ⟩)
    ((G.mapTypeFunctor Γ).map arrow)
  dsimp only [PseudoCwfMorphism.mapTypeObject] at mappedNaturality inverseNaturality
  dsimp only [PseudoCwfMorphism.mapTypeObject]
  change
    outerF.map ((F.mapTypeFunctor Γ).map arrow) ≫
        (outerF.map (transformation.family Γ
            (⟨B⟩ : TypeOver C.toCwf Γ)) ≫
          (outer.substitutionIso (transformation.base.app ⟨Γ⟩)
            ((G.mapTypeFunctor Γ).obj
              (⟨B⟩ : TypeOver C.toCwf Γ))).inv) =
      (outerF.map (transformation.family Γ
          (⟨A⟩ : TypeOver C.toCwf Γ)) ≫
          (outer.substitutionIso (transformation.base.app ⟨Γ⟩)
            ((G.mapTypeFunctor Γ).obj
              (⟨A⟩ : TypeOver C.toCwf Γ))).inv) ≫
        (TypeOver.reindexFunctor
          (outer.base.map (transformation.base.app ⟨Γ⟩))).map
            (outerG.map ((G.mapTypeFunctor Γ).map arrow))
  rw [← Category.assoc, ← outerF.map_comp, mappedNaturality,
    outerF.map_comp, Category.assoc, inverseNaturality,
    ← Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Right whiskering preserves the corrected comprehension square. -/
theorem rightWhiskerFamily_comprehension_coherence
    (transformation : CorrectedTransformationData F G)
    (outer : PseudoCwfMorphism D E)
    (Γ : C.toCwf.Ctx) (A : TypeOver C.toCwf Γ) :
    ((F.comp outer).comprehensionIso Γ A.val).hom ≫
        (rightWhiskerFamily transformation outer Γ A).substitution ≫
          TypeOver.extensionSubstitution
            ((Functor.whiskerRight transformation.base outer.base).app
              ⟨Γ⟩)
            ((G.comp outer).mapType A.val) =
      (Functor.whiskerRight transformation.base outer.base).app
          ⟨C.toCwf.ext Γ A.val⟩ ≫
        ((G.comp outer).comprehensionIso Γ A.val).hom := by
  let alpha := transformation.base
  let alphaΓ := alpha.app ⟨Γ⟩
  let alphaExtended := alpha.app ⟨C.toCwf.ext Γ A.val⟩
  let mappedA := F.mapTypeObject A
  let mappedG := G.mapTypeObject A
  let reindexedG := TypeOver.reindexObject alphaΓ mappedG
  let mappedFamily :=
    (outer.mapTypeFunctor (F.base.obj ⟨Γ⟩).val).map
      (transformation.family Γ A)
  let rhoF := F.comprehensionIso Γ A.val
  let rhoG := G.comprehensionIso Γ A.val
  let rhoOuterF := outer.comprehensionIso
    (F.base.obj ⟨Γ⟩).val mappedA.val
  let rhoOuterReindexed := outer.comprehensionIso
    (F.base.obj ⟨Γ⟩).val reindexedG.val
  let rhoOuterG := outer.comprehensionIso
    (G.base.obj ⟨Γ⟩).val mappedG.val
  let comparison := outer.substitutionIso alphaΓ mappedG
  let sourceLift := TypeOver.extensionSubstitution alphaΓ mappedG.val
  let targetLift := TypeOver.extensionSubstitution
    (outer.base.map alphaΓ) (outer.mapTypeObject mappedG).val
  cases (F.mapType_val A).symm
  cases (G.mapType_val A).symm
  have mappedDisplay := outer.display_preserved
    (F.base.obj ⟨Γ⟩).val mappedA reindexedG
      (transformation.family Γ A)
  have outerLift := outer.mapped_extensionSubstitution_comp_comprehension
    alphaΓ mappedG
  have sourceCoherence := transformation.comprehension_coherence Γ A
  change
      rhoF.hom ≫ (transformation.family Γ A).substitution ≫ sourceLift =
        alphaExtended ≫ rhoG.hom at sourceCoherence
  change
    (outer.base.map rhoF.hom ≫ rhoOuterF.hom) ≫
        (mappedFamily ≫ comparison.inv).substitution ≫ targetLift =
      outer.base.map alphaExtended ≫
        (outer.base.map rhoG.hom ≫ rhoOuterG.hom)
  change mappedFamily.substitution =
      rhoOuterF.inv ≫
        outer.base.map (transformation.family Γ A).substitution ≫
          rhoOuterReindexed.hom at mappedDisplay
  change outer.base.map sourceLift ≫ rhoOuterG.hom =
      rhoOuterReindexed.hom ≫ comparison.inv.substitution ≫ targetLift
    at outerLift
  have familySubstitutionRaw :
      (mappedFamily ≫ comparison.inv).substitution =
        E.toCwf.compS comparison.inv.substitution
          mappedFamily.substitution := rfl
  have mappedDisplayRaw :
      mappedFamily.substitution =
        E.toCwf.compS
          (E.toCwf.compS rhoOuterReindexed.hom
            (outer.base.map (transformation.family Γ A).substitution))
          rhoOuterF.inv := by
    simpa only [E.toCwf.base_comp_substitution] using mappedDisplay
  have outerLiftRaw := outerLift
  change E.toCwf.compS rhoOuterG.hom (outer.base.map sourceLift) =
      E.toCwf.compS
        (E.toCwf.compS targetLift comparison.inv.substitution)
        rhoOuterReindexed.hom at outerLiftRaw
  have mappedSourceExpanded := congrArg outer.base.map sourceCoherence
  simp only [outer.base.map_comp] at mappedSourceExpanded
  have mappedSourceCoherenceRaw :
      E.toCwf.compS
          (E.toCwf.compS (outer.base.map sourceLift)
            (outer.base.map (transformation.family Γ A).substitution))
          (outer.base.map rhoF.hom) =
        E.toCwf.compS (outer.base.map rhoG.hom)
          (outer.base.map alphaExtended) := by
    simpa only [E.toCwf.base_comp_substitution, sourceLift]
      using mappedSourceExpanded
  have rhoOuterFCancellation :
      E.toCwf.compS rhoOuterF.inv rhoOuterF.hom = E.toCwf.idS _ := by
    simpa only [E.toCwf.base_comp_substitution,
      E.toCwf.base_id_substitution] using rhoOuterF.hom_inv_id
  have rawCoherence :
      E.toCwf.compS targetLift
          (E.toCwf.compS
            (mappedFamily ≫ comparison.inv).substitution
            (E.toCwf.compS rhoOuterF.hom
              (outer.base.map rhoF.hom))) =
        E.toCwf.compS rhoOuterG.hom
          (E.toCwf.compS (outer.base.map rhoG.hom)
            (outer.base.map alphaExtended)) := by
    calc
      _ = E.toCwf.compS targetLift
          (E.toCwf.compS
            (E.toCwf.compS comparison.inv.substitution
              mappedFamily.substitution)
            (E.toCwf.compS rhoOuterF.hom
              (outer.base.map rhoF.hom))) :=
        congrArg (fun middle =>
          E.toCwf.compS targetLift
            (E.toCwf.compS middle
              (E.toCwf.compS rhoOuterF.hom
                (outer.base.map rhoF.hom)))) familySubstitutionRaw
      _ = E.toCwf.compS targetLift
          (E.toCwf.compS comparison.inv.substitution
            (E.toCwf.compS mappedFamily.substitution
              (E.toCwf.compS rhoOuterF.hom
                (outer.base.map rhoF.hom)))) := by
        simp only [E.toCwf.comp_assoc]
      _ = E.toCwf.compS targetLift
          (E.toCwf.compS comparison.inv.substitution
            (E.toCwf.compS
              (E.toCwf.compS
                (E.toCwf.compS rhoOuterReindexed.hom
                  (outer.base.map
                    (transformation.family Γ A).substitution))
                rhoOuterF.inv)
              (E.toCwf.compS rhoOuterF.hom
                (outer.base.map rhoF.hom)))) :=
        congrArg (fun mapped =>
          E.toCwf.compS targetLift
            (E.toCwf.compS comparison.inv.substitution
              (E.toCwf.compS mapped
                (E.toCwf.compS rhoOuterF.hom
                  (outer.base.map rhoF.hom))))) mappedDisplayRaw
      _ = E.toCwf.compS targetLift
          (E.toCwf.compS comparison.inv.substitution
            (E.toCwf.compS rhoOuterReindexed.hom
              (E.toCwf.compS
                (outer.base.map
                  (transformation.family Γ A).substitution)
                (E.toCwf.compS rhoOuterF.inv
                  (E.toCwf.compS rhoOuterF.hom
                    (outer.base.map rhoF.hom)))))) := by
        simp only [E.toCwf.comp_assoc]
      _ = E.toCwf.compS targetLift
          (E.toCwf.compS comparison.inv.substitution
            (E.toCwf.compS rhoOuterReindexed.hom
              (E.toCwf.compS
                (outer.base.map
                  (transformation.family Γ A).substitution)
                (outer.base.map rhoF.hom)))) := by
        rw [← E.toCwf.comp_assoc rhoOuterF.inv rhoOuterF.hom,
          rhoOuterFCancellation, E.toCwf.id_comp]
      _ = E.toCwf.compS
          (E.toCwf.compS
            (E.toCwf.compS targetLift comparison.inv.substitution)
            rhoOuterReindexed.hom)
          (E.toCwf.compS
            (outer.base.map (transformation.family Γ A).substitution)
            (outer.base.map rhoF.hom)) := by
        simp only [E.toCwf.comp_assoc]
      _ = E.toCwf.compS
          (E.toCwf.compS rhoOuterG.hom
            (outer.base.map sourceLift))
          (E.toCwf.compS
            (outer.base.map (transformation.family Γ A).substitution)
            (outer.base.map rhoF.hom)) :=
        congrArg (fun outerPath =>
          E.toCwf.compS outerPath
            (E.toCwf.compS
              (outer.base.map (transformation.family Γ A).substitution)
              (outer.base.map rhoF.hom))) outerLiftRaw.symm
      _ = E.toCwf.compS rhoOuterG.hom
          (E.toCwf.compS
            (E.toCwf.compS (outer.base.map sourceLift)
              (outer.base.map (transformation.family Γ A).substitution))
            (outer.base.map rhoF.hom)) := by
        simp only [E.toCwf.comp_assoc]
      _ = E.toCwf.compS rhoOuterG.hom
          (E.toCwf.compS (outer.base.map rhoG.hom)
            (outer.base.map alphaExtended)) :=
        congrArg (fun inner => E.toCwf.compS rhoOuterG.hom inner)
          mappedSourceCoherenceRaw
  simpa only [E.toCwf.base_comp_substitution,
    E.toCwf.comp_assoc] using rawCoherence

/-- Right whiskering of a corrected transformation by a pseudo CwF
morphism. -/
def rightWhisker
    (transformation : CorrectedTransformationData F G)
    (outer : PseudoCwfMorphism D E) :
    CorrectedTransformationData (F.comp outer) (G.comp outer) where
  base := Functor.whiskerRight transformation.base outer.base
  family := rightWhiskerFamily transformation outer
  family_naturality := rightWhiskerFamily_naturality transformation outer
  comprehension_coherence :=
    rightWhiskerFamily_comprehension_coherence transformation outer

/-- The displayed component of left whiskering.  Since the transformation
already lives in the outer hom category, it is evaluated directly at the
inner morphism's translated context and type. -/
def leftWhiskerFamily
    (inner : PseudoCwfMorphism C D)
    (transformation : CorrectedTransformationData H I)
    (Γ : C.toCwf.Ctx) (A : TypeOver C.toCwf Γ) :
    (inner.comp H).mapTypeObject A ⟶
      TypeOver.reindexObject
        ((Functor.whiskerLeft inner.base transformation.base).app ⟨Γ⟩)
        ((inner.comp I).mapTypeObject A) :=
  transformation.family (inner.base.obj ⟨Γ⟩).val
    (inner.mapTypeObject A)

set_option backward.isDefEq.respectTransparency false in
/-- Left whiskering preserves naturality in display maps. -/
theorem leftWhiskerFamily_naturality
    (inner : PseudoCwfMorphism C D)
    (transformation : CorrectedTransformationData H I)
    (Γ : C.toCwf.Ctx) {A B : TypeOver C.toCwf Γ}
    (arrow : A ⟶ B) :
    ((inner.comp H).mapTypeFunctor Γ).map arrow ≫
        leftWhiskerFamily inner transformation Γ B =
      leftWhiskerFamily inner transformation Γ A ≫
        (TypeOver.reindexFunctor
          ((Functor.whiskerLeft inner.base transformation.base).app
            ⟨Γ⟩)).map
          (((inner.comp I).mapTypeFunctor Γ).map arrow) := by
  exact transformation.family_naturality
    (inner.base.obj ⟨Γ⟩).val
    ((inner.mapTypeFunctor Γ).map arrow)

set_option backward.isDefEq.respectTransparency false in
/-- Left whiskering preserves the corrected comprehension square. -/
theorem leftWhiskerFamily_comprehension_coherence
    (inner : PseudoCwfMorphism C D)
    (transformation : CorrectedTransformationData H I)
    (Γ : C.toCwf.Ctx) (A : TypeOver C.toCwf Γ) :
    ((inner.comp H).comprehensionIso Γ A.val).hom ≫
        (leftWhiskerFamily inner transformation Γ A).substitution ≫
          TypeOver.extensionSubstitution
            ((Functor.whiskerLeft inner.base transformation.base).app
              ⟨Γ⟩)
            ((inner.comp I).mapType A.val) =
      (Functor.whiskerLeft inner.base transformation.base).app
          ⟨C.toCwf.ext Γ A.val⟩ ≫
        ((inner.comp I).comprehensionIso Γ A.val).hom := by
  let mappedA := inner.mapTypeObject A
  let rhoInner := inner.comprehensionIso Γ A.val
  let rhoH := H.comprehensionIso
    (inner.base.obj ⟨Γ⟩).val mappedA.val
  let rhoI := I.comprehensionIso
    (inner.base.obj ⟨Γ⟩).val mappedA.val
  let betaContext := transformation.base.app (inner.base.obj ⟨Γ⟩)
  let betaDisplay := transformation.base.app
    ⟨D.toCwf.ext (inner.base.obj ⟨Γ⟩).val mappedA.val⟩
  let betaExtended := transformation.base.app
    (inner.base.obj ⟨C.toCwf.ext Γ A.val⟩)
  let betaFamily := transformation.family
    (inner.base.obj ⟨Γ⟩).val mappedA
  let betaLift := TypeOver.extensionSubstitution betaContext
    (I.mapTypeObject mappedA).val
  have betaCoherence := transformation.comprehension_coherence
    (inner.base.obj ⟨Γ⟩).val mappedA
  have betaNaturality := transformation.base.naturality rhoInner.hom
  change
    (H.base.map rhoInner.hom ≫ rhoH.hom) ≫
        betaFamily.substitution ≫ betaLift =
      betaExtended ≫ (I.base.map rhoInner.hom ≫ rhoI.hom)
  change rhoH.hom ≫ betaFamily.substitution ≫ betaLift =
      betaDisplay ≫ rhoI.hom at betaCoherence
  change H.base.map rhoInner.hom ≫ betaDisplay =
      betaExtended ≫ I.base.map rhoInner.hom at betaNaturality
  calc
    _ = H.base.map rhoInner.hom ≫
        (rhoH.hom ≫ betaFamily.substitution ≫ betaLift) := by
      simp only [Category.assoc]
    _ = H.base.map rhoInner.hom ≫ (betaDisplay ≫ rhoI.hom) :=
      congrArg (fun tail => H.base.map rhoInner.hom ≫ tail)
        betaCoherence
    _ = (H.base.map rhoInner.hom ≫ betaDisplay) ≫ rhoI.hom :=
      (Category.assoc _ _ _).symm
    _ = (betaExtended ≫ I.base.map rhoInner.hom) ≫ rhoI.hom :=
      congrArg (fun head => head ≫ rhoI.hom) betaNaturality
    _ = _ := Category.assoc _ _ _

/-- Left whiskering of a corrected transformation by a pseudo CwF
morphism. -/
def leftWhisker
    (inner : PseudoCwfMorphism C D)
    (transformation : CorrectedTransformationData H I) :
    CorrectedTransformationData (inner.comp H) (inner.comp I) where
  base := Functor.whiskerLeft inner.base transformation.base
  family := leftWhiskerFamily inner transformation
  family_naturality := leftWhiskerFamily_naturality inner transformation
  comprehension_coherence :=
    leftWhiskerFamily_comprehension_coherence inner transformation

/-- Horizontal composition is the canonical pasting of right and left
whiskering. -/
def horizontal
    (first : CorrectedTransformationData F G)
    (second : CorrectedTransformationData H I) :
    CorrectedTransformationData (F.comp H) (G.comp I) :=
  vertical (rightWhisker first H) (leftWhisker G second)

@[simp]
theorem horizontal_base
    (first : CorrectedTransformationData F G)
    (second : CorrectedTransformationData H I) :
    (horizontal first second).base =
      Functor.whiskerRight first.base H.base ≫
        Functor.whiskerLeft G.base second.base := rfl

/-! ## Functoriality of horizontal composition -/

@[simp]
theorem rightWhisker_identity
    (morphism : PseudoCwfMorphism C D)
    (outer : PseudoCwfMorphism D E) :
    rightWhisker (identity morphism) outer =
      identity (morphism.comp outer) :=
  ext_of_base_eq _ _ (Functor.whiskerRight_id' outer.base)

@[simp]
theorem leftWhisker_identity
    (inner : PseudoCwfMorphism C D)
    (morphism : PseudoCwfMorphism D E) :
    leftWhisker inner (identity morphism) =
      identity (inner.comp morphism) :=
  ext_of_base_eq _ _ (Functor.whiskerLeft_id' inner.base)

theorem rightWhisker_vertical
    {J : PseudoCwfMorphism C D}
    (first : CorrectedTransformationData F G)
    (second : CorrectedTransformationData G J)
    (outer : PseudoCwfMorphism D E) :
    rightWhisker (vertical first second) outer =
      vertical (rightWhisker first outer)
        (rightWhisker second outer) :=
  ext_of_base_eq _ _
    (Functor.whiskerRight_comp first.base second.base outer.base)

theorem leftWhisker_vertical
    {J : PseudoCwfMorphism D E}
    (inner : PseudoCwfMorphism C D)
    (first : CorrectedTransformationData H I)
    (second : CorrectedTransformationData I J) :
    leftWhisker inner (vertical first second) =
      vertical (leftWhisker inner first)
        (leftWhisker inner second) :=
  ext_of_base_eq _ _
    (Functor.whiskerLeft_comp inner.base first.base second.base)

/-- The two possible whiskering orders agree.  This is the middle-four
interchange square from which horizontal composition is independent of the
chosen pasting order. -/
theorem whiskering_interchange
    (first : CorrectedTransformationData F G)
    (second : CorrectedTransformationData H I) :
    vertical (leftWhisker F second) (rightWhisker first I) =
      vertical (rightWhisker first H) (leftWhisker G second) :=
  ext_of_base_eq _ _
    (Functor.whiskerLeft_comp_whiskerRight first.base second.base)

/-- Horizontal composition can equivalently be pasted left-then-right. -/
theorem horizontal_eq_alternate
    (first : CorrectedTransformationData F G)
    (second : CorrectedTransformationData H I) :
    horizontal first second =
      vertical (leftWhisker F second) (rightWhisker first I) :=
  (whiskering_interchange first second).symm

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem horizontal_identity
    (inner : PseudoCwfMorphism C D)
    (outer : PseudoCwfMorphism D E) :
    horizontal (identity inner) (identity outer) =
      identity (inner.comp outer) := by
  apply ext_of_base_eq
  change Functor.whiskerRight (𝟙 inner.base) outer.base ≫
      Functor.whiskerLeft inner.base (𝟙 outer.base) =
    𝟙 (inner.base ⋙ outer.base)
  simp only [Functor.whiskerRight_id', Functor.whiskerLeft_id',
    Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Horizontal composition respects vertical composition in both inputs. -/
theorem horizontal_vertical
    {J : PseudoCwfMorphism C D}
    {K : PseudoCwfMorphism D E}
    (first₁ : CorrectedTransformationData F G)
    (first₂ : CorrectedTransformationData G J)
    (second₁ : CorrectedTransformationData H I)
    (second₂ : CorrectedTransformationData I K) :
    horizontal (vertical first₁ first₂) (vertical second₁ second₂) =
      vertical (horizontal first₁ second₁)
        (horizontal first₂ second₂) := by
  apply ext_of_base_eq
  change
    Functor.whiskerRight (first₁.base ≫ first₂.base) H.base ≫
        Functor.whiskerLeft J.base (second₁.base ≫ second₂.base) =
      (Functor.whiskerRight first₁.base H.base ≫
          Functor.whiskerLeft G.base second₁.base) ≫
        (Functor.whiskerRight first₂.base I.base ≫
          Functor.whiskerLeft J.base second₂.base)
  rw [Functor.whiskerRight_comp, Functor.whiskerLeft_comp]
  have middle :=
    (Functor.whiskerLeft_comp_whiskerRight
      first₂.base second₁.base).symm
  simpa only [Category.assoc] using congrArg
    (fun path => Functor.whiskerRight first₁.base H.base ≫
      path ≫ Functor.whiskerLeft J.base second₂.base)
    middle

/-- Composition of pseudo CwF morphisms is a bifunctor on the corrected hom
categories. -/
def horizontalCompositionFunctor :
    (PseudoCwfMorphism C D × PseudoCwfMorphism D E) ⥤
      PseudoCwfMorphism C E where
  obj pair := pair.1.comp pair.2
  map pair := horizontal pair.1 pair.2
  map_id pair := horizontal_identity pair.1 pair.2
  map_comp first second :=
    horizontal_vertical first.1 second.1 first.2 second.2

/-! ## Structural comparison laws -/

set_option backward.isDefEq.respectTransparency false in
/-- The selected comprehension comparison of a left-unital composite is the
original comparison. -/
theorem leftUnit_comprehensionIso_hom
    (morphism : PseudoCwfMorphism C D)
    (Γ : C.toCwf.Ctx) (A : C.toCwf.Ty Γ) :
    (((PseudoCwfMorphism.identity C).comp morphism).comprehensionIso
      Γ A).hom = (morphism.comprehensionIso Γ A).hom := by
  simp [PseudoCwfMorphism.comp,
    PseudoCwfMorphism.compositeComprehensionIso,
    PseudoCwfMorphism.identity_comprehensionIso_hom,
    PseudoCwfMorphism.identity_mapType]
  simp [PseudoCwfMorphism.identity]
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
/-- The selected comprehension comparison of a right-unital composite is
the original comparison. -/
theorem rightUnit_comprehensionIso_hom
    (morphism : PseudoCwfMorphism C D)
    (Γ : C.toCwf.Ctx) (A : C.toCwf.Ty Γ) :
    ((morphism.comp (PseudoCwfMorphism.identity D)).comprehensionIso
      Γ A).hom = (morphism.comprehensionIso Γ A).hom := by
  simp [PseudoCwfMorphism.comp,
    PseudoCwfMorphism.compositeComprehensionIso,
    PseudoCwfMorphism.identity_comprehensionIso_hom]
  simp [PseudoCwfMorphism.identity]
  exact Category.comp_id _

variable {K : CwfWithTerminal.{u, v, w, w'}}

set_option backward.isDefEq.respectTransparency false in
/-- Reassociating three pseudo morphisms does not change the selected
comprehension path. -/
theorem associator_comprehensionIso_hom
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E)
    (third : PseudoCwfMorphism E K)
    (Γ : C.toCwf.Ctx) (A : C.toCwf.Ty Γ) :
    ((((first.comp second).comp third).comprehensionIso Γ A).hom) =
      ((first.comp (second.comp third)).comprehensionIso Γ A).hom := by
  simp [PseudoCwfMorphism.comp,
    PseudoCwfMorphism.compositeComprehensionIso]
  rfl

/-! ## Unitors and associator -/

set_option backward.isDefEq.respectTransparency false in
/-- Left unitor for pseudo CwF morphisms.  Its base and fibre components are
the ordinary functor unitors, while the corrected square is discharged by
the selected-comprehension comparison law above. -/
def leftUnitor
    (morphism : PseudoCwfMorphism C D) :
    CorrectedTransformationData
      ((PseudoCwfMorphism.identity C).comp morphism) morphism where
  base := (Functor.leftUnitor morphism.base).hom
  family := fun Γ A =>
    (TypeOver.identityObjectIso (morphism.mapTypeObject A)).inv
  family_naturality := by
    intro Γ A B arrow
    exact (TypeOver.identityReindexIso
      (morphism.base.obj ⟨Γ⟩).val).inv.naturality
        ((morphism.mapTypeFunctor Γ).map arrow)
  comprehension_coherence := by
    intro Γ A
    let mappedType := morphism.mapTypeObject A
    let comparison := TypeOver.identityObjectIso mappedType
    have inverseThenHom :
        comparison.inv.substitution ≫ comparison.hom.substitution =
          𝟙
            (⟨D.toCwf.ext (morphism.base.obj ⟨Γ⟩).val
              mappedType.val⟩ : D.toCwf.base.Context) :=
      congrArg TypeOver.Hom.substitution comparison.inv_hom_id
    have liftIsHom :
        TypeOver.extensionSubstitution
            (D.toCwf.idS (morphism.base.obj ⟨Γ⟩).val)
            mappedType.val = comparison.hom.substitution :=
      (TypeOver.identityObjectIso_hom_substitution mappedType).symm
    rw [leftUnit_comprehensionIso_hom]
    change
      (morphism.comprehensionIso Γ A.val).hom ≫
          comparison.inv.substitution ≫
            TypeOver.extensionSubstitution
              (D.toCwf.idS (morphism.base.obj ⟨Γ⟩).val)
              mappedType.val =
        𝟙 _ ≫ (morphism.comprehensionIso Γ A.val).hom
    rw [liftIsHom]
    calc
      _ = (morphism.comprehensionIso Γ A.val).hom ≫
          (comparison.inv.substitution ≫
            comparison.hom.substitution) := rfl
      _ = (morphism.comprehensionIso Γ A.val).hom ≫ 𝟙 _ :=
        congrArg
          (fun tail => (morphism.comprehensionIso Γ A.val).hom ≫ tail)
          inverseThenHom
      _ = _ := by simp

set_option backward.isDefEq.respectTransparency false in
/-- Inverse left unitor for pseudo CwF morphisms. -/
def leftUnitorInv
    (morphism : PseudoCwfMorphism C D) :
    CorrectedTransformationData morphism
      ((PseudoCwfMorphism.identity C).comp morphism) where
  base := (Functor.leftUnitor morphism.base).inv
  family := fun Γ A =>
    (TypeOver.identityObjectIso (morphism.mapTypeObject A)).inv
  family_naturality := by
    intro Γ A B arrow
    exact (TypeOver.identityReindexIso
      (morphism.base.obj ⟨Γ⟩).val).inv.naturality
        ((morphism.mapTypeFunctor Γ).map arrow)
  comprehension_coherence := by
    intro Γ A
    let mappedType := morphism.mapTypeObject A
    let comparison := TypeOver.identityObjectIso mappedType
    have inverseThenHom :
        comparison.inv.substitution ≫ comparison.hom.substitution =
          𝟙
            (⟨D.toCwf.ext (morphism.base.obj ⟨Γ⟩).val
              mappedType.val⟩ : D.toCwf.base.Context) :=
      congrArg TypeOver.Hom.substitution comparison.inv_hom_id
    have liftIsHom :
        TypeOver.extensionSubstitution
            (D.toCwf.idS (morphism.base.obj ⟨Γ⟩).val)
            mappedType.val = comparison.hom.substitution :=
      (TypeOver.identityObjectIso_hom_substitution mappedType).symm
    rw [leftUnit_comprehensionIso_hom]
    change
      (morphism.comprehensionIso Γ A.val).hom ≫
          comparison.inv.substitution ≫
            TypeOver.extensionSubstitution
              (D.toCwf.idS (morphism.base.obj ⟨Γ⟩).val)
              mappedType.val =
        𝟙 _ ≫ (morphism.comprehensionIso Γ A.val).hom
    rw [liftIsHom]
    calc
      _ = (morphism.comprehensionIso Γ A.val).hom ≫
          (comparison.inv.substitution ≫
            comparison.hom.substitution) := rfl
      _ = (morphism.comprehensionIso Γ A.val).hom ≫ 𝟙 _ :=
        congrArg
          (fun tail => (morphism.comprehensionIso Γ A.val).hom ≫ tail)
          inverseThenHom
      _ = _ := by simp

set_option backward.isDefEq.respectTransparency false in
/-- Right unitor for pseudo CwF morphisms. -/
def rightUnitor
    (morphism : PseudoCwfMorphism C D) :
    CorrectedTransformationData
      (morphism.comp (PseudoCwfMorphism.identity D)) morphism where
  base := (Functor.rightUnitor morphism.base).hom
  family := fun Γ A =>
    (TypeOver.identityObjectIso (morphism.mapTypeObject A)).inv
  family_naturality := by
    intro Γ A B arrow
    exact (TypeOver.identityReindexIso
      (morphism.base.obj ⟨Γ⟩).val).inv.naturality
        ((morphism.mapTypeFunctor Γ).map arrow)
  comprehension_coherence := by
    intro Γ A
    let mappedType := morphism.mapTypeObject A
    let comparison := TypeOver.identityObjectIso mappedType
    have inverseThenHom :
        comparison.inv.substitution ≫ comparison.hom.substitution =
          𝟙
            (⟨D.toCwf.ext (morphism.base.obj ⟨Γ⟩).val
              mappedType.val⟩ : D.toCwf.base.Context) :=
      congrArg TypeOver.Hom.substitution comparison.inv_hom_id
    have liftIsHom :
        TypeOver.extensionSubstitution
            (D.toCwf.idS (morphism.base.obj ⟨Γ⟩).val)
            mappedType.val = comparison.hom.substitution :=
      (TypeOver.identityObjectIso_hom_substitution mappedType).symm
    rw [rightUnit_comprehensionIso_hom]
    change
      (morphism.comprehensionIso Γ A.val).hom ≫
          comparison.inv.substitution ≫
            TypeOver.extensionSubstitution
              (D.toCwf.idS (morphism.base.obj ⟨Γ⟩).val)
              mappedType.val =
        𝟙 _ ≫ (morphism.comprehensionIso Γ A.val).hom
    rw [liftIsHom]
    calc
      _ = (morphism.comprehensionIso Γ A.val).hom ≫
          (comparison.inv.substitution ≫
            comparison.hom.substitution) := rfl
      _ = (morphism.comprehensionIso Γ A.val).hom ≫ 𝟙 _ :=
        congrArg
          (fun tail => (morphism.comprehensionIso Γ A.val).hom ≫ tail)
          inverseThenHom
      _ = _ := by simp

set_option backward.isDefEq.respectTransparency false in
/-- Inverse right unitor for pseudo CwF morphisms. -/
def rightUnitorInv
    (morphism : PseudoCwfMorphism C D) :
    CorrectedTransformationData morphism
      (morphism.comp (PseudoCwfMorphism.identity D)) where
  base := (Functor.rightUnitor morphism.base).inv
  family := fun Γ A =>
    (TypeOver.identityObjectIso (morphism.mapTypeObject A)).inv
  family_naturality := by
    intro Γ A B arrow
    exact (TypeOver.identityReindexIso
      (morphism.base.obj ⟨Γ⟩).val).inv.naturality
        ((morphism.mapTypeFunctor Γ).map arrow)
  comprehension_coherence := by
    intro Γ A
    let mappedType := morphism.mapTypeObject A
    let comparison := TypeOver.identityObjectIso mappedType
    have inverseThenHom :
        comparison.inv.substitution ≫ comparison.hom.substitution =
          𝟙
            (⟨D.toCwf.ext (morphism.base.obj ⟨Γ⟩).val
              mappedType.val⟩ : D.toCwf.base.Context) :=
      congrArg TypeOver.Hom.substitution comparison.inv_hom_id
    have liftIsHom :
        TypeOver.extensionSubstitution
            (D.toCwf.idS (morphism.base.obj ⟨Γ⟩).val)
            mappedType.val = comparison.hom.substitution :=
      (TypeOver.identityObjectIso_hom_substitution mappedType).symm
    rw [rightUnit_comprehensionIso_hom]
    change
      (morphism.comprehensionIso Γ A.val).hom ≫
          comparison.inv.substitution ≫
            TypeOver.extensionSubstitution
              (D.toCwf.idS (morphism.base.obj ⟨Γ⟩).val)
              mappedType.val =
        𝟙 _ ≫ (morphism.comprehensionIso Γ A.val).hom
    rw [liftIsHom]
    calc
      _ = (morphism.comprehensionIso Γ A.val).hom ≫
          (comparison.inv.substitution ≫
            comparison.hom.substitution) := rfl
      _ = (morphism.comprehensionIso Γ A.val).hom ≫ 𝟙 _ :=
        congrArg
          (fun tail => (morphism.comprehensionIso Γ A.val).hom ≫ tail)
          inverseThenHom
      _ = _ := by simp

set_option backward.isDefEq.respectTransparency false in
/-- Associator for pseudo CwF morphisms.  The pointwise functor associator is
identity on objects and arrows in this concrete presentation; the theorem
`associator_comprehensionIso_hom` supplies its nontrivial structural
coherence. -/
def associator
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E)
    (third : PseudoCwfMorphism E K) :
    CorrectedTransformationData
      ((first.comp second).comp third)
      (first.comp (second.comp third)) where
  base := (Functor.associator first.base second.base third.base).hom
  family := fun Γ A =>
    (TypeOver.identityObjectIso
      (third.mapTypeObject
        (second.mapTypeObject (first.mapTypeObject A)))).inv
  family_naturality := by
    intro Γ A B arrow
    exact (TypeOver.identityReindexIso
      (third.base.obj
        (second.base.obj (first.base.obj ⟨Γ⟩))).val).inv.naturality
          (((first.comp (second.comp third)).mapTypeFunctor Γ).map arrow)
  comprehension_coherence := by
    intro Γ A
    let mappedType :=
      (first.comp (second.comp third)).mapTypeObject A
    let comparison := TypeOver.identityObjectIso mappedType
    have inverseThenHom :
        comparison.inv.substitution ≫ comparison.hom.substitution =
          𝟙
            (⟨K.toCwf.ext
              (third.base.obj
                (second.base.obj (first.base.obj ⟨Γ⟩))).val
              mappedType.val⟩ : K.toCwf.base.Context) :=
      congrArg TypeOver.Hom.substitution comparison.inv_hom_id
    have liftIsHom :
        TypeOver.extensionSubstitution
            (K.toCwf.idS
              (third.base.obj
                (second.base.obj (first.base.obj ⟨Γ⟩))).val)
            mappedType.val = comparison.hom.substitution :=
      (TypeOver.identityObjectIso_hom_substitution mappedType).symm
    rw [associator_comprehensionIso_hom]
    change
      ((first.comp (second.comp third)).comprehensionIso Γ A.val).hom ≫
          comparison.inv.substitution ≫
            TypeOver.extensionSubstitution
              (K.toCwf.idS
                (third.base.obj
                  (second.base.obj (first.base.obj ⟨Γ⟩))).val)
              mappedType.val =
        𝟙 _ ≫
          ((first.comp (second.comp third)).comprehensionIso Γ A.val).hom
    rw [liftIsHom]
    calc
      _ = ((first.comp (second.comp third)).comprehensionIso
            Γ A.val).hom ≫
          (comparison.inv.substitution ≫
            comparison.hom.substitution) := rfl
      _ = ((first.comp (second.comp third)).comprehensionIso
            Γ A.val).hom ≫ 𝟙 _ :=
        congrArg
          (fun tail =>
            ((first.comp (second.comp third)).comprehensionIso
              Γ A.val).hom ≫ tail)
          inverseThenHom
      _ = _ := by simp

set_option backward.isDefEq.respectTransparency false in
/-- Fibre component of the inverse associator. -/
def associatorInvFamily
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E)
    (third : PseudoCwfMorphism E K)
    (Γ : C.toCwf.Ctx) (A : TypeOver C.toCwf Γ) :
    (first.comp (second.comp third)).mapTypeObject A ⟶
      TypeOver.reindexObject
        ((Functor.associator first.base second.base third.base).inv.app ⟨Γ⟩)
        (((first.comp second).comp third).mapTypeObject A) :=
  (TypeOver.identityObjectIso
    (third.mapTypeObject
      (second.mapTypeObject (first.mapTypeObject A)))).inv

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the inverse associator's fibre component. -/
theorem associatorInvFamily_naturality
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E)
    (third : PseudoCwfMorphism E K)
    (Γ : C.toCwf.Ctx) {A B : TypeOver C.toCwf Γ}
    (arrow : A ⟶ B) :
    ((first.comp (second.comp third)).mapTypeFunctor Γ).map arrow ≫
        associatorInvFamily first second third Γ B =
      associatorInvFamily first second third Γ A ≫
        (TypeOver.reindexFunctor
          ((Functor.associator first.base second.base third.base).inv.app
            ⟨Γ⟩)).map
          ((((first.comp second).comp third).mapTypeFunctor Γ).map
            arrow) := by
  exact (TypeOver.identityReindexIso
      (third.base.obj
        (second.base.obj (first.base.obj ⟨Γ⟩))).val).inv.naturality
      (((first.comp (second.comp third)).mapTypeFunctor Γ).map arrow)

/-- The inverse associator's fibre component satisfies the corrected
comprehension square. -/
theorem associatorInvFamily_comprehension_coherence
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E)
    (third : PseudoCwfMorphism E K)
    (Γ : C.toCwf.Ctx) (A : TypeOver C.toCwf Γ) :
    ((first.comp (second.comp third)).comprehensionIso Γ A.val).hom ≫
        (associatorInvFamily first second third Γ A).substitution ≫
          TypeOver.extensionSubstitution
            ((Functor.associator first.base second.base third.base).inv.app
              ⟨Γ⟩)
            (((first.comp second).comp third).mapType A.val) =
      (Functor.associator first.base second.base third.base).inv.app
          ⟨C.toCwf.ext Γ A.val⟩ ≫
        (((first.comp second).comp third).comprehensionIso Γ A.val).hom := by
  let mappedType :=
    ((first.comp second).comp third).mapTypeObject A
  let comparison := TypeOver.identityObjectIso mappedType
  have inverseThenHom :
      comparison.inv.substitution ≫ comparison.hom.substitution =
        𝟙
          (⟨K.toCwf.ext
            (third.base.obj
              (second.base.obj (first.base.obj ⟨Γ⟩))).val
            mappedType.val⟩ : K.toCwf.base.Context) :=
    congrArg TypeOver.Hom.substitution comparison.inv_hom_id
  have liftIsHom :
      TypeOver.extensionSubstitution
          (K.toCwf.idS
            (third.base.obj
              (second.base.obj (first.base.obj ⟨Γ⟩))).val)
          mappedType.val = comparison.hom.substitution :=
    (TypeOver.identityObjectIso_hom_substitution mappedType).symm
  rw [← associator_comprehensionIso_hom]
  change
    (((first.comp second).comp third).comprehensionIso Γ A.val).hom ≫
        comparison.inv.substitution ≫
          TypeOver.extensionSubstitution
            (K.toCwf.idS
              (third.base.obj
                (second.base.obj (first.base.obj ⟨Γ⟩))).val)
            mappedType.val =
      𝟙 _ ≫
        (((first.comp second).comp third).comprehensionIso Γ A.val).hom
  rw [liftIsHom]
  calc
    _ = (((first.comp second).comp third).comprehensionIso
          Γ A.val).hom ≫
        (comparison.inv.substitution ≫
          comparison.hom.substitution) := rfl
    _ = (((first.comp second).comp third).comprehensionIso
          Γ A.val).hom ≫ 𝟙 _ :=
      congrArg
        (fun tail =>
          (((first.comp second).comp third).comprehensionIso
            Γ A.val).hom ≫ tail)
        inverseThenHom
    _ = _ := by simp

/-- Inverse associator for pseudo CwF morphisms. -/
def associatorInv
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E)
    (third : PseudoCwfMorphism E K) :
    CorrectedTransformationData
      (first.comp (second.comp third))
      ((first.comp second).comp third) where
  base := (Functor.associator first.base second.base third.base).inv
  family := associatorInvFamily first second third
  family_naturality := associatorInvFamily_naturality first second third
  comprehension_coherence :=
    associatorInvFamily_comprehension_coherence first second third

/-! ## Structural 2-isomorphisms -/

/-- Left unitor as an isomorphism in the corrected hom category. -/
def leftUnitorIso
    (morphism : PseudoCwfMorphism C D) :
    ((PseudoCwfMorphism.identity C).comp morphism) ≅ morphism where
  hom := leftUnitor morphism
  inv := leftUnitorInv morphism
  hom_inv_id :=
    ext_of_base_eq _ _ (Functor.leftUnitor morphism.base).hom_inv_id
  inv_hom_id :=
    ext_of_base_eq _ _ (Functor.leftUnitor morphism.base).inv_hom_id

/-- Right unitor as an isomorphism in the corrected hom category. -/
def rightUnitorIso
    (morphism : PseudoCwfMorphism C D) :
    (morphism.comp (PseudoCwfMorphism.identity D)) ≅ morphism where
  hom := rightUnitor morphism
  inv := rightUnitorInv morphism
  hom_inv_id :=
    ext_of_base_eq _ _ (Functor.rightUnitor morphism.base).hom_inv_id
  inv_hom_id :=
    ext_of_base_eq _ _ (Functor.rightUnitor morphism.base).inv_hom_id

/-- Associator as an isomorphism in the corrected hom category. -/
def associatorIso
    (first : PseudoCwfMorphism C D)
    (second : PseudoCwfMorphism D E)
    (third : PseudoCwfMorphism E K) :
    ((first.comp second).comp third) ≅
      (first.comp (second.comp third)) where
  hom := associator first second third
  inv := associatorInv first second third
  hom_inv_id :=
    ext_of_base_eq _ _
      (Functor.associator first.base second.base third.base).hom_inv_id
  inv_hom_id :=
    ext_of_base_eq _ _
      (Functor.associator first.base second.base third.base).inv_hom_id

end CorrectedTransformationData

/-! ## The bicategorical object layer -/

/-- Categories with families with selected terminal context, pseudo CwF
morphisms, and their ordinary composition form the object and 1-cell layer
of the bicategory. -/
instance pseudoCwfCategoryStruct :
    CategoryStruct (CwfWithTerminal.{u, v, w, w'}) where
  Hom := PseudoCwfMorphism
  id := PseudoCwfMorphism.identity
  comp := PseudoCwfMorphism.comp

/-- The corrected pseudo-CwF organization is a bicategory.  Every 2-cell
coherence law is reflected faithfully to the corresponding law for the
underlying context functors; the corrected comprehension square then forces
the displayed component. -/
instance pseudoCwfBicategory :
    Bicategory (CwfWithTerminal.{u, v, w, w'}) where
  homCategory := fun _ _ =>
    CorrectedTransformationData.pseudoCwfMorphismCategory
  whiskerLeft := fun {_ _ _} first {_ _} transformation =>
    CorrectedTransformationData.leftWhisker first transformation
  whiskerRight := fun {_ _ _} {_ _} transformation outer =>
    CorrectedTransformationData.rightWhisker transformation outer
  associator := fun first second third =>
    CorrectedTransformationData.associatorIso first second third
  leftUnitor := fun morphism =>
    CorrectedTransformationData.leftUnitorIso morphism
  rightUnitor := fun morphism =>
    CorrectedTransformationData.rightUnitorIso morphism
  whiskerLeft_id := by
    intro C D E first second
    apply CorrectedTransformationData.ext_of_base_eq
    exact congrArg Cat.Hom₂.toNatTrans
      (Bicategory.whiskerLeft_id (B := Cat)
        first.base.toCatHom second.base.toCatHom)
  whiskerLeft_comp := by
    intro C D E first F G H alpha beta
    apply CorrectedTransformationData.ext_of_base_eq
    exact congrArg Cat.Hom₂.toNatTrans
      (Bicategory.whiskerLeft_comp (B := Cat)
        first.base.toCatHom alpha.base.toCatHom₂ beta.base.toCatHom₂)
  id_whiskerLeft := by
    intro C D F G transformation
    apply CorrectedTransformationData.ext_of_base_eq
    exact congrArg Cat.Hom₂.toNatTrans
      (Bicategory.id_whiskerLeft (B := Cat)
        transformation.base.toCatHom₂)
  comp_whiskerLeft := by
    intro C D E K first second F G transformation
    apply CorrectedTransformationData.ext_of_base_eq
    exact congrArg Cat.Hom₂.toNatTrans
      (Bicategory.comp_whiskerLeft (B := Cat)
        first.base.toCatHom second.base.toCatHom
        transformation.base.toCatHom₂)
  id_whiskerRight := by
    intro C D E first second
    apply CorrectedTransformationData.ext_of_base_eq
    exact congrArg Cat.Hom₂.toNatTrans
      (Bicategory.id_whiskerRight (B := Cat)
        first.base.toCatHom second.base.toCatHom)
  comp_whiskerRight := by
    intro C D E F G H alpha beta outer
    apply CorrectedTransformationData.ext_of_base_eq
    exact congrArg Cat.Hom₂.toNatTrans
      (Bicategory.comp_whiskerRight (B := Cat)
        alpha.base.toCatHom₂ beta.base.toCatHom₂ outer.base.toCatHom)
  whiskerRight_id := by
    intro C D F G transformation
    apply CorrectedTransformationData.ext_of_base_eq
    exact congrArg Cat.Hom₂.toNatTrans
      (Bicategory.whiskerRight_id (B := Cat)
        transformation.base.toCatHom₂)
  whiskerRight_comp := by
    intro C D E K F G transformation first second
    apply CorrectedTransformationData.ext_of_base_eq
    exact congrArg Cat.Hom₂.toNatTrans
      (Bicategory.whiskerRight_comp (B := Cat)
        transformation.base.toCatHom₂
        first.base.toCatHom second.base.toCatHom)
  whisker_assoc := by
    intro C D E K first F G transformation outer
    apply CorrectedTransformationData.ext_of_base_eq
    exact congrArg Cat.Hom₂.toNatTrans
      (Bicategory.whisker_assoc (B := Cat)
        first.base.toCatHom transformation.base.toCatHom₂
        outer.base.toCatHom)
  whisker_exchange := by
    intro C D E F G H I first second
    apply CorrectedTransformationData.ext_of_base_eq
    exact congrArg Cat.Hom₂.toNatTrans
      (Bicategory.whisker_exchange (B := Cat)
        first.base.toCatHom₂ second.base.toCatHom₂)
  pentagon := by
    intro C D E K L first second third fourth
    apply CorrectedTransformationData.ext_of_base_eq
    exact congrArg Cat.Hom₂.toNatTrans
      (Bicategory.pentagon (B := Cat)
        first.base.toCatHom second.base.toCatHom
        third.base.toCatHom fourth.base.toCatHom)
  triangle := by
    intro C D E first second
    apply CorrectedTransformationData.ext_of_base_eq
    exact congrArg Cat.Hom₂.toNatTrans
      (Bicategory.triangle (B := Cat)
        first.base.toCatHom second.base.toCatHom)

#print axioms PseudoCwfMorphism.substitutionNatIso
#print axioms CorrectedTransformationData.rightWhisker
#print axioms CorrectedTransformationData.leftWhisker
#print axioms CorrectedTransformationData.horizontal
#print axioms CorrectedTransformationData.horizontalCompositionFunctor
#print axioms CorrectedTransformationData.leftUnitorIso
#print axioms CorrectedTransformationData.rightUnitorIso
#print axioms CorrectedTransformationData.associatorIso
#print axioms pseudoCwfBicategory

end Mettapedia.GSLT.Core.ContextualLadder
