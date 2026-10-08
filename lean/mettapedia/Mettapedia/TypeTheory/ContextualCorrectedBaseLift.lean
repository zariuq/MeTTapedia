import Mettapedia.TypeTheory.ContextualDisplayCartesianFactor
import Mettapedia.GSLT.Core.ContextualPseudoCwfTransformation

/-!
# Cartesian lifting of context transformations

The extension component of a base natural transformation lies over its base
component by the two projection equations. Actual cartesian factorization
therefore supplies the displayed component. Its naturality and corrected
comprehension square follow from the original context naturality and display
preservation; they are not independent input fields.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.ContextualCorrectedBaseLift

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualDisplayCartesianFactor

universe u v w w'
variable {C D : CwfWithTerminal.{u, v, w, w'}}
  {F G : PseudoCwfMorphism C D}

/-- The extension-context component, with both selected comprehension
comparisons retained. -/
def conjugate (base : F.base ⟶ G.base) (Γ : C.toCwf.Ctx)
    (A : TypeOver C.toCwf Γ) :
    (⟨D.toCwf.ext (F.base.obj ⟨Γ⟩).val (F.mapType A.val)⟩ : D.toCwf.base.Context) ⟶
      ⟨D.toCwf.ext (G.base.obj ⟨Γ⟩).val (G.mapType A.val)⟩ :=
  (F.comprehensionIso Γ A.val).inv ≫ base.app ⟨C.toCwf.ext Γ A.val⟩ ≫
    (G.comprehensionIso Γ A.val).hom

theorem conjugate_over (base : F.base ⟶ G.base) (Γ : C.toCwf.Ctx)
    (A : TypeOver C.toCwf Γ) :
    D.toCwf.compS (D.toCwf.wk (G.mapType A.val)) (conjugate base Γ A) =
      D.toCwf.compS (base.app ⟨Γ⟩) (D.toCwf.wk (F.mapType A.val)) := by
  let weakenFirst :
      (⟨D.toCwf.ext (F.base.obj ⟨Γ⟩).val (F.mapType A.val)⟩ : D.toCwf.base.Context) ⟶
        F.base.obj ⟨Γ⟩ := D.toCwf.wk (F.mapType A.val)
  let weakenSecond :
      (⟨D.toCwf.ext (G.base.obj ⟨Γ⟩).val (G.mapType A.val)⟩ : D.toCwf.base.Context) ⟶
        G.base.obj ⟨Γ⟩ := D.toCwf.wk (G.mapType A.val)
  have projectionFirst := F.projection_preserved Γ A.val
  change F.base.map (C.toCwf.wk A.val) = (F.comprehensionIso Γ A.val).hom ≫ weakenFirst
    at projectionFirst
  have projectionSecond := G.projection_preserved Γ A.val
  change G.base.map (C.toCwf.wk A.val) = (G.comprehensionIso Γ A.val).hom ≫ weakenSecond
    at projectionSecond
  change conjugate base Γ A ≫ weakenSecond = weakenFirst ≫ base.app ⟨Γ⟩
  dsimp only [conjugate]
  rw [Category.assoc, Category.assoc, ← projectionSecond,
    ← base.naturality, projectionFirst]
  simp only [← Category.assoc]
  erw [Iso.inv_hom_id, Category.id_comp]

/-- The displayed component obtained by actual cartesian factorization. -/
def component (base : F.base ⟶ G.base) (Γ : C.toCwf.Ctx)
    (A : TypeOver C.toCwf Γ) :
    F.mapTypeObject A ⟶ TypeOver.reindexObject (base.app ⟨Γ⟩) (G.mapTypeObject A) :=
  factor (base.app ⟨Γ⟩) (conjugate base Γ A) (conjugate_over base Γ A)

theorem component_lift (base : F.base ⟶ G.base) (Γ : C.toCwf.Ctx)
    (A : TypeOver C.toCwf Γ) :
    D.toCwf.compS (TypeOver.extensionSubstitution (base.app ⟨Γ⟩) (G.mapType A.val))
      (component base Γ A).substitution = conjugate base Γ A :=
  factor_composes (base.app ⟨Γ⟩) (conjugate base Γ A) (conjugate_over base Γ A)

theorem component_naturality (base : F.base ⟶ G.base) (Γ : C.toCwf.Ctx)
    {A B : TypeOver C.toCwf Γ} (arrow : A ⟶ B) :
    (F.mapTypeFunctor Γ).map arrow ≫ component base Γ B =
      component base Γ A ≫ (TypeOver.reindexFunctor (base.app ⟨Γ⟩)).map
        ((G.mapTypeFunctor Γ).map arrow) := by
  apply TypeOver.extensionSubstitution_cancel (base.app ⟨Γ⟩)
  change D.toCwf.compS (TypeOver.extensionSubstitution (base.app ⟨Γ⟩) (G.mapType B.val))
      (D.toCwf.compS (component base Γ B).substitution
        ((F.mapTypeFunctor Γ).map arrow).substitution) =
    D.toCwf.compS (TypeOver.extensionSubstitution (base.app ⟨Γ⟩) (G.mapType B.val))
      (D.toCwf.compS ((TypeOver.reindexFunctor (base.app ⟨Γ⟩)).map
        ((G.mapTypeFunctor Γ).map arrow)).substitution (component base Γ A).substitution)
  have reindexed := TypeOver.extensionSubstitution_naturality (base.app ⟨Γ⟩)
    ((G.mapTypeFunctor Γ).map arrow)
  change D.toCwf.compS (TypeOver.extensionSubstitution (base.app ⟨Γ⟩) (G.mapType B.val))
      ((TypeOver.reindexFunctor (base.app ⟨Γ⟩)).map
        ((G.mapTypeFunctor Γ).map arrow)).substitution =
    D.toCwf.compS ((G.mapTypeFunctor Γ).map arrow).substitution
      (TypeOver.extensionSubstitution (base.app ⟨Γ⟩) (G.mapType A.val)) at reindexed
  have leftComputation :
      D.toCwf.compS (TypeOver.extensionSubstitution (base.app ⟨Γ⟩) (G.mapType B.val))
        (D.toCwf.compS (component base Γ B).substitution
          ((F.mapTypeFunctor Γ).map arrow).substitution) =
      D.toCwf.compS (conjugate base Γ B) ((F.mapTypeFunctor Γ).map arrow).substitution :=
    (D.toCwf.comp_assoc _ _ _).symm.trans
      (congrArg (fun substitution => D.toCwf.compS substitution
        ((F.mapTypeFunctor Γ).map arrow).substitution) (component_lift base Γ B))
  have rightComputation :
      D.toCwf.compS (TypeOver.extensionSubstitution (base.app ⟨Γ⟩) (G.mapType B.val))
        (D.toCwf.compS ((TypeOver.reindexFunctor (base.app ⟨Γ⟩)).map
          ((G.mapTypeFunctor Γ).map arrow)).substitution (component base Γ A).substitution) =
      D.toCwf.compS ((G.mapTypeFunctor Γ).map arrow).substitution (conjugate base Γ A) :=
    (D.toCwf.comp_assoc _ _ _).symm.trans
      ((congrArg (fun substitution => D.toCwf.compS substitution
        (component base Γ A).substitution) reindexed).trans
        ((D.toCwf.comp_assoc _ _ _).trans
          (congrArg (fun substitution => D.toCwf.compS
            ((G.mapTypeFunctor Γ).map arrow).substitution substitution) (component_lift base Γ A))))
  apply leftComputation.trans
  apply Eq.trans _ rightComputation.symm
  have leftDisplay := F.display_preserved Γ A B arrow
  have rightDisplay := G.display_preserved Γ A B arrow
  change ((F.mapTypeFunctor Γ).map arrow).substitution = _ at leftDisplay
  change ((G.mapTypeFunctor Γ).map arrow).substitution = _ at rightDisplay
  erw [leftDisplay, rightDisplay]
  change ((F.comprehensionIso Γ A.val).inv ≫ F.base.map arrow.substitution ≫
      (F.comprehensionIso Γ B.val).hom) ≫ conjugate base Γ B =
    conjugate base Γ A ≫ ((G.comprehensionIso Γ A.val).inv ≫
      G.base.map arrow.substitution ≫ (G.comprehensionIso Γ B.val).hom)
  simp only [conjugate, Category.assoc, Iso.hom_inv_id_assoc]
  simpa only [Category.assoc] using congrArg
    (fun substitution => (F.comprehensionIso Γ A.val).inv ≫
      substitution ≫ (G.comprehensionIso Γ B.val).hom)
    (base.naturality (show (⟨C.toCwf.ext Γ A.val⟩ : C.toCwf.base.Context) ⟶
      ⟨C.toCwf.ext Γ B.val⟩ from arrow.substitution))

/-- Actual corrected transformation data constructed from the supplied
base transformation. Both displayed obligations have been proved. -/
def lift (base : F.base ⟶ G.base) : CorrectedTransformationData F G where
  base := base
  family := component base
  family_naturality := component_naturality base
  comprehension_coherence := by
    intro Γ A
    change D.toCwf.compS
        (D.toCwf.compS (TypeOver.extensionSubstitution (base.app ⟨Γ⟩) (G.mapType A.val))
          (component base Γ A).substitution) (F.comprehensionIso Γ A.val).hom =
      D.toCwf.compS (G.comprehensionIso Γ A.val).hom (base.app ⟨C.toCwf.ext Γ A.val⟩)
    rw [component_lift]
    change (F.comprehensionIso Γ A.val).hom ≫ conjugate base Γ A = _
    simp only [conjugate, ← Category.assoc]
    erw [Iso.hom_inv_id, Category.id_comp]
    rfl

@[simp] theorem lift_base (base : F.base ⟶ G.base) : (lift base).base = base := rfl

/-- The actual corrected square determines this cartesian lift uniquely. -/
theorem lift_unique (base : F.base ⟶ G.base)
    (other : CorrectedTransformationData F G) (same : other.base = base) :
    other = lift base := CorrectedTransformationData.ext_of_base_eq _ _ same

/-- Lifting respects actual vertical composition of corrected cells. -/
theorem lift_comp {H : PseudoCwfMorphism C D}
    (first : F.base ⟶ G.base) (second : G.base ⟶ H.base) :
    lift (first ≫ second) = CorrectedTransformationData.vertical (lift first) (lift second) :=
  CorrectedTransformationData.ext_of_base_eq _ _ rfl

@[simp] theorem lift_identity (F : PseudoCwfMorphism C D) :
    lift (𝟙 F.base) = CorrectedTransformationData.identity F :=
  CorrectedTransformationData.ext_of_base_eq _ _ rfl

/-- An actual base natural isomorphism lifts to an invertible corrected
cell. Its two inverse squares follow from earned composition coherence. -/
def liftIso (base : F.base ≅ G.base) : F ≅ G where
  hom := lift base.hom
  inv := lift base.inv
  hom_inv_id := CorrectedTransformationData.ext_of_base_eq _ _ base.hom_inv_id
  inv_hom_id := CorrectedTransformationData.ext_of_base_eq _ _ base.inv_hom_id

@[simp] theorem liftIso_hom_base (base : F.base ≅ G.base) :
    (liftIso base).hom.base = base.hom := rfl

@[simp] theorem liftIso_inv_base (base : F.base ≅ G.base) :
    (liftIso base).inv.base = base.inv := rfl

/-- For the existing display-preserving pseudo-morphism interface, the
actual cartesian construction supplies every base transformation. Combined
with corrected comprehension uniqueness, forgetting displayed data is fully
faithful. -/
instance baseForgetfulFunctor_full :
    (CorrectedTransformationData.baseForgetfulFunctor (C := C) (D := D)).Full where
  map_surjective base := ⟨lift base, rfl⟩

end Mettapedia.TypeTheory.ContextualCorrectedBaseLift
