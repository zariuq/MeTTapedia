import Mettapedia.TypeTheory.DependentProductRestrictionEvaluation

/-!
# Contravariant arguments in dependent products

A map of argument families acts on dependent functions by precomposition.
For a natural transformation of world functors, changing a body witness
and precomposing its argument give the two sides of a mixed product square.
All maps use the selected native right adjoint and its canonical section
comparison.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DependentProductArgumentTransport

open CategoryTheory
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent
open CategoryIndexedFamilyGeneralPi DependentProductNativeComparison
open DependentProductRestriction

universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]

/-- The argument is supplied through the actual family map, at every
future arrow. The dependent codomain is pulled back along that map. -/
def sectionPrecomposition {A₀ A₁ : C ⥤ Type u} (argument : A₀ ⟶ A₁)
    (B : A₁.Elements ⥤ Type u) :
    dependentFunctions A₁ B ⟶ dependentFunctions A₀ (argument.mapElements ⋙ B) :=
  curry (Functor.whiskerLeft argument.mapElements (evaluate A₁ B))

theorem sectionPrecomposition_readout {A₀ A₁ : C ⥤ Type u}
    (argument : A₀ ⟶ A₁) (B : A₁.Elements ⥤ Type u)
    {X : C} (function : DependentSection A₁ B X)
    (Y : C) (arrow : X ⟶ Y) (value : A₀.obj Y) :
    ((sectionPrecomposition argument B).app X function).app Y arrow value =
      function.app Y arrow (argument.app Y value) := by
  change function.app Y (arrow ≫ 𝟙 Y) (argument.app Y value) = _
  rw [Category.comp_id]

/-- Argument precomposition on the already chosen native product. -/
noncomputable def nativePrecomposition {A₀ A₁ : C ⥤ Type u} (argument : A₀ ⟶ A₁)
    (B : A₁.Elements ⥤ Type u) :
    generalPiFamily (context := Cat.of C) A₁ B ⟶
      generalPiFamily (context := Cat.of C) A₀ (argument.mapElements ⋙ B) :=
  (nativeIso A₁).hom.app B ≫ sectionPrecomposition argument B ≫
    (nativeIso A₀).inv.app (argument.mapElements ⋙ B)

set_option backward.isDefEq.respectTransparency false in
theorem nativePrecomposition_section {A₀ A₁ : C ⥤ Type u}
    (argument : A₀ ⟶ A₁) (B : A₁.Elements ⥤ Type u) :
    nativePrecomposition argument B ≫ (nativeIso A₀).hom.app _ =
      (nativeIso A₁).hom.app B ≫ sectionPrecomposition argument B := by
  simp only [nativePrecomposition, Category.assoc, Iso.inv_hom_id_app]
  ext X value
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem nativePrecomposition_readout {A₀ A₁ : C ⥤ Type u}
    (argument : A₀ ⟶ A₁) (B : A₁.Elements ⥤ Type u)
    {X : C} (function : (generalPiFamily (context := Cat.of C) A₁ B).obj X)
    (Y : C) (arrow : X ⟶ Y) (value : A₀.obj Y) :
    (((nativeIso A₀).hom.app (argument.mapElements ⋙ B)).app X
        ((nativePrecomposition argument B).app X function)).app Y arrow value =
      (((nativeIso A₁).hom.app B).app X function).app Y arrow
        (argument.app Y value) := by
  have square := ConcreteCategory.congr_hom (C := Type u)
    (congrArg (fun operation => operation.app X)
      (nativePrecomposition_section argument B)) function
  have readout := congrArg (fun functionValue :
    DependentSection A₀ (argument.mapElements ⋙ B) X => functionValue.app Y arrow value) square
  exact readout.trans (sectionPrecomposition_readout argument B
    (((nativeIso A₁).hom.app B).app X function) Y arrow value)

variable {F G : C ⥤ D}

def argumentChange (change : F ⟶ G) (A : D ⥤ Type u) : F ⋙ A ⟶ G ⋙ A :=
  Functor.whiskerRight change A

def elementChange (change : F ⟶ G) (A : D ⥤ Type u)
    (point : (F ⋙ A).Elements) :
    (Functor.Elements.precomp F A).obj point ⟶
      (Functor.Elements.precomp G A).obj ((argumentChange change A).mapElements.obj point) :=
  CategoryOfElements.homMk _ _ (change.app point.1) rfl

/-- Body evidence moves along the natural transformation at the complete
argument, rather than being erased or replaced by inhabitation. -/
def codomainChange (change : F ⟶ G) (A : D ⥤ Type u)
    (B : A.Elements ⥤ Type u) :
    restrictedFamily F A B ⟶
      (argumentChange change A).mapElements ⋙ restrictedFamily G A B where
  app point := B.map (elementChange change A point)
  naturality first second arrow := by
    ext evidence
    change B.map (elementChange change A second)
        (B.map ((Functor.Elements.precomp F A).map arrow) evidence) =
      B.map ((Functor.Elements.precomp G A).map
        ((argumentChange change A).mapElements.map arrow))
          (B.map (elementChange change A first) evidence)
    rw [← B.map_comp_apply, ← B.map_comp_apply]
    apply congrArg (fun route => B.map route evidence)
    apply CategoryOfElements.ext A
    exact change.naturality arrow.val

set_option backward.isDefEq.respectTransparency false in
/-- The mixed comparison square: covariant body transport equals changing
worlds followed by contravariant argument precomposition. No inversion of
the world change or argument map is required. -/
theorem section_mixed_square (change : F ⟶ G) (A : D ⥤ Type u)
    (B : A.Elements ⥤ Type u) :
    comparison F A B ≫ mapFamily (codomainChange change A B) =
      Functor.whiskerRight change (dependentFunctions A B) ≫
        comparison G A B ≫
          sectionPrecomposition (argumentChange change A) (restrictedFamily G A B) := by
  ext X function
  apply DependentSection.ext
  intro Y arrow value
  change B.map (elementChange change A (⟨Y, value⟩ : (F ⋙ A).Elements))
      (function.app (F.obj Y) (F.map arrow) value) =
    ((sectionPrecomposition (argumentChange change A) (restrictedFamily G A B)).app X
      (restrictSection G A B
        (DependentSection.restrict A B (change.app X) function))).app Y arrow value
  rw [sectionPrecomposition_readout]
  change B.map (argumentMap A (change.app Y) value)
      (function.app (F.obj Y) (F.map arrow) value) =
    function.app (G.obj Y) (change.app X ≫ G.map arrow)
      (A.map (change.app Y) value)
  rw [function.naturality]
  exact congrArg (fun route => function.app (G.obj Y) route
    (A.map (change.app Y) value)) (change.naturality arrow)

set_option backward.isDefEq.respectTransparency false in
/-- Every future-argument readout of the chosen native comparison agrees
with restriction of its evaluation-preserving section. -/
theorem nativeRestriction_readout (route : C ⥤ D) (A : D ⥤ Type u)
    (B : A.Elements ⥤ Type u) {X : C}
    (function : (generalPiFamily (context := Cat.of D) A B).obj (route.obj X))
    (Y : C) (arrow : X ⟶ Y) (value : A.obj (route.obj Y)) :
    (((nativeIso (route ⋙ A)).hom.app (restrictedFamily route A B)).app X
        ((nativeRestriction route A B).app X function)).app Y arrow value =
      (((nativeIso A).hom.app B).app (route.obj X) function).app
        (route.obj Y) (route.map arrow) value := by
  have square := ConcreteCategory.congr_hom (C := Type u)
    (congrArg (fun operation => operation.app X)
      (nativeRestriction_section route A B)) function
  exact congrArg (fun functionValue :
    DependentSection (route ⋙ A) (restrictedFamily route A B) X =>
      functionValue.app Y arrow value) square

set_option backward.isDefEq.respectTransparency false in
/-- The same mixed square for the selected right-Kan product, as equality
of full natural maps of proof-relevant functions. -/
theorem native_mixed_square (change : F ⟶ G) (A : D ⥤ Type u)
    (B : A.Elements ⥤ Type u) :
    nativeRestriction F A B ≫
        (CategoryOfElements.π (F ⋙ A)).ran.map (codomainChange change A B) =
      Functor.whiskerRight change (generalPiFamily (context := Cat.of D) A B) ≫
        nativeRestriction G A B ≫
          nativePrecomposition (argumentChange change A) (restrictedFamily G A B) := by
  apply (cancel_mono ((nativeIso (F ⋙ A)).hom.app
    ((argumentChange change A).mapElements ⋙ restrictedFamily G A B))).mp
  have natural :
      Functor.whiskerLeft F ((nativeIso A).hom.app B) ≫
          Functor.whiskerRight change (dependentFunctions A B) =
        Functor.whiskerRight change (generalPiFamily (context := Cat.of D) A B) ≫
          Functor.whiskerLeft G ((nativeIso A).hom.app B) := by
    apply NatTrans.ext
    funext X
    exact (((nativeIso A).hom.app B).naturality (change.app X)).symm
  calc
    _ = (nativeRestriction F A B ≫
        (nativeIso (F ⋙ A)).hom.app (restrictedFamily F A B)) ≫
          mapFamily (codomainChange change A B) := by
      rw [Category.assoc, (nativeIso (F ⋙ A)).hom.naturality]
      rfl
    _ = (Functor.whiskerLeft F ((nativeIso A).hom.app B) ≫ comparison F A B) ≫
        mapFamily (codomainChange change A B) := by rw [nativeRestriction_section]
    _ = Functor.whiskerLeft F ((nativeIso A).hom.app B) ≫
        (Functor.whiskerRight change (dependentFunctions A B) ≫
          comparison G A B ≫
            sectionPrecomposition (argumentChange change A) (restrictedFamily G A B)) := by
      rw [Category.assoc, section_mixed_square]
    _ = Functor.whiskerRight change (generalPiFamily (context := Cat.of D) A B) ≫
        (Functor.whiskerLeft G ((nativeIso A).hom.app B) ≫ comparison G A B) ≫
          sectionPrecomposition (argumentChange change A) (restrictedFamily G A B) := by
      rw [← Category.assoc, natural]
      simp only [Category.assoc]
    _ = Functor.whiskerRight change (generalPiFamily (context := Cat.of D) A B) ≫
        (nativeRestriction G A B ≫ (nativeIso (G ⋙ A)).hom.app _) ≫
          sectionPrecomposition (argumentChange change A) (restrictedFamily G A B) := by
      rw [nativeRestriction_section]
    _ = _ := by
      simp only [Category.assoc]
      rw [nativePrecomposition_section (argumentChange change A) (restrictedFamily G A B)]

end Mettapedia.TypeTheory.DependentProductArgumentTransport
