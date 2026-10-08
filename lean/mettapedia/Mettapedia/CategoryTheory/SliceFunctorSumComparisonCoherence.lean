import Mettapedia.CategoryTheory.SliceFunctorSumComparison

/-!
# Coherent complete dependent-sum comparisons

The chosen comparison is compatible with identity and composition of
functors. Each equation compares the actual natural isomorphisms, rather
than their object endpoints. Complete domain-map readouts fix the whole
slice comparison, and the independent functor composition laws determine
the displayed triangles.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.SliceFunctorSumComparisonCoherence

open _root_.CategoryTheory _root_.CategoryTheory.Functor
open SliceFunctorSumComparison

universe u₁ u₂ u₃ v₁ v₂ v₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]
variable (F : C ⥤ D) (G : D ⥤ E)
variable {X Y : C} (route : X ⟶ Y)

def postIdentity (base : C) : Over.post (X := base) (𝟭 C) ≅ 𝟭 (Over base) :=
  NatIso.ofComponents (fun display => Over.isoMk (Iso.refl display.left) (by
    change 𝟙 display.left ≫ display.hom = display.hom
    exact Category.id_comp _)) (by
    intro first second square
    apply Over.OverMorphism.ext
    change square.left ≫ 𝟙 _ = 𝟙 _ ≫ square.left
    rw [Category.comp_id, Category.id_comp])

def identityComparison : Over.map route ⋙ Over.post (𝟭 C) ≅
    Over.post (𝟭 C) ⋙ Over.map route :=
  isoWhiskerLeft (Over.map route) (postIdentity Y) ≪≫
    Functor.rightUnitor (Over.map route) ≪≫
    (Functor.leftUnitor (Over.map route)).symm ≪≫
    isoWhiskerRight (postIdentity X).symm (Over.map route)

theorem comparison_identity : comparison (𝟭 C) route = identityComparison route := by
  apply Iso.ext
  apply NatTrans.ext
  funext display
  apply Over.OverMorphism.ext
  change 𝟙 display.left = 𝟙 display.left ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
  simp only [Category.id_comp]

/-- The staged comparison includes the two genuine post-composition
isomorphisms and all associators. -/
def compositionComparison : Over.map route ⋙ Over.post (F ⋙ G) ≅
    Over.post (F ⋙ G) ⋙ Over.map ((F ⋙ G).map route) :=
  isoWhiskerLeft (Over.map route) (Over.postComp F G) ≪≫
    (Functor.associator (Over.map route) (Over.post F) (Over.post G)).symm ≪≫
    isoWhiskerRight (comparison F route) (Over.post G) ≪≫
    Functor.associator (Over.post F) (Over.map (F.map route)) (Over.post G) ≪≫
    isoWhiskerLeft (Over.post F) (comparison G (F.map route)) ≪≫
    (Functor.associator (Over.post F) (Over.post G)
      (Over.map ((F ⋙ G).map route))).symm ≪≫
    isoWhiskerRight (Over.postComp F G).symm (Over.map ((F ⋙ G).map route))

theorem component_composition (display : Over X) :
    (component (F ⋙ G) route display).hom =
      (Over.post G).map (component F route display).hom ≫
        (component G (F.map route) ((Over.post F).obj display)).hom := by
  apply Over.OverMorphism.ext
  change 𝟙 (G.obj (F.obj display.left)) =
    G.map (𝟙 (F.obj display.left)) ≫ 𝟙 (G.obj (F.obj display.left))
  rw [G.map_id, Category.id_comp]

theorem comparison_composition : comparison (F ⋙ G) route =
    compositionComparison F G route := by
  apply Iso.ext
  apply NatTrans.ext
  funext display
  apply Over.OverMorphism.ext
  simp [compositionComparison, Over.postComp, comparison, component]
  change 𝟙 (G.obj (F.obj display.left)) =
    𝟙 (G.obj (F.obj display.left)) ≫ 𝟙 (G.obj (F.obj display.left))
  exact (Category.id_comp _).symm

/-- Equality of complete slice arrows is determined by their domain
maps. This fixes the comparison for every actual display. -/
theorem component_unique (display : Over X)
    (candidate : (Over.map route ⋙ Over.post F).obj display ⟶
      (Over.post F ⋙ Over.map (F.map route)).obj display)
    (domain : candidate.left = 𝟙 (F.obj display.left)) :
    candidate = (component F route display).hom := by
  apply Over.OverMorphism.ext
  exact domain

end Mettapedia.CategoryTheory.SliceFunctorSumComparisonCoherence
