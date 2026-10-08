import Mettapedia.CategoryTheory.MonoArrowFibration
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# The action on predicate displays

A monomorphism-preserving functor maps the actual predicate category.
Natural transformations act through both sides of its commuting squares.
Finite-limit preservation then supplies preservation of every Cartesian
arrow. The comprehension and projection squares use the same functor and
the same components, rather than unrelated maps of fibre carriers.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.MonoArrowImageAdjunction

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u₁ u₂ u₃ v₁ v₂ v₃
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

def map (F : C ⥤ D) [F.PreservesMonomorphisms] : Predicate C ⥤ Predicate D where
  obj predicate := ⟨F.mapArrow.obj predicate.obj, by
    change Mono (F.map predicate.obj.hom)
    infer_instance⟩
  map square := ObjectProperty.homMk (F.mapArrow.map square.hom)
  map_id predicate := by
    apply ObjectProperty.hom_ext
    exact F.mapArrow.map_id predicate.obj
  map_comp first second := by
    apply ObjectProperty.hom_ext
    exact F.mapArrow.map_comp first.hom second.hom

def map₂ {F G : C ⥤ D} [F.PreservesMonomorphisms] [G.PreservesMonomorphisms]
    (change : F ⟶ G) : map F ⟶ map G where
  app predicate := ObjectProperty.homMk
    ((Functor.mapArrowFunctor C D).map change |>.app predicate.obj)
  naturality := by
    intro first second square
    apply ObjectProperty.hom_ext
    exact ((Functor.mapArrowFunctor C D).map change).naturality square.hom

@[simp] theorem map₂_component_left {F G : C ⥤ D}
    [F.PreservesMonomorphisms] [G.PreservesMonomorphisms]
    (change : F ⟶ G) (predicate : Predicate C) :
    ((map₂ change).app predicate).hom.left = change.app predicate.obj.left := rfl

@[simp] theorem map₂_component_right {F G : C ⥤ D}
    [F.PreservesMonomorphisms] [G.PreservesMonomorphisms]
    (change : F ⟶ G) (predicate : Predicate C) :
    ((map₂ change).app predicate).hom.right = change.app predicate.obj.right := rfl

theorem comprehension_square (F : C ⥤ D) [F.PreservesMonomorphisms] :
    map F ⋙ comprehension D = comprehension C ⋙ F.mapArrow := rfl

theorem projection_square (F : C ⥤ D) [F.PreservesMonomorphisms] :
    map F ⋙ projection D = projection C ⋙ F := rfl

theorem map₂_identity (F : C ⥤ D) [F.PreservesMonomorphisms] :
    map₂ (𝟙 F) = 𝟙 (map F) := by
  apply NatTrans.ext
  funext predicate
  apply predicate_hom_ext
  rfl

theorem map₂_composition {F G H : C ⥤ D}
    [F.PreservesMonomorphisms] [G.PreservesMonomorphisms] [H.PreservesMonomorphisms]
    (first : F ⟶ G) (second : G ⟶ H) :
    map₂ (first ≫ second) = map₂ first ≫ map₂ second := by
  apply NatTrans.ext
  funext predicate
  apply predicate_hom_ext
  rfl

theorem map_identity : map (𝟭 C) = 𝟭 (Predicate C) := by
  refine _root_.CategoryTheory.Functor.ext
    (fun predicate => ObjectProperty.FullSubcategory.ext (Arrow.mk_eq predicate.obj)) ?_
  · intro first second square
    rcases first with ⟨⟨_, _, _⟩, _⟩
    rcases second with ⟨⟨_, _, _⟩, _⟩
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · simp [map]
    · simp [map]

variable (F : C ⥤ D) (G : D ⥤ E)
variable [F.PreservesMonomorphisms] [G.PreservesMonomorphisms]

theorem map_composition : map (F ⋙ G) = map F ⋙ map G := rfl

variable [HasPullbacks C] [HasPullbacks D] [PreservesFiniteLimits F]

theorem map_preserves_cartesian {first second : Predicate C} (square : first ⟶ second)
    [(projection C).IsCartesian square.hom.right square] :
    (projection D).IsCartesian (F.map square.hom.right) ((map F).map square) := by
  exact (cartesian_iff_pullback ((map F).map square)).mpr
    (((cartesian_iff_pullback square).mp inferInstance).map F)

omit [F.PreservesMonomorphisms] in
theorem arrow_map_preserves_cartesian {first second : Arrow C} (square : first ⟶ second)
    [Arrow.rightFunc.IsCartesian square.right square] :
    Arrow.rightFunc.IsCartesian (F.map square.right) (F.mapArrow.map square) := by
  exact (CodomainComprehension.cartesian_iff_pullback (F.mapArrow.map square)).mpr
    (((CodomainComprehension.cartesian_iff_pullback square).mp inferInstance).map F)

end Mettapedia.CategoryTheory.MonoArrowImageAdjunction
