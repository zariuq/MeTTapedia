import Mathlib.CategoryTheory.Subobject.Classifier.Defs
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Canonical classifier comparisons for finite-limit functors

The comparison from a functor's image of a classifier to the destination
classifier is the characteristic map of the mapped truth monomorphism.
Pullback pasting proves preservation of every characteristic map and fixes
the comparison for identities and composites. Invertibility is an extra
logical condition; finite-limit preservation alone does not provide it.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.LogicalClassifierComparison

open _root_.CategoryTheory _root_.CategoryTheory.Limits

attribute [local instance] comp_preservesFiniteLimits

universe u₁ u₂ u₃ v₁ v₂ v₃
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]
variable (source : Subobject.Classifier C) (target : Subobject.Classifier D)
variable (F : C ⥤ D) [PreservesFiniteLimits F]

noncomputable def comparison : F.obj source.Ω ⟶ target.Ω :=
  target.χ (F.map source.truth)

theorem truth_square : IsPullback (F.map source.truth)
    (target.χ₀ (F.obj source.Ω₀)) (comparison source target F) target.truth :=
  target.isPullback (F.map source.truth)

theorem characteristic_preservation {selected object : C}
    (inclusion : selected ⟶ object) [Mono inclusion] :
    F.map (source.χ inclusion) ≫ comparison source target F =
      target.χ (F.map inclusion) := by
  apply target.uniq (F.map inclusion)
  exact ((source.isPullback inclusion).map F).paste_vert (truth_square source target F)

theorem identity (source : Subobject.Classifier C) :
    comparison source source (𝟭 C) = 𝟙 source.Ω := by
  symm
  change 𝟙 source.Ω = source.χ source.truth
  exact source.uniq source.truth (IsPullback.id_vert source.truth)

theorem composition (last : Subobject.Classifier E)
    (G : D ⥤ E) [PreservesFiniteLimits G] :
    comparison source last (F ⋙ G) =
      G.map (comparison source target F) ≫ comparison target last G := by
  symm
  exact characteristic_preservation target last G (F.map source.truth)

end Mettapedia.CategoryTheory.LogicalClassifierComparison
