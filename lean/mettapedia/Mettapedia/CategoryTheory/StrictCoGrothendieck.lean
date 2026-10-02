import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# The contravariant Grothendieck construction of a strict functor

For a functor `F : 𝒮ᵒᵖ ⥤ Cat`, the pseudofunctor coherences of `∫ᶜ F` are
equalities of functors. Identities and composites then have their fibre
components given by the fibre arrows followed by a single `eqToHom`.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.StrictCoGrothendieck

open _root_.CategoryTheory _root_.CategoryTheory.Pseudofunctor Opposite

universe v u

variable {𝒮 : Type u} [Category.{v} 𝒮] (F : 𝒮ᵒᵖ ⥤ Cat.{0, 0})

/-- The identity arrow over an object is the identity of its fibre, cast
along the identity law of `F`. -/
theorem id_fiber (a : CoGrothendieck F.toPseudofunctor') :
    (𝟙 a : a ⟶ a).fiber =
      eqToHom (show a.fiber = (F.map (𝟙 a.base).op).toFunctor.obj a.fiber by
        rw [op_id, F.map_id]; rfl) := by
  rw [CoGrothendieck.categoryStruct_id_fiber]
  simp only [Functor.toPseudofunctor'_mapId, eqToIso.inv]
  exact Cat.eqToHom_app _ _ _ _

/-- A composite is the first fibre arrow, then the reindexed second one,
cast along the composition law of `F`. -/
theorem comp_fiber {a b c : CoGrothendieck F.toPseudofunctor'} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).fiber = f.fiber ≫ (F.map f.base.op).toFunctor.map g.fiber ≫
      eqToHom (show (F.map f.base.op).toFunctor.obj ((F.map g.base.op).toFunctor.obj c.fiber) =
        (F.map (f.base ≫ g.base).op).toFunctor.obj c.fiber by
          rw [op_comp, F.map_comp]; rfl) := by
  rw [CoGrothendieck.categoryStruct_comp_fiber]
  congr 2
  simp only [Functor.toPseudofunctor'_mapComp, eqToIso.inv]
  exact Cat.eqToHom_app _ _ _ _

/-- A fibre arrow included over its base object. -/
theorem ι_map_fiber (S : 𝒮) {x y : F.toPseudofunctor'.obj ⟨op S⟩} (φ : x ⟶ y) :
    ((CoGrothendieck.ι F.toPseudofunctor' S).map φ).fiber =
      φ ≫ eqToHom (show y = (F.map (𝟙 S).op).toFunctor.obj y by
        rw [op_id, F.map_id]; rfl) := by
  change φ ≫ (F.toPseudofunctor'.mapId ⟨op S⟩).inv.toNatTrans.app y = _
  congr 1
  simp only [Functor.toPseudofunctor'_mapId, eqToIso.inv]
  exact Cat.eqToHom_app _ _ _ _

end Mettapedia.CategoryTheory.StrictCoGrothendieck
