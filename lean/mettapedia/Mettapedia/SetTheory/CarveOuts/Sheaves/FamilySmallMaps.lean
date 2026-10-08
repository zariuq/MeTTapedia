import Mettapedia.SetTheory.CarveOuts.Sheaves.SmallMaps

/-!
# Small maps on families of sheaves over the contexts

The category of the models is `D ⥤ Sheaf (Opens.grothendieckTopology X) (Type u)`. A map
of families is small when it is small at every context (`familySmall`). Limits, colimits, monos
and epis of families are computed context by context, so (S1)–(S5) and (M) for families follow
from those for sheaves (`familySmall_smallMapClass`, `familySmall_monosSmall`). An epimorphism of
families is locally surjective at every context.

Collection for families is not proved here: a covering square must be functorial in the
contexts, and the sheaf-level construction is made one context at a time.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.Sheaves

open CategoryTheory Limits TopologicalSpace
open Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps

universe w u

variable {X : Type u} [TopologicalSpace X] {D : Type u} [Category.{u} D]

/-- **Small maps of families**: small at every context. -/
def familySmall : MorphismProperty (D ⥤ SheafOn X) :=
  fun _ _ η => ∀ c, sheafSmall.{w} (η.app c)

/-- **(M) for families.** -/
theorem familySmall_monosSmall : MonosSmall (familySmall.{w} : MorphismProperty (D ⥤ SheafOn X)) := by
  intro F G m hm c
  exact sheafSmall_monosSmall _ ((NatTrans.mono_iff_mono_app m).mp hm c)

/-- **(S1)–(S5) for families.** -/
theorem familySmall_smallMapClass [Small.{w} (Opens X)] :
    SmallMapClass (familySmall.{w} : MorphismProperty (D ⥤ SheafOn X)) where
  comp f g hf hg c := sheafSmall_comp (f.app c) (g.app c) (hf c) (hg c)
  id F c := sheafSmall_smallMapClass.id (F.obj c)
  pullback sq hg c := sheafSmall_pullback (Functor.map_isPullback ((evaluation D _).obj c) sq) (hg c)
  diagonal F := familySmall_monosSmall _ (mono_of_mono_fac (prod.lift_fst (𝟙 F) (𝟙 F)))
  quotient e g he h c :=
    sheafSmall_quotient (e.app c) (g.app c) ((NatTrans.epi_iff_epi_app e).mp he c) (h c)
  copair f g hf hg c :=
    sheafSmall_copair_of_isColimit _
      ((isColimitMapCoconeBinaryCofanEquiv ((evaluation D _).obj c) coprod.inl coprod.inr)
        (isColimitOfPreserves ((evaluation D _).obj c) (coprodIsCoprod _ _)))
      (f.app c) (g.app c) ((coprod.desc f g).app c)
      ((NatTrans.comp_app coprod.inl (coprod.desc f g) c).symm.trans
        (congrArg (fun k => NatTrans.app k c) (coprod.inl_desc f g)))
      ((NatTrans.comp_app coprod.inr (coprod.desc f g) c).symm.trans
        (congrArg (fun k => NatTrans.app k c) (coprod.inr_desc f g))) (hf c) (hg c)

/-- **(S1)–(S5) for families over any context category, valued in sheaves on Cantor space.** -/
theorem cantor_familySmallMapClass (D : Type) [Category.{0} D] :
    SmallMapClass (familySmall.{w} : MorphismProperty (D ⥤ SheafOn (ℕ → Bool))) :=
  familySmall_smallMapClass.{w, 0}

/-- **(M) for families valued in sheaves on Cantor space.** -/
theorem cantor_familyMonosSmall (D : Type) [Category.{0} D] :
    MonosSmall (familySmall.{w} : MorphismProperty (D ⥤ SheafOn (ℕ → Bool))) :=
  familySmall_monosSmall.{w, 0}

end Mettapedia.SetTheory.CarveOuts.Sheaves
