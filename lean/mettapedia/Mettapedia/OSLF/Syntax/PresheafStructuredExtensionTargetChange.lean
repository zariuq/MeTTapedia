import Mettapedia.OSLF.Syntax.PresheafStructuredExtensionCore
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves

/-!
# Qualified target change for the presheaf extension

A target functor preserving the density colimits takes a Yoneda extension
to the extension of the transported interpretation. The comparison is
constructed from the left Kan extension property and is natural on all
maps. Preservation of limits, exponentials and images is not inferred.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Mettapedia.CategoryTheory.PresheafStructuredExtension

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe w u v u' v'
variable {C : Type} [Category C]
variable {D : Type u} [Category.{v} D]
variable {D' : Type u'} [Category.{v'} D']
variable [HasColimitsOfSize.{0, max w v v'} D]
variable [HasColimitsOfSize.{0, max w v v'} D']
variable (H : D ⥤ D') [PreservesColimitsOfSize.{0, max w v v'} H]

/-- The transported unit at the common presheaf universe. -/
def targetUnit (F : C ⥤ D) : F ⋙ H ≅
    embedding.{max w v, 0, 0, v'} ⋙
      ((embedding.{max w v', 0, 0, v} (C := C)).lan.obj F ⋙ H) :=
  Functor.isoWhiskerRight ((unitIso.{max w v', 0, 0, v, u}).app F) H ≪≫
    Functor.associator _ _ _

omit [HasColimitsOfSize.{0, max w v v'} D'] in
/-- Colimit preservation, exactly the extra qualification needed by density. -/
theorem targetExtension_cocontinuous (F : C ⥤ D) :
    PreservesColimitsOfSize.{0, max w v v'}
      ((embedding.{max w v', 0, 0, v} (C := C)).lan.obj F ⋙ H) := by
  have : PreservesColimitsOfSize.{0, max w v v'}
    ((embedding.{max w v', 0, 0, v} (C := C)).lan.obj F) :=
    extension_cocontinuous.{max w v', 0, 0, v, u} F
  infer_instance

omit [HasColimitsOfSize.{0, max w v v'} D'] in
/-- Actual target postcomposition of a left Kan extension is again a
Yoneda left Kan extension, derived from preserved density colimits. -/
theorem targetExtension_isLeftKan (F : C ⥤ D) :
    (((embedding.{max w v', 0, 0, v} (C := C)).lan.obj F) ⋙ H).IsLeftKanExtension
      (targetUnit.{w, u, v, u', v'} H F).hom := by
  have := targetExtension_cocontinuous.{w, u, v, u', v'} H F
  exact Presheaf.isLeftKanExtension_of_preservesColimits.{max w v, 0, v', 0, u'} _ (targetUnit.{w, u, v, u', v'} H F)

/-- The canonical comparison of the two actual left Kan extensions. -/
def targetExtensionIso (F : C ⥤ D) :
    ((embedding.{max w v', 0, 0, v} (C := C)).lan.obj F ⋙ H) ≅
      (embedding.{max w v, 0, 0, v'} (C := C)).lan.obj (F ⋙ H) := by
  have := targetExtension_isLeftKan.{w, u, v, u', v'} H F
  exact Functor.leftKanExtensionUnique _ (targetUnit.{w, u, v, u', v'} H F).hom _
    ((embedding.{max w v, 0, 0, v'} (C := C)).lanUnit.app (F ⋙ H))

/-- The target-change comparison commutes with the actual Yoneda unit. -/
theorem targetExtensionIso_fac (F : C ⥤ D) :
    (targetUnit.{w, u, v, u', v'} H F).hom ≫
      Functor.whiskerLeft embedding.{max w v, 0, 0, v'} (targetExtensionIso.{w, u, v, u', v'} H F).hom =
        (embedding.{max w v, 0, 0, v'} (C := C)).lanUnit.app (F ⋙ H) := by
  have := targetExtension_isLeftKan.{w, u, v, u', v'} H F
  simpa only [targetExtensionIso, Functor.leftKanExtensionUnique_hom] using
    Functor.descOfIsLeftKanExtension_fac
      ((embedding.{max w v', 0, 0, v} (C := C)).lan.obj F ⋙ H)
      (targetUnit.{w, u, v, u', v'} H F).hom
      ((embedding.{max w v, 0, 0, v'} (C := C)).lan.obj (F ⋙ H))
      ((embedding.{max w v, 0, 0, v'} (C := C)).lanUnit.app (F ⋙ H))

omit [HasColimitsOfSize.{0, max w v v'} D'] [PreservesColimitsOfSize.{0, max w v v'} H] in
/-- The transported extension unit is natural on arbitrary base maps. -/
theorem targetUnit_naturality {F G : C ⥤ D} (α : F ⟶ G) :
    (targetUnit.{w, u, v, u', v'} H F).hom ≫
      Functor.whiskerLeft embedding.{max w v, 0, 0, v'}
        (Functor.whiskerRight ((embedding.{max w v', 0, 0, v} (C := C)).lan.map α) H) =
      Functor.whiskerRight α H ≫ (targetUnit.{w, u, v, u', v'} H G).hom := by
  apply NatTrans.ext
  funext a
  dsimp [targetUnit, unitIso, restrict, extend]
  simp only [Category.comp_id]
  change H.map (((unitIso.{max w v', 0, 0, v, u}).app F).hom.app a) ≫
      H.map (((embedding.{max w v', 0, 0, v} (C := C)).lan.map α).app
        (embedding.{max w v', 0, 0, v}.obj a)) =
      H.map (α.app a) ≫ H.map (((unitIso.{max w v', 0, 0, v, u}).app G).hom.app a)
  rw [← H.map_comp, ← H.map_comp]
  exact congrArg H.map (NatTrans.congr_app
    ((unitIso.{max w v', 0, 0, v, u}).hom.naturality α) a).symm

/-- The target-change comparison is natural on all noninvertible maps. -/
theorem targetExtensionIso_naturality {F G : C ⥤ D} (α : F ⟶ G) :
    Functor.whiskerRight ((embedding.{max w v', 0, 0, v} (C := C)).lan.map α) H ≫
        (targetExtensionIso.{w, u, v, u', v'} H G).hom =
      (targetExtensionIso.{w, u, v, u', v'} H F).hom ≫
        (embedding.{max w v, 0, 0, v'} (C := C)).lan.map (Functor.whiskerRight α H) := by
  have := targetExtension_isLeftKan.{w, u, v, u', v'} H F
  apply Functor.hom_ext_of_isLeftKanExtension _ (targetUnit.{w, u, v, u', v'} H F).hom
  rw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp, ← Category.assoc,
    targetUnit_naturality.{w, u, v, u', v'} H α, Category.assoc,
    targetExtensionIso_fac.{w, u, v, u', v'} H G,
    ← Category.assoc, targetExtensionIso_fac.{w, u, v, u', v'} H F]
  exact (embedding.{max w v, 0, 0, v'} (C := C)).lanUnit.naturality (Functor.whiskerRight α H)

/-- The natural comparison of extending before and after qualified target change. -/
def targetExtensionNatIso :
    (embedding.{max w v', 0, 0, v} (C := C)).lan ⋙
        (Functor.whiskeringRight (Presheaves.{max w v', 0, 0, v} C) D D').obj H ≅
      (Functor.whiskeringRight C D D').obj H ⋙
        (embedding.{max w v, 0, 0, v'} (C := C)).lan :=
  NatIso.ofComponents (targetExtensionIso.{w, u, v, u', v'} H)
    (fun {_F _G} α => targetExtensionIso_naturality.{w, u, v, u', v'} H α)

end Mettapedia.CategoryTheory.PresheafStructuredExtension
