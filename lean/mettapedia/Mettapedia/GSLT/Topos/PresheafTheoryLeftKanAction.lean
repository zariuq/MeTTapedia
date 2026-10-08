import Mettapedia.GSLT.Topos.PresheafTheoryKanAdjunctions
import Mathlib.CategoryTheory.Functor.Flat

/-!
# The separate covariant left Kan construction

For small finitely complete categories, a lex source functor has a lex
left Kan extension action on presheaves. This covariant construction is
distinct from the contravariant inverse image used for theory restriction.
Its colimits are preserved by its earned adjunction.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Topos.PresheafTheoryAction

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Core

universe u

variable {C D : Type u} [SmallCategory C] [SmallCategory D]

def covariantLeftKan (F : C ⥤ D) : (Cᵒᵖ ⥤ Type u) ⥤ (Dᵒᵖ ⥤ Type u) := F.op.lan

instance covariantLeftKan_preservesFiniteLimits [HasFiniteLimits C]
    (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteLimits (covariantLeftKan F) := by
  unfold covariantLeftKan
  infer_instance

instance covariantLeftKan_preservesColimits (F : C ⥤ D) :
    PreservesColimitsOfSize.{u,u} (covariantLeftKan F) :=
  (F.op.lanAdjunction (Type u)).leftAdjoint_preservesColimits

def covariantAdjunction (F : C ⥤ D) : covariantLeftKan F ⊣ inverseImage F :=
  F.op.lanAdjunction (Type u)

/-- The original source functor's lex property supplies the flatness
hypothesis of the actual Kan construction, without a preservation callback. -/
theorem theoryLeftKan_lex {source target : LambdaTheory.{u,u}}
    (F : LambdaTheoryMap source target) :
    PreservesFiniteLimits (covariantLeftKan F.functor) := inferInstance

end Mettapedia.GSLT.Topos.PresheafTheoryAction
