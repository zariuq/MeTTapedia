import Mettapedia.GSLT.LanguageDef.Cost.StaticTypeThinning
import Mettapedia.GSLT.LanguageDef.CostRegionTree

/-!
# Comparison with the original continued static binder interface

The old type decoder is the exact generic specialization. Binder insertion
is compared to the independently defined retained CIGSLT context action.
This file is intentionally downstream of the retained tree; the generic
definitions do not import it.
-/

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax StructuralMorphism

theorem CostStaticTypeImage.decode_cigslt (source : CIGSLT) (color : CostStaticColor)
    (type : TypeExpr) :
    decode source.theory color type = decodeCostStaticTypeExpr source color type := rfl

namespace CostStaticBinderThinning

/-- Only the theory index changes; retained and foreign positions are kept. -/
def toTheory {source : CIGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning source color sourceBound targetBound) :
    CostStaticTypeThinning source.theory color sourceBound targetBound :=
  match thinning with
  | .nil => .nil
  | .mapped type tail => by
      cases color <;> exact .mapped type (toTheory tail)
  | .foreign type rejected tail =>
      .foreign type (by simpa only [CostStaticTypeImage.decode_cigslt] using rejected) (toTheory tail)

theorem toTheory_toTargetIndex {source : CIGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning source color sourceBound targetBound) (index : Nat) :
    thinning.toTheory.toTargetIndex index = thinning.toTargetIndex index := by
  induction thinning generalizing index with
  | nil => rfl
  | mapped type tail ih =>
      cases color <;> cases index
      all_goals simp only [toTheory, toTargetIndex]
      all_goals first | rfl | exact congrArg (fun n => n + 1) (ih _)
  | foreign type rejected tail ih =>
      simp [toTheory, CostStaticTypeThinning.toTargetIndex, toTargetIndex, ih]

/-- The shared ambient action agrees with the independent old traversal. -/
theorem toTheory_rename_eq_thicken {source : CIGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning source color sourceBound targetBound)
    (depth : Nat) (pattern : Pattern) :
    ContextSubstitution.renameAmbientBVarsAt thinning.toTheory.toTargetIndex depth pattern =
      thinning.thickenAmbientBVars depth pattern := by
  rw [thinning.thickenAmbientBVars_eq_renameAmbientBVarsAt]
  have maps : thinning.toTheory.toTargetIndex = thinning.toTargetIndex :=
    funext thinning.toTheory_toTargetIndex
  rw [maps]

theorem sourceContextOfTarget_eq_theory (source : CIGSLT) (color : CostStaticColor)
    (targetBound : List TypeExpr) :
    sourceContextOfTarget source color targetBound =
      CostStaticTypeThinning.sourceContextOfTarget source.theory color targetBound := by
  induction targetBound with
  | nil => simp only [sourceContextOfTarget, CostStaticTypeThinning.sourceContextOfTarget]
  | cons type tail ih =>
      simp only [sourceContextOfTarget, CostStaticTypeThinning.sourceContextOfTarget,
        CostStaticTypeImage.decode_cigslt]
      cases decodeCostStaticTypeExpr source color type <;> simp only [ih]

end CostStaticBinderThinning
end Mettapedia.GSLT.LanguageDef
