import Mettapedia.OSLF.Framework.Mode2Skeleton
import Mettapedia.OSLF.Framework.LanguageEqCategory

/-!
# ModeMapPredCommutingSquares

Theorem-level commuting-square statements connecting:
- `Mode2Skeleton.ModeHom.mapPred`
- `LanguageEqCategory.mapPred`

for runtime/runtime and runtime/behavioral edges.
-/

namespace Mettapedia.OSLF.Framework.ModeMapPredCommutingSquares

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.LanguageEqCategory
open Mettapedia.OSLF.Framework.Mode2Skeleton

/-- Runtime/runtime square:
mode-level pullback along `runtimeMap (f ≫ g)` agrees with category pullback. -/
theorem runtime_runtime_square
    {L₁ L₂ L₃ : Obj}
    (f : Hom L₁ L₂) (g : Hom L₂ L₃)
    (ψ : Pattern → Prop) :
    ModeHom.mapPred (ModeHom.runtimeMap (comp f g)) ψ =
      mapPred (comp f g) ψ := by
  rfl

/-- Runtime/runtime square, expanded as composition equality. -/
theorem runtime_runtime_square_comp
    {L₁ L₂ L₃ : Obj}
    (f : Hom L₁ L₂) (g : Hom L₂ L₃)
    (ψ : Pattern → Prop) :
    ModeHom.mapPred (ModeHom.runtimeMap (comp f g)) ψ =
      ModeHom.mapPred (ModeHom.runtimeMap f)
        (ModeHom.mapPred (ModeHom.runtimeMap g) ψ) := by
  calc
    ModeHom.mapPred (ModeHom.runtimeMap (comp f g)) ψ
        = mapPred (comp f g) ψ := by rfl
    _ = mapPred f (mapPred g ψ) := by
          exact mapPred_comp f g ψ
    _ = ModeHom.mapPred (ModeHom.runtimeMap f)
          (ModeHom.mapPred (ModeHom.runtimeMap g) ψ) := by
          rfl

/-- Runtime/behavioral square:
mode-level pullback along `runtimeToBehavioral (f ≫ g)` agrees with category pullback. -/
theorem runtime_behavioral_square
    {L₁ L₂ L₃ : Obj}
    (f : Hom L₁ L₂) (g : Hom L₂ L₃)
    (ψ : Pattern → Prop) :
    ModeHom.mapPred (ModeHom.runtimeToBehavioral (comp f g)) ψ =
      mapPred (comp f g) ψ := by
  rfl

/-- Runtime/behavioral square, expanded as composition equality. -/
theorem runtime_behavioral_square_comp
    {L₁ L₂ L₃ : Obj}
    (f : Hom L₁ L₂) (g : Hom L₂ L₃)
    (ψ : Pattern → Prop) :
    ModeHom.mapPred (ModeHom.runtimeToBehavioral (comp f g)) ψ =
      ModeHom.mapPred (ModeHom.runtimeMap f)
        (ModeHom.mapPred (ModeHom.runtimeToBehavioral g) ψ) := by
  calc
    ModeHom.mapPred (ModeHom.runtimeToBehavioral (comp f g)) ψ
        = mapPred (comp f g) ψ := by rfl
    _ = mapPred f (mapPred g ψ) := by
          exact mapPred_comp f g ψ
    _ = ModeHom.mapPred (ModeHom.runtimeMap f)
          (ModeHom.mapPred (ModeHom.runtimeToBehavioral g) ψ) := by
          rfl

/-- Single bundled theorem exposing both commuting-square families. -/
theorem mapPred_commuting_squares_bundle
    {L₁ L₂ L₃ : Obj}
    (f : Hom L₁ L₂) (g : Hom L₂ L₃)
    (ψ : Pattern → Prop) :
    ModeHom.mapPred (ModeHom.runtimeMap (comp f g)) ψ =
      mapPred (comp f g) ψ
    ∧
    ModeHom.mapPred (ModeHom.runtimeToBehavioral (comp f g)) ψ =
      mapPred (comp f g) ψ
    ∧
    ModeHom.mapPred (ModeHom.runtimeMap (comp f g)) ψ =
      ModeHom.mapPred (ModeHom.runtimeMap f)
        (ModeHom.mapPred (ModeHom.runtimeMap g) ψ)
    ∧
    ModeHom.mapPred (ModeHom.runtimeToBehavioral (comp f g)) ψ =
      ModeHom.mapPred (ModeHom.runtimeMap f)
        (ModeHom.mapPred (ModeHom.runtimeToBehavioral g) ψ) := by
  exact ⟨runtime_runtime_square f g ψ, runtime_behavioral_square f g ψ,
    runtime_runtime_square_comp f g ψ, runtime_behavioral_square_comp f g ψ⟩

end Mettapedia.OSLF.Framework.ModeMapPredCommutingSquares

