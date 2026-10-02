import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.PartialConstants
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles

/-!
# The witness is necessary

Over the cumulative tower, `Π (X : U₀). X` is a closed type with no closed
inhabitant of the tower itself. Adding a constant at that type makes the type
inhabited, by the constant itself.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel

/-- `Π (X : U₀). X` over the cumulative tower. -/
def emptyType : Tm (LevelTower.Head Nat) 0 :=
  .pi (.head (.sort Tower.zero)) (.var 0)

theorem emptyType_typed :
    Typed (LevelTower.rules Nat) .nil emptyType
      (.head (.sort (LevelExpr.max (.succ Tower.zero) Tower.zero))) :=
  .piForm (.headType (.sort Tower.zero)) (.sort _) (.var 0) (.sort _)
    (.sorts (.succ Tower.zero) Tower.zero)

/-- Adding a constant at the empty type makes that type inhabited, by the
constant itself. -/
theorem emptyType_inhabited (c : DeclName) :
    Typed ((LevelTower.rules Nat).addConstant c emptyType) .nil (.const c) emptyType := by
  have formed := Typed.to_addConstant (c := c) (T := emptyType) rfl emptyType_typed
  have declared :
      ((LevelTower.rules Nat).addConstant c emptyType).constantType c = some emptyType := by
    simp only [Rules.addConstant, beq_self_eq_true, cond_true]
  have typedConst := Derivable.const (Γ := .nil) declared formed (.sort _)
  rw [Tm.liftClosed_at_zero] at typedConst
  exact typedConst

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
