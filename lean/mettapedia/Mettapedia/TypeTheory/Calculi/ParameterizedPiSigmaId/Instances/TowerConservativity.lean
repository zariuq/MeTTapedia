import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.Tower
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Conservativity

/-!
# Conservativity in the cumulative tower

The cumulative tower has no root computations, so its untyped conversion is
Church–Rosser, and the map from formation-sensitive typing to the typed equality
holds without hypotheses.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

/-! ## The tower -/

section Tower

open TowerModel

theorem LevelTower.churchRosser : ConversionCoherence.ChurchRosser Tower.rules :=
  EmptyRootConversion.churchRosser Tower.rules rfl
    ⟨fun _ _ same => (levels fun _ => 0).headEq_symm same⟩

/-- In the tower, convertible typed terms are equal. -/
theorem Tower.conv_toEqual {n : Nat} {Γ : Ctx Tower.Head n} (formed : CtxFormed Tower.rules Γ)
    {a b T : Tm Tower.Head n} (conversion : Conv Tower.rules.headEq a b Tower.rules.computation)
    (ta : Typed Tower.rules Γ a T) (tb : Typed Tower.rules Γ b T) :
    Equal Tower.rules Γ a b T :=
  Conv.toEqual (S := setting fun _ => 0) facts roots heads LevelTower.churchRosser
    formed conversion ta tb

/-- In the tower, every formation-sensitive typing derivation in a formed
context is a typing derivation of the typed equality. -/
theorem Tower.formationSensitive_toTyped {n : Nat} {Γ : Ctx Tower.Head n}
    {t A : Tm Tower.Head n} (typing : FormationSensitive.Typing Tower.rules Γ t A)
    (formed : CtxFormed Tower.rules Γ) : Typed Tower.rules Γ t A :=
  FormationSensitive.Typing.toTyped (S := setting fun _ => 0) facts roots heads
    LevelTower.churchRosser typing formed

end Tower

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
