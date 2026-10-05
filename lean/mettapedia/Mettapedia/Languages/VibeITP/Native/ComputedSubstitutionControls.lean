import Mettapedia.Languages.VibeITP.Native.ComputedSubstitution

/-! # Computed Vibe substitution: binders, order, structural guards and overflow -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.ComputedSubstitutionControls

open Mettapedia.Languages.VibeITP.Spec
open Mettapedia.Languages.VibeITP.Native.ComputedSubstitution

private def signature : Sig := sigOf fun index =>
  if index = 0 then some { kind := .constant, binders := [1] } else none

/-- Vibe parameters are consumed in reverse de Bruijn order. -/
theorem reversed_parameter_order :
    run signature (.subst [.lit [1], .lit [2]] 0 (.bvar 0)) = some (.lit [2]) := by
  decide +kernel

/-- A replacement crossing one binder is shifted, preserving its reference. -/
theorem replacement_crosses_binder :
    run signature (.subst [.bvar 2] 0 (.app (.fresh 0) [.bvar 1])) =
      some (.app (.fresh 0) [.bvar 3]) := by
  decide +kernel

theorem captured_replacement_rejected :
    run signature (.subst [.bvar 2] 0 (.app (.fresh 0) [.bvar 1])) ≠
      some (.app (.fresh 0) [.bvar 2]) := by
  decide +kernel

theorem wrong_arity_refuses :
    run signature (.shift 0 0 (.app (.fresh 0) [])) = none := by
  decide +kernel

theorem unknown_symbol_refuses :
    run signature (.shift 0 0 (.app (.fresh 1) [])) = none := by
  decide +kernel

theorem shift_overflow_refuses :
    run signature (.shift 1 0 (.bvar (wordBound - 2))) = none := by
  decide +kernel

/-- Structural admission does not erase the original zero-shift early exit. -/
theorem zero_shift_preserves_unbounded_index :
    run signature (.shift 0 0 (.bvar (wordBound + 7))) =
      some (.bvar (wordBound + 7)) := by
  decide +kernel

theorem empty_top_substitution :
    run signature (.top [] (.app (.fresh 0) [.bvar 0])) =
      some (.app (.fresh 0) [.bvar 0]) := by
  decide +kernel

end Mettapedia.Languages.VibeITP.Native.ComputedSubstitutionControls
