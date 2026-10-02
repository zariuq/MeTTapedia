import Mettapedia.GSLT.LanguageDef.Cost.RegionPositionalRoundTrip
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RepeatedBoundaryPositionalRestoration

/-!
# General positional action on the repeated-input retained node

The independently checked concrete restoration is now an instance of the
class-wide action on actual retained source fibres. The original vector has
an exact round trip, while a real second-position update remains observable.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RepeatedBoundaryPositionalAction
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.Cost Mettapedia.OSLF.MeTTaIL.Syntax
open RepeatedBoundaryValueControls RetainedBoundaryGraftControls

/-- The general action instantiates to the independent mixed-value control. -/
theorem mixed_action : (frame.positionalActAvailable mixedValues).pattern =
    .collection .hashBag [inputPattern, zeroPattern] none := by
  rw [CostStaticRegionNode.positionalActAvailable_pattern,
    CostStaticBinderThinning.thickenAmbientBVars_eq_self_of_targetBound_eq_nil frame.thinning rfl]
  change (RepeatedBoundaryPositionalRestoration.restored mixedValues).1 = _
  exact RepeatedBoundaryPositionalRestoration.mixed_restored

theorem uniform_action : (frame.positionalActAvailable uniformValues).pattern = originalPattern := by
  rw [CostStaticRegionNode.positionalActAvailable_pattern,
    CostStaticBinderThinning.thickenAmbientBVars_eq_self_of_targetBound_eq_nil frame.thinning rfl]
  change (RepeatedBoundaryPositionalRestoration.restored uniformValues).1 = _
  exact RepeatedBoundaryPositionalRestoration.uniform_restored

/-- The class-wide original-vector inverse applies to this actual planner. -/
theorem original_action :
    (frame.positionalActAvailable (TypedCostRegionBoundaryTable.Values.original frame.boundaryTable)).pattern =
      originalPattern :=
  frame.positionalActAvailable_original

/-- Independent updates remain observable through the general typed action. -/
theorem public_second_update_distinguished :
    (frame.positionalActAvailable
      (BoundaryOccurrenceValues.set frame.boundaryTable uniformValues secondSlot zeroValue)).pattern ≠
      (frame.positionalActAvailable uniformValues).pattern := by
  rw [positional_second_update, mixed_action, uniform_action]
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RepeatedBoundaryPositionalAction
