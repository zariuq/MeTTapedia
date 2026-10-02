import Mettapedia.GSLT.LanguageDef.Cost.BoundaryRestorationCollision
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RepeatedBoundaryValueControls

/-!
# A positional retained update invisible to current frame action

The existing repeated-input rho fixture supplies the actual static plan,
compiled children and positional replacement. Both complete forests inhabit
the existing semantic carrier, while the current frame action gives the
same raw endpoint. This is reachability by the public retained update API;
no authored runtime transition from input to zero is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RepeatedBoundaryStateAction
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Cost
open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted LanguageDefContinuedInteraction CostCanonicalLaws
open RepeatedBoundaryValueControls
open RetainedBoundaryOriginTransport

/-- The original frame state uses the already proved actual rho canonical path. -/
def state : CostStaticFrameState frame :=
  .original frame (rho_costStaticCanonicalPathSafe frame)

/-- The loss holds before or after any valid source-frame evolution. -/
theorem action_same (current : CostStaticFrameState frame) :
    (current.actAvailable mixedValues).pattern =
      (current.actAvailable uniformValues).pattern :=
  BoundaryRestorationCollision.actAvailable_eq_of_assignment_eq
    current mixedValues uniformValues assignment_same

/-- Initial restoration still returns the certified original repeated input. -/
theorem uniform_endpoint : (state.actAvailable uniformValues).pattern = originalPattern := by
  exact CostStaticFrameState.original_actAvailable_pattern frame
    (rho_costStaticCanonicalPathSafe frame)

/-- The second child has changed, yet the actual frame endpoint remains the original. -/
theorem updated_endpoint : (state.actAvailable mixedValues).pattern = originalPattern :=
  (action_same state).trans uniform_endpoint

/-- Both forests are accepted by the actual retained semantic constructor. -/
def originalTree : CostSemanticTree rhoCIGSLT FreeTypeContext.empty [] []
    originalPattern (.base (costBaseSortName "Proc")) :=
  (CostSemanticTree.static frame state uniformChildren).reindexPattern uniform_endpoint

/-- Use the public occurrence update, preserving the same frame and plan certificates. -/
def updatedTree : CostSemanticTree rhoCIGSLT FreeTypeContext.empty [] []
    originalPattern (.base (costBaseSortName "Proc")) :=
  (CostSemanticTree.static frame state
    (BoundaryOccurrenceValues.setTree frame.boundaryTable uniformValues uniformChildren
      secondSlot zeroValue zeroTree)).reindexPattern updated_endpoint

/-- The independently updated complete child forest distinguishes the states. -/
theorem update_retains_distinct_children :
    packedChildren
      (BoundaryOccurrenceValues.setTree frame.boundaryTable uniformValues uniformChildren
        secondSlot zeroValue zeroTree) ≠ packedChildren uniformChildren := by
  rw [positional_second_tree_update]
  exact retained_children_different

/-- The same loss persists when the current source representative is normalized. -/
theorem normalized_action_same :
    (state.normalize.actAvailable mixedValues).pattern =
      (state.normalize.actAvailable uniformValues).pattern :=
  action_same state.normalize

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RepeatedBoundaryStateAction
