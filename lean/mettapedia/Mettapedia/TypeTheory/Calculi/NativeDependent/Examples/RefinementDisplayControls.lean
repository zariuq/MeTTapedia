import Mettapedia.TypeTheory.ContextualPredicateRefinementDisplayPreservation
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.RefinementContextualRefinementControls

/-!
# Retained values and erased base readings of actual refined displays

Two independently distinguished generated proposition values satisfy the
same refinement guard. Their complete display arrows and their forgotten
ambient display arrows remain distinct. Their base projections coincide,
showing why the base context alone cannot replace the retained data reading.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.RefinementDisplayControls

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateRefinementDisplay
open ContextualTypeOperations
open ContextualProductComparison (selfExtend)

noncomputable abbrev C := QuotientCwf.cwf Controls.signature
noncomputable abbrev operations := RefinementModel.operations Controls.signature
noncomputable abbrev refined := operations.refined RefinementControls.domain RefinementControls.selected

noncomputable def truthArrow : C.Sub RefinementControls.qcontext (C.ext RefinementControls.qcontext refined) :=
  selfExtend C RefinementControls.refinedTruth

noncomputable def falseArrow : C.Sub RefinementControls.qcontext (C.ext RefinementControls.qcontext refined) :=
  selfExtend C RefinementControls.refinedFalse

theorem supplied_display_arrows_remain_distinct : truthArrow ≠ falseArrow := by
  intro same
  have variablesRead : HEq (C.tmSub (C.vz refined) truthArrow)
      (C.tmSub (C.vz refined) falseArrow) := by rw [same]
  have values := (vz_selfExtend (C := C) (context := RefinementControls.qcontext)
    (type := refined) RefinementControls.refinedTruth).symm.trans
    (variablesRead.trans (vz_selfExtend (C := C) (context := RefinementControls.qcontext)
      (type := refined) RefinementControls.refinedFalse))
  exact RefinementControls.selected_values_remain_distinct (eq_of_heq values)

theorem forgetting_retains_the_distinct_supplied_values :
    C.compS (forgetDisplay operations RefinementControls.domain RefinementControls.selected) truthArrow ≠
      C.compS (forgetDisplay operations RefinementControls.domain RefinementControls.selected) falseArrow :=
  fun same => supplied_display_arrows_remain_distinct
    (forgetDisplay_monic operations RefinementControls.domain RefinementControls.selected same)

theorem true_underlying_readout :
    HEq (C.tmSub (C.vz RefinementControls.domain)
      (C.compS (forgetDisplay operations RefinementControls.domain RefinementControls.selected) truthArrow))
      (operations.forget
        (C.tySub RefinementControls.domain (C.compS (C.wk refined) truthArrow))
        ((predicateDoctrine Controls.signature).reindex
          (TypeOver.extensionSubstitution (C.compS (C.wk refined) truthArrow) RefinementControls.domain)
          RefinementControls.selected)
        (refinedRead operations RefinementControls.domain RefinementControls.selected truthArrow)) :=
  forgetDisplay_readout operations RefinementControls.domain RefinementControls.selected truthArrow

/-- Equal base readings erase actual distinct refined data; the complete
forgetting display therefore cannot be replaced by its base projection. -/
theorem base_projection_erases_the_supplied_values :
    C.compS (C.wk refined) truthArrow = C.compS (C.wk refined) falseArrow ∧ truthArrow ≠ falseArrow := by
  constructor
  · exact (wk_selfExtend (C := C) (context := RefinementControls.qcontext)
      (type := refined) RefinementControls.refinedTruth).trans
      (wk_selfExtend (C := C) (context := RefinementControls.qcontext)
        (type := refined) RefinementControls.refinedFalse).symm
  · exact supplied_display_arrows_remain_distinct

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.RefinementDisplayControls
