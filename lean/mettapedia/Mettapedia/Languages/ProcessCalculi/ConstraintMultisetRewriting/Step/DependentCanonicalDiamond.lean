import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentRunRearrangement

/-!
# The canonical helper diamond from both admitted orders

The existing helper-closing calculation gives agreement along the actual
block exchange. Retaining that conclusion exposes the provenance map needed
by execution coherence. No additional no-query or query-blindness condition
is imposed: both actual orders are the premises.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O]

theorem canonical_helper_agreement {s : State rules O} (f g : HelperFiring levels O s)
    (first : (helperStep levels O).Admits f) (second : (helperStep levels O).Admits g)
    (afterFirst : (helperStep levels O).Admits (helperResidual f first g))
    (afterSecond : (helperStep levels O).Admits (helperResidual g second f)) :
    Local.AgreeAlong (levels := levels) (exchange f.helpers g.helpers)
      ((helperStep levels O).result (helperResidual f first g) afterFirst).toLocal
      ((helperStep levels O).result (helperResidual g second f) afterSecond).toLocal := by
  obtain ⟨H₁, d₁⟩ := f
  obtain ⟨H₂, d₂⟩ := g
  have localFirst := (Natural.admits_withHelpers H₁ d₁).mp first
  have localSecond := (Natural.admits_withHelpers H₂ d₂).mp second
  have typedF := (Natural.shapes_move (H₂.reindex H₁.weaken).weaken d₁ localFirst.1).2.2.2.2
  have typedG := (Natural.shapes_move (Helpers.lift H₁.weaken H₂) d₂ localSecond.1).2.2.2.2
  -- the state after each firing, read at the common frame
  have stateOne : ((Natural.withHelpers H₁ d₁).after first).toLocal.move (H₂.reindex H₁.weaken).weaken =
      (d₁.move (H₂.reindex H₁.weaken).weaken).toPlain.after (jointState H₁ H₂) typedF :=
    (congrArg (Local.move (H₂.reindex H₁.weaken).weaken) (Natural.toLocal_after_withHelpers H₁ d₁ first)).trans
      ((Natural.after_move (H₂.reindex H₁.weaken).weaken d₁ (s.toLocal.move H₁.weaken) localFirst.1.2.2.2.2
        typedF).symm.trans (Plain.after_congr rfl (telescope_state_first H₁ H₂) _ _))
  have stateTwo : ((Natural.withHelpers H₂ d₂).after second).toLocal.move (Helpers.lift H₁.weaken H₂) =
      (d₂.move (Helpers.lift H₁.weaken H₂)).toPlain.after (jointState H₁ H₂) typedG :=
    (congrArg (Local.move (Helpers.lift H₁.weaken H₂)) (Natural.toLocal_after_withHelpers H₂ d₂ second)).trans
      ((Natural.after_move (Helpers.lift H₁.weaken H₂) d₂ (s.toLocal.move H₂.weaken) localSecond.1.2.2.2.2
        typedG).symm.trans (Plain.after_congr rfl (telescope_state_second H₁ H₂) _ _))
  have backFirst : (d₁.move (Helpers.lift H₂.weaken H₁)).move (exchange H₁ H₂) =
      d₁.move (H₂.reindex H₁.weaken).weaken := by
    rw [Natural.move_comp, exchange_lift]
  have backState : (((Natural.withHelpers H₂ d₂).after second).toLocal.move
        (H₁.reindex H₂.weaken).weaken).move (exchange H₁ H₂) =
      (d₂.move (Helpers.lift H₁.weaken H₂)).toPlain.after (jointState H₁ H₂) typedG :=
    (Local.move_comp (H₁.reindex H₂.weaken).weaken (exchange H₁ H₂)
      ((Natural.withHelpers H₂ d₂).after second).toLocal).trans
      ((congrArg (fun σ => Local.move σ ((Natural.withHelpers H₂ d₂).after second).toLocal)
        (exchange_weaken H₁ H₂)).trans stateTwo)
  -- each order is admitted at the common frame
  have gAfterF : (d₂.move (Helpers.lift H₁.weaken H₂)).toPlain.Admits
      ((d₁.move (H₂.reindex H₁.weaken).weaken).toPlain.after (jointState H₁ H₂) typedF) :=
    (Plain.admits_congr rfl stateOne).mp
      ((Natural.admits_withHelpers (s := (Natural.withHelpers H₁ d₁).after first) (H₂.reindex H₁.weaken)
        (d₂.move (Helpers.lift H₁.weaken H₂))).mp afterFirst)
  have fAfterG : (d₁.move (H₂.reindex H₁.weaken).weaken).toPlain.Admits
      ((d₂.move (Helpers.lift H₁.weaken H₂)).toPlain.after (jointState H₁ H₂) typedG) :=
    (Plain.admits_congr (congrArg Natural.toPlain backFirst) backState).mp
      ((Natural.admits_move_iff (d₁.move (Helpers.lift H₂.weaken H₁)) (exchangeIso H₁ H₂) _).mpr
        ((Natural.admits_withHelpers (s := (Natural.withHelpers H₂ d₂).after second) (H₁.reindex H₂.weaken)
          (d₁.move (Helpers.lift H₂.weaken H₁))).mp afterSecond))
  have admitF : (d₁.move (H₂.reindex H₁.weaken).weaken).toPlain.Admits (jointState H₁ H₂) := by
    have moved := Natural.admits_move (H₂.reindex H₁.weaken).weaken d₁ localFirst (by
      rw [← Natural.information_move, telescope_state_first]
      exact Frames.solvable_of_subset (fun e member => List.mem_append_left _ member) gAfterF.2.2.1)
    exact (Plain.admits_congr rfl (telescope_state_first H₁ H₂)).mp moved
  have admitG : (d₂.move (Helpers.lift H₁.weaken H₂)).toPlain.Admits (jointState H₁ H₂) := by
    have moved := Natural.admits_move (Helpers.lift H₁.weaken H₂) d₂ localSecond (by
      rw [← Natural.information_move, telescope_state_second]
      exact Frames.solvable_of_subset (fun e member => List.mem_append_left _ member) fAfterG.2.2.1)
    exact (Plain.admits_congr rfl (telescope_state_second H₁ H₂)).mp moved
  obtain ⟨knowledge, present, label⟩ := agree_of_residuals admitF admitG gAfterF fAfterG
  -- the two composites, read at the common frame
  have one : ((Natural.residualHelpers d₁ d₂ first).after afterFirst).toLocal =
      (d₂.move (Helpers.lift H₁.weaken H₂)).toPlain.after
        ((d₁.move (H₂.reindex H₁.weaken).weaken).toPlain.after (jointState H₁ H₂) typedF) typedG :=
    (Natural.toLocal_after_withHelpers (s := (Natural.withHelpers H₁ d₁).after first) (H₂.reindex H₁.weaken)
      (d₂.move (Helpers.lift H₁.weaken H₂)) afterFirst).trans (Plain.after_congr rfl stateOne _ _)
  have two : ((Natural.residualHelpers d₂ d₁ second).after afterSecond).toLocal.move (exchange H₁ H₂) =
      (d₁.move (H₂.reindex H₁.weaken).weaken).toPlain.after
        ((d₂.move (Helpers.lift H₁.weaken H₂)).toPlain.after (jointState H₁ H₂) typedG) typedF :=
    (congrArg (Local.move (exchange H₁ H₂))
      (Natural.toLocal_after_withHelpers (s := (Natural.withHelpers H₂ d₂).after second) (H₁.reindex H₂.weaken)
        (d₁.move (Helpers.lift H₂.weaken H₁)) afterSecond)).trans
      ((Natural.after_move (exchange H₁ H₂) (d₁.move (Helpers.lift H₂.weaken H₁)) _ afterSecond.1.2.2.2.2
        (Natural.shapes_move (exchange H₁ H₂) (d₁.move (Helpers.lift H₂.weaken H₁)) afterSecond.1).2.2.2.2).symm.trans
        (Plain.after_congr (congrArg Natural.toPlain backFirst) backState _ _))
  have agree : Local.AgreeAlong (levels := levels) (exchange H₁ H₂)
      ((Natural.residualHelpers d₁ d₂ first).after afterFirst).toLocal
      ((Natural.residualHelpers d₂ d₁ second).after afterSecond).toLocal := by
    unfold Local.AgreeAlong
    rw [one, two]
    exact ⟨knowledge, present, label⟩
  exact agree


namespace DependentRun

theorem diamond_of_admitted_orders {state : State rules O} (first second : HelperFiring levels O state)
    (accepted : (helperStep levels O).Admits first) (accepted' : (helperStep levels O).Admits second)
    (afterFirst : (helperStep levels O).Admits (helperResidual first accepted second))
    (afterSecond : (helperStep levels O).Admits (helperResidual second accepted' first)) :
    Diamond first second accepted accepted' :=
  ⟨afterFirst, afterSecond, canonical_helper_agreement first second accepted accepted' afterFirst afterSecond⟩

end DependentRun

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.canonical_helper_agreement
