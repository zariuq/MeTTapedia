import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentStrengthenedBraid
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentKnowledgeControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentExecutionBraidControls

/-!
# A nontrivial added equation through the actual three-event braid

Learning X = Ground restricts the original models. The observer can still
be extended through each helper pullback, so all six publication orders
remain admitted and form an actual strengthened three-cell.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.StrengtheningControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull.Controls TelescopeControls
open KnowledgeChange KnowledgeControls DependentRun.Controls

theorem triple_consistent : FinalConsistent ExecutionBraidControls.schedules.abc.run learned := by
  have one := helpers_keep_solvability (levels := setting.levels) pathHelpers learned learned_solvable
  have two := helpers_keep_solvability (levels := setting.levels) (pointHelpers.reindex pathHelpers.weaken)
    ((frames setting.levels).applyStore pathHelpers.weaken learned) one
  have three := helpers_keep_solvability (levels := setting.levels)
    (DependentRun.Controls.diamond.thirdForward DependentRun.Controls.third).helpers
    (transmitted DependentRun.Controls.diamond.forward learned) two
  change (frames setting.levels).Solvable
    (pushed (DependentRun.Controls.diamond.thirdForward DependentRun.Controls.third)
      (transmitted DependentRun.Controls.diamond.forward learned) ++
      ([] : EquationStore (TotalTerm (DependentRun.Controls.diamond.thirdForward DependentRun.Controls.third).helpers.frame)))
  simpa only [List.append_nil, pushed] using three

theorem strengthened_three_cell :
    (helperTransport setting.levels Nat).Cell (strengthen baseState learned)
      [KnowledgeChange.firing learned first, KnowledgeChange.firing learned second, KnowledgeChange.firing learned third] :=
  ExecutionBraid.strengthened_cell ExecutionBraidControls.actual_three_cell learned triple_consistent

theorem strengthened_full_braid :
    let schedules := strengthened_three_cell.six_schedules
    Transport.RunRearrangement.events (helperTransport setting.levels Nat) (ExecutionBraid.leftRoute schedules) =
      Transport.RunRearrangement.events (helperTransport setting.levels Nat) (ExecutionBraid.rightRoute schedules) ∧
      RunStateGroupoid.endpointMap setting.levels Nat (ExecutionBraid.leftRoute schedules) =
        RunStateGroupoid.endpointMap setting.levels Nat (ExecutionBraid.rightRoute schedules) :=
  ExecutionBraid.admitted_cell_braid strengthened_three_cell

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.StrengtheningControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.StrengtheningControls.strengthened_full_braid
