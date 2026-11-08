import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualViewNaturality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceRelabeling

/-!
# Actual prepared problems commute with capture-interface transport

The occupied ledger and physical selection are fixed explicitly. Each rule,
take and read view uses its original computed scope. The full equation
problem and original guard rows transport together; no future equations or
new execution assumption enters this representation law.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPreparationNaturality

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualViewNaturality

variable {S : Signature} {Local Shared Next O : Type}
  (locals : Local → MetaArity S) {captures : Shared → MetaArity S} {next : Next → MetaArity S}
  (change : Assignment captures next) (occupied : Finset Nat) (selection : Selection O)
  {Γ : Ctx S} {sort : S.Srt}
  (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort))
  (rows : O → ContextualStoredRows.Row locals captures Γ sort)

theorem prepared_rule_transport :
    ((ContextualActivatedStep.prepared locals captures occupied selection rule rows).rule).map
        (instantiate (activeLift locals change)) =
      (ContextualActivatedStep.prepared locals next occupied selection
        (rule.map (instantiate (ContextualStoredRows.liftCaptures locals change)))
        (fun occurrence => (rows occurrence).map locals change)).rule := by
  change (rule.map (ContextualFreshening.termAt locals captures
      (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.rulePort selection)))).map _ = _
  rw [OccurrenceRelabeling.rule_map_comp]
  change rule.map _ = (rule.map (instantiate (ContextualStoredRows.liftCaptures locals change))).map _
  rw [OccurrenceRelabeling.rule_map_comp]
  apply congrArg (fun function => rule.map function)
  funext value
  exact termAt_transport locals change _ value

theorem prepared_take_transport (port : Fin selection.taken.length) :
    instantiate (activeLift locals change)
        ((ContextualActivatedStep.prepared locals captures occupied selection rule rows).taken port) =
      (ContextualActivatedStep.prepared locals next occupied selection
        (rule.map (instantiate (ContextualStoredRows.liftCaptures locals change)))
        (fun occurrence => (rows occurrence).map locals change)).taken port := by
  rw [ContextualActivatedStep.prepared_taken_view, ContextualActivatedStep.prepared_taken_view]
  exact viewAt_transport locals change _ _

theorem prepared_read_transport (port : Fin selection.read.length) :
    instantiate (activeLift locals change)
        ((ContextualActivatedStep.prepared locals captures occupied selection rule rows).read port) =
      (ContextualActivatedStep.prepared locals next occupied selection
        (rule.map (instantiate (ContextualStoredRows.liftCaptures locals change)))
        (fun occurrence => (rows occurrence).map locals change)).read port := by
  rw [ContextualActivatedStep.prepared_read_view, ContextualActivatedStep.prepared_read_view]
  exact viewAt_transport locals change _ _

theorem framed_equations_transport (before : Configuration (Term (signature S captures) Γ sort) O) :
    ContextualFrameUnifier.mapProblem (activeLift locals change) (ContextualActivatedStep.frame locals captures before).equations =
      (ContextualActivatedStep.frame locals next (ContextualTransportedActivation.configurationMap change before)).equations := by
  change ContextualFrameUnifier.mapProblem (activeLift locals change)
      (ContextualFrameUnifier.mapProblem (ContextualSelectionViews.capturedTarget locals captures) before.equations) =
    ContextualFrameUnifier.mapProblem (ContextualSelectionViews.capturedTarget locals next)
      (ContextualFrameUnifier.mapProblem change before.equations)
  rw [ContextualComputedFreshFrame.map_compose, ContextualComputedFreshFrame.map_compose, capture_square]

theorem problem_transport (before : Configuration (Term (signature S captures) Γ sort) O) :
    ContextualFrameUnifier.mapProblem (activeLift locals change)
        (ContextualActivatedStep.problem locals captures occupied selection rule rows before) =
      ContextualActivatedStep.problem locals next occupied selection
        (rule.map (instantiate (ContextualStoredRows.liftCaptures locals change)))
        (fun occurrence => (rows occurrence).map locals change)
        (ContextualTransportedActivation.configurationMap change before) := by
  have mappedRule := prepared_rule_transport locals change occupied selection rule rows
  have takes := congrArg RuleInstance.take mappedRule
  have reads := congrArg RuleInstance.read mappedRule
  have tells := congrArg RuleInstance.tell mappedRule
  dsimp only [RuleInstance.map] at takes reads tells
  change ContextualFrameUnifier.mapProblem (activeLift locals change)
      (ContextualActivatedStep.prepared locals captures occupied selection rule rows).rule.tell =
    (ContextualActivatedStep.prepared locals next occupied selection
      (rule.map (instantiate (ContextualStoredRows.liftCaptures locals change)))
      (fun occurrence => (rows occurrence).map locals change)).rule.tell at tells
  have takenViews :
      (List.ofFn (ContextualActivatedStep.prepared locals captures occupied selection rule rows).taken).map
          (instantiate (activeLift locals change)) =
        List.ofFn (ContextualActivatedStep.prepared locals next occupied selection
          (rule.map (instantiate (ContextualStoredRows.liftCaptures locals change)))
          (fun occurrence => (rows occurrence).map locals change)).taken := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext port
    exact prepared_take_transport locals change occupied selection rule rows port
  have readViews :
      (List.ofFn (ContextualActivatedStep.prepared locals captures occupied selection rule rows).read).map
          (instantiate (activeLift locals change)) =
        List.ofFn (ContextualActivatedStep.prepared locals next occupied selection
          (rule.map (instantiate (ContextualStoredRows.liftCaptures locals change)))
          (fun occurrence => (rows occurrence).map locals change)).read := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext port
    exact prepared_read_transport locals change occupied selection rule rows port
  simp only [ContextualActivatedStep.problem, ContextualTransportedActivation.map_append,
    ContextualTransportedActivation.map_useEquations, framed_equations_transport, takes, reads,
    tells, takenViews, readViews]
  rfl

/-- The equations contributed by the event transport independently of the
incoming store, with every selected view at its original scope. -/
theorem added_equations_transport :
    ContextualFrameUnifier.mapProblem (activeLift locals change)
        (ContextualActivatedStep.addedEquations locals captures occupied selection rule rows) =
      ContextualActivatedStep.addedEquations locals next occupied selection
        (rule.map (instantiate (ContextualStoredRows.liftCaptures locals change)))
        (fun occurrence => (rows occurrence).map locals change) := by
  have transported := problem_transport locals change occupied selection rule rows ⟨[], ∅⟩
  simpa only [ContextualActivatedStep.problem_eq_frame_append,
    ContextualActivatedStep.frame, ContextualTransportedActivation.configurationMap,
    ContextualFrameUnifier.mapProblem, List.map_nil, List.nil_append] using transported

theorem ask_forward (before : Configuration (Term (signature S captures) Γ sort) O)
    (check : Check (Term (signature S (ContextualActivatedStep.target locals captures)) Γ sort))
    (asked : ContextualGuardSemantics.Ask locals
      (ContextualActivatedStep.problem locals captures occupied selection rule rows before)
      (ContextualGuardedStep.guardRows locals captures rows) before.present check) :
    ContextualGuardSemantics.Ask locals
      (ContextualActivatedStep.problem locals next occupied selection
        (rule.map (instantiate (ContextualStoredRows.liftCaptures locals change)))
        (fun occurrence => (rows occurrence).map locals change)
        (ContextualTransportedActivation.configurationMap change before))
      (ContextualGuardedStep.guardRows locals next (fun occurrence => (rows occurrence).map locals change)) before.present
      (check.map (instantiate (activeLift locals change))) := by
  have transported := asked.transport locals (activeLift locals change)
  rw [problem_transport locals change occupied selection rule rows before, guardRows_transport] at transported
  exact transported

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPreparationNaturality
