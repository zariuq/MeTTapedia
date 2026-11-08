import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommonEventProblems
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualInteractionFactors
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionPaths
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchedulePromotion
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Exactness

/-!
# Common scoped event data construct original admissions and actual returns

Physical port conditions, common output shape and original all-future asks
construct an Admission in the actual activation frame. A common model then
excludes a computed refutation. The existing structural-pattern termination
theorem supplies a completed actual worklist return in its stated fragment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommonEventExecution

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ContextualEventViewRelocation

variable {S : Signature} {Local Shared O Future : Type} {n : Nat} [DecidableEq O]
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
  {selections : Fin n → Selection O} (localLedger globalLedger : Finset Nat) (event : Fin n)
  (permutation : Equiv.Perm Nat)
  (aligned : ∀ port : ContextualActivationScopes.Port (selections event),
    permutation (ContextualActivationScopes.scopeAt localLedger port) =
      ContextualEventViewScopes.scope selections globalLedger ⟨event, port⟩)
  {Γ : Ctx S} {sort : S.Srt}
  (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
  (rows : O → ContextualStoredRows.Row locals captures Γ sort)
  (before : Configuration (Term (signature S captures) Γ sort) O)
  (outputs : O → Term (signature S (ContextualSelectionViews.target locals captures)) Γ sort)

def pullOutputs : O → Term (signature S (ContextualSelectionViews.target locals captures)) Γ sort :=
  fun occurrence => instantiate (assignment locals captures permutation.symm) (outputs occurrence)

include aligned

theorem admission_from_common
    (takeDistinct : (selections event).taken.Nodup) (madeDistinct : (selections event).made.Nodup)
    (takeLength : rule.take.length = (selections event).taken.length)
    (readLength : rule.read.length = (selections event).read.length)
    (outputShape : (selections event).made.map outputs =
      (ContextualEventViewScopes.prepared locals captures selections globalLedger event rule rows).rule.produce)
    (takeAvailable : (selections event).taken.toFinset ⊆ before.present)
    (readAvailable : (selections event).read.toFinset ⊆ before.present)
    (takeReadApart : Disjoint (selections event).taken.toFinset (selections event).read.toFinset)
    (fresh : Disjoint (selections event).made.toFinset before.present)
    (checks : ∀ check ∈ (ContextualEventViewScopes.prepared locals captures selections globalLedger event rule rows).rule.checks,
      ContextualGuardSemantics.Ask locals
        (ContextualCommonEventProblems.problem locals captures selections globalLedger event rule rows before)
        (ContextualGuardedStep.guardRows locals captures rows) before.present check) :
    ContextualGuardedStep.Requirements locals captures localLedger (selections event) rule rows before
      (pullOutputs locals captures permutation outputs) := by
  have mappedRule := prepared_rule_relocated locals captures localLedger globalLedger event permutation aligned rule rows
  have restoredRule :
      (ContextualEventViewScopes.prepared locals captures selections globalLedger event rule rows).rule.map
          (instantiate (assignment locals captures permutation.symm)) =
        (ContextualActivatedStep.prepared locals captures localLedger (selections event) rule rows).rule := by
    rw [← mappedRule, OccurrenceRelabeling.rule_map_comp]
    have inverse : (instantiate (assignment locals captures permutation.symm) ∘
        instantiate (assignment locals captures permutation)) =
        (id : Term (signature S (ContextualSelectionViews.target locals captures)) Γ sort → _) := by
      funext value
      exact instantiate_reindex_inverse _ _ _ _ (names_left_inverse permutation) value
    rw [inverse]
    have checkIdentity : Check.map (id : Term (signature S (ContextualSelectionViews.target locals captures)) Γ sort → _) = id := by
      funext check
      cases check <;> rfl
    have pairIdentity : (fun pair : Term (signature S (ContextualSelectionViews.target locals captures)) Γ sort ×
        Term (signature S (ContextualSelectionViews.target locals captures)) Γ sort => (id pair.1, id pair.2)) = id := rfl
    cases (ContextualActivatedStep.prepared locals captures localLedger (selections event) rule rows).rule
    simp only [RuleInstance.map, pairIdentity, checkIdentity, List.map_id]
  refine ⟨takeDistinct, madeDistinct, takeLength, readLength, ?_,
    ⟨takeAvailable, readAvailable, takeReadApart, fresh, fun query member => by cases member⟩, ?_⟩
  · have restoredOutputs := congrArg (List.map (instantiate (assignment locals captures permutation.symm))) outputShape
    have produced := congrArg RuleInstance.produce restoredRule
    exact (List.map_map ..).symm.trans (restoredOutputs.trans produced)
  · intro check member
    have mappedChecks := congrArg RuleInstance.checks mappedRule
    have commonMember : check.map (instantiate (assignment locals captures permutation)) ∈
        (ContextualEventViewScopes.prepared locals captures selections globalLedger event rule rows).rule.checks := by
      rw [← mappedChecks]
      exact List.mem_map.mpr ⟨check, member, rfl⟩
    exact (ContextualCommonEventProblems.original_ask_relocated_iff locals captures localLedger globalLedger event
      permutation aligned rule rows before check).mp (checks _ commonMember)

variable [DecidableEq Local] [DecidableEq Shared] [DecidableEq S.Srt]
  [∀ result, DecidableEq (S.Op result)]

theorem actual_return_from_common
    (takeDistinct : (selections event).taken.Nodup) (madeDistinct : (selections event).made.Nodup)
    (takeLength : rule.take.length = (selections event).taken.length)
    (readLength : rule.read.length = (selections event).read.length)
    (outputShape : (selections event).made.map outputs =
      (ContextualEventViewScopes.prepared locals captures selections globalLedger event rule rows).rule.produce)
    (takeAvailable : (selections event).taken.toFinset ⊆ before.present)
    (readAvailable : (selections event).read.toFinset ⊆ before.present)
    (takeReadApart : Disjoint (selections event).taken.toFinset (selections event).read.toFinset)
    (fresh : Disjoint (selections event).made.toFinset before.present)
    (checks : ∀ check ∈ (ContextualEventViewScopes.prepared locals captures selections globalLedger event rule rows).rule.checks,
      ContextualGuardSemantics.Ask locals
        (ContextualCommonEventProblems.problem locals captures selections globalLedger event rule rows before)
        (ContextualGuardedStep.guardRows locals captures rows) before.present check)
    (patterned : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals captures localLedger (selections event) rule rows before)))
    {future : Future → MetaArity S}
    (candidate : Assignment (ContextualSelectionViews.target locals captures) future)
    (model : ContextualFrameUnifier.Models candidate
      (ContextualCommonEventProblems.problem locals captures selections globalLedger event rule rows before)) :
    ∃ fuel update, ContextualTransportedActivation.FromRun locals captures fuel localLedger (selections event)
      rule rows before (pullOutputs locals captures permutation outputs) update := by
  have admitted := admission_from_common locals captures localLedger globalLedger event permutation aligned
    rule rows before outputs takeDistinct madeDistinct takeLength readLength outputShape takeAvailable readAvailable
    takeReadApart fresh checks
  have sourceModel := (ContextualCommonEventProblems.models_relocated locals captures localLedger globalLedger event
    permutation aligned candidate rule rows before).mp model
  obtain ⟨fuel, solved | refused⟩ := ContextualTransportedActivation.solve_or_refute locals captures admitted patterned
  · obtain ⟨update, returned⟩ := solved
    exact ⟨fuel, update, returned⟩
  · obtain ⟨impossible, _computed⟩ := refused
    exact False.elim (impossible future (Assignment.compose candidate (assignment locals captures permutation))
      ((ContextualResidual.models_observeProblem _ _).mpr sourceModel))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommonEventExecution

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairFrames

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {Local Shared O : Type} [DecidableEq O]
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
  (virtualLedger actualLedger : Finset Nat) (firstSelection secondSelection : Selection O)
  (relocation : Equiv.Perm Nat)
  (aligned : ∀ port : ContextualActivationScopes.Port secondSelection,
    relocation (ContextualActivationScopes.scopeAt virtualLedger port) = ContextualActivationScopes.scopeAt actualLedger port)
  {Γ : Ctx S} {sort : S.Srt}
  (firstRule secondRule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
  (rows : O → ContextualStoredRows.Row locals captures Γ sort)
  (before : Configuration (Term (signature S captures) Γ sort) O)
  (firstOutputs secondOutputs : O → Term (signature S (ContextualSelectionViews.target locals captures)) Γ sort)
  (update : ContextualFrameUpdate.Update (ContextualResidual.observeProblem
    (ContextualActivatedStep.problem locals captures virtualLedger firstSelection firstRule rows before)))

include aligned

set_option backward.isDefEq.respectTransparency false in
/-- Producer-origin constraints construct the consumer admission, with shared outputs shared and guards kept at their cut. -/
theorem second_admission_causal
    (shape : ContextualInteractionFactors.Formation locals captures virtualLedger secondSelection secondRule rows secondOutputs)
    (resources : ContextualInteractionFactors.Resources secondSelection (fire before.present (firstSelection.commit (T := Unit))))
    (solvable : ContextualFrameUnifier.Solvable
      (causalProblem locals captures rows firstSelection firstOutputs virtualLedger secondSelection secondRule firstRule before))
    (checks : ∀ check ∈ (ContextualActivatedStep.prepared locals captures virtualLedger secondSelection secondRule rows).rule.checks,
      ContextualGuardSemantics.Ask locals
        (causalProblem locals captures rows firstSelection firstOutputs virtualLedger secondSelection secondRule firstRule before)
        (rowsAfterFirst locals captures rows firstSelection firstOutputs)
        (fire before.present (firstSelection.commit (T := Unit)))
        (check.map (instantiate (second locals captures).assignment))) :
    ContextualGuardedStep.Valid locals (afterFirst locals captures update.declaration)
      actualLedger secondSelection
      (secondRule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures update.declaration).assignment)))
      (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
        firstSelection firstOutputs rows)
      (ContextualTransportedActivation.result locals captures (ContextualComputedFreshFrame.includeSource update)
        virtualLedger firstSelection firstRule rows before)
      (fun occurrence => instantiate (secondView locals captures update.declaration relocation) (secondOutputs occurrence)) := by
  have physical := (ContextualInteractionFactors.resources_iff
    (fun occurrence => instantiate (secondView locals captures update.declaration relocation) (secondOutputs occurrence))
    secondSelection (fire before.present (firstSelection.commit (T := Unit)))).mp resources
  have mapped := second_rule_preparation locals captures update.declaration virtualLedger actualLedger secondSelection
    relocation aligned secondRule rows
  refine ⟨⟨physical.1, physical.2.1, ?_, ?_, ?_, physical.2.2, ?_⟩, ?_⟩
  · simpa only [RuleInstance.map, List.length_map] using shape.take_length
  · simpa only [RuleInstance.map, List.length_map] using shape.read_length
  · exact (List.map_map ..).symm.trans
      ((congrArg (List.map (instantiate (secondView locals captures update.declaration relocation))) shape.outputs).trans
        (congrArg RuleInstance.produce mapped))
  · intro check member
    have changedChecks := congrArg RuleInstance.checks mapped
    change check ∈ (ContextualActivatedStep.prepared locals (afterFirst locals captures update.declaration)
      actualLedger secondSelection
      (secondRule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures update.declaration).assignment)))
      (fun occurrence => (rows occurrence).map locals (oldCaller locals captures update.declaration).assignment)).rule.checks at member
    rw [← changedChecks] at member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    have transported := (causal_ask_iff locals captures rows firstSelection firstOutputs virtualLedger secondSelection
      secondRule firstRule before actualLedger relocation update aligned
      (original.map (instantiate (second locals captures).assignment))).mpr (checks original present)
    have maps : (original.map (instantiate (second locals captures).assignment)).map
        (instantiate (secondActive locals captures update.declaration relocation).assignment) =
      original.map (instantiate (secondView locals captures update.declaration relocation)) := by
      cases original <;> simp only [Check.map, secondView, Assignment.instantiate_compose]
    rw [maps] at transported
    exact transported
  · exact (causal_solvable_iff locals captures rows firstSelection firstOutputs virtualLedger secondSelection secondRule
      firstRule before actualLedger relocation update aligned).mpr solvable

/-- A common, independently prepared joint problem supplies the second
actual admission. Its guards are stated at the computed intermediate world,
not assumed as an already constructed source firing. -/
theorem second_admission_from_common
    (shape : ContextualInteractionFactors.Formation locals captures virtualLedger secondSelection secondRule rows secondOutputs)
    (resources : ContextualInteractionFactors.Resources secondSelection (fire before.present (firstSelection.commit (T := Unit))))
    (untouched : ∀ occurrence ∈ secondSelection.taken ++ secondSelection.read, occurrence ∉ firstSelection.made)
    (solvable : ContextualFrameUnifier.Solvable
      (jointProblem locals captures virtualLedger secondSelection secondRule rows firstSelection firstRule before))
    (checks : ∀ check ∈ (ContextualActivatedStep.prepared locals captures virtualLedger secondSelection secondRule rows).rule.checks,
      ContextualGuardSemantics.Ask locals
        (jointProblem locals captures virtualLedger secondSelection secondRule rows firstSelection firstRule before)
        (rowsAfterFirst locals captures rows firstSelection firstOutputs)
        (fire before.present (firstSelection.commit (T := Unit)))
        (check.map (instantiate (second locals captures).assignment))) :
    ContextualGuardedStep.Valid locals (afterFirst locals captures update.declaration)
      actualLedger secondSelection
      (secondRule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures update.declaration).assignment)))
      (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
        firstSelection firstOutputs rows)
      (ContextualTransportedActivation.result locals captures (ContextualComputedFreshFrame.includeSource update)
        virtualLedger firstSelection firstRule rows before)
      (fun occurrence => instantiate (secondView locals captures update.declaration relocation) (secondOutputs occurrence)) := by
  have same := causal_problem_eq_joint locals captures rows firstSelection firstOutputs virtualLedger secondSelection
    secondRule firstRule before untouched
  exact second_admission_causal locals captures virtualLedger actualLedger firstSelection secondSelection relocation aligned
    firstRule secondRule rows before firstOutputs secondOutputs update shape resources
    (by simpa only [same] using solvable) (by simpa only [same] using checks)

/-- The second worklist return is obtained from the common problem's model
and structural-pattern certificate, not supplied in the premises. -/
theorem actual_second_return_causal [DecidableEq Local] [DecidableEq Shared] [DecidableEq S.Srt]
    [∀ result, DecidableEq (S.Op result)]
    (shape : ContextualInteractionFactors.Formation locals captures virtualLedger secondSelection secondRule rows secondOutputs)
    (resources : ContextualInteractionFactors.Resources secondSelection (fire before.present (firstSelection.commit (T := Unit))))
    (solvable : ContextualFrameUnifier.Solvable
      (causalProblem locals captures rows firstSelection firstOutputs virtualLedger secondSelection secondRule firstRule before))
    (checks : ∀ check ∈ (ContextualActivatedStep.prepared locals captures virtualLedger secondSelection secondRule rows).rule.checks,
      ContextualGuardSemantics.Ask locals
        (causalProblem locals captures rows firstSelection firstOutputs virtualLedger secondSelection secondRule firstRule before)
        (rowsAfterFirst locals captures rows firstSelection firstOutputs)
        (fire before.present (firstSelection.commit (T := Unit)))
        (check.map (instantiate (second locals captures).assignment)))
    (patterned : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
      (causalProblem locals captures rows firstSelection firstOutputs virtualLedger secondSelection secondRule firstRule before))) :
    letI := update.equality
    ∃ fuel secondUpdate, ContextualTransportedActivation.FromRun locals (afterFirst locals captures update.declaration)
      fuel actualLedger secondSelection
      (secondRule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures update.declaration).assignment)))
      (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
        firstSelection firstOutputs rows)
      (ContextualTransportedActivation.result locals captures (ContextualComputedFreshFrame.includeSource update)
        virtualLedger firstSelection firstRule rows before)
      (fun occurrence => instantiate (secondView locals captures update.declaration relocation) (secondOutputs occurrence)) secondUpdate := by
  let _ := update.equality
  have admitted := second_admission_causal locals captures virtualLedger actualLedger firstSelection secondSelection
    relocation aligned firstRule secondRule rows before firstOutputs secondOutputs update shape resources solvable checks
  exact (ContextualTransportedActivation.semantic_admission_iff_completed_run locals
    (afterFirst locals captures update.declaration)
    (causal_pattern locals captures rows firstSelection firstOutputs virtualLedger secondSelection secondRule firstRule before
      actualLedger relocation update aligned patterned)).mp admitted


/-- The second worklist return is obtained from the common problem's model
and structural-pattern certificate, not supplied in the premises. -/
theorem actual_second_return_from_common [DecidableEq Local] [DecidableEq Shared] [DecidableEq S.Srt]
    [∀ result, DecidableEq (S.Op result)]
    (shape : ContextualInteractionFactors.Formation locals captures virtualLedger secondSelection secondRule rows secondOutputs)
    (resources : ContextualInteractionFactors.Resources secondSelection (fire before.present (firstSelection.commit (T := Unit))))
    (untouched : ∀ occurrence ∈ secondSelection.taken ++ secondSelection.read, occurrence ∉ firstSelection.made)
    (solvable : ContextualFrameUnifier.Solvable
      (jointProblem locals captures virtualLedger secondSelection secondRule rows firstSelection firstRule before))
    (checks : ∀ check ∈ (ContextualActivatedStep.prepared locals captures virtualLedger secondSelection secondRule rows).rule.checks,
      ContextualGuardSemantics.Ask locals
        (jointProblem locals captures virtualLedger secondSelection secondRule rows firstSelection firstRule before)
        (rowsAfterFirst locals captures rows firstSelection firstOutputs)
        (fire before.present (firstSelection.commit (T := Unit)))
        (check.map (instantiate (second locals captures).assignment)))
    (patterned : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
      (jointProblem locals captures virtualLedger secondSelection secondRule rows firstSelection firstRule before))) :
    letI := update.equality
    ∃ fuel secondUpdate, ContextualTransportedActivation.FromRun locals (afterFirst locals captures update.declaration)
      fuel actualLedger secondSelection
      (secondRule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures update.declaration).assignment)))
      (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
        firstSelection firstOutputs rows)
      (ContextualTransportedActivation.result locals captures (ContextualComputedFreshFrame.includeSource update)
        virtualLedger firstSelection firstRule rows before)
      (fun occurrence => instantiate (secondView locals captures update.declaration relocation) (secondOutputs occurrence)) secondUpdate := by
  let _ := update.equality
  have admitted := second_admission_from_common locals captures virtualLedger actualLedger firstSelection secondSelection
    relocation aligned firstRule secondRule rows before firstOutputs secondOutputs update shape resources untouched solvable checks
  exact (ContextualTransportedActivation.semantic_admission_iff_completed_run locals
    (afterFirst locals captures update.declaration)
    (second_problem_pattern locals captures virtualLedger actualLedger secondSelection relocation aligned secondRule rows
      firstSelection firstRule before firstOutputs update untouched patterned)).mp admitted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairFrames

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairFrames

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ContextualExecution ContextualSchedulePromotion ContextualScopeSupport ContextualWorldScopeLedger

variable {S : Signature} {Local O : Type} [DecidableEq O] [DecidableEq Local]
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  (locals : Local → MetaArity S) {Γ : Ctx S} {sort : S.Srt}

set_option backward.isDefEq.respectTransparency false in
/-- Two actual family-changing events are constructed from one initial
endpoint and common producer-origin constraints. The consumer can read or
consume newly produced shared data while retaining the producer's variables.
No first or second solver return is supplied. -/
theorem realize_causal_pair
    (before : Endpoint locals O Γ sort)
    (firstSelection secondSelection : Selection O)
    (firstRule secondRule : RuleInstance
      (Term (signature S (ContextualSelectionViews.source locals before.declarations)) Γ sort))
    (firstOutputs secondOutputs : O → Term (signature S (ContextualSelectionViews.target locals before.declarations)) Γ sort)
    (firstCovered : RuleCovered (privateScopes before.scopes) before.occupied firstRule)
    (secondCovered : RuleCovered (privateScopes before.scopes) before.occupied secondRule)
    (firstReady : ContextualGuardedStep.Valid locals before.declarations before.occupied
      firstSelection firstRule before.inventory.rows before.inventory.configuration firstOutputs)
    (firstPattern : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals before.declarations before.occupied firstSelection firstRule
        before.inventory.rows before.inventory.configuration)))
    (secondShape : ContextualInteractionFactors.Formation locals before.declarations before.occupied secondSelection
      secondRule before.inventory.rows secondOutputs)
    (secondResources : ContextualInteractionFactors.Resources secondSelection
      (fire before.inventory.configuration.present (firstSelection.commit (T := Unit))))
    (joint : ContextualFrameUnifier.Solvable (causalProblem locals before.declarations before.inventory.rows firstSelection firstOutputs before.occupied
        secondSelection secondRule firstRule before.inventory.configuration))
    (checks : ∀ check ∈ (ContextualActivatedStep.prepared locals before.declarations before.occupied
      secondSelection secondRule before.inventory.rows).rule.checks,
      ContextualGuardSemantics.Ask locals
        (causalProblem locals before.declarations before.inventory.rows firstSelection firstOutputs before.occupied
        secondSelection secondRule firstRule before.inventory.configuration)
        (rowsAfterFirst locals before.declarations before.inventory.rows firstSelection firstOutputs)
        (fire before.inventory.configuration.present (firstSelection.commit (T := Unit)))
        (check.map (instantiate (second locals before.declarations).assignment)))
    (jointPattern : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
      (causalProblem locals before.declarations before.inventory.rows firstSelection firstOutputs before.occupied
        secondSelection secondRule firstRule before.inventory.configuration))) :
    ∃ firstPrepared : Prepared locals before, ∃ secondPrepared : Prepared locals firstPrepared.target,
      ∃ relocation : Equiv.Perm Nat,
        firstPrepared.rule = firstRule ∧ firstPrepared.selection = firstSelection ∧ firstPrepared.outputs = firstOutputs ∧
        secondPrepared.rule = secondRule.map (instantiate (ContextualStoredRows.liftCaptures locals
          (oldCaller locals before.declarations firstPrepared.update.declaration).assignment)) ∧
        secondPrepared.selection = secondSelection ∧
        secondPrepared.outputs = (fun occurrence => instantiate
          (secondView locals before.declarations firstPrepared.update.declaration relocation) (secondOutputs occurrence)) ∧
        (∀ port : ContextualActivationScopes.Port secondSelection,
          relocation (ContextualActivationScopes.scopeAt before.occupied port) =
            ContextualActivationScopes.scopeAt firstPrepared.target.occupied port) ∧
        Checked locals firstPrepared.questions ∧ Checked locals secondPrepared.questions ∧
        (∃ path : Quiver.Path before secondPrepared.target,
          ContextualExecution.selections path = [firstSelection, secondSelection]) ∧
        (∀ check : Check (Term (signature S (common locals before.declarations)) Γ sort),
          ContextualGuardSemantics.Ask locals secondPrepared.target.inventory.configuration.equations
            secondPrepared.target.inventory.rows secondPrepared.target.inventory.configuration.present
            (check.map (instantiate (Assignment.compose (ContextualComputedFreshFrame.includeSource secondPrepared.update)
              (secondActive locals before.declarations firstPrepared.update.declaration relocation).assignment))) ↔
          ContextualGuardSemantics.Ask locals
            (causalProblem locals before.declarations before.inventory.rows firstSelection firstOutputs before.occupied
        secondSelection secondRule firstRule before.inventory.configuration)
            (rowsAfterBoth locals before.declarations before.inventory.rows firstSelection secondSelection firstOutputs secondOutputs)
            (fire (fire before.inventory.configuration.present (firstSelection.commit (T := Unit)))
              (secondSelection.commit (T := Unit))) check) := by
  let _ := before.equality
  obtain ⟨firstFuel, update, returned⟩ :=
    (ContextualTransportedActivation.semantic_admission_iff_completed_run locals before.declarations firstPattern).mp firstReady
  let firstPrepared : Prepared locals before := {
    rule := firstRule
    ruleCovered := firstCovered
    selection := firstSelection
    outputs := firstOutputs
    formation := ⟨firstReady.take_length, firstReady.read_length, firstReady.outputs⟩
    resources := (ContextualInteractionFactors.resources_iff firstOutputs firstSelection before.inventory.configuration.present).mpr
      ⟨firstReady.take_distinct, firstReady.output_distinct, firstReady.occurrences⟩
    fuel := firstFuel
    update := update
    computed := returned.computed
    finished := returned.empty }
  have firstChecked : Checked locals firstPrepared.questions := by
    intro question member
    obtain ⟨check, present, rfl⟩ := List.mem_map.mp member
    exact firstReady.checks check present
  obtain ⟨relocation, aligned⟩ := exists_scope_relocation secondSelection before.occupied firstPrepared.target.occupied
  let _ := update.equality
  obtain ⟨secondFuel, secondUpdate, secondReturned⟩ := actual_second_return_causal locals before.declarations
    before.occupied firstPrepared.target.occupied firstSelection secondSelection relocation aligned firstRule secondRule
    before.inventory.rows before.inventory.configuration firstOutputs secondOutputs update
    secondShape secondResources joint checks jointPattern
  have capturesRespect : Respects before.scopes firstPrepared.target.scopes
      (oldCaller locals before.declarations update.declaration).assignment := by
    intro name
    change term (ContextualFreshFrameScopeLedger.frameScopes (ContextualScopeSupport.activeScopes before.scopes)
      (ContextualFreshFrameScopeLedger.helperScope (ContextualActivationScopes.after before.occupied firstSelection)))
      (generator (afterFirst locals before.declarations update.declaration) (Sum.inl (Sum.inr name))) ⊆ before.scopes name
    rw [term_generator]
    exact Finset.Subset.refl _
  have ledgerRetained : before.occupied ⊆ firstPrepared.target.occupied :=
    (ContextualActivationScopes.old_scopes_retained before.occupied firstSelection).trans
      (ContextualFreshFrameScopeLedger.old_scopes_retained _)
  have nextCovered := (secondCovered.map
    (ContextualStoredRows.liftCaptures locals (oldCaller locals before.declarations update.declaration).assignment)
    (respects_liftCaptures locals before.scopes firstPrepared.target.scopes _ capturesRespect)).mono ledgerRetained
  let secondPrepared : Prepared locals firstPrepared.target := {
    rule := secondRule.map (instantiate (ContextualStoredRows.liftCaptures locals
      (oldCaller locals before.declarations update.declaration).assignment))
    ruleCovered := nextCovered
    selection := secondSelection
    outputs := fun occurrence => instantiate (secondView locals before.declarations update.declaration relocation) (secondOutputs occurrence)
    formation := ⟨secondReturned.valid.admitted.take_length, secondReturned.valid.admitted.read_length,
      secondReturned.valid.admitted.outputs⟩
    resources := (ContextualInteractionFactors.resources_iff _ _ _).mpr
      ⟨secondReturned.valid.admitted.take_distinct, secondReturned.valid.admitted.output_distinct,
        secondReturned.valid.admitted.occurrences⟩
    fuel := secondFuel
    update := secondUpdate
    computed := secondReturned.computed
    finished := secondReturned.empty }
  have secondChecked : Checked locals secondPrepared.questions := by
    intro question member
    obtain ⟨check, present, rfl⟩ := List.mem_map.mp member
    exact secondReturned.valid.admitted.checks check present
  let firstPath : Quiver.Path before firstPrepared.target := .cons .nil (firstPrepared.firing firstChecked)
  let secondPath : Quiver.Path firstPrepared.target secondPrepared.target := .cons .nil (secondPrepared.firing secondChecked)
  let path := firstPath.comp secondPath
  refine ⟨firstPrepared, secondPrepared, relocation, rfl, rfl, rfl, rfl, rfl, rfl,
    aligned, firstChecked, secondChecked, ⟨path, rfl⟩, ?_⟩
  intro check
  have targetAsk := secondPrepared.target_ask_iff
    (check.map (instantiate (secondActive locals before.declarations update.declaration relocation).assignment))
  have checkMaps : (check.map (instantiate (secondActive locals before.declarations update.declaration relocation).assignment)).map
      (instantiate (ContextualComputedFreshFrame.includeSource secondPrepared.update)) =
    check.map (instantiate (Assignment.compose (ContextualComputedFreshFrame.includeSource secondPrepared.update)
      (secondActive locals before.declarations update.declaration relocation).assignment)) := by
    cases check <;> simp only [Check.map, Assignment.instantiate_compose]
  rw [checkMaps] at targetAsk
  exact targetAsk.trans (causal_result_ask_iff locals before.declarations before.inventory.rows firstSelection firstOutputs before.occupied
    secondSelection secondRule firstRule before.inventory.configuration firstPrepared.target.occupied relocation update aligned
    secondOutputs check)


set_option backward.isDefEq.respectTransparency false in
/-- Two actual family-changing events are constructed from one initial
endpoint and independently prepared common constraints. The second event
does not read a newly produced occurrence; that dataflow case needs its
producer-origin views. Its guard may nevertheless be enabled by the first
event's equations. No first or second solver return is supplied. -/
theorem realize_ordered_pair
    (before : Endpoint locals O Γ sort)
    (firstSelection secondSelection : Selection O)
    (firstRule secondRule : RuleInstance
      (Term (signature S (ContextualSelectionViews.source locals before.declarations)) Γ sort))
    (firstOutputs secondOutputs : O → Term (signature S (ContextualSelectionViews.target locals before.declarations)) Γ sort)
    (firstCovered : RuleCovered (privateScopes before.scopes) before.occupied firstRule)
    (secondCovered : RuleCovered (privateScopes before.scopes) before.occupied secondRule)
    (firstReady : ContextualGuardedStep.Valid locals before.declarations before.occupied
      firstSelection firstRule before.inventory.rows before.inventory.configuration firstOutputs)
    (firstPattern : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals before.declarations before.occupied firstSelection firstRule
        before.inventory.rows before.inventory.configuration)))
    (secondShape : ContextualInteractionFactors.Formation locals before.declarations before.occupied secondSelection
      secondRule before.inventory.rows secondOutputs)
    (secondResources : ContextualInteractionFactors.Resources secondSelection
      (fire before.inventory.configuration.present (firstSelection.commit (T := Unit))))
    (untouched : ∀ occurrence ∈ secondSelection.taken ++ secondSelection.read, occurrence ∉ firstSelection.made)
    (joint : ContextualFrameUnifier.Solvable (jointProblem locals before.declarations before.occupied
      secondSelection secondRule before.inventory.rows firstSelection firstRule before.inventory.configuration))
    (checks : ∀ check ∈ (ContextualActivatedStep.prepared locals before.declarations before.occupied
      secondSelection secondRule before.inventory.rows).rule.checks,
      ContextualGuardSemantics.Ask locals
        (jointProblem locals before.declarations before.occupied secondSelection secondRule before.inventory.rows
          firstSelection firstRule before.inventory.configuration)
        (rowsAfterFirst locals before.declarations before.inventory.rows firstSelection firstOutputs)
        (fire before.inventory.configuration.present (firstSelection.commit (T := Unit)))
        (check.map (instantiate (second locals before.declarations).assignment)))
    (jointPattern : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
      (jointProblem locals before.declarations before.occupied secondSelection secondRule before.inventory.rows
        firstSelection firstRule before.inventory.configuration))) :
    ∃ firstPrepared : Prepared locals before, ∃ secondPrepared : Prepared locals firstPrepared.target,
      ∃ relocation : Equiv.Perm Nat,
        firstPrepared.rule = firstRule ∧ firstPrepared.selection = firstSelection ∧ firstPrepared.outputs = firstOutputs ∧
        secondPrepared.rule = secondRule.map (instantiate (ContextualStoredRows.liftCaptures locals
          (oldCaller locals before.declarations firstPrepared.update.declaration).assignment)) ∧
        secondPrepared.selection = secondSelection ∧
        secondPrepared.outputs = (fun occurrence => instantiate
          (secondView locals before.declarations firstPrepared.update.declaration relocation) (secondOutputs occurrence)) ∧
        (∀ port : ContextualActivationScopes.Port secondSelection,
          relocation (ContextualActivationScopes.scopeAt before.occupied port) =
            ContextualActivationScopes.scopeAt firstPrepared.target.occupied port) ∧
        Checked locals firstPrepared.questions ∧ Checked locals secondPrepared.questions ∧
        (∃ path : Quiver.Path before secondPrepared.target,
          ContextualExecution.selections path = [firstSelection, secondSelection]) ∧
        (∀ check : Check (Term (signature S (common locals before.declarations)) Γ sort),
          ContextualGuardSemantics.Ask locals secondPrepared.target.inventory.configuration.equations
            secondPrepared.target.inventory.rows secondPrepared.target.inventory.configuration.present
            (check.map (instantiate (Assignment.compose (ContextualComputedFreshFrame.includeSource secondPrepared.update)
              (secondActive locals before.declarations firstPrepared.update.declaration relocation).assignment))) ↔
          ContextualGuardSemantics.Ask locals
            (jointProblem locals before.declarations before.occupied secondSelection secondRule before.inventory.rows
              firstSelection firstRule before.inventory.configuration)
            (rowsAfterBoth locals before.declarations before.inventory.rows firstSelection secondSelection firstOutputs secondOutputs)
            (fire (fire before.inventory.configuration.present (firstSelection.commit (T := Unit)))
              (secondSelection.commit (T := Unit))) check) := by
  have same := causal_problem_eq_joint locals before.declarations before.inventory.rows firstSelection firstOutputs
    before.occupied secondSelection secondRule firstRule before.inventory.configuration untouched
  have constructed := realize_causal_pair locals before firstSelection secondSelection firstRule secondRule
    firstOutputs secondOutputs firstCovered secondCovered firstReady firstPattern secondShape secondResources
    (by simpa only [same] using joint) (by simpa only [same] using checks)
    (by simpa only [same] using jointPattern)
  simpa only [same] using constructed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairFrames

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairFrames

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ContextualExecution ContextualSchedulePromotion ContextualScopeSupport ContextualWorldScopeLedger

variable {S : Signature} {Local O : Type} [DecidableEq O] [DecidableEq Local]
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  (locals : Local → MetaArity S) {Γ : Ctx S} {sort : S.Srt}

set_option backward.isDefEq.respectTransparency false in
/-- Construct both actual contextual paths and compare every final Check.
The premises concern original events, resource selections and common-cut
questions; neither a completed solver return nor a path is supplied.
Original and intermediate guards remain separate obligations. -/
theorem realize_two_orders
    (before : Endpoint locals O Γ sort)
    (selected : Bool → Selection O)
    (rules : Bool → RuleInstance (Term (signature S (ContextualSelectionViews.source locals before.declarations)) Γ sort))
    (outputs : Bool → O → Term (signature S (ContextualSelectionViews.target locals before.declarations)) Γ sort)
    (covered : ∀ event, RuleCovered (privateScopes before.scopes) before.occupied (rules event))
    (ready : ∀ event, ContextualGuardedStep.Valid locals before.declarations before.occupied
      (selected event) (rules event) before.inventory.rows before.inventory.configuration (outputs event))
    (patterns : ∀ event, ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals before.declarations before.occupied (selected event) (rules event)
        before.inventory.rows before.inventory.configuration)))
    (resources : ∀ event, ContextualInteractionFactors.Resources (selected (!event))
      (fire before.inventory.configuration.present ((selected event).commit (T := Unit))))
    (joint : ∀ event, ContextualFrameUnifier.Solvable
      (jointProblem locals before.declarations before.occupied (selected (!event)) (rules (!event)) before.inventory.rows
        (selected event) (rules event) before.inventory.configuration))
    (checks : ∀ event, ∀ check ∈ (ContextualActivatedStep.prepared locals before.declarations before.occupied
      (selected (!event)) (rules (!event)) before.inventory.rows).rule.checks,
      ContextualGuardSemantics.Ask locals
        (jointProblem locals before.declarations before.occupied (selected (!event)) (rules (!event)) before.inventory.rows
          (selected event) (rules event) before.inventory.configuration)
        (rowsAfterFirst locals before.declarations before.inventory.rows (selected event) (outputs event))
        (fire before.inventory.configuration.present ((selected event).commit (T := Unit)))
        (check.map (instantiate (second locals before.declarations).assignment)))
    (jointPatterns : ∀ event, ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
      (jointProblem locals before.declarations before.occupied (selected (!event)) (rules (!event)) before.inventory.rows
        (selected event) (rules event) before.inventory.configuration))) :
    ∃ forward backward : Endpoint locals O Γ sort,
      ∃ forwardPath : Quiver.Path before forward, ∃ backwardPath : Quiver.Path before backward,
      ∃ forwardView : Assignment (common locals before.declarations) forward.declarations,
      ∃ backwardView : Assignment (common locals before.declarations) backward.declarations,
        selections forwardPath = [selected false, selected true] ∧
        selections backwardPath = [selected true, selected false] ∧
        (∀ check : Check (Term (signature S (common locals before.declarations)) Γ sort),
          ContextualGuardSemantics.Ask locals forward.inventory.configuration.equations
            forward.inventory.rows forward.inventory.configuration.present
            (check.map (instantiate forwardView)) ↔
          ContextualGuardSemantics.Ask locals backward.inventory.configuration.equations
            backward.inventory.rows backward.inventory.configuration.present
            (check.map (instantiate (Assignment.compose backwardView
              (exchangeEvents locals before.declarations).assignment)))) := by
  have shape (event : Bool) : ContextualInteractionFactors.Formation locals before.declarations before.occupied
      (selected (!event)) (rules (!event)) before.inventory.rows (outputs (!event)) :=
    ⟨(ready (!event)).take_length, (ready (!event)).read_length, (ready (!event)).outputs⟩
  have untouched (event : Bool) : ∀ occurrence ∈ (selected (!event)).taken ++ (selected (!event)).read,
      occurrence ∉ (selected event).made := by
    intro occurrence member made
    have old : occurrence ∈ before.inventory.configuration.present := by
      rcases List.mem_append.mp member with taken | read
      · exact (ready (!event)).occurrences.taken_subset (List.mem_toFinset.mpr taken)
      · exact (ready (!event)).occurrences.kept_subset (List.mem_toFinset.mpr read)
    exact Finset.disjoint_left.mp (ready event).occurrences.fresh (List.mem_toFinset.mpr made) old
  have realizes := fun event : Bool => realize_ordered_pair locals before (selected event) (selected (!event))
    (rules event) (rules (!event)) (outputs event) (outputs (!event)) (covered event) (covered (!event)) (ready event)
    (patterns event) (shape event) (resources event) (untouched event) (joint event) (checks event) (jointPatterns event)
  obtain ⟨f1, f2, fp, _fr, _fs, _fo, _sr, _ss, _so, _fa, _fc, _sc, ⟨fpath, fpicks⟩, fqueries⟩ := realizes false
  obtain ⟨b1, b2, bp, _br, _bs, _bo, _tr, _ts, _to, _ba, _bc, _tc, ⟨bpath, bpicks⟩, bqueries⟩ := realizes true
  have apart : Disjoint (selected false).made.toFinset (selected true).made.toFinset := by
    have physical := ((ContextualInteractionFactors.resources_iff (outputs true) _ _).mp (resources false)).2.2
    apply Finset.disjoint_left.mpr
    intro occurrence madeFirst madeSecond
    exact Finset.disjoint_left.mp physical.fresh madeSecond (made_subset_fire madeFirst)
  have otherPhysical : Enabled (outputs false) before.inventory.configuration.present (selected true).commit :=
    ⟨(ready true).occurrences.taken_subset, (ready true).occurrences.kept_subset,
      (ready true).occurrences.apart, (ready true).occurrences.fresh, fun query member => by cases member⟩
  have sameWorld := fire_comm (ready false).occurrences otherPhysical
  let forwardView := Assignment.compose (ContextualComputedFreshFrame.includeSource f2.update)
    (secondActive locals before.declarations f1.update.declaration fp).assignment
  let backwardView := Assignment.compose (ContextualComputedFreshFrame.includeSource b2.update)
    (secondActive locals before.declarations b1.update.declaration bp).assignment
  refine ⟨f2.target, b2.target, fpath, bpath, forwardView, backwardView, fpicks, bpicks, ?_⟩
  intro check
  have middle := final_asks_exchange locals before.declarations before.occupied (selected false) (selected true)
    (rules false) (rules true) before.inventory.rows before.inventory.configuration
    (outputs false) (outputs true) apart sameWorld check
  have last := bqueries (check.map (instantiate (exchangeEvents locals before.declarations).assignment))
  have maps : (check.map (instantiate (exchangeEvents locals before.declarations).assignment)).map
      (instantiate backwardView) =
    check.map (instantiate (Assignment.compose backwardView (exchangeEvents locals before.declarations).assignment)) := by
    cases check <;> simp only [Check.map, Assignment.instantiate_compose]
  change ContextualGuardSemantics.Ask locals b2.target.inventory.configuration.equations b2.target.inventory.rows
    b2.target.inventory.configuration.present
    ((check.map (instantiate (exchangeEvents locals before.declarations).assignment)).map (instantiate backwardView)) ↔ _ at last
  rw [maps] at last
  exact (fqueries check).trans (middle.trans last.symm)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairFrames
