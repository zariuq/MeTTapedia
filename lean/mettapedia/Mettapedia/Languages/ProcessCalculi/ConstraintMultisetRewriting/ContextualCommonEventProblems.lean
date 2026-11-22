import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualEventViewRelocation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTransportedActivation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutationNames
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedPatternImages
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionAsks

/-!
# Common event equations retain the original computed activation and asks

The common problem opens the rule and each physical row use at its indexed
port scope. An actual activation's finite scope alignment transports every
equation to that problem. Incoming captures, physical row identities and
the original all-future guard contract remain unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommonEventProblems

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualEventViewRelocation

variable {S : Signature} {Local Shared O Future : Type} {n : Nat}
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
  (selections : Fin n → Selection O)

def problem (globalLedger : Finset Nat) (event : Fin n) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O) :
    EquationStore (Term (signature S (ContextualSelectionViews.target locals captures)) Γ sort) :=
  let views := ContextualEventViewScopes.prepared locals captures selections globalLedger event rule rows
  (ContextualActivatedStep.frame locals captures before).equations ++
    ContextualActivatedStep.useEquations views.rule.take (List.ofFn views.taken) ++
      ContextualActivatedStep.useEquations views.rule.read (List.ofFn views.read) ++ views.rule.tell

theorem framed_equations_fixed (permutation : Equiv.Perm Nat) {Γ : Ctx S} {sort : S.Srt}
    (before : Configuration (Term (signature S captures) Γ sort) O) :
    ContextualFrameUnifier.mapProblem (assignment locals captures permutation)
        (ContextualActivatedStep.frame locals captures before).equations =
      (ContextualActivatedStep.frame locals captures before).equations := by
  change ContextualFrameUnifier.mapProblem (assignment locals captures permutation)
      (ContextualFrameUnifier.mapProblem (ContextualSelectionViews.capturedTarget locals captures) before.equations) = _
  rw [ContextualComputedFreshFrame.map_compose, capture_assignment_fixed]
  rfl

variable {selections}

theorem original_problem_relocated (localLedger globalLedger : Finset Nat) (event : Fin n)
    (permutation : Equiv.Perm Nat)
    (aligned : ∀ port : ContextualActivationScopes.Port (selections event),
      permutation (ContextualActivationScopes.scopeAt localLedger port) =
        ContextualEventViewScopes.scope selections globalLedger ⟨event, port⟩)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O) :
    ContextualFrameUnifier.mapProblem (assignment locals captures permutation)
        (ContextualActivatedStep.problem locals captures localLedger (selections event) rule rows before) =
      problem locals captures selections globalLedger event rule rows before := by
  have mappedRule := prepared_rule_relocated locals captures localLedger globalLedger event permutation aligned rule rows
  have takes : ((ContextualActivatedStep.prepared locals captures localLedger (selections event) rule rows).rule.take).map
      (instantiate (assignment locals captures permutation)) =
        (ContextualEventViewScopes.prepared locals captures selections globalLedger event rule rows).rule.take :=
    congrArg RuleInstance.take mappedRule
  have reads : ((ContextualActivatedStep.prepared locals captures localLedger (selections event) rule rows).rule.read).map
      (instantiate (assignment locals captures permutation)) =
        (ContextualEventViewScopes.prepared locals captures selections globalLedger event rule rows).rule.read :=
    congrArg RuleInstance.read mappedRule
  have tells : ContextualFrameUnifier.mapProblem (assignment locals captures permutation)
      (ContextualActivatedStep.prepared locals captures localLedger (selections event) rule rows).rule.tell =
        (ContextualEventViewScopes.prepared locals captures selections globalLedger event rule rows).rule.tell :=
    congrArg RuleInstance.tell mappedRule
  have takenViews : (List.ofFn (ContextualActivatedStep.prepared locals captures localLedger
      (selections event) rule rows).taken).map (instantiate (assignment locals captures permutation)) =
        List.ofFn (ContextualEventViewScopes.prepared locals captures selections globalLedger event rule rows).taken := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext port
    exact prepared_take_relocated locals captures localLedger globalLedger event permutation aligned rule rows port
  have readViews : (List.ofFn (ContextualActivatedStep.prepared locals captures localLedger
      (selections event) rule rows).read).map (instantiate (assignment locals captures permutation)) =
        List.ofFn (ContextualEventViewScopes.prepared locals captures selections globalLedger event rule rows).read := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext port
    exact prepared_read_relocated locals captures localLedger globalLedger event permutation aligned rule rows port
  simp only [ContextualActivatedStep.problem, ContextualTransportedActivation.map_append,
    ContextualTransportedActivation.map_useEquations, framed_equations_fixed, takes, reads,
    tells, takenViews, readViews, problem]

theorem models_relocated (localLedger globalLedger : Finset Nat) (event : Fin n)
    (permutation : Equiv.Perm Nat)
    (aligned : ∀ port : ContextualActivationScopes.Port (selections event),
      permutation (ContextualActivationScopes.scopeAt localLedger port) =
        ContextualEventViewScopes.scope selections globalLedger ⟨event, port⟩)
    {future : Future → MetaArity S}
    (candidate : Assignment (ContextualSelectionViews.target locals captures) future)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O) :
    ContextualFrameUnifier.Models candidate (problem locals captures selections globalLedger event rule rows before) ↔
      ContextualFrameUnifier.Models (Assignment.compose candidate (assignment locals captures permutation))
        (ContextualActivatedStep.problem locals captures localLedger (selections event) rule rows before) := by
  rw [← original_problem_relocated locals captures localLedger globalLedger event permutation aligned rule rows before]
  exact ContextualFrameUnifier.models_mapProblem _ _ _

theorem original_ask_relocated_iff (localLedger globalLedger : Finset Nat) (event : Fin n)
    (permutation : Equiv.Perm Nat)
    (aligned : ∀ port : ContextualActivationScopes.Port (selections event),
      permutation (ContextualActivationScopes.scopeAt localLedger port) =
        ContextualEventViewScopes.scope selections globalLedger ⟨event, port⟩)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O)
    (check : Check (Term (signature S (ContextualSelectionViews.target locals captures)) Γ sort)) :
    ContextualGuardSemantics.Ask locals (problem locals captures selections globalLedger event rule rows before)
        (ContextualGuardedStep.guardRows locals captures rows) before.present
        (check.map (instantiate (assignment locals captures permutation))) ↔
      ContextualGuardSemantics.Ask locals
        (ContextualActivatedStep.problem locals captures localLedger (selections event) rule rows before)
        (ContextualGuardedStep.guardRows locals captures rows) before.present check := by
  have reflected := ContextualGuardSemantics.Ask.reindex_iff locals
    (names permutation) (names permutation.symm) (preserves locals captures permutation)
    (preserves locals captures permutation.symm) (names_left_inverse permutation)
    (ContextualActivatedStep.problem locals captures localLedger (selections event) rule rows before)
    (ContextualGuardedStep.guardRows locals captures rows) before.present check
  change ContextualGuardSemantics.Ask locals
      (ContextualFrameUnifier.mapProblem (assignment locals captures permutation)
        (ContextualActivatedStep.problem locals captures localLedger (selections event) rule rows before))
      (fun occurrence => (ContextualGuardedStep.guardRows locals captures rows occurrence).map locals
        (assignment locals captures permutation)) before.present
      (check.map (instantiate (assignment locals captures permutation))) ↔ _ at reflected
  rw [original_problem_relocated locals captures localLedger globalLedger event permutation aligned rule rows before,
    guard_rows_fixed] at reflected
  exact reflected

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommonEventProblems

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairFrames

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {Local Shared Helper O : Type}
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
  (helpers : Helper → MetaArity S) (virtualLedger actualLedger : Finset Nat)
  (selection : Selection O) (relocation : Equiv.Perm Nat)
  (aligned : ∀ port : ContextualActivationScopes.Port selection,
    relocation (ContextualActivationScopes.scopeAt virtualLedger port) =
      ContextualActivationScopes.scopeAt actualLedger port)
  {Γ : Ctx S} {sort : S.Srt}
  (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
  (rows : O → ContextualStoredRows.Row locals captures Γ sort)

def rowsAfterFirst [DecidableEq O] (firstSelection : Selection O)
    (outputs : O → Term (signature S (ContextualSelectionViews.target locals captures)) Γ sort) :
    O → ContextualStoredRows.Row locals (common locals captures) Γ sort :=
  fun occurrence => if occurrence ∈ firstSelection.made then
    .shared (instantiate (first locals captures).assignment (outputs occurrence))
  else (rows occurrence).map locals (caller locals captures)

def jointProblem (firstSelection : Selection O)
    (firstRule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (before : Configuration (Term (signature S captures) Γ sort) O) :
    EquationStore (Term (signature S (common locals captures)) Γ sort) :=
  ContextualFrameUnifier.mapProblem (first locals captures).assignment
      (ContextualActivatedStep.problem locals captures virtualLedger firstSelection firstRule rows before) ++
    ContextualFrameUnifier.mapProblem (second locals captures).assignment
      (ContextualActivatedStep.addedEquations locals captures virtualLedger selection rule rows)

def rowsAfterBoth [DecidableEq O] (firstSelection secondSelection : Selection O)
    (firstOutputs secondOutputs : O → Term (signature S (ContextualSelectionViews.target locals captures)) Γ sort) :
    O → ContextualStoredRows.Row locals (common locals captures) Γ sort :=
  fun occurrence => if occurrence ∈ secondSelection.made then
    .shared (instantiate (second locals captures).assignment (secondOutputs occurrence))
  else rowsAfterFirst locals captures rows firstSelection firstOutputs occurrence

include aligned

theorem second_rule_preparation :
    ((ContextualActivatedStep.prepared locals captures virtualLedger selection rule rows).rule).map
        (instantiate (secondView locals captures helpers relocation)) =
      (ContextualActivatedStep.prepared locals (afterFirst locals captures helpers) actualLedger selection
        (rule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures helpers).assignment)))
        (fun occurrence => (rows occurrence).map locals (oldCaller locals captures helpers).assignment)).rule := by
  change (rule.map (ContextualFreshening.termAt locals captures
    (ContextualActivationScopes.scopeAt virtualLedger (ContextualActivationScopes.rulePort selection)))).map _ = _
  rw [OccurrenceRelabeling.rule_map_comp]
  change rule.map _ = (rule.map (instantiate (ContextualStoredRows.liftCaptures locals
    (oldCaller locals captures helpers).assignment))).map _
  rw [OccurrenceRelabeling.rule_map_comp]
  apply congrArg (fun mapping => rule.map mapping)
  funext term
  exact (second_view_opening locals captures helpers relocation _ term).trans
    (congrArg (fun scope => ContextualFreshening.termAt locals (afterFirst locals captures helpers) scope
      (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures helpers).assignment) term))
      (aligned (ContextualActivationScopes.rulePort selection)))

theorem second_take_preparation (port : Fin selection.taken.length) :
    instantiate (secondView locals captures helpers relocation)
        ((ContextualActivatedStep.prepared locals captures virtualLedger selection rule rows).taken port) =
      (ContextualActivatedStep.prepared locals (afterFirst locals captures helpers) actualLedger selection
        (rule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures helpers).assignment)))
        (fun occurrence => (rows occurrence).map locals (oldCaller locals captures helpers).assignment)).taken port := by
  rw [ContextualActivatedStep.prepared_taken_view, ContextualActivatedStep.prepared_taken_view]
  rw [second_view_row]
  exact congrArg (fun scope => ContextualStoredRows.viewAt locals (afterFirst locals captures helpers) scope
    ((rows (selection.taken.get port)).map locals (oldCaller locals captures helpers).assignment))
    (aligned (ContextualActivationScopes.takePort selection port))

theorem second_read_preparation (port : Fin selection.read.length) :
    instantiate (secondView locals captures helpers relocation)
        ((ContextualActivatedStep.prepared locals captures virtualLedger selection rule rows).read port) =
      (ContextualActivatedStep.prepared locals (afterFirst locals captures helpers) actualLedger selection
        (rule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures helpers).assignment)))
        (fun occurrence => (rows occurrence).map locals (oldCaller locals captures helpers).assignment)).read port := by
  rw [ContextualActivatedStep.prepared_read_view, ContextualActivatedStep.prepared_read_view]
  rw [second_view_row]
  exact congrArg (fun scope => ContextualStoredRows.viewAt locals (afterFirst locals captures helpers) scope
    ((rows (selection.read.get port)).map locals (oldCaller locals captures helpers).assignment))
    (aligned (ContextualActivationScopes.readPort selection port))

/-- The equations added by the second event agree with its independently
prepared common-frame equations. The incoming first-event equations remain
separate and must be retained in the second event's complete problem. -/
theorem second_added_equations :
    ContextualFrameUnifier.mapProblem (secondView locals captures helpers relocation)
      (ContextualActivatedStep.addedEquations locals captures virtualLedger selection rule rows) =
    ContextualActivatedStep.addedEquations locals (afterFirst locals captures helpers) actualLedger selection
      (rule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures helpers).assignment)))
      (fun occurrence => (rows occurrence).map locals (oldCaller locals captures helpers).assignment) := by
  have mapped := second_rule_preparation locals captures helpers virtualLedger actualLedger selection relocation aligned rule rows
  have takes := congrArg RuleInstance.take mapped
  have reads := congrArg RuleInstance.read mapped
  have tells := congrArg RuleInstance.tell mapped
  have takeViews :
      (List.ofFn (ContextualActivatedStep.prepared locals captures virtualLedger selection rule rows).taken).map
          (instantiate (secondView locals captures helpers relocation)) =
        List.ofFn (ContextualActivatedStep.prepared locals (afterFirst locals captures helpers) actualLedger selection
          (rule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures helpers).assignment)))
          (fun occurrence => (rows occurrence).map locals (oldCaller locals captures helpers).assignment)).taken := by
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext (second_take_preparation locals captures helpers virtualLedger actualLedger
      selection relocation aligned rule rows))
  have readViews :
      (List.ofFn (ContextualActivatedStep.prepared locals captures virtualLedger selection rule rows).read).map
          (instantiate (secondView locals captures helpers relocation)) =
        List.ofFn (ContextualActivatedStep.prepared locals (afterFirst locals captures helpers) actualLedger selection
          (rule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures helpers).assignment)))
          (fun occurrence => (rows occurrence).map locals (oldCaller locals captures helpers).assignment)).read := by
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext (second_read_preparation locals captures helpers virtualLedger actualLedger
      selection relocation aligned rule rows))
  dsimp only [RuleInstance.map] at takes reads tells
  change ContextualFrameUnifier.mapProblem (secondView locals captures helpers relocation)
      (ContextualActivatedStep.prepared locals captures virtualLedger selection rule rows).rule.tell = _ at tells
  simp only [ContextualActivatedStep.addedEquations, ContextualTransportedActivation.map_append,
    ContextualTransportedActivation.map_useEquations, takes, reads, tells, takeViews, readViews]
  rfl

/-- The complete second problem retains the first event's equations. It is
the common two-event problem transported into the actual helper-expanded
second activation. Only selected-row preservation is assumed here; resource
availability and guard admission remain separate obligations. -/
theorem second_problem_after_first [DecidableEq O]
    (firstSelection : Selection O)
    (firstRule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (before : Configuration (Term (signature S captures) Γ sort) O)
    (firstOutputs : O → Term (signature S (ContextualSelectionViews.target locals captures)) Γ sort)
    (update : ContextualFrameUpdate.Update (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals captures virtualLedger firstSelection firstRule rows before)))
    (untouched : ∀ occurrence ∈ selection.taken ++ selection.read, occurrence ∉ firstSelection.made) :
    ContextualActivatedStep.problem locals (afterFirst locals captures update.declaration) actualLedger selection
      (rule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures update.declaration).assignment)))
      (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
        firstSelection firstOutputs rows)
      (ContextualTransportedActivation.result locals captures (ContextualComputedFreshFrame.includeSource update)
        virtualLedger firstSelection firstRule rows before) =
    ContextualFrameUnifier.mapProblem (secondActive locals captures update.declaration relocation).assignment
      (ContextualFrameUnifier.mapProblem (first locals captures).assignment
          (ContextualActivatedStep.problem locals captures virtualLedger firstSelection firstRule rows before) ++
        ContextualFrameUnifier.mapProblem (second locals captures).assignment
          (ContextualActivatedStep.addedEquations locals captures virtualLedger selection rule rows)) := by
  have capturesAgree : (oldCaller locals captures update.declaration).assignment =
      Assignment.compose (ContextualComputedFreshFrame.includeSource update)
        (ContextualSelectionViews.capturedTarget locals captures) := by
    rw [← oldCaller_square, firstSource_actual]
  have selectedRows : ∀ occurrence ∈ selection.taken ++ selection.read,
      ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
        firstSelection firstOutputs rows occurrence =
      (rows occurrence).map locals (oldCaller locals captures update.declaration).assignment := by
    intro occurrence selected
    rw [ContextualTransportedActivation.retained_row_keeps_private_locals locals captures
      (ContextualComputedFreshFrame.includeSource update) firstSelection firstOutputs rows (untouched occurrence selected),
      capturesAgree]
  have incomingEq :
      (ContextualActivatedStep.frame locals (afterFirst locals captures update.declaration)
        (ContextualTransportedActivation.result locals captures (ContextualComputedFreshFrame.includeSource update)
          virtualLedger firstSelection firstRule rows before)).equations =
      ContextualFrameUnifier.mapProblem (secondActive locals captures update.declaration relocation).assignment
        (ContextualFrameUnifier.mapProblem (first locals captures).assignment
          (ContextualActivatedStep.problem locals captures virtualLedger firstSelection firstRule rows before)) := by
    change ContextualFrameUnifier.mapProblem
      (ContextualSelectionViews.capturedTarget locals (afterFirst locals captures update.declaration))
      (ContextualFrameUnifier.mapProblem (ContextualComputedFreshFrame.includeSource update) _) = _
    rw [ContextualComputedFreshFrame.map_compose, ContextualComputedFreshFrame.map_compose,
      first_activation_square, firstSource_actual]
    rfl
  have contribution := second_added_equations locals captures update.declaration virtualLedger actualLedger
    selection relocation aligned rule rows
  rw [secondView, ← ContextualComputedFreshFrame.map_compose] at contribution
  apply (ContextualActivatedStep.problem_eq_frame_append locals (afterFirst locals captures update.declaration)
    actualLedger selection
    (rule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures update.declaration).assignment)))
    (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
      firstSelection firstOutputs rows)
    (ContextualTransportedActivation.result locals captures (ContextualComputedFreshFrame.includeSource update)
      virtualLedger firstSelection firstRule rows before)).trans
  exact (congrArg₂ List.append incomingEq
    ((ContextualActivatedStep.addedEquations_rows_congr locals (afterFirst locals captures update.declaration)
      actualLedger selection _ selectedRows).trans contribution.symm)).trans
    (ContextualTransportedActivation.map_append _ _ _).symm

theorem second_solvable_iff_joint [DecidableEq O]
    (firstSelection : Selection O)
    (firstRule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (before : Configuration (Term (signature S captures) Γ sort) O)
    (firstOutputs : O → Term (signature S (ContextualSelectionViews.target locals captures)) Γ sort)
    (update : ContextualFrameUpdate.Update (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals captures virtualLedger firstSelection firstRule rows before)))
    (untouched : ∀ occurrence ∈ selection.taken ++ selection.read, occurrence ∉ firstSelection.made) :
    ContextualFrameUnifier.Solvable
      (ContextualActivatedStep.problem locals (afterFirst locals captures update.declaration) actualLedger selection
        (rule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures update.declaration).assignment)))
        (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
          firstSelection firstOutputs rows)
        (ContextualTransportedActivation.result locals captures (ContextualComputedFreshFrame.includeSource update)
          virtualLedger firstSelection firstRule rows before)) ↔
    ContextualFrameUnifier.Solvable
      (ContextualFrameUnifier.mapProblem (first locals captures).assignment
          (ContextualActivatedStep.problem locals captures virtualLedger firstSelection firstRule rows before) ++
        ContextualFrameUnifier.mapProblem (second locals captures).assignment
          (ContextualActivatedStep.addedEquations locals captures virtualLedger selection rule rows)) := by
  rw [second_problem_after_first locals captures virtualLedger actualLedger selection relocation aligned
    rule rows firstSelection firstRule before firstOutputs update untouched]
  exact (secondActive locals captures update.declaration relocation).exists_model_iff _

omit aligned in
/-- The common frame describes every surviving row, including schemas and
new shared outputs. It is then embedded into the actual second activation. -/
theorem second_guard_rows [DecidableEq O]
    (firstSelection : Selection O)
    (firstRule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (before : Configuration (Term (signature S captures) Γ sort) O)
    (firstOutputs : O → Term (signature S (ContextualSelectionViews.target locals captures)) Γ sort)
    (update : ContextualFrameUpdate.Update (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals captures virtualLedger firstSelection firstRule rows before))) :
    ContextualGuardedStep.guardRows locals (afterFirst locals captures update.declaration)
      (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
        firstSelection firstOutputs rows) =
    fun occurrence => (rowsAfterFirst locals captures rows firstSelection firstOutputs occurrence).map locals
      (secondActive locals captures update.declaration relocation).assignment := by
  funext occurrence
  by_cases made : occurrence ∈ firstSelection.made
  · simp only [ContextualGuardedStep.guardRows, ContextualTransportedActivation.resultRows,
      ContextualActivatedStep.resultRows, rowsAfterFirst, if_pos made, ContextualStoredRows.Row.map]
    apply congrArg ContextualStoredRows.Row.shared
    rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose,
      first_activation_square, firstSource_actual]
  · simp only [ContextualGuardedStep.guardRows, ContextualTransportedActivation.resultRows,
      ContextualActivatedStep.resultRows, rowsAfterFirst, if_neg made, ContextualStoredRows.Row.map_compose]
    apply congrArg (fun mapping => (rows occurrence).map locals mapping)
    rw [← firstSource_actual, Assignment.compose_associative, ← first_activation_square,
      ← Assignment.compose_associative, first_caller]

/-- Original-cut questions in the common two-event presentation agree with
the actual second event's questions, across its unknown helper family. -/
theorem second_ask_iff_common [DecidableEq O]
    (firstSelection : Selection O)
    (firstRule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (before : Configuration (Term (signature S captures) Γ sort) O)
    (firstOutputs : O → Term (signature S (ContextualSelectionViews.target locals captures)) Γ sort)
    (update : ContextualFrameUpdate.Update (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals captures virtualLedger firstSelection firstRule rows before)))
    (untouched : ∀ occurrence ∈ selection.taken ++ selection.read, occurrence ∉ firstSelection.made)
    (check : Check (Term (signature S (ContextualSelectionViews.target locals captures)) Γ sort)) :
    ContextualGuardSemantics.Ask locals
      (ContextualActivatedStep.problem locals (afterFirst locals captures update.declaration) actualLedger selection
        (rule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures update.declaration).assignment)))
        (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
          firstSelection firstOutputs rows)
        (ContextualTransportedActivation.result locals captures (ContextualComputedFreshFrame.includeSource update)
          virtualLedger firstSelection firstRule rows before))
      (ContextualGuardedStep.guardRows locals (afterFirst locals captures update.declaration)
        (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
          firstSelection firstOutputs rows))
      (ContextualTransportedActivation.result locals captures (ContextualComputedFreshFrame.includeSource update)
        virtualLedger firstSelection firstRule rows before).present
      (check.map (instantiate (secondView locals captures update.declaration relocation))) ↔
    ContextualGuardSemantics.Ask locals
      (jointProblem locals captures virtualLedger selection rule rows firstSelection firstRule before)
      (rowsAfterFirst locals captures rows firstSelection firstOutputs)
      (MeTTaCalculus.OccurrenceCommits.fire before.present (firstSelection.commit (T := Unit)))
      (check.map (instantiate (second locals captures).assignment)) := by
  have reflected := ContextualGuardSemantics.Ask.extension_iff locals
    (secondActive locals captures update.declaration relocation)
    (jointProblem locals captures virtualLedger selection rule rows firstSelection firstRule before)
    (rowsAfterFirst locals captures rows firstSelection firstOutputs)
    (MeTTaCalculus.OccurrenceCommits.fire before.present (firstSelection.commit (T := Unit)))
    (check.map (instantiate (second locals captures).assignment))
  have checkMaps : (check.map (instantiate (second locals captures).assignment)).map
      (instantiate (secondActive locals captures update.declaration relocation).assignment) =
      check.map (instantiate (secondView locals captures update.declaration relocation)) := by
    cases check <;> simp only [Check.map, secondView, Assignment.instantiate_compose]
  dsimp only [jointProblem] at reflected
  rw [← second_problem_after_first locals captures virtualLedger actualLedger selection relocation aligned
    rule rows firstSelection firstRule before firstOutputs update untouched,
    ← second_guard_rows locals captures virtualLedger relocation rows firstSelection firstRule before firstOutputs update,
    checkMaps] at reflected
  exact reflected

/-- Pattern completeness is checked once in the common problem and carried
through the actual frame embedding; no second completed run is assumed. -/
theorem second_problem_pattern [DecidableEq O]
    (firstSelection : Selection O)
    (firstRule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (before : Configuration (Term (signature S captures) Γ sort) O)
    (firstOutputs : O → Term (signature S (ContextualSelectionViews.target locals captures)) Γ sort)
    (update : ContextualFrameUpdate.Update (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals captures virtualLedger firstSelection firstRule rows before)))
    (untouched : ∀ occurrence ∈ selection.taken ++ selection.read, occurrence ∉ firstSelection.made)
    (patterned : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
      (jointProblem locals captures virtualLedger selection rule rows firstSelection firstRule before))) :
    ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals (afterFirst locals captures update.declaration) actualLedger selection
        (rule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures update.declaration).assignment)))
        (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
          firstSelection firstOutputs rows)
        (ContextualTransportedActivation.result locals captures (ContextualComputedFreshFrame.includeSource update)
          virtualLedger firstSelection firstRule rows before))) := by
  rw [second_problem_after_first locals captures virtualLedger actualLedger selection relocation aligned
    rule rows firstSelection firstRule before firstOutputs update untouched,
    ContextualResidual.observeProblem_mapProblem]
  exact ContextualPatternFragment.map_patterns
    (secondActive locals captures update.declaration relocation).assignment
    (ContextualNamedPatternImages.reindex_images _ _) _ patterned

omit aligned in
/-- The entire final row inventory, including produced shared terms and
unselected schemas, is the common row inventory embedded into the actual
second activation. No equality of private helper families is required. -/
theorem second_result_rows [DecidableEq O]
    (firstSelection : Selection O)
    (firstRule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (before : Configuration (Term (signature S captures) Γ sort) O)
    (firstOutputs secondOutputs : O → Term (signature S (ContextualSelectionViews.target locals captures)) Γ sort)
    (update : ContextualFrameUpdate.Update (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals captures virtualLedger firstSelection firstRule rows before))) :
    ContextualActivatedStep.resultRows locals (afterFirst locals captures update.declaration) selection
      (fun occurrence => instantiate (secondView locals captures update.declaration relocation) (secondOutputs occurrence))
      (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
        firstSelection firstOutputs rows) =
    fun occurrence => (rowsAfterBoth locals captures rows firstSelection selection firstOutputs secondOutputs occurrence).map locals
      (secondActive locals captures update.declaration relocation).assignment := by
  funext occurrence
  by_cases made : occurrence ∈ selection.made
  · simp only [ContextualActivatedStep.resultRows, rowsAfterBoth, if_pos made, ContextualStoredRows.Row.map]
    apply congrArg ContextualStoredRows.Row.shared
    exact Assignment.instantiate_compose _ _ _
  · simp only [ContextualActivatedStep.resultRows, rowsAfterBoth, if_neg made]
    exact congrFun (second_guard_rows locals captures virtualLedger relocation rows firstSelection firstRule before
      firstOutputs update) occurrence

/-- Every all-future equality, absence or occurrence-count query on the
common final interface is preserved and reflected after the second
activation. The first event's constraints remain in the joint problem. -/
theorem second_result_ask_iff_common [DecidableEq O]
    (firstSelection : Selection O)
    (firstRule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (before : Configuration (Term (signature S captures) Γ sort) O)
    (firstOutputs secondOutputs : O → Term (signature S (ContextualSelectionViews.target locals captures)) Γ sort)
    (update : ContextualFrameUpdate.Update (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals captures virtualLedger firstSelection firstRule rows before)))
    (untouched : ∀ occurrence ∈ selection.taken ++ selection.read, occurrence ∉ firstSelection.made)
    (check : Check (Term (signature S (common locals captures)) Γ sort)) :
    ContextualGuardSemantics.Ask locals
      (ContextualActivatedStep.problem locals (afterFirst locals captures update.declaration) actualLedger selection
        (rule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures update.declaration).assignment)))
        (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
          firstSelection firstOutputs rows)
        (ContextualTransportedActivation.result locals captures (ContextualComputedFreshFrame.includeSource update)
          virtualLedger firstSelection firstRule rows before))
      (ContextualActivatedStep.resultRows locals (afterFirst locals captures update.declaration) selection
        (fun occurrence => instantiate (secondView locals captures update.declaration relocation) (secondOutputs occurrence))
        (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
          firstSelection firstOutputs rows))
      (MeTTaCalculus.OccurrenceCommits.fire
        (MeTTaCalculus.OccurrenceCommits.fire before.present (firstSelection.commit (T := Unit)))
        (selection.commit (T := Unit)))
      (check.map (instantiate (secondActive locals captures update.declaration relocation).assignment)) ↔
    ContextualGuardSemantics.Ask locals
      (jointProblem locals captures virtualLedger selection rule rows firstSelection firstRule before)
      (rowsAfterBoth locals captures rows firstSelection selection firstOutputs secondOutputs)
      (MeTTaCalculus.OccurrenceCommits.fire
        (MeTTaCalculus.OccurrenceCommits.fire before.present (firstSelection.commit (T := Unit)))
        (selection.commit (T := Unit))) check := by
  rw [second_problem_after_first locals captures virtualLedger actualLedger selection relocation aligned rule rows
    firstSelection firstRule before firstOutputs update untouched,
    second_result_rows locals captures virtualLedger selection relocation rows firstSelection firstRule before
      firstOutputs secondOutputs update]
  exact ContextualGuardSemantics.Ask.extension_iff locals
    (secondActive locals captures update.declaration relocation) _ _ _ check

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairFrames

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairFrames

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {Local Shared O : Type} [DecidableEq O]
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
  {Γ : Ctx S} {sort : S.Srt}
  (rows : O → ContextualStoredRows.Row locals captures Γ sort)
  (producer : Selection O)
  (produced : O → Term (signature S (ContextualSelectionViews.target locals captures)) Γ sort)

/-- A produced occurrence keeps its producer's shared variables. An older
schema instead opens at the consumer port's own fresh scope. -/
def causalInput (scope : Nat) (occurrence : O) : Term (signature S (common locals captures)) Γ sort :=
  if occurrence ∈ producer.made then instantiate (first locals captures).assignment (produced occurrence)
  else instantiate (second locals captures).assignment (ContextualStoredRows.viewAt locals captures scope (rows occurrence))

variable (occupied : Finset Nat) (consumer : Selection O)
  (consumerRule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))

def causalAdded : EquationStore (Term (signature S (common locals captures)) Γ sort) :=
  let prepared := ContextualActivatedStep.prepared locals captures occupied consumer consumerRule rows
  ContextualActivatedStep.useEquations (prepared.rule.take.map (instantiate (second locals captures).assignment))
    (List.ofFn fun port => causalInput locals captures rows producer produced
      (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.takePort consumer port)) (consumer.taken.get port)) ++
  ContextualActivatedStep.useEquations (prepared.rule.read.map (instantiate (second locals captures).assignment))
    (List.ofFn fun port => causalInput locals captures rows producer produced
      (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.readPort consumer port)) (consumer.read.get port)) ++
  ContextualFrameUnifier.mapProblem (second locals captures).assignment prepared.rule.tell

variable (producerRule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
  (before : Configuration (Term (signature S captures) Γ sort) O)

def causalProblem : EquationStore (Term (signature S (common locals captures)) Γ sort) :=
  ContextualFrameUnifier.mapProblem (first locals captures).assignment
    (ContextualActivatedStep.problem locals captures occupied producer producerRule rows before) ++
  causalAdded locals captures rows producer produced occupied consumer consumerRule

variable (actualLedger : Finset Nat) (relocation : Equiv.Perm Nat)
  (update : ContextualFrameUpdate.Update (ContextualResidual.observeProblem
    (ContextualActivatedStep.problem locals captures occupied producer producerRule rows before)))

/-- Each actual consumer view is the corresponding common origin view.
Fresh scope allocation changes old schemas, never the identity of a shared
value just published by the producer. -/
theorem causal_input_transport (scope : Nat) (occurrence : O) :
    instantiate (secondActive locals captures update.declaration relocation).assignment
      (causalInput locals captures rows producer produced scope occurrence) =
    ContextualStoredRows.viewAt locals (afterFirst locals captures update.declaration) (relocation scope)
      (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
        producer produced rows occurrence) := by
  by_cases made : occurrence ∈ producer.made
  · simp only [causalInput, if_pos made, ContextualTransportedActivation.resultRows,
      ContextualActivatedStep.resultRows, ContextualStoredRows.Row.map, ContextualStoredRows.viewAt]
    rw [← Assignment.instantiate_compose, first_activation_square, firstSource_actual,
      Assignment.instantiate_compose]
  · have old := ContextualTransportedActivation.retained_row_keeps_private_locals locals captures
      (ContextualComputedFreshFrame.includeSource update) producer produced rows made
    have capturesAgree : Assignment.compose (ContextualComputedFreshFrame.includeSource update)
        (ContextualSelectionViews.capturedTarget locals captures) =
        (oldCaller locals captures update.declaration).assignment := by
      rw [← firstSource_actual, oldCaller_square]
    rw [causalInput, if_neg made, old, capturesAgree,
      ← second_view_row locals captures update.declaration relocation scope (rows occurrence)]
    exact (Assignment.instantiate_compose _ _ _).symm

variable (aligned : ∀ port : ContextualActivationScopes.Port consumer,
  relocation (ContextualActivationScopes.scopeAt occupied port) =
    ContextualActivationScopes.scopeAt actualLedger port)

include aligned

theorem causal_added_transport :
    ContextualFrameUnifier.mapProblem (secondActive locals captures update.declaration relocation).assignment
      (causalAdded locals captures rows producer produced occupied consumer consumerRule) =
    ContextualActivatedStep.addedEquations locals (afterFirst locals captures update.declaration) actualLedger consumer
      (consumerRule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures update.declaration).assignment)))
      (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
        producer produced rows) := by
  have mapped :
      ((ContextualActivatedStep.prepared locals captures occupied consumer consumerRule rows).rule.map
        (instantiate (second locals captures).assignment)).map
          (instantiate (secondActive locals captures update.declaration relocation).assignment) =
      (ContextualActivatedStep.prepared locals (afterFirst locals captures update.declaration) actualLedger consumer
        (consumerRule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures update.declaration).assignment)))
        (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
          producer produced rows)).rule := by
    rw [OccurrenceRelabeling.rule_map_comp]
    have functions : (instantiate (secondActive locals captures update.declaration relocation).assignment ∘
        instantiate (second locals captures).assignment) = instantiate (secondView locals captures update.declaration relocation)
        (Γ := Γ) (sort := sort) := by
      funext value
      exact (Assignment.instantiate_compose _ _ _).symm
    rw [functions]
    exact second_rule_preparation locals captures update.declaration occupied actualLedger consumer relocation aligned consumerRule rows
  have takes := congrArg RuleInstance.take mapped
  have reads := congrArg RuleInstance.read mapped
  have tells := congrArg RuleInstance.tell mapped
  have takeViews :
      (List.ofFn fun port => causalInput locals captures rows producer produced
        (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.takePort consumer port))
        (consumer.taken.get port)).map (instantiate (secondActive locals captures update.declaration relocation).assignment) =
      List.ofFn (ContextualActivatedStep.prepared locals (afterFirst locals captures update.declaration) actualLedger consumer
        (consumerRule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures update.declaration).assignment)))
        (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
          producer produced rows)).taken := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext port
    rw [ContextualActivatedStep.prepared_taken_view]
    apply (causal_input_transport locals captures rows producer produced occupied producerRule before relocation update
      (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.takePort consumer port))
      (consumer.taken.get port)).trans
    exact congrArg (fun scope => ContextualStoredRows.viewAt locals (afterFirst locals captures update.declaration) scope
      (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
        producer produced rows (consumer.taken.get port))) (aligned (ContextualActivationScopes.takePort consumer port))
  have readViews :
      (List.ofFn fun port => causalInput locals captures rows producer produced
        (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.readPort consumer port))
        (consumer.read.get port)).map (instantiate (secondActive locals captures update.declaration relocation).assignment) =
      List.ofFn (ContextualActivatedStep.prepared locals (afterFirst locals captures update.declaration) actualLedger consumer
        (consumerRule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures update.declaration).assignment)))
        (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
          producer produced rows)).read := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext port
    rw [ContextualActivatedStep.prepared_read_view]
    apply (causal_input_transport locals captures rows producer produced occupied producerRule before relocation update
      (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.readPort consumer port))
      (consumer.read.get port)).trans
    exact congrArg (fun scope => ContextualStoredRows.viewAt locals (afterFirst locals captures update.declaration) scope
      (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
        producer produced rows (consumer.read.get port))) (aligned (ContextualActivationScopes.readPort consumer port))
  dsimp only [RuleInstance.map] at takes reads tells
  change ContextualFrameUnifier.mapProblem (secondActive locals captures update.declaration relocation).assignment
    (ContextualFrameUnifier.mapProblem (second locals captures).assignment
      (ContextualActivatedStep.prepared locals captures occupied consumer consumerRule rows).rule.tell) = _ at tells
  simp only [causalAdded, ContextualActivatedStep.addedEquations, ContextualTransportedActivation.map_append,
    ContextualTransportedActivation.map_useEquations, takes, reads, tells, takeViews, readViews]
  rfl

/-- Causal composition keeps the producer equations and uses its actual shared
outputs in consumer ports. It neither freshens those outputs as schemas nor
assumes that the consumer's inputs already existed before the producer. -/
theorem causal_problem_after_first :
    ContextualActivatedStep.problem locals (afterFirst locals captures update.declaration) actualLedger consumer
      (consumerRule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures update.declaration).assignment)))
      (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
        producer produced rows)
      (ContextualTransportedActivation.result locals captures (ContextualComputedFreshFrame.includeSource update)
        occupied producer producerRule rows before) =
    ContextualFrameUnifier.mapProblem (secondActive locals captures update.declaration relocation).assignment
      (causalProblem locals captures rows producer produced occupied consumer consumerRule producerRule before) := by
  have incomingEq :
      (ContextualActivatedStep.frame locals (afterFirst locals captures update.declaration)
        (ContextualTransportedActivation.result locals captures (ContextualComputedFreshFrame.includeSource update)
          occupied producer producerRule rows before)).equations =
      ContextualFrameUnifier.mapProblem (secondActive locals captures update.declaration relocation).assignment
        (ContextualFrameUnifier.mapProblem (first locals captures).assignment
          (ContextualActivatedStep.problem locals captures occupied producer producerRule rows before)) := by
    change ContextualFrameUnifier.mapProblem
      (ContextualSelectionViews.capturedTarget locals (afterFirst locals captures update.declaration))
      (ContextualFrameUnifier.mapProblem (ContextualComputedFreshFrame.includeSource update) _) = _
    rw [ContextualComputedFreshFrame.map_compose, ContextualComputedFreshFrame.map_compose,
      first_activation_square, firstSource_actual]
    rfl
  apply (ContextualActivatedStep.problem_eq_frame_append locals (afterFirst locals captures update.declaration)
    actualLedger consumer
    (consumerRule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures update.declaration).assignment)))
    (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
      producer produced rows)
    (ContextualTransportedActivation.result locals captures (ContextualComputedFreshFrame.includeSource update)
      occupied producer producerRule rows before)).trans
  exact (congrArg₂ List.append incomingEq
    (causal_added_transport locals captures rows producer produced occupied consumer consumerRule producerRule before
      actualLedger relocation update aligned).symm).trans (ContextualTransportedActivation.map_append _ _ _).symm

omit aligned in
theorem causal_added_eq_independent
    (untouched : ∀ occurrence ∈ consumer.taken ++ consumer.read, occurrence ∉ producer.made) :
    causalAdded locals captures rows producer produced occupied consumer consumerRule =
    ContextualFrameUnifier.mapProblem (second locals captures).assignment
      (ContextualActivatedStep.addedEquations locals captures occupied consumer consumerRule rows) := by
  have takes :
      (List.ofFn fun port => causalInput locals captures rows producer produced
        (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.takePort consumer port)) (consumer.taken.get port)) =
      (List.ofFn (ContextualActivatedStep.prepared locals captures occupied consumer consumerRule rows).taken).map
        (instantiate (second locals captures).assignment) := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext port
    dsimp only [Function.comp_def]
    rw [ContextualActivatedStep.prepared_taken_view, causalInput,
      if_neg (untouched _ (List.mem_append_left _ (List.get_mem _ _)))]
  have reads :
      (List.ofFn fun port => causalInput locals captures rows producer produced
        (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.readPort consumer port)) (consumer.read.get port)) =
      (List.ofFn (ContextualActivatedStep.prepared locals captures occupied consumer consumerRule rows).read).map
        (instantiate (second locals captures).assignment) := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext port
    dsimp only [Function.comp_def]
    rw [ContextualActivatedStep.prepared_read_view, causalInput,
      if_neg (untouched _ (List.mem_append_right _ (List.get_mem _ _)))]
  simp only [causalAdded, ContextualActivatedStep.addedEquations,
    ContextualTransportedActivation.map_append, ContextualTransportedActivation.map_useEquations, takes, reads]

omit aligned in
/-- Independently available inputs recover the earlier common problem
exactly. The causal construction extends that result rather than replacing
it with an unrelated transition relation. -/
theorem causal_problem_eq_joint
    (untouched : ∀ occurrence ∈ consumer.taken ++ consumer.read, occurrence ∉ producer.made) :
    causalProblem locals captures rows producer produced occupied consumer consumerRule producerRule before =
      jointProblem locals captures occupied consumer consumerRule rows producer producerRule before := by
  rw [causalProblem, causal_added_eq_independent locals captures rows producer produced occupied consumer consumerRule untouched]
  rfl

theorem causal_solvable_iff :
    ContextualFrameUnifier.Solvable
      (ContextualActivatedStep.problem locals (afterFirst locals captures update.declaration) actualLedger consumer
        (consumerRule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures update.declaration).assignment)))
        (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
          producer produced rows)
        (ContextualTransportedActivation.result locals captures (ContextualComputedFreshFrame.includeSource update)
          occupied producer producerRule rows before)) ↔
    ContextualFrameUnifier.Solvable
      (causalProblem locals captures rows producer produced occupied consumer consumerRule producerRule before) := by
  rw [causal_problem_after_first locals captures rows producer produced occupied consumer consumerRule producerRule before
    actualLedger relocation update aligned]
  exact (secondActive locals captures update.declaration relocation).exists_model_iff _

theorem causal_ask_iff (check : Check (Term (signature S (common locals captures)) Γ sort)) :
    ContextualGuardSemantics.Ask locals
      (ContextualActivatedStep.problem locals (afterFirst locals captures update.declaration) actualLedger consumer
        (consumerRule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures update.declaration).assignment)))
        (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
          producer produced rows)
        (ContextualTransportedActivation.result locals captures (ContextualComputedFreshFrame.includeSource update)
          occupied producer producerRule rows before))
      (ContextualGuardedStep.guardRows locals (afterFirst locals captures update.declaration)
        (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
          producer produced rows))
      (MeTTaCalculus.OccurrenceCommits.fire before.present (producer.commit (T := Unit)))
      (check.map (instantiate (secondActive locals captures update.declaration relocation).assignment)) ↔
    ContextualGuardSemantics.Ask locals
      (causalProblem locals captures rows producer produced occupied consumer consumerRule producerRule before)
      (rowsAfterFirst locals captures rows producer produced)
      (MeTTaCalculus.OccurrenceCommits.fire before.present (producer.commit (T := Unit))) check := by
  rw [causal_problem_after_first locals captures rows producer produced occupied consumer consumerRule producerRule before
    actualLedger relocation update aligned,
    second_guard_rows locals captures occupied relocation rows producer producerRule before produced update]
  exact ContextualGuardSemantics.Ask.extension_iff locals
    (secondActive locals captures update.declaration relocation) _ _ _ check

theorem causal_pattern
    (patterned : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
      (causalProblem locals captures rows producer produced occupied consumer consumerRule producerRule before))) :
    ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals (afterFirst locals captures update.declaration) actualLedger consumer
        (consumerRule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures update.declaration).assignment)))
        (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
          producer produced rows)
        (ContextualTransportedActivation.result locals captures (ContextualComputedFreshFrame.includeSource update)
          occupied producer producerRule rows before))) := by
  rw [causal_problem_after_first locals captures rows producer produced occupied consumer consumerRule producerRule before
    actualLedger relocation update aligned, ContextualResidual.observeProblem_mapProblem]
  exact ContextualPatternFragment.map_patterns
    (secondActive locals captures update.declaration relocation).assignment
    (ContextualNamedPatternImages.reindex_images _ _) _ patterned

theorem causal_result_ask_iff
    (consumerOutputs : O → Term (signature S (ContextualSelectionViews.target locals captures)) Γ sort)
    (check : Check (Term (signature S (common locals captures)) Γ sort)) :
    ContextualGuardSemantics.Ask locals
      (ContextualActivatedStep.problem locals (afterFirst locals captures update.declaration) actualLedger consumer
        (consumerRule.map (instantiate (ContextualStoredRows.liftCaptures locals (oldCaller locals captures update.declaration).assignment)))
        (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
          producer produced rows)
        (ContextualTransportedActivation.result locals captures (ContextualComputedFreshFrame.includeSource update)
          occupied producer producerRule rows before))
      (ContextualActivatedStep.resultRows locals (afterFirst locals captures update.declaration) consumer
        (fun occurrence => instantiate (secondView locals captures update.declaration relocation) (consumerOutputs occurrence))
        (ContextualTransportedActivation.resultRows locals captures (ContextualComputedFreshFrame.includeSource update)
          producer produced rows))
      (MeTTaCalculus.OccurrenceCommits.fire
        (MeTTaCalculus.OccurrenceCommits.fire before.present (producer.commit (T := Unit))) (consumer.commit (T := Unit)))
      (check.map (instantiate (secondActive locals captures update.declaration relocation).assignment)) ↔
    ContextualGuardSemantics.Ask locals
      (causalProblem locals captures rows producer produced occupied consumer consumerRule producerRule before)
      (rowsAfterBoth locals captures rows producer consumer produced consumerOutputs)
      (MeTTaCalculus.OccurrenceCommits.fire
        (MeTTaCalculus.OccurrenceCommits.fire before.present (producer.commit (T := Unit))) (consumer.commit (T := Unit))) check := by
  rw [causal_problem_after_first locals captures rows producer produced occupied consumer consumerRule producerRule before
    actualLedger relocation update aligned,
    second_result_rows locals captures occupied consumer relocation rows producer producerRule before
      produced consumerOutputs update]
  exact ContextualGuardSemantics.Ask.extension_iff locals
    (secondActive locals captures update.declaration relocation) _ _ _ check

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairFrames

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairFrames

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualGuardMatching

set_option backward.isDefEq.respectTransparency false

variable {S : Signature} {Local Shared O : Type}
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)

def exchangeEventNames : ScopedVar Local ⊕ (ScopedVar Local ⊕ Shared) →
    ScopedVar Local ⊕ (ScopedVar Local ⊕ Shared)
  | .inl name => .inr (.inl name)
  | .inr (.inl name) => .inl name
  | .inr (.inr name) => .inr (.inr name)

theorem exchangeEventNames_twice (name : ScopedVar Local ⊕ (ScopedVar Local ⊕ Shared)) :
    exchangeEventNames (exchangeEventNames name) = name := by
  rcases name with name | (name | name) <;> rfl

abbrev exchangeEvents : Extension (common locals captures) where
  Names := ScopedVar Local ⊕ (ScopedVar Local ⊕ Shared)
  declarations := common locals captures
  name := exchangeEventNames
  injective := Function.LeftInverse.injective exchangeEventNames_twice
  preserves name := by rcases name with name | (name | name) <;> rfl

theorem exchange_first :
    Assignment.compose (exchangeEvents locals captures).assignment (first locals captures).assignment =
      (second locals captures).assignment := by
  funext name
  cases name <;> exact instantiate_generator _ _

theorem exchange_second :
    Assignment.compose (exchangeEvents locals captures).assignment (second locals captures).assignment =
      (first locals captures).assignment := by
  funext name
  cases name <;> exact instantiate_generator _ _

theorem exchange_caller :
    Assignment.compose (exchangeEvents locals captures).assignment (caller locals captures) = caller locals captures := by
  funext name
  exact instantiate_generator _ _

variable {Γ : Ctx S} {sort : S.Srt} (occupied : Finset Nat)
  (firstSelection secondSelection : Selection O)
  (firstRule secondRule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
  (rows : O → ContextualStoredRows.Row locals captures Γ sort)
  (before : Configuration (Term (signature S captures) Γ sort) O)

/-- Incoming equations occur once. Each event contributes its independently
prepared views and tells, in its own private summand. -/
theorem joint_problem_parts :
    jointProblem locals captures occupied secondSelection secondRule rows firstSelection firstRule before =
      ContextualFrameUnifier.mapProblem (caller locals captures) before.equations ++
        (ContextualFrameUnifier.mapProblem (first locals captures).assignment
          (ContextualActivatedStep.addedEquations locals captures occupied firstSelection firstRule rows) ++
         ContextualFrameUnifier.mapProblem (second locals captures).assignment
          (ContextualActivatedStep.addedEquations locals captures occupied secondSelection secondRule rows)) := by
  rw [jointProblem, ContextualActivatedStep.problem_eq_frame_append,
    ContextualTransportedActivation.map_append]
  change (_ ++ _) ++ _ = _
  rw [List.append_assoc]
  congr 1
  change ContextualFrameUnifier.mapProblem (first locals captures).assignment
    (ContextualFrameUnifier.mapProblem (ContextualSelectionViews.capturedTarget locals captures) before.equations) = _
  rw [ContextualComputedFreshFrame.map_compose, first_caller]

/-- Swapping event-private summands and equation order preserves the entire
joint model set. The caller summand and incoming constraints stay fixed. -/
theorem joint_models_exchange {Future : Type} (future : Future → MetaArity S)
    (candidate : Assignment (common locals captures) future) :
    ContextualFrameUnifier.Models candidate
      (ContextualFrameUnifier.mapProblem (exchangeEvents locals captures).assignment
        (jointProblem locals captures occupied secondSelection secondRule rows firstSelection firstRule before)) ↔
    ContextualFrameUnifier.Models candidate
      (jointProblem locals captures occupied firstSelection firstRule rows secondSelection secondRule before) := by
  rw [joint_problem_parts, joint_problem_parts]
  simp only [ContextualTransportedActivation.map_append, ContextualComputedFreshFrame.map_compose,
    exchange_caller locals captures, exchange_first locals captures, exchange_second locals captures,
    ContextualFrameUnifier.models_append]
  tauto

variable [DecidableEq O]
  (firstOutputs secondOutputs : O → Term (signature S (ContextualSelectionViews.target locals captures)) Γ sort)

theorem final_rows_exchange (apart : Disjoint firstSelection.made.toFinset secondSelection.made.toFinset) :
    (fun occurrence => (rowsAfterBoth locals captures rows firstSelection secondSelection firstOutputs secondOutputs occurrence).map
      locals (exchangeEvents locals captures).assignment) =
    rowsAfterBoth locals captures rows secondSelection firstSelection secondOutputs firstOutputs := by
  funext occurrence
  by_cases madeFirst : occurrence ∈ firstSelection.made
  · have notSecond : occurrence ∉ secondSelection.made := fun member =>
      Finset.disjoint_left.mp apart (List.mem_toFinset.mpr madeFirst) (List.mem_toFinset.mpr member)
    simp only [rowsAfterBoth, rowsAfterFirst, if_pos madeFirst, if_neg notSecond, ContextualStoredRows.Row.map]
    apply congrArg ContextualStoredRows.Row.shared
    rw [← Assignment.instantiate_compose, exchange_first]
  · by_cases madeSecond : occurrence ∈ secondSelection.made
    · simp only [rowsAfterBoth, rowsAfterFirst, if_neg madeFirst, if_pos madeSecond, ContextualStoredRows.Row.map]
      apply congrArg ContextualStoredRows.Row.shared
      rw [← Assignment.instantiate_compose, exchange_second]
    · simp only [rowsAfterBoth, rowsAfterFirst, if_neg madeFirst, if_neg madeSecond,
        ContextualStoredRows.Row.map_compose, exchange_caller locals captures]

/-- The final observations agree under event exchange, provided the two
physical orders have the same result. This comparison does not identify
the intermediate states or any externally visible execution history. -/
theorem final_asks_exchange
    (apart : Disjoint firstSelection.made.toFinset secondSelection.made.toFinset)
    (sameWorld : MeTTaCalculus.OccurrenceCommits.fire
        (MeTTaCalculus.OccurrenceCommits.fire before.present (firstSelection.commit (T := Unit)))
        (secondSelection.commit (T := Unit)) =
      MeTTaCalculus.OccurrenceCommits.fire
        (MeTTaCalculus.OccurrenceCommits.fire before.present (secondSelection.commit (T := Unit)))
        (firstSelection.commit (T := Unit)))
    (check : Check (Term (signature S (common locals captures)) Γ sort)) :
    ContextualGuardSemantics.Ask locals
      (jointProblem locals captures occupied secondSelection secondRule rows firstSelection firstRule before)
      (rowsAfterBoth locals captures rows firstSelection secondSelection firstOutputs secondOutputs)
      (MeTTaCalculus.OccurrenceCommits.fire
        (MeTTaCalculus.OccurrenceCommits.fire before.present (firstSelection.commit (T := Unit)))
        (secondSelection.commit (T := Unit))) check ↔
    ContextualGuardSemantics.Ask locals
      (jointProblem locals captures occupied firstSelection firstRule rows secondSelection secondRule before)
      (rowsAfterBoth locals captures rows secondSelection firstSelection secondOutputs firstOutputs)
      (MeTTaCalculus.OccurrenceCommits.fire
        (MeTTaCalculus.OccurrenceCommits.fire before.present (secondSelection.commit (T := Unit)))
        (firstSelection.commit (T := Unit)))
      (check.map (instantiate (exchangeEvents locals captures).assignment)) := by
  have extension := ContextualGuardSemantics.Ask.extension_iff locals (exchangeEvents locals captures)
    (jointProblem locals captures occupied secondSelection secondRule rows firstSelection firstRule before)
    (rowsAfterBoth locals captures rows firstSelection secondSelection firstOutputs secondOutputs)
    (MeTTaCalculus.OccurrenceCommits.fire
      (MeTTaCalculus.OccurrenceCommits.fire before.present (firstSelection.commit (T := Unit)))
      (secondSelection.commit (T := Unit))) check
  rw [final_rows_exchange locals captures firstSelection secondSelection rows firstOutputs secondOutputs apart,
    sameWorld] at extension
  rw [sameWorld]
  refine extension.symm.trans ?_
  constructor <;> intro admitted Future future candidate model
  · exact admitted Future future candidate
      ((joint_models_exchange locals captures occupied firstSelection secondSelection firstRule secondRule rows before future candidate).mpr model)
  · exact admitted Future future candidate
      ((joint_models_exchange locals captures occupied firstSelection secondSelection firstRule secondRule rows before future candidate).mp model)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairFrames
