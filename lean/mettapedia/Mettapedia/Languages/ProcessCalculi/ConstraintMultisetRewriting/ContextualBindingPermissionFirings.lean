import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingPermissionGuards
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessTransport

/-!
# Binding permissions on actual computed contextual firings

The completed solver's helper frame contains the transported old equations
and the actual selected take/read/tell equations. Their split is computed
from existing activation data. The solver supplies consistency; an explicit
structural grant checks which dependencies may be refined.

The joint observation laws use this actual common declaration frame. The
original endpoint is related to it by the existing injective capture
extension. Guard transport retains the input row snapshot; it does not
assert that a physical write cannot change a current-world guard.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingPermissionFirings

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualBindingPermissions ContextualBindingPermissionGuards
open ContextualExecution ContextualSchedulePromotion

variable {S : Signature} {Local O : Type} {locals : Local → MetaArity S}
  [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  {Γ : Ctx S} {sort : S.Srt} {before after : Endpoint locals O Γ sort}

def incoming (prepared : Prepared locals before) :
    EquationStore (Term (signature S prepared.target.declarations) Γ sort) :=
  ContextualFrameUnifier.mapProblem (ContextualProcessTransport.captureExtension prepared).assignment
    before.inventory.configuration.equations

def additions (prepared : Prepared locals before) :
    EquationStore (Term (signature S prepared.target.declarations) Γ sort) :=
  let views := ContextualActivatedStep.prepared locals before.declarations before.occupied
    prepared.selection prepared.rule before.inventory.rows
  ContextualFrameUnifier.mapProblem (ContextualComputedFreshFrame.includeSource prepared.update)
    (ContextualActivatedStep.useEquations views.rule.take (List.ofFn views.taken) ++
      ContextualActivatedStep.useEquations views.rule.read (List.ofFn views.read) ++ views.rule.tell)

theorem incoming_is_mapped_frame (prepared : Prepared locals before) :
    incoming prepared =
      ContextualFrameUnifier.mapProblem (ContextualComputedFreshFrame.includeSource prepared.update)
        (ContextualActivatedStep.frame locals before.declarations before.inventory.configuration).equations := by
  unfold incoming ContextualProcessTransport.captureExtension
  rw [ContextualComputedFreshFrame.capturedDeclarationExtension_assignment]
  exact (ContextualComputedFreshFrame.map_compose
    (ContextualSelectionViews.capturedTarget locals before.declarations)
    (ContextualComputedFreshFrame.includeSource prepared.update) before.inventory.configuration.equations).symm

/-- The actual target contains exactly these equations; it is not an
independently invented update relation. -/
theorem target_equations_split (prepared : Prepared locals before) :
    prepared.target.inventory.configuration.equations = incoming prepared ++ additions prepared := by
  rw [incoming_is_mapped_frame]
  change ContextualFrameUnifier.mapProblem (ContextualComputedFreshFrame.includeSource prepared.update)
      (ContextualActivatedStep.problem locals before.declarations before.occupied prepared.selection
        prepared.rule before.inventory.rows before.inventory.configuration) = _
  simp only [ContextualActivatedStep.problem, additions, ContextualFrameUnifier.mapProblem,
    List.map_append, List.append_assoc]
  rfl

theorem actual_problem_consistent (prepared : Prepared locals before) :
    (ContextualFamilies.action prepared.target.declarations Γ sort).Consistent
      (incoming prepared ++ additions prepared) := by
  rw [← target_equations_split]
  exact ContextualComputedFreshFrame.consistent
    (ContextualActivatedStep.problem locals before.declarations before.occupied prepared.selection
      prepared.rule before.inventory.rows before.inventory.configuration)
    prepared.update prepared.finished

def computedAnswer (prepared : Prepared locals before) :
    Assignment prepared.target.declarations prepared.target.declarations :=
  ContextualComputedFreshFrame.answer prepared.update

theorem computedAnswer_models (prepared : Prepared locals before) :
    ContextualFrameUnifier.Models (computedAnswer prepared) (incoming prepared ++ additions prepared) := by
  rw [← target_equations_split]
  exact (ContextualComputedFreshFrame.principal_on
    (ContextualActivatedStep.problem locals before.declarations before.occupied prepared.selection
      prepared.rule before.inventory.rows before.inventory.configuration)
    prepared.update prepared.finished []).sound

def callerView (prepared : Prepared locals before) (observed : List (Observation S before.declarations)) :
    List (Observation S prepared.target.declarations) :=
  observed.map (instantiateObservation (ContextualProcessTransport.captureExtension prepared).assignment)

theorem prepared_joint_possible_iff (prepared : Prepared locals before)
    (granted : Set prepared.target.Names) (observed : List (Observation S before.declarations))
    (permission : Permitted granted (incoming prepared) (additions prepared) (callerView prepared observed))
    {Future : Type} (future : Future → MetaArity S) (question : List (Observation S future) → Prop) :
    (∃ candidate : Assignment prepared.target.declarations future,
      ContextualFrameUnifier.Models candidate prepared.target.inventory.configuration.equations ∧
        question (jointView candidate (callerView prepared observed))) ↔
    ∃ candidate : Assignment prepared.target.declarations future,
      ContextualFrameUnifier.Models candidate (incoming prepared) ∧
        question (jointView candidate (callerView prepared observed)) := by
  rw [target_equations_split]
  exact permission.joint_possible_iff (actual_problem_consistent prepared) question

theorem prepared_joint_entails_iff (prepared : Prepared locals before)
    (granted : Set prepared.target.Names) (observed : List (Observation S before.declarations))
    (permission : Permitted granted (incoming prepared) (additions prepared) (callerView prepared observed))
    {Future : Type} (future : Future → MetaArity S) (question : List (Observation S future) → Prop) :
    (∀ candidate : Assignment prepared.target.declarations future,
      ContextualFrameUnifier.Models candidate prepared.target.inventory.configuration.equations →
        question (jointView candidate (callerView prepared observed))) ↔
    ∀ candidate : Assignment prepared.target.declarations future,
      ContextualFrameUnifier.Models candidate (incoming prepared) →
        question (jointView candidate (callerView prepared observed)) := by
  rw [target_equations_split]
  exact permission.joint_entails_iff (actual_problem_consistent prepared) question

theorem computed_answer_joint_possible_iff (prepared : Prepared locals before)
    (granted : Set prepared.target.Names) (observed : List (Observation S before.declarations))
    (permission : AnswerPermitted granted (computedAnswer prepared) (callerView prepared observed))
    {Future : Type} (future : Future → MetaArity S) (question : List (Observation S future) → Prop) :
    (∃ candidate : Assignment prepared.target.declarations future,
      ContextualFrameUnifier.Models candidate prepared.target.inventory.configuration.equations ∧
        question (jointView candidate (callerView prepared observed))) ↔
    ∃ candidate : Assignment prepared.target.declarations future,
      ContextualFrameUnifier.Models candidate (incoming prepared) ∧
        question (jointView candidate (callerView prepared observed)) := by
  rw [target_equations_split]
  exact permission.joint_possible_iff (computedAnswer_models prepared) question

/-- This is the original actual firing, expressed in its computed target
chart. The chart equality retains the real endpoint and selected source use. -/
theorem firing_preserves_joint_possibilities (firing : Firing locals before after)
    (granted : Set (Prepared.ofFiring firing).target.Names)
    (observed : List (Observation S before.declarations))
    (permission : Permitted granted (incoming (Prepared.ofFiring firing)) (additions (Prepared.ofFiring firing))
      (callerView (Prepared.ofFiring firing) observed))
    {Future : Type} (future : Future → MetaArity S) (question : List (Observation S future) → Prop) :
    (Prepared.ofFiring firing).target = after ∧
    ((∃ candidate : Assignment (Prepared.ofFiring firing).target.declarations future,
      ContextualFrameUnifier.Models candidate (Prepared.ofFiring firing).target.inventory.configuration.equations ∧
        question (jointView candidate (callerView (Prepared.ofFiring firing) observed))) ↔
    ∃ candidate : Assignment (Prepared.ofFiring firing).target.declarations future,
      ContextualFrameUnifier.Models candidate (incoming (Prepared.ofFiring firing)) ∧
        question (jointView candidate (callerView (Prepared.ofFiring firing) observed))) :=
  ⟨Prepared.target_ofFiring firing,
    prepared_joint_possible_iff (Prepared.ofFiring firing) granted observed permission future question⟩

def inputRows (prepared : Prepared locals before) :
    O → ContextualStoredRows.Row locals prepared.target.declarations Γ sort :=
  fun occurrence => (before.inventory.rows occurrence).map locals
    (ContextualProcessTransport.captureExtension prepared).assignment

def inputCheck (prepared : Prepared locals before)
    (check : Check (Term (signature S before.declarations) Γ sort)) :
    Check (Term (signature S prepared.target.declarations) Γ sort) :=
  check.map (instantiate (ContextualProcessTransport.captureExtension prepared).assignment)

/-- Explicit permissions preserve a watched input guard, including all of
its hidden row dependencies, across the actual completed equation update. -/
theorem prepared_input_ask_iff (prepared : Prepared locals before)
    (granted : Set prepared.target.Names) (observed : List (Observation S before.declarations))
    (check : Check (Term (signature S before.declarations) Γ sort))
    (permission : Permitted granted (incoming prepared) (additions prepared)
      (callerView prepared observed ++ guardObservations locals (inputRows prepared)
        before.inventory.configuration.present (inputCheck prepared check))) :
    ContextualGuardSemantics.Ask locals prepared.target.inventory.configuration.equations
        (inputRows prepared) before.inventory.configuration.present (inputCheck prepared check) ↔
      ContextualGuardSemantics.Ask locals before.inventory.configuration.equations before.inventory.rows
        before.inventory.configuration.present check := by
  rw [target_equations_split]
  exact (permitted_ask_iff locals granted (incoming prepared) (additions prepared) (inputRows prepared)
    before.inventory.configuration.present (inputCheck prepared check) (callerView prepared observed)
    permission (actual_problem_consistent prepared)).trans
      (ContextualGuardSemantics.Ask.extension_iff locals
        (ContextualProcessTransport.captureExtension prepared) before.inventory.configuration.equations
        before.inventory.rows before.inventory.configuration.present check)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingPermissionFirings
