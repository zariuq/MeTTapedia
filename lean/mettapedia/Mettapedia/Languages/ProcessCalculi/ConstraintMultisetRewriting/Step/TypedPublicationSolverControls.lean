import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentWorklistControls

/-!
# Actual worklist outcomes consumed by publication

The positive case is the existing heterogeneous wake-up problem: solving its
type equation makes its retained value usable at the second declared type.
The actual driver's solved certificate constructs the application. Refutation,
postponement and budget exhaustion remain different outcomes. The cumulative
cross store remains a nonprincipal family with an exact nonempty residual.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.SolverControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open ContextualDependentWorklist

abbrev setting := ContextualDependentWorklist.Controls.setting
abbrev actualSolver := ContextualDependentWorklist.Controls.step

def stateOf {Γ : Context Tower.rules} (value : TotalTerm Γ) : State Tower.rules Nat :=
  ⟨Γ, [], ∅, fun _ => value⟩

def schemaOf {Γ : Context Tower.rules} (value : TotalTerm Γ) (expected : TypeOver Γ)
    (information : EquationStore (TotalTerm Γ)) : Schema setting.levels Nat Γ where
  helpers := .nil _
  takes := []
  reads := []
  outputs := [.value ⟨value, expected⟩]
  tells := information
  guards := []
  queries := []

def pickOf {Γ : Context Tower.rules} (value : TotalTerm Γ) (expected : TypeOver Γ)
    (information : EquationStore (TotalTerm Γ)) : Pick (schemaOf value expected information) :=
  ⟨⟨[], [], [5]⟩, rfl⟩

abbrev wakeEquation := ContextualDependentFlex.Wakeup.pending
abbrev wakeInformation := ContextualDependentWorklist.Controls.twinStore
abbrev wakeState := stateOf wakeEquation.1
abbrev wakeSchema := schemaOf wakeEquation.1 wakeEquation.2.1 wakeInformation
abbrev wakePick := pickOf wakeEquation.1 wakeEquation.2.1 wakeInformation

theorem wake_information : (wakeSchema.compile (state := wakeState) wakePick).information = wakeInformation := rfl

/-- The existing executable driver actually reaches a certificate that
licenses this non-frame-typed heterogeneous output. -/
theorem computed_publication :
    ∃ (update : ContextualDependentUpdate.Update setting.levels wakeInformation)
      (finished : update.remaining = []) (application : Application setting.levels Nat wakeState),
      run actualSolver wakeInformation 2 = .solved update finished ∧
      application.schema = wakeSchema ∧
      (realizationStep setting.levels Nat).Admits application ∧
      application.target = update.target := by
  obtain ⟨update, finished, computed⟩ :=
    ContextualDependentWorklist.Controls.solved_of_commit
      ContextualDependentWorklist.Controls.woken_after_type_solution
  let certificate := update.completed finished
  let application : Application setting.levels Nat wakeState :=
    ⟨wakeSchema, wakePick, update.target, update.answer, .principal certificate⟩
  refine ⟨update, finished, application, computed, rfl, ?_, rfl⟩
  refine ⟨⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl⟩, ?_⟩, ?_,
    ⟨update.target, update.answer, certificate.sound⟩, ?_⟩
  · intro output member
    obtain rfl := List.mem_singleton.mp member
    exact NativeTypesOnTheStep.below_of_typeEq (certificate.sound wakeEquation (List.mem_cons_self ..)).1
  · apply (DependentFull.enabled_iff application.compile).mpr
    exact ⟨(fun _ member => nomatch member), (fun _ member => nomatch member),
      (fun _ member => nomatch member), (fun occurrence _ inside => Finset.notMem_empty occurrence inside)⟩
  · intro target substitution _
    exact ⟨(fun _ member => nomatch member), (fun _ member => nomatch member)⟩

theorem computed_resolution_is_ready :
    ∃ target answer certificate,
      wakeSchema.resolve (state := wakeState) wakePick actualSolver 2 = .ready target answer certificate := by
  obtain ⟨update, finished, computed⟩ :=
    ContextualDependentWorklist.Controls.solved_of_commit
      ContextualDependentWorklist.Controls.woken_after_type_solution
  refine ⟨update.target, update.answer, update.completed finished, ?_⟩
  exact congrArg (fun outcome : Outcome setting.levels wakeInformation =>
    wakeSchema.resolveOutcome (state := wakeState) wakePick outcome) computed

abbrev clashInformation := ContextualDependentWorklist.Controls.clash
abbrev clashValue := ContextualDependentWorklist.Controls.groundCode
abbrev clashState := stateOf clashValue
abbrev clashSchema := schemaOf clashValue clashValue.1 clashInformation
abbrev clashPick := pickOf clashValue clashValue.1 clashInformation

theorem computed_refutation :
    ∃ absent, clashSchema.resolve (state := clashState) clashPick actualSolver 1 = .refuted absent := by
  have refutes := ContextualDependentWorklist.Controls.clash_run_refutes
  cases computed : run actualSolver clashInformation 1 with
  | refuted absent =>
      exact ⟨absent, congrArg (fun outcome : Outcome setting.levels clashInformation =>
        clashSchema.resolveOutcome (state := clashState) clashPick outcome) computed⟩
  | solved update finished => rw [computed] at refutes; cases refutes
  | stuck update => rw [computed] at refutes; cases refutes
  | cutoff update => rw [computed] at refutes; cases refutes

theorem inconsistent_source_refused : ¬ clashSchema.Admits (state := clashState) clashPick :=
  clashSchema.refuted_excludes_source (state := clashState) clashPick
    ContextualDependentWorklist.Controls.clash_refuted

theorem exhausted_keeps_original :
    wakeSchema.resolve (state := wakeState) wakePick actualSolver 0 =
      .suspended .budget (ContextualDependentUpdate.Update.pending setting.levels wakeInformation) := rfl

open ContextualDependentSweep.Witnesses in
/-- No certified worklist update for the actual cross store can drop its
residual, regardless of how many solver rounds have been tried. -/
theorem cross_residual_never_empty
    (update : ContextualDependentUpdate.Update setting.levels crossStore) :
    update.remaining ≠ [] ∧
      UnificationWithLevels.Exact (frames setting.levels) crossStore update.answer update.remaining := by
  refine ⟨fun finished => ?_, UnificationWithLevels.DependentFibre.update_exact update⟩
  exact fragment_without_principal_answer.2.2 update.answer (update.completed finished)

open ContextualDependentSweep.Witnesses in
theorem cross_never_refuted (fuel : Nat) :
    (run actualSolver crossStore fuel).readout ≠ .refuted := by
  intro refuted
  exact Outcome.readout_eq_refuted refuted fragment_without_principal_answer.2.1

open ContextualDependentSweep.Witnesses in
/-- The real terminating worklist stops postponed, retaining its exact family;
neither a principal answer nor refutation is invented at this boundary. -/
theorem cross_finishes_postponed :
    ∃ (fuel : Nat) (update : ContextualDependentUpdate.Update setting.levels crossStore),
      run actualSolver crossStore fuel = .stuck update ∧ update.remaining ≠ [] ∧
        UnificationWithLevels.Exact (frames setting.levels) crossStore update.answer update.remaining := by
  obtain ⟨fuel, finished⟩ := drive_finishes actualSolver
    (ContextualDependentUpdate.Update.pending setting.levels crossStore)
  change (run actualSolver crossStore fuel).Finished at finished
  cases computed : run actualSolver crossStore fuel with
  | solved update empty => exact False.elim ((cross_residual_never_empty update).1 empty)
  | refuted absent => exact False.elim (absent fragment_without_principal_answer.2.1)
  | cutoff update => rw [computed] at finished; exact False.elim finished
  | stuck update => exact ⟨fuel, update, computed, cross_residual_never_empty update⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.SolverControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.SolverControls.computed_publication
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.SolverControls.cross_finishes_postponed
