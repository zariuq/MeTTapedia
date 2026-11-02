import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceRequestExecution

/-!
# Exact inference derivability through actual protected authority-system runs

Existing source derivations construct ordinary client-post and kernel-firing
runs. Conversely, observing a judgment in protected space after such a run
extracts an existing source derivation. The acceptance relation mentions only
physical occurrences, actual authority-system steps, and their equation model.
No proof interpreter participates in runtime activation or acceptance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceKernelReachability

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open InferenceSchemaActivation (Tm action judgment)
open InferenceSchemaKernel (Space Value locatedAction)
open InferenceRequestExecution (Occurrence label location payload system)

def CanRun (definition : ValidatedCalculusLanguageDef) (goal : Pattern) : Prop :=
  ∀ before : Configuration Value Occurrence, locatedAction.Consistent before.equations →
    ∃ after actors, (system definition).Run payload before actors after ∧
      before.present ⊆ after.present ∧
      ∃ occurrence ∈ after.present, label occurrence = (.judgments, judgment goal)

private theorem premises_run (definition : ValidatedCalculusLanguageDef) (premises : List Pattern)
    (realizable : ∀ premise ∈ premises, CanRun definition premise)
    (before : Configuration Value Occurrence) (background : locatedAction.Consistent before.equations) :
    ∃ after actors, (system definition).Run payload before actors after ∧
      before.present ⊆ after.present ∧
      ∀ premise ∈ premises, ∃ occurrence ∈ after.present, label occurrence = (.judgments, judgment premise) := by
  induction premises generalizing before with
  | nil => exact ⟨before, [], .nil _, fun _ member => member, by simp⟩
  | cons first rest ih =>
      obtain ⟨middle, firstActors, firstRun, firstKept, occurrence, present, readback⟩ :=
        realizable first (List.mem_cons_self ..) before background
      obtain ⟨after, restActors, restRun, restKept, available⟩ :=
        ih (fun premise member => realizable premise (List.mem_cons_of_mem _ member)) middle
          (firstRun.consistent background)
      refine ⟨after, firstActors ++ restActors, firstRun.append restRun,
        fun item member => restKept (firstKept member), ?_⟩
      intro premise member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨occurrence, restKept present, readback⟩
      · exact available premise member

theorem derivation_runs {definition : ValidatedCalculusLanguageDef} {goal : Pattern}
    (derivation : Derivation definition goal) : CanRun definition goal := by
  apply derivation.sound_of_ruleApplications (CanRun definition)
  intro instance_ premises conclusion applied children before background
  obtain ⟨middle, childActors, childRun, childKept, available⟩ :=
    premises_run definition premises children before background
  obtain ⟨after, applicationRun, applicationKept, output⟩ :=
    InferenceRequestExecution.application_runs definition applied middle
      (childRun.consistent background) available
  exact ⟨after, childActors ++ [false, true], childRun.append applicationRun,
    fun occurrence member => applicationKept (childKept member), output⟩

def initial : Configuration Value Occurrence := ⟨[], ∅⟩

theorem initial_consistent : locatedAction.Consistent initial.equations :=
  ⟨action.identity, by simp [initial]⟩

/-- Acceptance observes a protected physical occurrence under a final equation
model. Neither a source proof nor its derivability is a field of this relation. -/
def Reaches (definition : ValidatedCalculusLanguageDef) (goal : Pattern) : Prop :=
  ∃ after actors, (system definition).Run payload initial actors after ∧
    ∃ assignment, locatedAction.Models assignment after.equations ∧
      ∃ occurrence ∈ after.present, location occurrence = .judgments ∧
        action.apply assignment (payload occurrence) = judgment goal

theorem reaches_of_derivation {definition : ValidatedCalculusLanguageDef} {goal : Pattern}
    (derivation : Derivation definition goal) : Reaches definition goal := by
  obtain ⟨after, actors, run, _, occurrence, present, readback⟩ :=
    derivation_runs derivation initial initial_consistent
  obtain ⟨assignment, solved⟩ := run.consistent initial_consistent
  have scopedGoal : goal.isWellScoped = true := by
    cases derivation with
    | byRule _ applied _ => exact (InferenceSchemaActivation.application_scopes applied).2
  refine ⟨after, actors, run, assignment, solved, occurrence, present,
    congrArg Prod.fst readback, ?_⟩
  change action.apply assignment (label occurrence).2 = judgment goal
  rw [readback]
  exact InferenceSchemaActivation.judgment_fixed goal scopedGoal assignment

theorem derivation_of_reaches {definition : ValidatedCalculusLanguageDef} {goal : Pattern}
    (accepted : Reaches definition goal) : Nonempty (Derivation definition goal) := by
  obtain ⟨after, actors, run, assignment, solved, occurrence, present, protectedHere, observed⟩ := accepted
  exact (system definition).published_judgment_has_source_derivation payload run
    (by intro _ _ item member; cases member) assignment solved occurrence present protectedHere goal observed

/-- Whole-catalog exactness through actual ordinary CMR authority-system runs. -/
theorem reaches_iff_derivation (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    Reaches definition goal ↔ Nonempty (Derivation definition goal) :=
  ⟨derivation_of_reaches, fun ⟨derivation⟩ => reaches_of_derivation derivation⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceKernelReachability
