import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CompositeComposition

/-!
# Inspectable conditional compilation of ordinary firing schedules

A schedule consists only of existing rules and occurrence selections.
Compilation constructs finite resource conditions, equations, output shapes
and transported guards. Testing the compiled object does not replay the source
schedule. Expansion and contraction use the ordinary `Selection.Valid` judge.

The empty schedule requires a consistent incoming equation store. The result
compares final occurrence stores and constraints, not observable event traces
or atomic replacement in an interfering execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ConditionalSchedule

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ConditionalComposite

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

abbrev Firing (T : Type uT) (O : Type uO) := RuleInstance T × Selection O

def single (label : O → T) (firing : Firing T O) : ConditionalComposite T O :=
  let equations := addedEquations label firing.1 firing.2
  ⟨CommitPrecondition.ofCommit firing.2.commit, firing.2.commit, equations,
    [ShapeTest.ofSelection firing.1 firing.2],
    firing.1.checks.map fun check => ⟨equations, emptyEffect, check⟩⟩

def empty : ConditionalComposite T O :=
  ⟨CommitPrecondition.ofCommit emptyEffect, emptyEffect, [], [], []⟩

theorem single_resourceSound (label : O → T) (firing : Firing T O) : ResourceSound label (single label firing) := by
  intro world holds
  exact (CommitPrecondition.ofCommit_holds_iff _ _ _).mp holds

theorem empty_resourceSound (label : O → T) : ResourceSound label (empty (T := T) (O := O)) := by
  intro world holds
  exact (CommitPrecondition.ofCommit_holds_iff _ _ _).mp holds

theorem single_holds_iff (A : SubstitutionAction T S) (label : O → T)
    (firing : Firing T O) (before : Configuration T O) :
    (single label firing).Holds A label before ↔ firing.2.Valid A label firing.1 before := by
  have checks :
      (∀ check ∈ (single label firing).checks, check.Holds A label before) ↔
        ∀ check ∈ firing.1.checks, A.Entails (firing.2.problem label firing.1 before)
          (fun assignment => check.Holds A assignment label before.present) := by
    simp only [single, List.forall_mem_map, TransportedCheck.Holds, fire_emptyEffect, problem_eq]
  constructor
  · rintro ⟨shapes, resources, consistent, guards⟩
    have shape := shapes _ (List.mem_singleton_self _)
    exact ⟨shape.1, shape.2.1, shape.2.2.1, shape.2.2.2.1, shape.2.2.2.2,
      (CommitPrecondition.ofCommit_holds_iff _ _ _).mp resources,
      by simpa only [single, problem_eq] using consistent, checks.mp guards⟩
  · intro valid
    refine ⟨?_, (CommitPrecondition.ofCommit_holds_iff _ _ _).mpr valid.occurrences,
      by simpa only [single, problem_eq] using valid.consistent, checks.mpr valid.checks⟩
    intro shape member
    have only := List.mem_singleton.mp member
    subst shape
    exact ⟨valid.take_distinct, valid.output_distinct, valid.take_length, valid.read_length, valid.outputs⟩

theorem single_result (label : O → T) (firing : Firing T O) (before : Configuration T O) :
    (single label firing).result before = firing.2.result label firing.1 before := by
  apply congrArg₂ Configuration.mk
  · exact (problem_eq label firing.1 firing.2 before).symm
  · rfl

theorem empty_holds_iff (A : SubstitutionAction T S) (label : O → T) (before : Configuration T O) :
    (empty (T := T) (O := O)).Holds A label before ↔ A.Consistent before.equations := by
  simp [ConditionalComposite.Holds, empty, CommitPrecondition.Holds, CommitPrecondition.ofCommit,
    emptyEffect]

theorem empty_result (before : Configuration T O) : (empty (T := T) (O := O)).result before = before := by
  cases before
  simp [result, empty, fire_emptyEffect]

def compile (label : O → T) : List (Firing T O) → ConditionalComposite T O
  | [] => empty
  | firing :: rest => compose label (single label firing) (compile label rest)

def follow (label : O → T) (before : Configuration T O) : List (Firing T O) → Configuration T O
  | [] => before
  | firing :: rest => follow label (firing.2.result label firing.1 before) rest

def Executable (A : SubstitutionAction T S) (label : O → T) (before : Configuration T O) : List (Firing T O) → Prop
  | [] => A.Consistent before.equations
  | firing :: rest => firing.2.Valid A label firing.1 before ∧
      Executable A label (firing.2.result label firing.1 before) rest

theorem compile_resourceSound (label : O → T) : ∀ schedule : List (Firing T O), ResourceSound label (compile label schedule)
  | [] => empty_resourceSound label
  | firing :: rest => resourceSound_compose label (single_resourceSound label firing) (compile_resourceSound label rest)

theorem compile_holds_iff (A : SubstitutionAction T S) (label : O → T) (before : Configuration T O) :
    ∀ schedule : List (Firing T O), (compile label schedule).Holds A label before ↔ Executable A label before schedule
  | [] => empty_holds_iff A label before
  | firing :: rest => by
      rw [compile, holds_compose_iff A label (single_resourceSound label firing) before,
        single_holds_iff, single_result, compile_holds_iff]
      rfl

theorem compile_result (A : SubstitutionAction T S) (label : O → T) :
    ∀ (before : Configuration T O) (schedule : List (Firing T O)),
    Executable A label before schedule → (compile label schedule).result before = follow label before schedule
  | before, [], _ => empty_result before
  | before, firing :: rest, executable => by
      have admitted := (compile_holds_iff A label before (firing :: rest)).mpr executable
      rw [compile, result_compose A label (single_resourceSound label firing)
        (compile_resourceSound label rest) before admitted, single_result]
      exact compile_result A label _ rest executable.2

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ConditionalSchedule
