import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SequentialComposition

/-!
# Inspectable conditions for two symbolic occurrence firings

The composite contains finite occurrence preconditions, a net effect,
unresolved equations, static shape tests and checks transported to their
original equation prefixes and occurrence worlds. Applying it does not run
the two original steps or inspect a proof object.

In particular, a later binding may not retroactively discharge an earlier
undecided check. This module concerns fixed occurrence selections, not overlap
enumeration or atomic replacement in an interfering concurrent execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-- Static tests contain data, rather than callbacks into a source firing. -/
structure ShapeTest (T : Type uT) (O : Type uO) where
  taken : List O
  made : List O
  takeCount : Nat
  readCount : Nat
  expectedTakeCount : Nat
  expectedReadCount : Nat
  outputs : List T

namespace ShapeTest

def ofSelection (rule : RuleInstance T) (selection : Selection O) : ShapeTest T O :=
  ⟨selection.taken, selection.made, selection.taken.length, selection.read.length,
    rule.take.length, rule.read.length, rule.produce⟩

def Holds (test : ShapeTest T O) (label : O → T) : Prop :=
  test.taken.Nodup ∧ test.made.Nodup ∧ test.expectedTakeCount = test.takeCount ∧
    test.expectedReadCount = test.readCount ∧ test.made.map label = test.outputs

end ShapeTest

/-- A check's own equation prefix and its pre-step occurrence world. -/
structure TransportedCheck (T : Type uT) (O : Type uO) where
  equations : EquationStore T
  effect : Commit O T
  check : Check T

def TransportedCheck.Holds (A : SubstitutionAction T S) (label : O → T)
    (before : Configuration T O) (transported : TransportedCheck T O) : Prop :=
  A.Entails (before.equations ++ transported.equations)
    (fun σ => transported.check.Holds A σ label (fire before.present transported.effect))

structure ConditionalComposite (T : Type uT) (O : Type uO) where
  resources : CommitPrecondition O T
  effect : Commit O T
  equations : EquationStore T
  shapes : List (ShapeTest T O)
  checks : List (TransportedCheck T O)

namespace ConditionalComposite

def Holds (composite : ConditionalComposite T O) (A : SubstitutionAction T S)
    (label : O → T) (before : Configuration T O) : Prop :=
  (∀ test ∈ composite.shapes, test.Holds label) ∧
    composite.resources.Holds label before.present ∧
    A.Consistent (before.equations ++ composite.equations) ∧
    ∀ check ∈ composite.checks, check.Holds A label before

def result (composite : ConditionalComposite T O) (before : Configuration T O) : Configuration T O :=
  ⟨before.equations ++ composite.equations, fire before.present composite.effect⟩

def addedEquations (label : O → T) (rule : RuleInstance T) (selection : Selection O) :
    EquationStore T :=
  Selection.equations label rule.take selection.taken ++
    Selection.equations label rule.read selection.read ++ rule.tell

omit [DecidableEq O] in
theorem problem_eq (label : O → T) (rule : RuleInstance T) (selection : Selection O)
    (before : Configuration T O) :
    selection.problem label rule before = before.equations ++ addedEquations label rule selection := by
  simp only [Selection.problem, addedEquations, List.append_assoc]

def emptyEffect : Commit O T := ⟨∅, ∅, ∅, []⟩

@[simp] theorem fire_emptyEffect (world : Finset O) : fire world (emptyEffect (T := T)) = world := by
  simp [fire, emptyEffect]

def compilePair (label : O → T) (first second : RuleInstance T)
    (left right : Selection O) : ConditionalComposite T O :=
  let leftEquations := addedEquations label first left
  let rightEquations := addedEquations label second right
  ⟨CommitPrecondition.sequential label left.commit right.commit, left.commit.compose right.commit,
    leftEquations ++ rightEquations,
    [ShapeTest.ofSelection first left, ShapeTest.ofSelection second right],
    (first.checks.map fun check => ⟨leftEquations, emptyEffect, check⟩) ++
      (second.checks.map fun check => ⟨leftEquations ++ rightEquations, left.commit, check⟩)⟩

theorem checks_pair_iff (A : SubstitutionAction T S) (label : O → T)
    (first second : RuleInstance T) (left right : Selection O) (before : Configuration T O) :
    (∀ check ∈ (compilePair label first second left right).checks, check.Holds A label before) ↔
      (∀ check ∈ first.checks, A.Entails (left.problem label first before)
        (fun σ => check.Holds A σ label before.present)) ∧
      ∀ check ∈ second.checks, A.Entails
        (right.problem label second (left.result label first before))
        (fun σ => check.Holds A σ label (left.result label first before).present) := by
  simp only [compilePair, List.forall_mem_append, List.forall_mem_map, TransportedCheck.Holds,
    fire_emptyEffect, problem_eq, Selection.result, List.append_assoc]

/-- Expansion and contraction retain the intermediate check world and all
unresolved equations. No successful concrete instance is generalized. -/
theorem holds_pair_iff (A : SubstitutionAction T S) (label : O → T)
    (first second : RuleInstance T) (left right : Selection O) (before : Configuration T O) :
    (compilePair label first second left right).Holds A label before ↔
      left.Valid A label first before ∧ right.Valid A label second (left.result label first before) := by
  have shapeSplit :
      (∀ test ∈ (compilePair label first second left right).shapes, test.Holds label) ↔
        (ShapeTest.ofSelection first left).Holds label ∧
        (ShapeTest.ofSelection second right).Holds label := by
    simp [compilePair]
  constructor
  · rintro ⟨shapes, resources, consistent, checks⟩
    obtain ⟨leftShape, rightShape⟩ := shapeSplit.mp shapes
    obtain ⟨leftEnabled, rightEnabled⟩ :=
      (CommitPrecondition.sequential_holds_iff label left.commit right.commit before.present).mp resources
    obtain ⟨leftChecks, rightChecks⟩ := (checks_pair_iff A label first second left right before).mp checks
    have secondConsistent : A.Consistent (right.problem label second (left.result label first before)) := by
      simpa only [compilePair, problem_eq, Selection.result, List.append_assoc] using consistent
    have firstConsistent : A.Consistent (left.problem label first before) := by
      obtain ⟨σ, solved⟩ := secondConsistent
      refine ⟨σ, ?_⟩
      rw [problem_eq] at solved
      exact (A.models_append _ _ _).mp solved |>.1
    exact ⟨⟨leftShape.1, leftShape.2.1, leftShape.2.2.1, leftShape.2.2.2.1,
        leftShape.2.2.2.2, leftEnabled, firstConsistent, leftChecks⟩,
      ⟨rightShape.1, rightShape.2.1, rightShape.2.2.1, rightShape.2.2.2.1,
        rightShape.2.2.2.2, rightEnabled, secondConsistent, rightChecks⟩⟩
  · rintro ⟨one, two⟩
    refine ⟨shapeSplit.mpr ⟨?_, ?_⟩,
      (CommitPrecondition.sequential_holds_iff label left.commit right.commit before.present).mpr
        ⟨one.occurrences, two.occurrences⟩, ?_,
      (checks_pair_iff A label first second left right before).mpr ⟨one.checks, two.checks⟩⟩
    · exact ⟨one.take_distinct, one.output_distinct, one.take_length, one.read_length, one.outputs⟩
    · exact ⟨two.take_distinct, two.output_distinct, two.take_length, two.read_length, two.outputs⟩
    · simpa only [compilePair, problem_eq, Selection.result, List.append_assoc] using two.consistent

theorem result_pair (A : SubstitutionAction T S) (label : O → T)
    (first second : RuleInstance T) (left right : Selection O) (before : Configuration T O)
    (admitted : (compilePair label first second left right).Holds A label before) :
    (compilePair label first second left right).result before =
      right.result label second (left.result label first before) := by
  obtain ⟨one, two⟩ := (holds_pair_iff A label first second left right before).mp admitted
  apply congrArg₂ Configuration.mk
  · simp only [compilePair, Selection.result, problem_eq, List.append_assoc]
  · exact Commit.compose_fire one.occurrences two.occurrences

end ConditionalComposite

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
