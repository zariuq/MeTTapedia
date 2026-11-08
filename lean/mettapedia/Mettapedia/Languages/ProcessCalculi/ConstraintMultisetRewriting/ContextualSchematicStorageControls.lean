import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchematicStorage
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameWorklist

/-!
# Two readers of one ordinary stored rule

The stored atom is `(= (f a) (b a 2))`. Two successive readers ask for
`f 1` and `f 2`. Their retained equation store gives answers `b 1 2` and
`b 2 2`, while the original occurrence stays schematic. Any assignment to
the caller's shared variables extends to both reads.

The operators below are the literal constructors of this example; the
storage and per-use interpretation come from the generic owners.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchematicStorage.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualStoredRows (store)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

inductive Operator where
  | number : Nat → Operator
  | f | b | equation
  deriving DecidableEq, Repr

abbrev base : Signature where
  Srt := Unit
  Op _ := Operator
  arity
    | .number _ => []
    | .f => [([], ())]
    | .b | .equation => [([], ()), ([], ())]

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq Operator)

abbrev locals (_ : Nat) : MetaArity base := ([], ())
abbrev captures (_ : Nat) : MetaArity base := ([], ())
abbrev raw := ContextualActivatedStep.source locals captures
abbrev active := ContextualActivatedStep.target locals captures
abbrev laterRaw := ContextualActivatedStep.source locals active
abbrev later := ContextualActivatedStep.target locals active
abbrev Closed {V : Type} (declaration : V → MetaArity base) := Term (signature base declaration) [] ()

variable {V W : Type} {declaration : V → MetaArity base} {next : W → MetaArity base}

def number (n : Nat) : Closed declaration := .op (.inl (.number n)) .nil
def f (x : Closed declaration) : Closed declaration := .op (.inl .f) (.cons x .nil)
def b (x y : Closed declaration) : Closed declaration := .op (.inl .b) (.cons x (.cons y .nil))
def equation (x y : Closed declaration) : Closed declaration := .op (.inl .equation) (.cons x (.cons y .nil))

private def equationFields : Closed declaration → Option (Closed declaration × Closed declaration)
  | .op (.inl .equation) (.cons x (.cons y .nil)) => some (x,y)
  | _ => none

theorem equation_left {x y z w : Closed declaration} (same : equation x y = equation z w) : x = z :=
  congrArg Prod.fst (Option.some.inj (congrArg equationFields same))

theorem equation_right {x y z w : Closed declaration} (same : equation x y = equation z w) : y = w :=
  congrArg Prod.snd (Option.some.inj (congrArg equationFields same))

private def fField : Closed declaration → Option (Closed declaration)
  | .op (.inl .f) (.cons x .nil) => some x
  | _ => none

theorem f_injective {x y : Closed declaration} (same : f x = f y) : x = y :=
  Option.some.inj (congrArg fField same)

theorem read_answer (candidate : Assignment declaration next) (argument answer : Closed declaration)
    (n : Nat)
    (matched : instantiate candidate (equation (f (number n)) answer) =
      instantiate candidate (equation (f argument) (b argument (number 2)))) :
    instantiate candidate answer = b (number n) (number 2) := by
  change equation (f (number n)) (instantiate candidate answer) =
    equation (f (instantiate candidate argument)) (b (instantiate candidate argument) (number 2)) at matched
  have value := f_injective (equation_left matched)
  have result := equation_right matched
  rw [← value] at result
  exact result

theorem read_argument (candidate : Assignment declaration next) (argument answer : Closed declaration)
    (n : Nat)
    (matched : instantiate candidate (equation (f (number n)) answer) =
      instantiate candidate (equation (f argument) (b argument (number 2)))) :
    instantiate candidate argument = number n := by
  change equation (f (number n)) (instantiate candidate answer) =
    equation (f (instantiate candidate argument)) (b (instantiate candidate argument) (number 2)) at matched
  exact (f_injective (equation_left matched)).symm

def storedRule : Closed locals :=
  equation (f (generator locals 0)) (b (generator locals 0) (number 2))

def query {Shared : Type} (shared : Shared → MetaArity base) (n : Nat) :
    RuleInstance (Closed (ContextualActivatedStep.source locals shared)) :=
  ⟨[], [equation (f (number n)) (generator (ContextualActivatedStep.source locals shared) (.inl 1))],
    [], [], [generator (ContextualActivatedStep.source locals shared) (.inl 1)]⟩

def before : Configuration (Closed captures) Nat := ⟨[], {7,8}⟩
def rows (o : Nat) : ContextualStoredRows.Row locals captures [] () :=
  if o = 7 then store locals captures storedRule else .shared (generator captures 0)
def occupied : Finset Nat := {0}
def first : Selection Nat := ⟨[], [7], [99]⟩
def second : Selection Nat := ⟨[], [7], [100]⟩
def localVariable (scope name : Nat) : Closed active := generator active (.inl (ScopedVar.at scope name))
def laterVariable (scope name : Nat) : Closed later := generator later (.inl (ScopedVar.at scope name))
def firstOutput (_ : Nat) : Closed active := localVariable 1 1
def firstProblem := ContextualActivatedStep.problem locals captures occupied first (query captures 1) rows before
def firstAfter := ContextualActivatedStep.result locals captures occupied first (query captures 1) rows before
def firstRows := ContextualActivatedStep.resultRows locals captures first firstOutput rows
def firstOccupied := ContextualActivationScopes.after occupied first
def keep : Assignment active later := ContextualSelectionViews.capturedTarget locals active
def secondOutput (_ : Nat) : Closed later := laterVariable 3 1
def secondProblem := ContextualActivatedStep.problem locals active firstOccupied second (query active 2) firstRows firstAfter
def secondAfter := ContextualActivatedStep.result locals active firstOccupied second (query active 2) firstRows firstAfter
def secondRows := ContextualActivatedStep.resultRows locals active second secondOutput firstRows

theorem first_problem :
    firstProblem = [(equation (f (number 1)) (localVariable 1 1),
      equation (f (localVariable 2 0)) (b (localVariable 2 0) (number 2)))] := by
  with_unfolding_all rfl

theorem second_problem :
    secondProblem =
      [(instantiate keep (equation (f (number 1)) (localVariable 1 1)),
        instantiate keep (equation (f (localVariable 2 0)) (b (localVariable 2 0) (number 2)))),
       (equation (f (number 2)) (laterVariable 3 1),
        equation (f (laterVariable 4 0)) (b (laterVariable 4 0) (number 2)))] := by
  with_unfolding_all rfl

def firstSolution {Next : Type} (target : Next → MetaArity base) (caller : Assignment captures target) :
    Assignment active target
  | .inl ⟨scope,name⟩ => if scope = 1 ∧ name = 1 then b (number 1) (number 2) else number 1
  | .inr name => caller name

def secondSolution {Next : Type} (target : Next → MetaArity base) (caller : Assignment captures target) :
    Assignment later target
  | .inl ⟨scope,name⟩ => if scope = 3 ∧ name = 1 then b (number 2) (number 2) else number 2
  | .inr name => firstSolution target caller name

theorem first_read_accepts_every_caller_assignment {Next : Type} (target : Next → MetaArity base)
    (caller : Assignment captures target) : ContextualFrameUnifier.Models (firstSolution target caller) firstProblem := by
  rw [first_problem]
  intro e member
  have same := List.mem_singleton.mp member
  subst e
  with_unfolding_all rfl

theorem both_reads_accept_every_caller_assignment {Next : Type} (target : Next → MetaArity base)
    (caller : Assignment captures target) : ContextualFrameUnifier.Models (secondSolution target caller) secondProblem := by
  rw [second_problem]
  intro e member
  rcases List.mem_cons.mp member with same | member
  · subst e
    with_unfolding_all rfl
  · have same := List.mem_singleton.mp member
    subst e
    with_unfolding_all rfl

def firstWitness : Assignment active active :=
  firstSolution active (ContextualSelectionViews.capturedTarget locals captures)
def secondWitness : Assignment later later :=
  secondSolution later (Assignment.compose keep (ContextualSelectionViews.capturedTarget locals captures))

theorem first_valid :
    ContextualActivatedStep.Valid locals captures occupied first (query captures 1) rows before firstOutput := by
  refine ⟨rfl, by decide, by decide, rfl, rfl, ?_, by decide, ?_⟩
  · with_unfolding_all rfl
  · exact ContextualFrameUnifier.solvable_of_consistent ⟨firstWitness,first_read_accepts_every_caller_assignment _ _⟩

theorem second_valid :
    ContextualActivatedStep.Valid locals active firstOccupied second (query active 2) firstRows firstAfter secondOutput := by
  refine ⟨rfl, by decide, by decide, rfl, rfl, ?_, by decide, ?_⟩
  · with_unfolding_all rfl
  · exact ContextualFrameUnifier.solvable_of_consistent ⟨secondWitness,both_reads_accept_every_caller_assignment _ _⟩

theorem two_successive_reads :
    ContextualActivatedStep.Step locals captures occupied (query captures 1) rows before
      firstOutput firstAfter firstRows firstOccupied ∧
    ContextualActivatedStep.Step locals active firstOccupied (query active 2) firstRows firstAfter
      secondOutput secondAfter secondRows (ContextualActivationScopes.after firstOccupied second) :=
  ⟨⟨first,first_valid,rfl,rfl,rfl⟩,⟨second,second_valid,rfl,rfl,rfl⟩⟩

theorem first_answer_in_every_model (candidate : Assignment active next)
    (solved : ContextualFrameUnifier.Models candidate firstProblem) :
    instantiate candidate (firstOutput 99) = b (number 1) (number 2) := by
  rw [first_problem] at solved
  exact read_answer candidate (localVariable 2 0) (localVariable 1 1) 1
    (solved _ List.mem_cons_self)

theorem both_answers_in_every_later_model (candidate : Assignment later next)
    (solved : ContextualFrameUnifier.Models candidate secondProblem) :
    instantiate candidate (instantiate keep (firstOutput 99)) = b (number 1) (number 2) ∧
    instantiate candidate (secondOutput 100) = b (number 2) (number 2) := by
  rw [second_problem] at solved
  constructor
  · exact read_answer candidate (instantiate keep (localVariable 2 0))
      (instantiate keep (localVariable 1 1)) 1 (solved _ List.mem_cons_self)
  · exact read_answer candidate (laterVariable 4 0) (laterVariable 3 1) 2
      (solved (equation (f (number 2)) (laterVariable 3 1),
        equation (f (laterVariable 4 0)) (b (laterVariable 4 0) (number 2))) (by simp))

theorem stored_rule_is_preserved_after_both_reads :
    firstRows 7 = store locals active storedRule ∧
    secondRows 7 = store locals later storedRule := by
  constructor <;> with_unfolding_all rfl

theorem the_same_physical_rule_survives :
    firstAfter.present = {7,8,99} ∧ secondAfter.present = {7,8,99,100} := by decide +kernel

theorem the_callers_shared_variable_remains_arbitrary {Next : Type} (target : Next → MetaArity base)
    (caller : Assignment captures target) :
    instantiate (secondSolution target caller)
      (instantiate keep (instantiate (ContextualSelectionViews.capturedTarget locals captures) (generator captures 0))) =
      caller 0 := by
  have copied :
      instantiate keep (instantiate (ContextualSelectionViews.capturedTarget locals captures) (generator captures 0)) =
        generator later (.inr (.inr 0)) := by with_unfolding_all rfl
  rw [copied]
  exact instantiate_generator (secondSolution target caller) (.inr (.inr 0))

def remainingCount {D : Type} {decl : D → MetaArity base} {problem : ContextualResidual.Problem decl} :
    ContextualFrameWorklist.Result problem → Option Nat
  | .refuted _ => none
  | .residual update => some update.remaining.length

theorem first_actual_solver_completes :
    remainingCount (ContextualFrameWorklist.run 32 active (ContextualResidual.observeProblem firstProblem)) = some 0 := by
  rw [ContextualFrameWorklist.run_eq_local_on_model 32 (ContextualResidual.observeProblem firstProblem)
    active firstWitness ((ContextualResidual.models_observeProblem _ _).mpr
      (first_read_accepts_every_caller_assignment _ _))]
  decide +kernel

theorem second_actual_solver_completes :
    remainingCount (ContextualFrameWorklist.run 32 later (ContextualResidual.observeProblem secondProblem)) = some 0 := by
  rw [ContextualFrameWorklist.run_eq_local_on_model 32 (ContextualResidual.observeProblem secondProblem)
    later secondWitness ((ContextualResidual.models_observeProblem _ _).mpr
      (both_reads_accept_every_caller_assignment _ _))]
  decide +kernel

def explicitSharedRows (o : Nat) : ContextualStoredRows.Row locals captures [] () :=
  if o = 7 then .shared (equation (f (generator captures 0)) (b (generator captures 0) (number 2)))
    else rows o
def sharedFirstProblem := ContextualActivatedStep.problem locals captures occupied first
  (query captures 1) explicitSharedRows before
def sharedFirstAfter := ContextualActivatedStep.result locals captures occupied first
  (query captures 1) explicitSharedRows before
def sharedFirstRows := ContextualActivatedStep.resultRows locals captures first firstOutput explicitSharedRows
def sharedSecondProblem := ContextualActivatedStep.problem locals active firstOccupied second
  (query active 2) sharedFirstRows sharedFirstAfter
def ownerAfter : Closed later := generator later (.inr (.inr 0))

theorem explicit_shared_first_problem :
    sharedFirstProblem = [(equation (f (number 1)) (localVariable 1 1),
      equation (f (generator active (.inr 0))) (b (generator active (.inr 0)) (number 2)))] := by
  with_unfolding_all rfl

theorem explicit_shared_second_problem :
    sharedSecondProblem =
      [(equation (f (number 1)) (instantiate keep (localVariable 1 1)),
        equation (f ownerAfter) (b ownerAfter (number 2))),
       (equation (f (number 2)) (laterVariable 3 1),
        equation (f ownerAfter) (b ownerAfter (number 2)))] := by
  with_unfolding_all rfl

theorem reading_an_explicit_shared_reference_binds_it (candidate : Assignment active next)
    (solved : ContextualFrameUnifier.Models candidate sharedFirstProblem) :
    instantiate candidate (generator active (.inr 0)) = number 1 := by
  rw [explicit_shared_first_problem] at solved
  exact read_argument candidate (generator active (.inr 0)) (localVariable 1 1) 1
    (solved _ List.mem_cons_self)

def sharedFirstWitness : Assignment active active := firstSolution active (fun _ => number 1)

theorem explicit_shared_first_valid :
    ContextualActivatedStep.Valid locals captures occupied first (query captures 1)
      explicitSharedRows before firstOutput := by
  refine ⟨rfl, by decide, by decide, rfl, rfl, ?_, by decide, ContextualFrameUnifier.solvable_of_consistent ⟨sharedFirstWitness, ?_⟩⟩
  · with_unfolding_all rfl
  · change ContextualFrameUnifier.Models sharedFirstWitness sharedFirstProblem
    rw [explicit_shared_first_problem]
    intro e member
    have same := List.mem_singleton.mp member
    subst e
    with_unfolding_all rfl

private def numberValue : Closed declaration → Option Nat
  | .op (.inl (.number n)) .nil => some n
  | _ => none

theorem one_and_two_are_distinct : (number 1 : Closed declaration) ≠ number 2 := by
  intro same
  exact (by decide : (1 : Nat) ≠ 2) (Option.some.inj (congrArg numberValue same))

/-- Explicit sharing retains the earlier binding; the second reader cannot
resample that one shared variable to a different value. -/
theorem the_two_reads_cannot_independently_bind_one_shared_reference (candidate : Assignment later next) :
    ¬ ContextualFrameUnifier.Models candidate sharedSecondProblem := by
  intro solved
  rw [explicit_shared_second_problem] at solved
  have one := read_argument candidate ownerAfter (instantiate keep (localVariable 1 1)) 1
    (solved _ List.mem_cons_self)
  have two := read_argument candidate ownerAfter (laterVariable 3 1) 2
    (solved (equation (f (number 2)) (laterVariable 3 1),
      equation (f ownerAfter) (b ownerAfter (number 2))) (by simp))
  exact one_and_two_are_distinct (one.symm.trans two)

theorem the_explicit_shared_second_read_is_refused :
    ¬ ContextualActivatedStep.Valid locals active firstOccupied second (query active 2)
      sharedFirstRows sharedFirstAfter secondOutput := by
  intro valid
  obtain ⟨Future, future, candidate, solved⟩ := valid.solvable
  exact the_two_reads_cannot_independently_bind_one_shared_reference candidate solved

def takeFirst : Selection Nat := ⟨[7],[],[99]⟩
def takeQuery : RuleInstance (Closed raw) :=
  { query captures 1 with take := (query captures 1).read, read := [] }

theorem taking_a_schema_uses_a_fresh_instance :
    ContextualActivatedStep.Valid locals captures occupied takeFirst takeQuery rows before firstOutput := by
  refine ⟨rfl, by decide, by decide, rfl, rfl, ?_, by decide, ContextualFrameUnifier.solvable_of_consistent ⟨firstWitness, ?_⟩⟩
  · with_unfolding_all rfl
  · have same : ContextualActivatedStep.problem locals captures occupied takeFirst takeQuery rows before =
        firstProblem := by with_unfolding_all rfl
    rw [same]
    exact first_read_accepts_every_caller_assignment _ _

theorem taking_consumes_the_original_occurrence :
    (ContextualActivatedStep.result locals captures occupied takeFirst takeQuery rows before).present = {8,99} := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchematicStorage.Controls
