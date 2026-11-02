import Mettapedia.Machines.GuardConjunctionCompiler

/-!
# Eager relational Booleans versus scalar short-circuit guards

An eager Boolean relation combines the answer occurrences of both operands.
A short-circuit controller may skip an operand only after qualifying it as
pure, complete and singleton-Boolean. Under that contract the answer agrees;
the read trace generally does not. Empty and duplicate operand answers are
explicit counterexamples to the unrestricted rewrite.

This is a pure finite-answer comparison, not a model of source argument effects
or general relational variable refinement. Those are additional admission
conditions, not silently erased by Boolean algebra.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.GuardEvaluationRegimes

open GuardConjunctionCompiler

variable {Query : Type}

def scalar (world : Query → Bool) : Guard Query → Bool
  | .constant value => value
  | .atom query => world query
  | .neg body => !(scalar world body)
  | .both left right => scalar world left && scalar world right
  | .either left right => scalar world left || scalar world right

/-- Eager Cartesian answer combination retains every answer occurrence. -/
def eager (world : Query → List Bool) : Guard Query → List Bool
  | .constant value => [value]
  | .atom query => world query
  | .neg body => (eager world body).map Bool.not
  | .both left right => (eager world left).flatMap fun l =>
      (eager world right).map (fun r => l && r)
  | .either left right => (eager world left).flatMap fun l =>
      (eager world right).map (fun r => l || r)

theorem eager_singleton (world : Query → Bool) (guard : Guard Query) :
    eager (fun q => [world q]) guard = [scalar world guard] := by
  induction guard <;> simp_all [eager, scalar]

theorem short_circuit_scalar {Fault : Type} (world : Query → Bool) (guard : Guard Query) :
    (evaluate (fun q => (Verdict.boolean (world q) : Verdict Fault)) guard).answer =
      .boolean (scalar world guard) := by
  induction guard with
  | constant value => rfl
  | atom query => rfl
  | neg body ih => simp [evaluate, negate, ih, scalar, Verdict.flip]
  | both left right ihl ihr =>
      simp only [evaluate, continueWhen, ihl]
      cases observed : scalar world left <;> simp [scalar, observed, ihr, ihl]
  | either left right ihl ihr =>
      simp only [evaluate, continueWhen, ihl]
      cases observed : scalar world left <;> simp [scalar, observed, ihr, ihl]

/-- This bridge preserves answers under the scalar qualification. It does
not claim equal executed read sets, resource cost, or arbitrary effects. -/
theorem eager_short_circuit_answers {Fault : Type} (world : Query → Bool) (guard : Guard Query) :
    (eager (fun q => [world q]) guard).map (Verdict.boolean : Bool → Verdict Fault) =
      [(evaluate (fun q => (Verdict.boolean (world q) : Verdict Fault)) guard).answer] := by
  rw [eager_singleton, short_circuit_scalar]
  rfl

namespace Controls

def emptyRight : Bool → List Bool
  | false => [false]
  | true => []

def duplicateRight : Bool → List Bool
  | false => [false]
  | true => [true, true]

theorem skipped_empty_changes_answer_count :
    eager emptyRight (.both (.atom false) (.atom true)) = [] ∧
    eager emptyRight (.atom false) = [false] := by decide

theorem skipped_duplicates_change_multiplicity :
    eager duplicateRight (.both (.atom false) (.atom true)) = [false, false] ∧
    eager duplicateRight (.atom false) = [false] := by decide

theorem scalar_contract_does_not_preserve_all_reads :
    (evaluate (fun q : Bool => (Verdict.boolean q : Verdict Unit))
      (.both (.atom false) (.atom true))).reads = [(false, .boolean false)] := by decide

end Controls

#print axioms eager_short_circuit_answers
#print axioms Controls.skipped_empty_changes_answer_count
#print axioms Controls.skipped_duplicates_change_multiplicity

end Mettapedia.Machines.GuardEvaluationRegimes
