import Mettapedia.Machines.ReadOnlyQuery
import Mathlib.Tactic

/-!
# Short-circuit guard compilation with exact read observations

Atoms denote already resolved operations or queries, not arbitrary surface
spellings. Their observations distinguish Boolean answers, faults and an
unavailable realization. Conjunction and disjunction short-circuit in source
order. The compiler uses the shared adaptive read-program interface and
preserves both the result and the complete executed read certificate.

Normalization removes constant-controlled branches and double negations,
without suppressing a fault or evaluating an unused query. Source extraction,
binding substitution, active-profile authority and native execution are
separate obligations. In particular an unknown operator is not false.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.GuardConjunctionCompiler

variable {Query Fault : Type}

inductive Verdict (Fault : Type) where
  | boolean (value : Bool)
  | fault (reason : Fault)
  | unavailable
  deriving DecidableEq

def Verdict.flip : Verdict Fault → Verdict Fault
  | .boolean value => .boolean (!value)
  | .fault reason => .fault reason
  | .unavailable => .unavailable

@[simp] theorem Verdict.flip_flip (value : Verdict Fault) : value.flip.flip = value := by
  cases value <;> simp [Verdict.flip]

inductive Guard (Query : Type) where
  | constant (value : Bool)
  | atom (query : Query)
  | neg (body : Guard Query)
  | both (left right : Guard Query)
  | either (left right : Guard Query)
  deriving DecidableEq

abbrev Observation (Query Fault : Type) :=
  ReadOnlyQuery.Observation Query (Verdict Fault) (Verdict Fault)
abbrev Code (Query Fault : Type) :=
  ReadOnlyQuery.Program Query (Verdict Fault) (Verdict Fault)

def negate (observed : Observation Query Fault) : Observation Query Fault :=
  ⟨observed.answer.flip, observed.reads⟩

def continueWhen (expected : Bool) (observed : Observation Query Fault)
    (later : Unit → Observation Query Fault) : Observation Query Fault :=
  match observed.answer with
  | .boolean value => if value = expected then
      let suffix := later ()
      ⟨suffix.answer, observed.reads ++ suffix.reads⟩
    else observed
  | _ => observed

/-- Independent recursive source interpreter, including read order. -/
def evaluate (world : Query → Verdict Fault) : Guard Query → Observation Query Fault
  | .constant value => ⟨.boolean value, []⟩
  | .atom query => ⟨world query, [(query, world query)]⟩
  | .neg body => negate (evaluate world body)
  | .both left right => continueWhen true (evaluate world left) (fun _ => evaluate world right)
  | .either left right => continueWhen false (evaluate world left) (fun _ => evaluate world right)

def branchCode (expected : Bool) (later : Code Query Fault) : Verdict Fault → Code Query Fault
  | .boolean value => if value = expected then later else .pure (.boolean value)
  | .fault reason => .pure (.fault reason)
  | .unavailable => .pure .unavailable

def compile : Guard Query → Code Query Fault
  | .constant value => .pure (.boolean value)
  | .atom query => .read query .pure
  | .neg body => ReadOnlyQuery.bind (compile body) (fun answer => .pure answer.flip)
  | .both left right => ReadOnlyQuery.bind (compile left) (branchCode true (compile right))
  | .either left right => ReadOnlyQuery.bind (compile left) (branchCode false (compile right))

theorem branchCode_run (world : Query → Verdict Fault) (expected : Bool)
    (later : Code Query Fault) (observed : Observation Query Fault) :
    (let suffix := ReadOnlyQuery.run world (branchCode expected later observed.answer)
     (⟨suffix.answer, observed.reads ++ suffix.reads⟩ : Observation Query Fault)) =
      continueWhen expected observed (fun _ => ReadOnlyQuery.run world later) := by
  cases observed with
  | mk answer reads =>
      cases answer with
      | boolean value => by_cases same : value = expected <;> simp [branchCode, continueWhen, same, ReadOnlyQuery.run]
      | fault reason => simp [branchCode, continueWhen, ReadOnlyQuery.run]
      | unavailable => simp [branchCode, continueWhen, ReadOnlyQuery.run]

theorem compile_correct (world : Query → Verdict Fault) (guard : Guard Query) :
    ReadOnlyQuery.run world (compile guard) = evaluate world guard := by
  induction guard with
  | constant value => rfl
  | atom query => rfl
  | neg body ih => simp [compile, ReadOnlyQuery.run_bind, ih, ReadOnlyQuery.run, evaluate, negate]
  | both left right ihl ihr =>
      simp only [compile, ReadOnlyQuery.run_bind, ihl, branchCode_run, evaluate, ihr]
  | either left right ihl ihr =>
      simp only [compile, ReadOnlyQuery.run_bind, ihl, branchCode_run, evaluate, ihr]

theorem evaluate_neg_neg (world : Query → Verdict Fault) (guard : Guard Query) :
    evaluate world (.neg (.neg guard)) = evaluate world guard := by
  simp only [evaluate, negate, Verdict.flip_flip]

def smartNeg : Guard Query → Guard Query
  | .constant value => .constant (!value)
  | .neg body => body
  | other => .neg other

def smartBoth : Guard Query → Guard Query → Guard Query
  | .constant true, right => right
  | .constant false, _ => .constant false
  | left, right => .both left right

def smartEither : Guard Query → Guard Query → Guard Query
  | .constant false, right => right
  | .constant true, _ => .constant true
  | left, right => .either left right

theorem smartNeg_correct (world : Query → Verdict Fault) (guard : Guard Query) :
    evaluate world (smartNeg guard) = evaluate world (.neg guard) := by
  cases guard with
  | constant value => rfl
  | neg body => exact (evaluate_neg_neg world body).symm
  | atom query => rfl
  | both left right => rfl
  | either left right => rfl

theorem smartBoth_correct (world : Query → Verdict Fault) (left right : Guard Query) :
    evaluate world (smartBoth left right) = evaluate world (.both left right) := by
  cases left with
  | constant value =>
      cases value <;> simp [smartBoth, evaluate, continueWhen]
  | atom query => rfl
  | neg body => rfl
  | both a b => rfl
  | either a b => rfl

theorem smartEither_correct (world : Query → Verdict Fault) (left right : Guard Query) :
    evaluate world (smartEither left right) = evaluate world (.either left right) := by
  cases left with
  | constant value =>
      cases value <;> simp [smartEither, evaluate, continueWhen]
  | atom query => rfl
  | neg body => rfl
  | both a b => rfl
  | either a b => rfl

def normalize : Guard Query → Guard Query
  | .constant value => .constant value
  | .atom query => .atom query
  | .neg body => smartNeg (normalize body)
  | .both left right => smartBoth (normalize left) (normalize right)
  | .either left right => smartEither (normalize left) (normalize right)

theorem normalize_correct (world : Query → Verdict Fault) (guard : Guard Query) :
    evaluate world (normalize guard) = evaluate world guard := by
  induction guard with
  | constant value => rfl
  | atom query => rfl
  | neg body ih => rw [normalize, smartNeg_correct]; simp only [evaluate, ih]
  | both left right ihl ihr =>
      rw [normalize, smartBoth_correct]
      simp only [evaluate, ihl, ihr]
  | either left right ihl ihr =>
      rw [normalize, smartEither_correct]
      simp only [evaluate, ihl, ihr]

/-- One validated read certificate preserves the full path, including
negative lookups and source primitive failures. -/
theorem validated_reuse [DecidableEq Fault] (before after : Query → Verdict Fault)
    (guard : Guard Query)
    (valid : ReadOnlyQuery.checkReads after (evaluate before guard).reads = true) :
    evaluate after guard = evaluate before guard := by
  rw [← compile_correct] at valid
  rw [← compile_correct, ← compile_correct]
  exact ReadOnlyQuery.run_eq_of_agrees before after (compile guard)
    ((ReadOnlyQuery.checkReads_iff _ _).mp valid)

namespace Controls

def world : Nat → Verdict Nat
  | 0 => .boolean false
  | 1 => .fault 7
  | _ => .unavailable

theorem conjunction_does_not_read_unused_fault :
    (evaluate world (.both (.atom 0) (.atom 1))).answer = .boolean false ∧
    (evaluate world (.both (.atom 0) (.atom 1))).reads = [(0, .boolean false)] := by decide

theorem reordering_can_expose_a_fault :
    (evaluate world (.both (.atom 1) (.atom 0))).answer = .fault 7 := by decide

theorem right_false_cannot_erase_left_fault :
    (evaluate world (.both (.atom 1) (.constant false))).answer ≠
      (evaluate world (.constant false)).answer := by decide

theorem unsupported_is_not_false :
    (evaluate world (.neg (.atom 2))).answer = .unavailable ∧
    (evaluate world (.neg (.atom 2))).answer ≠ .boolean true := by decide

end Controls

#print axioms compile_correct
#print axioms normalize_correct
#print axioms validated_reuse

end Mettapedia.Machines.GuardConjunctionCompiler
