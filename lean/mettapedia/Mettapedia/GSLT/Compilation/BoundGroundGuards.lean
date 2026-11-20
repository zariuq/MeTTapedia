import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax
import Mettapedia.Machines.SemiNaiveInsertSaturation

/-!
# Already-bound guards filter ground propagations

These are tests of the values obtained from the positive read patterns.
They do not acquire any additional store read, bind a variable, or write
a row. The loader rejects operands outside the read variables. Integer
comparisons use the declared literal reading and refuse a non-integer.
The finite ground theorem reuses the existing delta engine; it does not
assert that any particular native loader has been verified.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.BoundGroundGuards

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax
  (Program Rule)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.OneFrame (Terms)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax
  (Propagates GroundMatch varsIn apply_ground_iff consequence ground_read_variables
    apply_eq_of_agree)

inductive Op where
  | different
  | less
  | lessEq
  deriving DecidableEq

structure Guard (signature : LPSignature) where
  op : Op
  left : Term signature
  right : Term signature

variable {signature : LPSignature} [DecidableEq signature.vars]
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]

/-- Neither operand may supply a variable of its own. -/
def CheckBound (reads : List (Term signature)) (g : Guard signature) : Prop :=
  g.left.freeVars ∪ g.right.freeVars ⊆ varsIn reads

def loadChecks (reads : List (Term signature)) (guards : List (Guard signature)) : Bool :=
  guards.all fun g => decide (g.left.freeVars ∪ g.right.freeVars ⊆ varsIn reads)

omit [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem loadChecks_iff (reads : List (Term signature)) (guards : List (Guard signature)) :
    loadChecks reads guards = true ↔ ∀ g ∈ guards, CheckBound reads g := by
  simp [loadChecks, List.all_eq_true, CheckBound]

omit [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem guard_operands_ground {P : Program (Terms (Term signature))}
    (match_ : GroundMatch P) (g : Guard signature) (bound : CheckBound match_.rule.body.read g) :
    (match_.assignment.applyTerm g.left).isGround ∧
      (match_.assignment.applyTerm g.right).isGround := by
  refine ⟨(apply_ground_iff _ _).mpr ?_, (apply_ground_iff _ _).mpr ?_⟩
  · intro v member
    exact ground_read_variables match_ v (bound (Finset.mem_union_left _ member))
  · intro v member
    exact ground_read_variables match_ v (bound (Finset.mem_union_right _ member))

def integerOf (readLiteral : signature.constants → Option Int) : Term signature → Option Int
  | .const c => readLiteral c
  | _ => none

/-- These tests inspect only their two supplied values. A different
literal carrier can supply its own verified decoder for integer literals. -/
def test (readLiteral : signature.constants → Option Int) (op : Op)
    (left right : Term signature) : Option Bool :=
  match op with
  | .different => some (decide (left ≠ right))
  | .less => do
      let a ← integerOf readLiteral left
      let b ← integerOf readLiteral right
      return decide (a < b)
  | .lessEq => do
      let a ← integerOf readLiteral left
      let b ← integerOf readLiteral right
      return decide (a ≤ b)

theorem test_different_iff (readLiteral : signature.constants → Option Int)
    (left right : Term signature) :
    test readLiteral .different left right = some true ↔ left ≠ right := by
  simp [test]

theorem test_less_iff (readLiteral : signature.constants → Option Int)
    (left right : Term signature) :
    test readLiteral .less left right = some true ↔
      ∃ a b, integerOf readLiteral left = some a ∧
        integerOf readLiteral right = some b ∧ a < b := by
  cases a : integerOf readLiteral left <;> cases b : integerOf readLiteral right <;> simp [test, a, b]

theorem test_lessEq_iff (readLiteral : signature.constants → Option Int)
    (left right : Term signature) :
    test readLiteral .lessEq left right = some true ↔
      ∃ a b, integerOf readLiteral left = some a ∧
        integerOf readLiteral right = some b ∧ a ≤ b := by
  cases a : integerOf readLiteral left <;> cases b : integerOf readLiteral right <;> simp [test, a, b]

/-- A reversed non-strict comparison implements the not-less provider
on integers. Negating a failed decoding would not give this contract. -/
theorem test_not_less_iff (readLiteral : signature.constants → Option Int)
    (left right : Term signature) :
    test readLiteral .lessEq right left = some true ↔
      ∃ a b, integerOf readLiteral left = some a ∧
        integerOf readLiteral right = some b ∧ ¬ a < b := by
  rw [test_lessEq_iff]
  constructor
  · rintro ⟨b, a, readB, readA, ordered⟩
    exact ⟨a, b, readA, readB, not_lt_of_ge ordered⟩
  · rintro ⟨a, b, readA, readB, ordered⟩
    exact ⟨b, a, readB, readA, le_of_not_gt ordered⟩

def accepts (readLiteral : signature.constants → Option Int)
    (assignment : Subst signature) (g : Guard signature) : Bool :=
  test readLiteral g.op (assignment.applyTerm g.left) (assignment.applyTerm g.right) == some true

/-- Unchanged read bindings preserve the guard even if the rest of the
store or the ambient substitution changes. -/
theorem accepts_eq_of_agree_reads (readLiteral : signature.constants → Option Int)
    {reads : List (Term signature)} {g : Guard signature} (bound : CheckBound reads g)
    {first second : Subst signature} (agree : ∀ v ∈ varsIn reads, first v = second v) :
    accepts readLiteral first g = accepts readLiteral second g := by
  have left := apply_eq_of_agree first second g.left fun v member =>
    agree v (bound (Finset.mem_union_left _ member))
  have right := apply_eq_of_agree first second g.right fun v member =>
    agree v (bound (Finset.mem_union_right _ member))
  simp only [accepts, left, right]

section Finite

variable {P : Program (Terms (Term signature))}

abbrev SourceRule := Rule (Terms (Term signature))

def keep (readLiteral : signature.constants → Option Int)
    (guards : SourceRule (signature := signature) → List (Guard signature))
    (match_ : GroundMatch P) : Bool :=
  (guards match_.rule).all (accepts readLiteral match_.assignment)

/-- Export the existing ordinary consequence of each accepted binding.
Splitting multiple makes into Horn heads does not add a premise. -/
def groundProgram (readLiteral : signature.constants → Option Int)
    (guards : SourceRule (signature := signature) → List (Guard signature))
    (instances : List (GroundMatch P)) : PropProgram (Term signature) :=
  ((instances.filter (keep readLiteral guards)).flatMap fun match_ =>
    let effect := consequence match_
    (match_.rule.body.produce.map match_.assignment.applyTerm).map fun head =>
      (⟨effect.read, head⟩ : PropRule (Term signature))).toFinset

theorem mem_groundProgram (readLiteral : signature.constants → Option Int)
    (guards : SourceRule (signature := signature) → List (Guard signature))
    (instances : List (GroundMatch P)) (rule : PropRule (Term signature)) :
    rule ∈ groundProgram readLiteral guards instances ↔
      ∃ match_ ∈ instances, keep readLiteral guards match_ = true ∧
        rule.premises = (consequence match_).read ∧ rule.head ∈ (consequence match_).made := by
  simp only [groundProgram, List.mem_toFinset, List.mem_flatMap, List.mem_filter,
    List.mem_map]
  constructor
  · rintro ⟨match_, ⟨listed, accepted⟩, _, ⟨term, made, rfl⟩, rfl⟩
    exact ⟨match_, listed, accepted, rfl, List.mem_toFinset.mpr (List.mem_map.mpr ⟨term, made, rfl⟩)⟩
  · rintro ⟨match_, listed, accepted, read, made⟩
    obtain ⟨term, inside, equal⟩ := List.mem_map.mp (List.mem_toFinset.mp made)
    refine ⟨match_, ⟨listed, accepted⟩, rule.head, ⟨term, inside, equal⟩, ?_⟩
    cases rule
    simp_all

end Finite

/-- Once grounded, the finite guarded program is a positive Horn program.
The existing semi-naive result applies at every round, not only at quiescence. -/
theorem guarded_delta_eq_naive {signature : LPSignature.{0,0,0,0}}
    [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
    {P : Program (Terms (Term signature))}
    (readLiteral : signature.constants → Option Int)
    (guards : SourceRule (signature := signature) → List (Guard signature))
    (instances : List (GroundMatch P)) (seed : Finset (Term signature)) (rounds : Nat) :
    (Mettapedia.Machines.RecursiveInsert.SemiNaive.rounds
      (groundProgram readLiteral guards instances) seed rounds).known =
      iterate (groundProgram readLiteral guards instances) seed rounds :=
  Mettapedia.Machines.RecursiveInsert.SemiNaive.rounds_eq_iterate _ _ _

namespace Controls

abbrev sig : LPSignature := ⟨Int, Nat, Empty, (fun e => nomatch e), Empty, (fun e => nomatch e)⟩
abbrev T := Term sig

def cheaper : Guard sig := ⟨.less, .var 0, .var 1⟩

theorem guarded_join_checks_bound_operands :
    loadChecks ([.var 0, .var 1] : List T) [cheaper] = true ∧
      accepts (signature := sig) some (fun v => if v = 0 then .const 1 else .const 4) cheaper = true ∧
      accepts (signature := sig) some (fun v => if v = 0 then .const 4 else .const 1) cheaper = false := by
  decide +kernel

theorem unbound_guard_refused : loadChecks ([.var 0] : List T) [cheaper] = false := by
  decide +kernel

end Controls

#print axioms loadChecks_iff
#print axioms guard_operands_ground
#print axioms test_different_iff
#print axioms test_less_iff
#print axioms test_lessEq_iff
#print axioms test_not_less_iff
#print axioms accepts_eq_of_agree_reads
#print axioms mem_groundProgram
#print axioms guarded_delta_eq_naive
#print axioms Controls.guarded_join_checks_bound_operands
#print axioms Controls.unbound_guard_refused

end Mettapedia.GSLT.Compilation.BoundGroundGuards
