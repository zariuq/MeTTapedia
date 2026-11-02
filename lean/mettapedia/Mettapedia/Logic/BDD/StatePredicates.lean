import Mettapedia.Logic.BDD.Operations
import Mettapedia.Machines.GuardEvaluationRegimes

/-!
# Ordered Boolean state predicates and simultaneous substitution

The existing BDD tree and Boolean operations supply the representation. The
ordered/reduced invariant reflects semantic unsatisfiability to the zero node,
giving a complete executable equivalence test without enumerating assignments.
Substitution compiles every occurrence of a variable through the same Boolean
state function. It is simultaneous, not an in-place sequence of assignments.

These are set-valued, pure state observations. No claim about arena identity,
memoization cost, source answer multiplicity or C realization is made here.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.StatePredicates

open Mettapedia.Machines.GuardConjunctionCompiler (Guard)
open Mettapedia.Machines.GuardEvaluationRegimes (scalar)

abbrev State (n : Nat) := Fin n → Bool
abbrev Diagram (n : Nat) := { tree : BDD n // tree.WF }

theorem ordered_unsat_zero {n : Nat} (tree : BDD n) {bound : Option (Fin n)}
    (ordered : tree.Ordered bound) (unsat : ∀ state, tree.eval state = false) : tree = .zero := by
  induction tree generalizing bound with
  | zero => rfl
  | one => have impossible := unsat (fun _ => false); cases impossible
  | node v lo hi ihlo ihhi =>
    cases ordered with
    | node _ lower higher different =>
      have loZero : lo = .zero := by
        apply ihlo lower
        intro state
        have value := unsat (Function.update state v false)
        simpa only [BDD.eval, Function.update_self, Bool.false_eq_true, ↓reduceIte,
          BDD.eval_independent lo lower state v le_rfl false] using value
      have hiZero : hi = .zero := by
        apply ihhi higher
        intro state
        have value := unsat (Function.update state v true)
        simpa only [BDD.eval, Function.update_self, ↓reduceIte,
          BDD.eval_independent hi higher state v le_rfl true] using value
      exact False.elim (different (loZero.trans hiZero.symm))

def equivalent {n : Nat} (left right : Diagram n) : Bool :=
  decide (apply (· != ·) left.val right.val = .zero)

theorem equivalent_iff {n : Nat} (left right : Diagram n) :
    equivalent left right = true ↔ ∀ state, left.val.eval state = right.val.eval state := by
  simp only [equivalent, decide_eq_true_eq]
  constructor
  · intro zero state
    have value := congrArg (fun tree : BDD n => tree.eval state) zero
    simpa using value
  · intro same
    apply ordered_unsat_zero _ (apply_ordered _ _ _ none left.property right.property)
    intro state
    simp [same state]

def falsity (n : Nat) : Diagram n := ⟨.zero, .zero⟩
def truth (n : Nat) : Diagram n := ⟨.one, .one⟩
def bit {n : Nat} (v : Fin n) : Diagram n := ⟨bddVar v, bddVar_ordered v⟩
def neg {n : Nat} (body : Diagram n) : Diagram n :=
  ⟨bddNot body.val, bddNot_ordered body.val none body.property⟩
def conj {n : Nat} (left right : Diagram n) : Diagram n :=
  ⟨apply (· && ·) left.val right.val, apply_ordered _ _ _ none left.property right.property⟩
def disj {n : Nat} (left right : Diagram n) : Diagram n :=
  ⟨apply (· || ·) left.val right.val, apply_ordered _ _ _ none left.property right.property⟩

def choose {n : Nat} (test yes no : Diagram n) : Diagram n :=
  disj (conj test yes) (conj (neg test) no)

theorem choose_eval {n : Nat} (test yes no : Diagram n) (state : State n) :
    (choose test yes no).val.eval state =
      if test.val.eval state then yes.val.eval state else no.val.eval state := by
  simp only [choose, disj, conj, neg, apply_eval, bddNot_eval]
  cases test.val.eval state <;> simp

def compileGuard {n : Nat} : Guard (Fin n) → Diagram n
  | .constant false => falsity n
  | .constant true => truth n
  | .atom v => bit v
  | .neg body => neg (compileGuard body)
  | .both left right => conj (compileGuard left) (compileGuard right)
  | .either left right => disj (compileGuard left) (compileGuard right)

theorem compileGuard_eval {n : Nat} (guard : Guard (Fin n)) (state : State n) :
    (compileGuard guard).val.eval state = scalar state guard := by
  induction guard with
  | constant value => cases value <;> rfl
  | atom v => simp [compileGuard, bit, scalar]
  | neg body ih => simp [compileGuard, neg, scalar, ih]
  | both left right ihl ihr => simp [compileGuard, conj, scalar, ihl, ihr]
  | either left right ihl ihr => simp [compileGuard, disj, scalar, ihl, ihr]

def substitute {n m : Nat} (images : Fin m → Diagram n) : BDD m → Diagram n
  | .zero => falsity n
  | .one => truth n
  | .node v lo hi => choose (images v) (substitute images hi) (substitute images lo)

theorem substitute_eval {n m : Nat} (images : Fin m → Diagram n) (tree : BDD m) (state : State n) :
    (substitute images tree).val.eval state = tree.eval (fun v => (images v).val.eval state) := by
  induction tree with
  | zero => rfl
  | one => rfl
  | node v lo hi ihlo ihhi => simp [substitute, choose_eval, BDD.eval, ihlo, ihhi]

def denote {n : Nat} (diagram : Diagram n) : Set (State n) := diagram.val.satSet

theorem equivalent_denote {n : Nat} (left right : Diagram n) :
    equivalent left right = true ↔ denote left = denote right := by
  rw [equivalent_iff]
  constructor
  · intro equal; ext state; simp [denote, BDD.satSet, equal state]
  · intro equal state
    have values := Set.ext_iff.mp equal state
    simp only [denote, BDD.satSet, Set.mem_ofPred_eq] at values
    exact Bool.eq_iff_iff.mpr values

namespace Controls

def swapped : Fin 2 → Diagram 2 := ![bit 1, bit 0]

theorem simultaneous_swap :
    (substitute swapped (bddVar 0)).val.eval ![true, false] = false ∧
    (substitute swapped (bddVar 1)).val.eval ![true, false] = true := by
  simp [substitute_eval, swapped, bit]

def sameInput : Fin 2 → Diagram 1 := fun _ => bit 0

theorem shared_input_is_not_two_independent_choices :
    ∀ state, (substitute sameInput (apply (· != ·) (bddVar 0) (bddVar 1))).val.eval state = false := by
  intro state
  simp [substitute_eval, sameInput, bit]

theorem distinct_variables_are_not_equivalent : equivalent (bit (0 : Fin 2)) (bit 1) = false := by
  simp [equivalent, bit, bddVar, mk, apply]

end Controls
end Mettapedia.Logic.BDDCore.StatePredicates
