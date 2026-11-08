import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineExecution
import Mettapedia.Languages.CHR.MachineMatching

/-! The CHR machine source executes as `Mettapedia.Languages.CHR.Machine`:
values, terms, environments, lookup, matching and instantiation. Integers
are integers, atoms are strings, tuples are `(ChrTuple values)`. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Mettapedia.Languages.MeTTa.PeTTa.Eval
open Mettapedia.Languages.MeTTa.PeTTa.BridgeKit
open WireKit StrictCallKit CHRMachineSource
open Mettapedia.Languages.CHR (Value Term Environment)

/-! ## Constructors -/

theorem make_returns (caller : Subst) (state : State) (head : String) (arguments values : List Atom)
    (inert : BridgeKit.inertHead runtime head = true)
    (returns : List.Forall₂ (fun argument value => Returns caller state argument value) arguments values) :
    Returns caller state (.expression (.symbol head :: arguments)) (.expression (.symbol head :: values)) := by
  simp only [BridgeKit.inertHead, Bool.and_eq_true, Bool.not_eq_true'] at inert
  apply constructor_returns runtime caller state head arguments values inert.1 _ returns
  intro special
  have member : head ∈ specialForms := by
    unfold specialForms
    simp only [List.mem_cons, List.not_mem_nil, or_false] at special ⊢
    tauto
  have contains : specialForms.contains head = true := by simpa using member
  rw [contains] at inert
  cases inert.2

/-- An inert constructor of the machine's data. -/
scoped macro "inert" : term => `(inert_of_mem (by decide))

/-! ## Encodings -/

mutual
  def valueAtom : Value → Atom
    | .integer number => integer number
    | .atom name => .grounded (.string name)
    | .tuple fields => .expression [.symbol "ChrTuple", valuesAtom fields]
  def valuesAtom : List Value → Atom
    | [] => nil
    | first :: rest => cons (valueAtom first) (valuesAtom rest)
end

mutual
  theorem valueAtom_inj : ∀ {first second : Value}, valueAtom first = valueAtom second → first = second
    | .integer _, .integer _, same => by simp_all [valueAtom, integer]
    | .integer _, .atom _, same => by simp [valueAtom, integer] at same
    | .integer _, .tuple _, same => by simp [valueAtom, integer] at same
    | .atom _, .integer _, same => by simp [valueAtom, integer] at same
    | .atom _, .atom _, same => by simp_all [valueAtom]
    | .atom _, .tuple _, same => by simp [valueAtom] at same
    | .tuple _, .integer _, same => by simp [valueAtom, integer] at same
    | .tuple _, .atom _, same => by simp [valueAtom] at same
    | .tuple first, .tuple second, same => by
      simp only [valueAtom, Atom.expression.injEq, List.cons.injEq, true_and, and_true] at same
      rw [valuesAtom_inj same]
  theorem valuesAtom_inj : ∀ {first second : List Value}, valuesAtom first = valuesAtom second → first = second
    | [], [], _ => rfl
    | [], _ :: _, same => by simp [valuesAtom, nil, cons] at same
    | _ :: _, [], same => by simp [valuesAtom, nil, cons] at same
    | _ :: _, _ :: _, same => by
      simp only [valuesAtom, cons, Atom.expression.injEq, List.cons.injEq, true_and, and_true] at same
      rw [valueAtom_inj same.1, valuesAtom_inj same.2]
end

theorem valueAtom_decide (first second : Value) :
    decide (valueAtom first = valueAtom second) = decide (first = second) :=
  decide_eq_decide.mpr ⟨valueAtom_inj, fun same => same ▸ rfl⟩

theorem valuesAtom_eq (values : List Value) : valuesAtom values = listAtom (values.map valueAtom) := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp [valuesAtom, listAtom, ih]

mutual
  def termAtom : Term → Atom
    | .value datum => .expression [.symbol "ChrValue", valueAtom datum]
    | .var index => .expression [.symbol "ChrVar", integer index]
    | .tuple fields => .expression [.symbol "ChrTupleTerm", termsAtom fields]
  def termsAtom : List Term → Atom
    | [] => nil
    | first :: rest => cons (termAtom first) (termsAtom rest)
end

def bindAtom (binding : Nat × Value) : Atom :=
  .expression [.symbol "ChrBind", integer binding.1, valueAtom binding.2]

def environmentAtom (environment : Environment) : Atom := listAtom (environment.map bindAtom)

def optionAtom : Option Atom → Atom
  | none => .symbol "ChrNone"
  | some value => .expression [.symbol "ChrSome", value]

theorem integer_nat_decide (first second : Nat) :
    decide (integer (first : Int) = integer (second : Int)) = decide (first = second) := by
  apply decide_eq_decide.mpr
  simp [integer]

/-- Case selection over the machine's encodings. -/
scoped syntax "machine_case " term (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| machine_case $scrutinee $[unfolding [$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic|
      (apply pure_case_returns _ _ _ _ _ _ _ _ rfl $scrutinee
       · metta_select [listAtom, nil, cons, valueAtom, valuesAtom, termAtom, termsAtom, environmentAtom,
           bindAtom, optionAtom, integer, List.map, $extra,*]
       intro selected body selection
       metta_select [listAtom, nil, cons, valueAtom, valuesAtom, termAtom, termsAtom, environmentAtom,
         bindAtom, optionAtom, integer, List.map, $extra,*] at selection
       obtain ⟨selectedEq, bodyEq⟩ := selection
       subst selectedEq
       subst bodyEq))

/-- A call by value to a machine head. -/
scoped syntax "machine_call " term : tactic
macro_rules
  | `(tactic| machine_call $returns) => `(tactic|
      (apply strict_call library checked machine_ready _ _ _ _ _ $returns (by metta_literal; rfl)
       metta_literal))

/-- A bound variable. -/
scoped macro "bound" : term => `(bound_returns _ _ _ (by rfl))

/-! ## Lookup -/

theorem lookup_returns (state : State) (index : Nat) :
    ∀ (environment : Environment) (caller : Subst) (left right : Atom),
      Returns caller state left (integer index) → Returns caller state right (environmentAtom environment) →
      Returns caller state (apply "gslt:chr-machine:lookup" [left, right])
        (optionAtom ((Mettapedia.Languages.CHR.lookup environment index).map valueAtom)) := by
  intro environment
  induction environment with
  | nil =>
    intro caller left right one two
    machine_call (.cons one (.cons two .nil))
    machine_case (bound)
    simp only [Mettapedia.Languages.CHR.lookup, List.find?_nil, Option.map_none, optionAtom]
    exact Eval.symbol_returns runtime _ state "ChrNone"
  | cons binding rest ih =>
    obtain ⟨other, value⟩ := binding
    intro caller left right one two
    machine_call (.cons one (.cons two .nil))
    machine_case (bound)
    apply pure_if_returns _ _ _ _ (decide (integer (index : Int) = integer (other : Int))) _ _ _
      (equal_returns _ _ _ _ _ _ bound bound)
    rw [integer_nat_decide, Mettapedia.Languages.CHR.Machine.lookup_cons]
    by_cases same : index = other
    · subst same
      simp only [decide_true, ↓reduceIte, Option.map_some, optionAtom]
      exact make_returns _ _ "ChrSome" _ _ inert (.cons bound .nil)
    · have different : other ≠ index := fun equal => same equal.symm
      simp only [same, different, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih _ _ _ bound bound

theorem environment_cons (index : Nat) (value : Value) (environment : Environment) :
    environmentAtom ((index, value) :: environment) =
      cons (.expression [.symbol "ChrBind", integer index, valueAtom value]) (environmentAtom environment) := rfl

open Mettapedia.Languages.CHR.Machine (matchTerm matchTerms instantiateTerm instantiateTerms)

/-! ## Matching -/

mutual
  theorem match_returns (state : State) :
      ∀ (term : Term) (value : Value) (environment : Environment) (caller : Subst) (first second third : Atom),
        Returns caller state first (termAtom term) → Returns caller state second (valueAtom value) →
        Returns caller state third (environmentAtom environment) →
        Returns caller state (apply "gslt:chr-machine:match" [first, second, third])
          (optionAtom ((matchTerm term value environment).map environmentAtom))
    | .value datum, value, environment, caller, first, second, third, one, two, three => by
      machine_call (.cons one (.cons two (.cons three .nil)))
      machine_case (bound)
      apply pure_if_returns _ _ _ _ (decide (valueAtom datum = valueAtom value)) _ _ _
        (equal_returns _ _ _ _ _ _ bound bound)
      rw [valueAtom_decide]
      by_cases same : datum = value
      · simp only [same, decide_true, ↓reduceIte, matchTerm, Option.map_some, optionAtom]
        exact make_returns _ _ "ChrSome" _ _ inert (.cons bound .nil)
      · simp only [same, decide_false, Bool.false_eq_true, ↓reduceIte, matchTerm, Option.map_none, optionAtom]
        exact Eval.symbol_returns runtime _ state "ChrNone"
    | .var index, value, environment, caller, first, second, third, one, two, three => by
      machine_call (.cons one (.cons two (.cons three .nil)))
      machine_case (bound)
      have looked := lookup_returns state index environment
      cases found : Mettapedia.Languages.CHR.lookup environment index with
      | none =>
        rw [found] at looked
        machine_case (looked _ _ _ bound bound)
        simp only [matchTerm, found, Option.map_some, optionAtom, environment_cons]
        exact make_returns _ _ "ChrSome" _ _ inert (.cons (make_returns _ _ "ChrCons" _ _ inert
          (.cons (make_returns _ _ "ChrBind" _ _ inert (.cons bound (.cons bound .nil))) (.cons bound .nil))) .nil)
      | some old =>
        rw [found] at looked
        machine_case (looked _ _ _ bound bound)
        apply pure_if_returns _ _ _ _ (decide (valueAtom old = valueAtom value)) _ _ _
          (equal_returns _ _ _ _ _ _ bound bound)
        rw [valueAtom_decide]
        by_cases same : old = value
        · simp only [same, decide_true, ↓reduceIte, matchTerm, found, Option.map_some, optionAtom]
          exact make_returns _ _ "ChrSome" _ _ inert (.cons bound .nil)
        · simp only [same, decide_false, Bool.false_eq_true, ↓reduceIte, matchTerm, found, Option.map_none,
            optionAtom]
          exact Eval.symbol_returns runtime _ state "ChrNone"
    | .tuple terms, value, environment, caller, first, second, third, one, two, three => by
      machine_call (.cons one (.cons two (.cons three .nil)))
      machine_case (bound)
      cases value with
      | integer number =>
        machine_case (bound)
        simp only [matchTerm, Option.map_none, optionAtom]
        exact Eval.symbol_returns runtime _ state "ChrNone"
      | atom name =>
        machine_case (bound)
        simp only [matchTerm, Option.map_none, optionAtom]
        exact Eval.symbol_returns runtime _ state "ChrNone"
      | tuple fields =>
        machine_case (bound)
        simp only [matchTerm]
        exact matchAll_returns state terms fields environment _ _ _ _ bound bound bound

  theorem matchAll_returns (state : State) :
      ∀ (terms : List Term) (values : List Value) (environment : Environment) (caller : Subst)
        (first second third : Atom),
        Returns caller state first (termsAtom terms) → Returns caller state second (valuesAtom values) →
        Returns caller state third (environmentAtom environment) →
        Returns caller state (apply "gslt:chr-machine:match-all" [first, second, third])
          (optionAtom ((matchTerms terms values environment).map environmentAtom))
    | [], [], environment, caller, first, second, third, one, two, three => by
      machine_call (.cons one (.cons two (.cons three .nil)))
      machine_case (tuple_variables_return runtime _ state ["terms", "values"])
        unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst]
      simp only [matchTerms, Option.map_some, optionAtom]
      exact make_returns _ _ "ChrSome" _ _ inert (.cons bound .nil)
    | [], _ :: _, environment, caller, first, second, third, one, two, three => by
      machine_call (.cons one (.cons two (.cons three .nil)))
      machine_case (tuple_variables_return runtime _ state ["terms", "values"])
        unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst]
      simp only [matchTerms, Option.map_none, optionAtom]
      exact Eval.symbol_returns runtime _ state "ChrNone"
    | _ :: _, [], environment, caller, first, second, third, one, two, three => by
      machine_call (.cons one (.cons two (.cons three .nil)))
      machine_case (tuple_variables_return runtime _ state ["terms", "values"])
        unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst]
      simp only [matchTerms, Option.map_none, optionAtom]
      exact Eval.symbol_returns runtime _ state "ChrNone"
    | term :: terms, value :: values, environment, caller, first, second, third, one, two, three => by
      machine_call (.cons one (.cons two (.cons three .nil)))
      machine_case (tuple_variables_return runtime _ state ["terms", "values"])
        unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst]
      have matched := match_returns state term value environment
      cases found : matchTerm term value environment with
      | none =>
        rw [found] at matched
        machine_case (matched _ _ _ _ bound bound bound)
        simp only [matchTerms, found, Option.map_none, optionAtom]
        exact Eval.symbol_returns runtime _ state "ChrNone"
      | some extended =>
        rw [found] at matched
        machine_case (matched _ _ _ _ bound bound bound)
        simp only [matchTerms, found]
        exact matchAll_returns state terms values extended _ _ _ _ bound bound bound
end

/-! ## Instantiation -/

mutual
  theorem instantiate_returns (state : State) :
      ∀ (term : Term) (environment : Environment) (caller : Subst) (first second : Atom),
        Returns caller state first (termAtom term) → Returns caller state second (environmentAtom environment) →
        Returns caller state (apply "gslt:chr-machine:instantiate" [first, second])
          (optionAtom ((instantiateTerm environment term).map valueAtom))
    | .value datum, environment, caller, first, second, one, two => by
      machine_call (.cons one (.cons two .nil))
      machine_case (bound)
      simp only [instantiateTerm, Option.map_some, optionAtom]
      exact make_returns _ _ "ChrSome" _ _ inert (.cons bound .nil)
    | .var index, environment, caller, first, second, one, two => by
      machine_call (.cons one (.cons two .nil))
      machine_case (bound)
      exact lookup_returns state index environment _ _ _ bound bound
    | .tuple terms, environment, caller, first, second, one, two => by
      machine_call (.cons one (.cons two .nil))
      machine_case (bound)
      have instantiated := instantiateAll_returns state terms environment
      cases found : instantiateTerms environment terms with
      | none =>
        rw [found] at instantiated
        machine_case (instantiated _ _ _ bound bound)
        simp only [instantiateTerm, found, Option.map_none, optionAtom]
        exact Eval.symbol_returns runtime _ state "ChrNone"
      | some values =>
        rw [found] at instantiated
        machine_case (instantiated _ _ _ bound bound)
        simp only [instantiateTerm, found, Option.map_some, optionAtom, valueAtom]
        exact make_returns _ _ "ChrSome" _ _ inert (.cons (make_returns _ _ "ChrTuple" _ _ inert (.cons bound .nil)) .nil)

  theorem instantiateAll_returns (state : State) :
      ∀ (terms : List Term) (environment : Environment) (caller : Subst) (first second : Atom),
        Returns caller state first (termsAtom terms) → Returns caller state second (environmentAtom environment) →
        Returns caller state (apply "gslt:chr-machine:instantiate-all" [first, second])
          (optionAtom ((instantiateTerms environment terms).map valuesAtom))
    | [], environment, caller, first, second, one, two => by
      machine_call (.cons one (.cons two .nil))
      machine_case (bound)
      simp only [instantiateTerms, Option.map_some, optionAtom, valuesAtom, nil]
      exact make_returns _ _ "ChrSome" _ _ inert (.cons (Eval.symbol_returns runtime _ state "ChrNil") .nil)
    | term :: terms, environment, caller, first, second, one, two => by
      machine_call (.cons one (.cons two .nil))
      machine_case (bound)
      have instantiated := instantiate_returns state term environment
      cases found : instantiateTerm environment term with
      | none =>
        rw [found] at instantiated
        machine_case (instantiated _ _ _ bound bound)
        simp only [instantiateTerms, found, Option.map_none, optionAtom]
        exact Eval.symbol_returns runtime _ state "ChrNone"
      | some value =>
        rw [found] at instantiated
        machine_case (instantiated _ _ _ bound bound)
        have rest := instantiateAll_returns state terms environment
        cases restFound : instantiateTerms environment terms with
        | none =>
          rw [restFound] at rest
          machine_case (rest _ _ _ bound bound)
          simp only [instantiateTerms, found, restFound, Option.map_none, optionAtom]
          exact Eval.symbol_returns runtime _ state "ChrNone"
        | some values =>
          rw [restFound] at rest
          machine_case (rest _ _ _ bound bound)
          simp only [instantiateTerms, found, restFound, Option.map_some, optionAtom, valuesAtom]
          exact make_returns _ _ "ChrSome" _ _ inert (.cons (make_returns _ _ "ChrCons" _ _ inert
            (.cons bound (.cons bound .nil))) .nil)
end

#print axioms lookup_returns
#print axioms match_returns
#print axioms matchAll_returns
#print axioms instantiate_returns
#print axioms instantiateAll_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineExecution
