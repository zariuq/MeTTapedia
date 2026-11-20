import Mettapedia.ProbabilityTheory.BayesianNetworks.ExecutableFactorTable

/-!
# Scope-based compilation of variable elimination

Compile one elimination order using only the scopes of the input factors.
Any later assignment of tables to those same factor slots evaluates to the
existing exact bucket eliminator. This is the reference for retaining
intermediate tables across evidence updates.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

open ExecutableFactorTable

inductive EliminationPlan (nVars inputs : Nat) where
  | unit
  | input (slot : Fin inputs)
  | mul (left right : EliminationPlan nVars inputs)
  | sumOut (v : Fin nVars) (body : EliminationPlan nVars inputs)

namespace EliminationPlan

variable {n m : Nat} {domains : Fin n → Nat}

def scope (scopes : Fin m → List (Fin n)) : EliminationPlan n m → List (Fin n)
  | .unit => []
  | .input slot => scopes slot
  | .mul left right => (left.scope scopes ++ right.scope scopes).dedup
  | .sumOut v body => (body.scope scopes).erase v

def evaluate (positive : ∀ v, 0 < domains v) (tables : Fin m → Table domains) :
    EliminationPlan n m → Table domains
  | .unit => ExecutableFactorTable.one domains positive
  | .input slot => tables slot
  | .mul left right => (left.evaluate positive tables).mul domains positive (right.evaluate positive tables)
  | .sumOut v body => (body.evaluate positive tables).sumOut domains positive v

theorem evaluate_scope (positive : ∀ v, 0 < domains v) (tables : Fin m → Table domains)
    (scopes : Fin m → List (Fin n)) (agrees : ∀ slot, (tables slot).scope = scopes slot)
    (plan : EliminationPlan n m) : (plan.evaluate positive tables).scope = plan.scope scopes := by
  induction plan with
  | unit => rfl
  | input slot => exact agrees slot
  | mul left right ihl ihr =>
    simp only [evaluate, scope, Table.mul, tabulate, ihl, ihr]
  | sumOut v body ih =>
    simp only [evaluate, scope, Table.sumOut, ih]
    split
    · simp [tabulate]
    · rw [List.erase_of_not_mem (by assumption)]
      exact ih

def product (plans : List (EliminationPlan n m)) : EliminationPlan n m :=
  plans.foldr .mul .unit

theorem evaluate_product (positive : ∀ v, 0 < domains v) (tables : Fin m → Table domains)
    (plans : List (EliminationPlan n m)) :
    (product plans).evaluate positive tables =
      ExecutableFactorTable.combineAll domains positive (plans.map (evaluate positive tables)) := by
  induction plans with
  | nil => rfl
  | cons plan plans ih =>
    change (plan.evaluate positive tables).mul domains positive ((product plans).evaluate positive tables) =
      (plan.evaluate positive tables).mul domains positive _
    rw [ih]
    rfl

def compileVar (scopes : Fin m → List (Fin n)) (plans : List (EliminationPlan n m))
    (v : Fin n) : List (EliminationPlan n m) :=
  let selected := plans.filter fun plan => decide (v ∈ plan.scope scopes)
  let rest := plans.filter fun plan => !decide (v ∈ plan.scope scopes)
  match selected with
  | [] => rest
  | _ => .sumOut v (product selected) :: rest

theorem evaluate_compileVar (positive : ∀ v, 0 < domains v) (tables : Fin m → Table domains)
    (scopes : Fin m → List (Fin n)) (agrees : ∀ slot, (tables slot).scope = scopes slot)
    (plans : List (EliminationPlan n m)) (v : Fin n) :
    (compileVar scopes plans v).map (evaluate positive tables) =
      ExecutableFactorTable.eliminateVar domains positive (plans.map (evaluate positive tables)) v := by
  unfold compileVar ExecutableFactorTable.eliminateVar
  simp only [List.filter_map, Function.comp_def, evaluate_scope positive tables scopes agrees]
  generalize plans.filter (fun plan => decide (v ∈ plan.scope scopes)) = selected
  cases selected with
  | nil => rfl
  | cons plan plans =>
    simp only [List.map_cons, evaluate, evaluate_product]

def compile (scopes : Fin m → List (Fin n)) (order : List (Fin n)) : EliminationPlan n m :=
  product (order.foldl (compileVar scopes) (List.ofFn .input))

theorem evaluate_compile (positive : ∀ v, 0 < domains v) (tables : Fin m → Table domains)
    (scopes : Fin m → List (Fin n)) (agrees : ∀ slot, (tables slot).scope = scopes slot)
    (order : List (Fin n)) :
    (compile scopes order).evaluate positive tables =
      ExecutableFactorTable.combineAll domains positive
        (ExecutableFactorTable.eliminateVars domains positive (List.ofFn tables) order) := by
  have agenda (plans : List (EliminationPlan n m)) :
      (order.foldl (compileVar scopes) plans).map (evaluate positive tables) =
        ExecutableFactorTable.eliminateVars domains positive (plans.map (evaluate positive tables)) order := by
    induction order generalizing plans with
    | nil => rfl
    | cons v order ih =>
      simp only [List.foldl_cons, ExecutableFactorTable.eliminateVars]
      rw [show (order.foldl (compileVar scopes) (compileVar scopes plans v)).map
          (evaluate positive tables) = _ from ih _]
      rw [evaluate_compileVar positive tables scopes agrees]
      rfl
  rw [compile, evaluate_product, agenda, List.map_ofFn]
  rfl

/-- The compiled schedule has the valuation semantics of full elimination. -/
theorem compile_refines (positive : ∀ v, 0 < domains v) (tables : Fin m → Table domains)
    (scopes : Fin m → List (Fin n)) (agrees : ∀ slot, (tables slot).scope = scopes slot)
    (order : List (Fin n)) :
    ((compile scopes order).evaluate positive tables).toValuation domains positive =
      BayesianNetworks.sumOutAll
        (BayesianNetworks.combineAll ((List.ofFn tables).map (Table.toValuation domains positive))) order := by
  rw [evaluate_compile positive tables scopes agrees]
  exact ExecutableFactorTable.elimination_correct domains positive (List.ofFn tables) order

end EliminationPlan
end Mettapedia.ProbabilityTheory.BayesianNetworks
