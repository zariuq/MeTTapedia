import Mettapedia.ProbabilityTheory.StochasticInference.Finite
import Mettapedia.ProbabilityTheory.BayesianNetworks.EliminationCache
import Mettapedia.ProbabilityTheory.BayesianNetworks.SeparatorFactorization

/-!
# Scope-directed elimination and retained messages

Schedules are free to choose small buckets because correctness holds for any
complete elimination order. A retained elimination can serve every later
payoff on its remaining scope. An accepted factor replacement reuses the
existing dependency-aware cache on the same factor slots.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.StochasticInference

open Mettapedia.ProbabilityTheory.BayesianNetworks
open ExecutableFactorTable ScopedFactorReadout

variable {n m : Nat} {domains : Fin n → Nat}

namespace Schedule

private def bucket (scopes : List (List (Fin n))) (v : Fin n) : List (Fin n) :=
  (scopes.filter fun scope => decide (v ∈ scope)).flatten.dedup

private def exchange (scopes : List (List (Fin n))) (v : Fin n) : List (List (Fin n)) :=
  (bucket scopes v).erase v :: scopes.filter (fun scope => !decide (v ∈ scope))

private def preferred (domains : Fin n → Nat) (scopes : List (List (Fin n)))
    (first : Fin n) (rest : List (Fin n)) : Fin n :=
  let index := scopes.foldl (fun index scope =>
    scope.foldl (fun index v =>
      index.set v.val (scope ++ index[v.val]) v.isLt) index)
    (Vector.replicate n ([] : List (Fin n)))
  let cost := fun (v : Fin n) => volume domains index[v.val].dedup
  (rest.foldl (fun best v =>
    let size := cost v
    if size < best.2 then (v, size) else best) (first, cost first)).1

private def greedyOrder (domains : Fin n → Nat) (scopes : List (List (Fin n)))
    (pending : List (Fin n)) : Nat → List (Fin n)
  | 0 => pending
  | fuel + 1 =>
    match pending with
    | [] => []
    | first :: rest =>
      let chosen := preferred domains scopes first rest
      chosen :: greedyOrder domains (exchange scopes chosen) (pending.erase chosen) fuel

private theorem greedy_covers (domains : Fin n → Nat) (scopes : List (List (Fin n)))
    (pending : List (Fin n)) (fuel : Nat) (v : Fin n) (member : v ∈ pending) :
    v ∈ greedyOrder domains scopes pending fuel := by
  induction fuel generalizing scopes pending with
  | zero => exact member
  | succ fuel ih =>
    cases pending with
    | nil => cases member
    | cons first rest =>
      simp only [greedyOrder]
      let chosen := preferred domains scopes first rest
      change v ∈ chosen :: greedyOrder domains (exchange scopes chosen)
        ((first :: rest).erase chosen) fuel
      by_cases same : v = chosen
      · simp [same]
      · apply List.mem_cons_of_mem
        exact ih _ _ ((List.mem_erase_of_ne same).mpr member)

/-- Prefer the bucket with the fewest cells. With a fixed common domain size
this also favors a leaf over a branch point in a pairwise forest. -/
def greedy (domains : Fin n → Nat) (scopes : List (List (Fin n))) : Schedule n :=
  ⟨greedyOrder domains scopes (List.finRange n) n,
    fun v => greedy_covers domains scopes _ _ v (by simp)⟩

end Schedule

namespace Retained

variable {positive : ∀ v, 0 < domains v} {scopes : Fin m → List (Fin n)}
variable {early : List (Fin n)}

abbrev Bank (positive : ∀ v, 0 < domains v) (scopes : Fin m → List (Fin n))
    (early : List (Fin n)) := EliminationPlan.Runtime positive scopes early

def tables (bank : Bank positive scopes early) : List (Table domains) :=
  List.ofFn fun i : Fin m => bank.factors[i]

/-- Ensure that variables without an explicit factor still have counting
measure on their full domain. -/
def inputs (positive : ∀ v, 0 < domains v) (factors : List (Table domains)) :=
  (factors ++ covering domains positive).toArray.toVector

def prepare (positive : ∀ v, 0 < domains v) (factors : List (Table domains))
    (early : List (Fin n)) :=
  EliminationPlan.Runtime.prepare positive (inputs positive factors) early

private theorem singleton_valuation (table : Table domains) :
    BayesianNetworks.combineAll ([table].map (Table.toValuation domains positive)) =
      table.toValuation domains positive := by
  apply BayesianNetworks.Valuation.ext
  · simp [BayesianNetworks.combineAll, combine, oneValuation]
  · intro x
    simp [BayesianNetworks.combineAll, combine, oneValuation]

private theorem cached_valuation (bank : Bank positive scopes early) :
    bank.table.toValuation domains positive =
      sumOutAll (BayesianNetworks.combineAll ((tables bank).map
        (Table.toValuation domains positive))) early := by
  rw [EliminationPlan.Runtime.table_exact]
  exact elimination_correct domains positive (tables bank) early

private theorem valuation_append (left right : List (Table domains)) :
    BayesianNetworks.combineAll ((left ++ right).map (Table.toValuation domains positive)) =
      combine (BayesianNetworks.combineAll (left.map (Table.toValuation domains positive)))
        (BayesianNetworks.combineAll (right.map (Table.toValuation domains positive))) := by
  induction left with
  | nil =>
    apply BayesianNetworks.Valuation.ext
    · simp [BayesianNetworks.combineAll, combine, oneValuation]
    · intro x
      simp [BayesianNetworks.combineAll, combine, oneValuation]
  | cons first rest ih =>
    simp only [List.cons_append, List.map_cons, BayesianNetworks.combineAll, List.foldr_cons] at ih ⊢
    rw [ih, combine_assoc]

theorem finish_exact (bank : Bank positive scopes early) (suffix : List (Fin n)) :
    weight domains positive [bank.table] suffix =
      weight domains positive (tables bank) (early ++ suffix) := by
  let v (factors : List (Table domains)) (order : List (Fin n)) :=
    (ExecutableFactorTable.combineAll domains positive
      (eliminateVars domains positive factors order)).toValuation domains positive
  have same : v [bank.table] suffix = v (tables bank) (early ++ suffix) := by
    simp only [v, elimination_correct, singleton_valuation, cached_valuation,
      sumOutAll, List.foldl_append]
  exact congrArg (fun φ : BayesianNetworks.Valuation (Fin n) (fun i => Fin (domains i)) ℚ =>
    φ.val (fun i => ⟨0, positive i⟩)) same

theorem finish_with_payoff_exact (bank : Bank positive scopes early) (suffix : List (Fin n))
    (payoff : Table domains) (retained : ∀ v ∈ early, v ∉ payoff.scope) :
    weight domains positive [bank.table, payoff] suffix =
      weight domains positive (tables bank ++ [payoff]) (early ++ suffix) := by
  let v (tables : List (Table domains)) (order : List (Fin n)) :=
    (ExecutableFactorTable.combineAll domains positive
      (eliminateVars domains positive tables order)).toValuation domains positive
  have advance : sumOutAll (combine
      (BayesianNetworks.combineAll ((tables bank).map (Table.toValuation domains positive)))
      (payoff.toValuation domains positive)) early =
      combine (sumOutAll
        (BayesianNetworks.combineAll ((tables bank).map (Table.toValuation domains positive))) early)
        (payoff.toValuation domains positive) :=
    SeparatorFactorization.sumOutAll_combine _ _ _ (payoff.respects domains positive) (by
      intro i member
      simpa [Table.toValuation] using retained i member)
  have after : v [bank.table, payoff] suffix = v (tables bank ++ [payoff]) (early ++ suffix) := by
    have pair : [bank.table, payoff] = [bank.table] ++ [payoff] := rfl
    rw [pair]
    simp only [v, elimination_correct, valuation_append,
      singleton_valuation, cached_valuation]
    have append (φ : BayesianNetworks.Valuation (Fin n) (fun i => Fin (domains i)) ℚ) :
        sumOutAll φ (early ++ suffix) = sumOutAll (sumOutAll φ early) suffix := by
      simp only [sumOutAll, List.foldl_append]
    rw [append, advance]
  exact congrArg (fun φ : BayesianNetworks.Valuation (Fin n) (fun i => Fin (domains i)) ℚ =>
    φ.val (fun i => ⟨0, positive i⟩)) after

/-- Read a payoff from one retained message. A query that reads an eliminated
variable needs a different plan. -/
def read? (bank : Bank positive scopes early) (suffix : List (Fin n)) (payoff : Table domains) :
    Option Masses :=
  if (∀ v : Fin n, v ∈ early ++ suffix) ∧ (∀ v ∈ early, v ∉ payoff.scope) ∧
      (∀ v : Fin n, ∃ slot : Fin m, v ∈ scopes slot) then
    some ⟨weight domains positive [bank.table, payoff] suffix,
      weight domains positive [bank.table] suffix⟩
  else none

theorem read_exact (bank : Bank positive scopes early) (suffix : List (Fin n))
    (payoff : Table domains) (covers : ∀ v : Fin n, v ∈ early ++ suffix)
    (retained : ∀ v ∈ early, v ∉ payoff.scope)
    (full : ∀ v : Fin n, ∃ slot : Fin m, v ∈ scopes slot) :
    read? bank suffix payoff =
      some ⟨weight domains positive (tables bank ++ [payoff]) (early ++ suffix),
        weight domains positive (tables bank) (early ++ suffix)⟩ := by
  rw [read?, if_pos ⟨covers, retained, full⟩, finish_exact,
    finish_with_payoff_exact bank suffix payoff retained]

end Retained

end Mettapedia.ProbabilityTheory.StochasticInference
