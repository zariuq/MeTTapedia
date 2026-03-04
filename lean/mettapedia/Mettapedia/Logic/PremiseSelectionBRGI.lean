import Mathlib.Data.Finset.Max
import Mettapedia.Logic.PremiseSelectionCoverage

/-!
# Finite BRGI Object (Chapter 9 Positive Core)

This module adds a concrete finite object for Chapter-9-style
batch reasoning graph inference (BRGI):

- finite premise pool
- dependency objective (`|S ∩ D|`)
- explicit independence/admissibility policy
- global finite optimization theorem over feasible premise sets

The focus is theorem-level semantics (not runtime scheduling).
-/

namespace Mettapedia.Logic.PremiseSelection

open scoped Classical

variable {Fact : Type*} [DecidableEq Fact]

/-- Independence/admissibility policy for selected premise sets. -/
structure IndependencePolicy (Fact : Type*) [DecidableEq Fact] where
  admissible : Finset Fact → Prop
  dec_admissible : DecidablePred admissible
  empty_admissible : admissible ∅

attribute [instance] IndependencePolicy.dec_admissible

/-- Finite BRGI problem instance. -/
structure BRGIProblem (Fact : Type*) [DecidableEq Fact] where
  pool : Finset Fact
  dependencies : Finset Fact
  budget : Nat
  indep : IndependencePolicy Fact

/-- Chapter-9 BRGI surrogate objective: dependency coverage in the selected set. -/
def brgiObjective (P : BRGIProblem Fact) (S : Finset Fact) : Nat :=
  dependencyCoverage P.dependencies S

/-- Feasible selected sets: subset of pool, budget-respecting, and independence-admissible. -/
def feasibleSets (P : BRGIProblem Fact) : Finset (Finset Fact) :=
  (P.pool.powerset).filter (fun S => decide (S.card ≤ P.budget ∧ P.indep.admissible S))

theorem mem_feasibleSets_iff (P : BRGIProblem Fact) (S : Finset Fact) :
    S ∈ feasibleSets P ↔
      S ⊆ P.pool ∧ S.card ≤ P.budget ∧ P.indep.admissible S := by
  simp [feasibleSets]

theorem empty_mem_feasibleSets (P : BRGIProblem Fact) :
    (∅ : Finset Fact) ∈ feasibleSets P := by
  exact (mem_feasibleSets_iff (P := P) ∅).2
    ⟨by simp, Nat.zero_le P.budget, P.indep.empty_admissible⟩

theorem brgiObjective_le_of_feasible {P : BRGIProblem Fact} {S : Finset Fact}
    (hS : S ∈ feasibleSets P) :
    brgiObjective P S ≤ Nat.min P.budget P.dependencies.card := by
  rcases (mem_feasibleSets_iff (P := P) S).1 hS with ⟨_, hCard, _⟩
  exact dependencyCoverage_le_min_of_card_le (D := P.dependencies) (S := S) hCard

/-- Finite optimization endpoint:
there exists a globally optimal feasible selected set. -/
theorem exists_optimal_feasible_set (P : BRGIProblem Fact) :
    ∃ S, S ∈ feasibleSets P
      ∧ ∀ T, T ∈ feasibleSets P → brgiObjective P T ≤ brgiObjective P S := by
  have hne : (feasibleSets P).Nonempty := ⟨∅, empty_mem_feasibleSets (P := P)⟩
  rcases Finset.exists_max_image (feasibleSets P) (brgiObjective P) hne
    with ⟨S, hS, hmax⟩
  exact ⟨S, hS, hmax⟩

/-- There exists a dependency-contained set that reaches the cardinality upper bound. -/
theorem exists_dependency_subset_attaining_min
    (D : Finset Fact) (k : Nat) :
    ∃ S : Finset Fact, S ⊆ D ∧ S.card ≤ k ∧ dependencyCoverage D S = Nat.min k D.card := by
  by_cases hk : k ≤ D.card
  · obtain ⟨S, hSD, hcard⟩ := Finset.exists_subset_card_eq hk
    refine ⟨S, hSD, ?_, ?_⟩
    · simp [hcard]
    · have hinter : S ∩ D = S := Finset.inter_eq_left.mpr hSD
      simp [dependencyCoverage, hinter, hcard, Nat.min_eq_left hk]
  · have hlt : D.card < k := Nat.lt_of_not_ge hk
    refine ⟨D, subset_rfl, le_of_lt hlt, ?_⟩
    simp [dependencyCoverage, Nat.min_eq_right (Nat.le_of_lt hlt)]

/-- Policy-sensitive witness theorem:
if all dependency subsets are admissible and dependencies are in-pool, a feasible
set achieves the maximal bound `min(budget, |dependencies|)`. -/
theorem exists_feasible_with_optimal_value_of_policy
    (P : BRGIProblem Fact)
    (hDepPool : P.dependencies ⊆ P.pool)
    (hPolicy : ∀ S : Finset Fact, S ⊆ P.dependencies → P.indep.admissible S) :
    ∃ S, S ∈ feasibleSets P
      ∧ brgiObjective P S = Nat.min P.budget P.dependencies.card := by
  rcases exists_dependency_subset_attaining_min (D := P.dependencies) (k := P.budget)
    with ⟨S, hSD, hCard, hObj⟩
  refine ⟨S, (mem_feasibleSets_iff (P := P) S).2 ?_, hObj⟩
  exact ⟨subset_trans hSD hDepPool, hCard, hPolicy S hSD⟩

/-- Policy-sensitive objective refinement:
under the policy assumptions, the feasible optimum value is characterized exactly
as `min(budget, |dependencies|)`. -/
theorem exists_optimal_feasible_set_with_policy_characterization
    (P : BRGIProblem Fact)
    (hDepPool : P.dependencies ⊆ P.pool)
    (hPolicy : ∀ S : Finset Fact, S ⊆ P.dependencies → P.indep.admissible S) :
    ∃ S, S ∈ feasibleSets P
      ∧ brgiObjective P S = Nat.min P.budget P.dependencies.card
      ∧ ∀ T, T ∈ feasibleSets P → brgiObjective P T ≤ brgiObjective P S := by
  rcases exists_feasible_with_optimal_value_of_policy (P := P) hDepPool hPolicy
    with ⟨S, hS, hObj⟩
  refine ⟨S, hS, hObj, ?_⟩
  intro T hT
  have hBound := brgiObjective_le_of_feasible (P := P) (S := T) hT
  simpa [hObj] using hBound

/-- Any feasible maximizer has the policy-characterized objective value. -/
theorem optimal_value_eq_min_of_policy
    {P : BRGIProblem Fact} {S : Finset Fact}
    (hS : S ∈ feasibleSets P)
    (hMax : ∀ T, T ∈ feasibleSets P → brgiObjective P T ≤ brgiObjective P S)
    (hDepPool : P.dependencies ⊆ P.pool)
    (hPolicy : ∀ T : Finset Fact, T ⊆ P.dependencies → P.indep.admissible T) :
    brgiObjective P S = Nat.min P.budget P.dependencies.card := by
  rcases exists_feasible_with_optimal_value_of_policy (P := P) hDepPool hPolicy
    with ⟨T, hT, hTObj⟩
  have hLower : Nat.min P.budget P.dependencies.card ≤ brgiObjective P S := by
    calc
      Nat.min P.budget P.dependencies.card = brgiObjective P T := hTObj.symm
      _ ≤ brgiObjective P S := hMax T hT
  have hUpper : brgiObjective P S ≤ Nat.min P.budget P.dependencies.card :=
    brgiObjective_le_of_feasible (P := P) (S := S) hS
  exact Nat.le_antisymm hUpper hLower

/-! ## Graph-level BRGI object and refinement wrappers -/

/-- Explicit finite BRG graph object (nodes/edges + dependency-marked nodes). -/
structure BRGGraph (Fact : Type*) [DecidableEq Fact] where
  nodes : Finset Fact
  edges : Finset (Fact × Fact)
  dependencies : Finset Fact

/-- Policy-parameterized finite BRG instance. -/
structure BRGInstance (Fact : Type*) [DecidableEq Fact] where
  graph : BRGGraph Fact
  budget : Nat
  indep : IndependencePolicy Fact

/-- Graph instance lowered to the finite-set BRGI objective layer. -/
def BRGInstance.toProblem (I : BRGInstance Fact) : BRGIProblem Fact where
  pool := I.graph.nodes
  dependencies := I.graph.dependencies
  budget := I.budget
  indep := I.indep

/-- Graph-level feasible sets. -/
def brgFeasibleSets (I : BRGInstance Fact) : Finset (Finset Fact) :=
  feasibleSets I.toProblem

/-- Graph-level objective. -/
def brgObjective (I : BRGInstance Fact) (S : Finset Fact) : Nat :=
  brgiObjective I.toProblem S

theorem mem_brgFeasibleSets_iff (I : BRGInstance Fact) (S : Finset Fact) :
    S ∈ brgFeasibleSets I ↔
      S ⊆ I.graph.nodes ∧ S.card ≤ I.budget ∧ I.indep.admissible S := by
  simpa [brgFeasibleSets, BRGInstance.toProblem] using mem_feasibleSets_iff (P := I.toProblem) S

/-- Graph-level finite optimization endpoint, refined from `BRGIProblem`. -/
theorem exists_optimal_feasible_set_brg (I : BRGInstance Fact) :
    ∃ S, S ∈ brgFeasibleSets I
      ∧ ∀ T, T ∈ brgFeasibleSets I → brgObjective I T ≤ brgObjective I S := by
  simpa [brgFeasibleSets, brgObjective] using
    exists_optimal_feasible_set (P := I.toProblem)

/-- Graph-level policy-sensitive optimum characterization, preserved from
the finite-set BRGI layer. -/
theorem exists_optimal_feasible_set_brg_with_policy_characterization
    (I : BRGInstance Fact)
    (hDepNodes : I.graph.dependencies ⊆ I.graph.nodes)
    (hPolicy : ∀ S : Finset Fact, S ⊆ I.graph.dependencies → I.indep.admissible S) :
    ∃ S, S ∈ brgFeasibleSets I
      ∧ brgObjective I S = Nat.min I.budget I.graph.dependencies.card
      ∧ ∀ T, T ∈ brgFeasibleSets I → brgObjective I T ≤ brgObjective I S := by
  simpa [brgFeasibleSets, brgObjective, BRGInstance.toProblem] using
    exists_optimal_feasible_set_with_policy_characterization
      (P := I.toProblem) hDepNodes hPolicy

/-- Graph-level optimal-value characterization for any feasible maximizer. -/
theorem brg_optimal_value_eq_min_of_policy
    {I : BRGInstance Fact} {S : Finset Fact}
    (hS : S ∈ brgFeasibleSets I)
    (hMax : ∀ T, T ∈ brgFeasibleSets I → brgObjective I T ≤ brgObjective I S)
    (hDepNodes : I.graph.dependencies ⊆ I.graph.nodes)
    (hPolicy : ∀ T : Finset Fact, T ⊆ I.graph.dependencies → I.indep.admissible T) :
    brgObjective I S = Nat.min I.budget I.graph.dependencies.card := by
  simpa [brgFeasibleSets, brgObjective, BRGInstance.toProblem] using
    optimal_value_eq_min_of_policy (P := I.toProblem) (S := S) hS hMax hDepNodes hPolicy

/-! ## Concrete finite BRGI fixture -/

abbrev Fact4 := Fin 4

/-- Simple independence policy: never select both `a` and `b` together. -/
def banPairPolicy (a b : Fact4) : IndependencePolicy Fact4 where
  admissible S := ¬ (a ∈ S ∧ b ∈ S)
  dec_admissible := by
    intro S
    infer_instance
  empty_admissible := by simp

def toyBRGI : BRGIProblem Fact4 where
  pool := ({0, 1, 2, 3} : Finset Fact4)
  dependencies := ({0, 1, 2} : Finset Fact4)
  budget := 2
  indep := banPairPolicy 2 3

def toyWitness : Finset Fact4 := ({0, 1} : Finset Fact4)

theorem toyWitness_feasible : toyWitness ∈ feasibleSets toyBRGI := by
  exact (mem_feasibleSets_iff (P := toyBRGI) toyWitness).2
    ⟨by decide, by decide, by decide⟩

theorem toyWitness_objective : brgiObjective toyBRGI toyWitness = 2 := by
  decide

/-- Concrete Chapter-9 BRGI optimization theorem:
for the finite fixture, feasible global optimum value is exactly `2`. -/
theorem ch9_brgi_toy_optimal_value :
    ∃ S, S ∈ feasibleSets toyBRGI
      ∧ brgiObjective toyBRGI S = 2
      ∧ ∀ T, T ∈ feasibleSets toyBRGI →
          brgiObjective toyBRGI T ≤ brgiObjective toyBRGI S := by
  rcases exists_optimal_feasible_set (P := toyBRGI) with ⟨S, hS, hMax⟩
  have hUpper : brgiObjective toyBRGI S ≤ 2 := by
    have hBound := brgiObjective_le_of_feasible (P := toyBRGI) (S := S) hS
    exact le_trans hBound (by decide : Nat.min toyBRGI.budget toyBRGI.dependencies.card ≤ 2)
  have hLower : 2 ≤ brgiObjective toyBRGI S := by
    calc
      2 = brgiObjective toyBRGI toyWitness := (toyWitness_objective).symm
      _ ≤ brgiObjective toyBRGI S := hMax toyWitness toyWitness_feasible
  have hEq : brgiObjective toyBRGI S = 2 := Nat.le_antisymm hUpper hLower
  exact ⟨S, hS, hEq, hMax⟩

/-! ## Concrete graph-level BRGI fixture -/

def toyBRGGraph : BRGGraph Fact4 where
  nodes := ({0, 1, 2, 3} : Finset Fact4)
  edges := ({(0, 2), (1, 2), (2, 3)} : Finset (Fact4 × Fact4))
  dependencies := ({0, 1, 2} : Finset Fact4)

def toyBRGInstance : BRGInstance Fact4 where
  graph := toyBRGGraph
  budget := 2
  indep := banPairPolicy 2 3

theorem toyBRG_toProblem_eq_toyBRGI :
    toyBRGInstance.toProblem = toyBRGI := by
  rfl

/-- Graph-object refinement canary:
the graph-level instance preserves the same optimum characterization as `toyBRGI`. -/
theorem ch9_brg_graph_toy_optimal_value :
    ∃ S, S ∈ brgFeasibleSets toyBRGInstance
      ∧ brgObjective toyBRGInstance S = 2
      ∧ ∀ T, T ∈ brgFeasibleSets toyBRGInstance →
          brgObjective toyBRGInstance T ≤ brgObjective toyBRGInstance S := by
  simpa [brgFeasibleSets, brgObjective, toyBRG_toProblem_eq_toyBRGI] using
    ch9_brgi_toy_optimal_value

end Mettapedia.Logic.PremiseSelection
