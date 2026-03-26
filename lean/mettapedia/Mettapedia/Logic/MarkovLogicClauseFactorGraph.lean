import Mettapedia.Logic.MarkovLogicClauseSemantics
import Mettapedia.ProbabilityTheory.BayesianNetworks.VEBridge

/-!
# Clause-Scope Factor Graphs for Ground MLNs

This module upgrades the MLN bridge from extensional world-weight storage to an actual
clause-scope factor graph:

- variables are ground atoms,
- factors are active weighted clauses,
- each factor scope is exactly the atoms mentioned by its clause,
- VE constraint weights coincide with MLN query masses for finite constraint queries.

This repairs the main semantic-scope gap in the earlier extensional factor-graph bridge.
-/

namespace Mettapedia.Logic.MarkovLogicClauseFactorGraph

open scoped ENNReal BigOperators
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicCountable
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.ProbabilityTheory.BayesianNetworks

/-- Finite conjunctions of atom-value constraints. -/
abbrev ConstraintQuery (Atom : Type*) := List (Sigma fun _ : Atom => Bool)

/-- A Boolean valuation satisfies a finite constraint list if it matches every listed atom value. -/
def satisfiesConstraints {Atom : Type*} (W : AtomValuation Atom) (constraints : ConstraintQuery Atom) : Prop :=
  ∀ c ∈ constraints, W c.1 = c.2

instance satisfiesConstraintsDecidable {Atom : Type*}
    (W : AtomValuation Atom) (constraints : ConstraintQuery Atom) :
    Decidable (satisfiesConstraints W constraints) := by
  unfold satisfiesConstraints; infer_instance

/-- Query interpretation for finite atom-value constraints. -/
def constraintQueryHolds {Atom : Type*} : ConstraintQuery Atom → AtomValuation Atom → Prop :=
  fun constraints W => satisfiesConstraints W constraints

namespace GroundMLN

-- Bring the original GroundMLN members (ActiveClause, worldWeight, etc.) into scope
open Mettapedia.Logic.MarkovLogicClauseSemantics.GroundMLN

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- Actual clause-scope factor graph for a finite active clause family. -/
noncomputable def compiledClauseFactorGraph
    (M : GroundMLN Atom ClauseId)
    (support : Finset ClauseId) : FactorGraph Atom ENNReal where
  stateSpace _ := Bool
  factors := ActiveClause support
  scope i := (M.clauseData i.1).clause.atoms
  potential i := (M.clauseData i.1).evalOnScope

private instance compiledClauseFactorGraphFactorsFintype
    (M : GroundMLN Atom ClauseId)
    (support : Finset ClauseId) :
    Fintype (compiledClauseFactorGraph M support).factors := by
  dsimp [compiledClauseFactorGraph, ActiveClause]
  infer_instance

private instance compiledClauseFactorGraphStateFintype
    (M : GroundMLN Atom ClauseId)
    (support : Finset ClauseId) (a : Atom) :
    Fintype ((compiledClauseFactorGraph M support).stateSpace a) := by
  dsimp [compiledClauseFactorGraph]
  infer_instance

private instance compiledClauseFactorGraphStateDecidableEq
    (M : GroundMLN Atom ClauseId)
    (support : Finset ClauseId) (a : Atom) :
    DecidableEq ((compiledClauseFactorGraph M support).stateSpace a) := by
  dsimp [compiledClauseFactorGraph]
  infer_instance

omit [DecidableEq ClauseId] in
/-- The compiled clause factor graph computes exactly the MLN world weight. -/
theorem compiledClauseFactorGraph_unnormalizedJoint_eq_worldWeight
    (M : GroundMLN Atom ClauseId)
    (support : Finset ClauseId) (W : AtomValuation Atom) :
    (compiledClauseFactorGraph M support).unnormalizedJoint W = M.worldWeight support W := by
  classical
  unfold FactorGraph.unnormalizedJoint worldWeight
  refine Finset.prod_congr rfl ?_
  intro ⟨i, hi⟩ _
  dsimp [compiledClauseFactorGraph, FactorGraph.restrictToScope]
  exact WeightedGroundClause.evalOnScope_eq_eval _ W

omit [DecidableEq ClauseId] in
/-- VE-style constraint event for the compiled clause factor graph. -/
lemma weightOfConstraints_eq_worldWeight_sum
    [Fintype Atom]
    (M : GroundMLN Atom ClauseId)
    (support : Finset ClauseId)
    (constraints : ConstraintQuery Atom) :
    VariableElimination.weightOfConstraints (fg := compiledClauseFactorGraph M support) constraints =
      ∑ W : AtomValuation Atom,
        if satisfiesConstraints W constraints then M.worldWeight support W else 0 := by
  classical
  have hpot : ∀ W : AtomValuation Atom,
      (VariableElimination.combineAll
        (fg := compiledClauseFactorGraph M support)
        (VariableElimination.factorsOfGraph (fg := compiledClauseFactorGraph M support))).potential
        (VariableElimination.FactorGraph.fullAssign (fg := compiledClauseFactorGraph M support) W
          (VariableElimination.combineAll
            (fg := compiledClauseFactorGraph M support)
            (VariableElimination.factorsOfGraph (fg := compiledClauseFactorGraph M support))).scope) =
      M.worldWeight support W := by
    intro W
    have h := VariableElimination.combineAll_factorsOfGraph_potential_eq_unnormalizedJoint
      (fg := compiledClauseFactorGraph M support) (x := W)
    simpa [compiledClauseFactorGraph_unnormalizedJoint_eq_worldWeight] using h
  unfold VariableElimination.weightOfConstraints
  simp only [VariableElimination.weightOfConstraintsList, satisfiesConstraints]
  refine Finset.sum_congr rfl ?_
  intro W _
  -- Two `if` expressions with same Prop condition but different Decidable instances;
  -- split_ifs creates 4 cases, 2 contradictory.
  split_ifs
  · exact hpot W
  · contradiction
  · contradiction
  · rfl

omit [DecidableEq ClauseId] in
/-- The countable query mass for finite constraint queries agrees with VE constraint weight. -/
lemma weightOfConstraints_eq_queryMass
    [Fintype Atom]
    (M : GroundMLN Atom ClauseId)
    (support : Finset ClauseId)
    (constraints : ConstraintQuery Atom) :
    VariableElimination.weightOfConstraints (fg := compiledClauseFactorGraph M support) constraints =
      CountableMLNSemantics.queryMass
        (M.toCountableMLNSemantics (Query := ConstraintQuery Atom) support constraintQueryHolds)
        constraints := by
  classical
  rw [weightOfConstraints_eq_worldWeight_sum]
  unfold CountableMLNSemantics.queryMass constraintQueryHolds satisfiesConstraints
  rw [tsum_eq_sum (s := (Finset.univ : Finset (AtomValuation Atom)))
    (fun W hW => (hW (Finset.mem_univ W)).elim)]
  refine Finset.sum_congr rfl ?_
  intro W _
  -- Structure projections + Decidable instance mismatch
  simp only [toCountableMLNSemantics]
  split_ifs <;> rfl

omit [DecidableEq ClauseId] in
/-- The compiled clause factor-graph partition function agrees with total MLN mass. -/
lemma partitionFunction_eq_totalMass
    [Fintype Atom]
    (M : GroundMLN Atom ClauseId)
    (support : Finset ClauseId) :
    (compiledClauseFactorGraph M support).partitionFunction =
      CountableMLNSemantics.totalMass
        (M.toCountableMLNSemantics (Query := ConstraintQuery Atom) support constraintQueryHolds) := by
  classical
  -- Both sides are finite sums; connect them via the unnormalized joint theorem.
  unfold CountableMLNSemantics.totalMass
  rw [tsum_eq_sum (s := (Finset.univ : Finset (AtomValuation Atom)))
    (fun W hW => (hW (Finset.mem_univ W)).elim)]
  unfold FactorGraph.partitionFunction
  simp only [Fintype.piFinset_univ]
  refine Finset.sum_congr rfl ?_
  intro W _
  exact compiledClauseFactorGraph_unnormalizedJoint_eq_worldWeight M support W

end GroundMLN

end Mettapedia.Logic.MarkovLogicClauseFactorGraph
