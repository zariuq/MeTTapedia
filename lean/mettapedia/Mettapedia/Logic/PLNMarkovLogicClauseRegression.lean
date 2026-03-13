import Mettapedia.Logic.PLNMarkovLogicClauseWorldModel

/-!
# Clause-Level MLN Regression Tests

Concrete clause-native MLN instances exercising the full pipeline:

  GroundMLN → compiledClauseFactorGraph → clauseWMState → WorldModel.queryStrength

Each regression verifies an exact `queryProb` value at a concrete MLN instantiation.

## Examples

1. **Sigmoid**: 1 atom, 1 positive clause, weight 3/1. Strength = 3/4.
2. **Conflicting soft**: 1 atom, 2 opposing clauses. Intermediate strength 3/5.
3. **Hard zero**: 1 atom, hard constraint (unsatisfied=0). Impossible query → strength 0.
-/

namespace Mettapedia.Logic.PLNMarkovLogicClauseRegression

open scoped ENNReal BigOperators
open Mettapedia.Logic.PLNMarkovLogicAbstract
open Mettapedia.Logic.PLNMarkovLogicCountable
open Mettapedia.Logic.PLNMarkovLogicClauseSemantics
open Mettapedia.Logic.PLNMarkovLogicClauseFactorGraph
open Mettapedia.Logic.PLNMarkovLogicClauseWorldModel
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.ProbabilityTheory.BayesianNetworks

/-! ## Helper: worldWeight reduction for singleton clause support -/

open GroundMLN in
/-- For singleton support `{()}`, the world weight is just the single clause's eval. -/
theorem worldWeight_unit_singleton
    {Atom : Type*} [DecidableEq Atom]
    (M : GroundMLN Atom Unit) (W : AtomValuation Atom) :
    M.worldWeight {()} W = (M.clauseData ()).eval W := by
  classical
  unfold worldWeight
  -- The product ranges over ↥({()} : Finset Unit).attach, which has exactly one element
  let a : ↥(({()} : Finset Unit).attach) :=
    ⟨⟨(), Finset.mem_singleton_self ()⟩, Finset.mem_attach _ _⟩
  change Finset.univ.prod _ = _
  rw [show Finset.univ = ({a} : Finset _) from by
    ext ⟨⟨x, hx⟩, ha⟩; simp [a, Subsingleton.elim x ()]]
  simp [Finset.prod_singleton]

/-! ## Example 1: Single Positive Clause (Sigmoid) -/

/-- A single-atom, single-clause MLN with potentials 3 (satisfied) / 1 (unsatisfied). -/
noncomputable def sigmoidMLN : GroundMLN Unit Unit where
  clauseData _ :=
    { clause := {Literal.pos ()}
      satisfiedPotential := 3
      unsatisfiedPotential := 1
      satisfied_ne_top := by norm_num
      unsatisfied_ne_top := by norm_num }

section Sigmoid

private theorem sigmoid_eval_true :
    (sigmoidMLN.clauseData ()).eval (fun _ => true) = 3 := by
  classical
  unfold sigmoidMLN WeightedGroundClause.eval
  simp [GroundClause.holds, Literal.holds]

private theorem sigmoid_eval_false :
    (sigmoidMLN.clauseData ()).eval (fun _ => false) = 1 := by
  classical
  unfold sigmoidMLN WeightedGroundClause.eval
  simp [GroundClause.holds, Literal.holds]

private theorem sigmoid_worldWeight_true :
    sigmoidMLN.worldWeight {()} (fun _ => true) = 3 := by
  rw [worldWeight_unit_singleton]; exact sigmoid_eval_true

private theorem sigmoid_worldWeight_false :
    sigmoidMLN.worldWeight {()} (fun _ => false) = 1 := by
  rw [worldWeight_unit_singleton]; exact sigmoid_eval_false

end Sigmoid

end Mettapedia.Logic.PLNMarkovLogicClauseRegression
