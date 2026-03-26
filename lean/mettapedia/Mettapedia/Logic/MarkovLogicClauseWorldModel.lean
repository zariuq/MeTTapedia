import Mettapedia.Logic.MarkovLogicClauseFactorGraph
import Mettapedia.ProbabilityTheory.BayesianNetworks.ValuationWorldModel

/-!
# Clause-Level MLN as a Valuation World Model

This module closes the semantic bridge from clause-native MLN semantics
to the canonical factorized world model (`ValuationWorldModel`):

- A ground MLN with finite clause support compiles to a factor graph.
- The factor graph's factor list is a `WMSource`.
- The singleton `WMState` induces a `BinaryWorldModel` instance.
- `queryStrength` on this WM state equals the MLN `queryProb`.

This routes through the real factorized WM instance (VE-backed evidence),
not the abstract `MassState` wrapper.
-/

namespace Mettapedia.Logic.MarkovLogicClauseWorldModel

open scoped ENNReal BigOperators
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicCountable
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.ProbabilityTheory.BayesianNetworks

variable {Atom ClauseId : Type*} [DecidableEq Atom] [Fintype Atom]

open GroundMLN

/-- The factor list for a compiled clause factor graph. -/
noncomputable def clauseWMSource
    (M : GroundMLN Atom ClauseId)
    (support : Finset ClauseId) :
    ValuationWorldModel.WMSource (compiledClauseFactorGraph M support) :=
  VariableElimination.factorsOfGraph (fg := compiledClauseFactorGraph M support)

/-- Singleton WM state: a single clause-factorized evidence source. -/
noncomputable def clauseWMState
    (M : GroundMLN Atom ClauseId)
    (support : Finset ClauseId) :
    ValuationWorldModel.WMState (compiledClauseFactorGraph M support) :=
  ({clauseWMSource M support} : Multiset _)

/-- The mass semantics induced by the clause-level MLN (via countable specialization). -/
noncomputable def clauseMassSemantics
    (M : GroundMLN Atom ClauseId)
    (support : Finset ClauseId) :
    MassSemantics (ConstraintQuery Atom) :=
  (M.toCountableMLNSemantics (Query := ConstraintQuery Atom) support constraintQueryHolds).toMassSemantics

/-- The `BinaryWorldModel` instance for clause WM state over constraint queries.

`ConstraintQuery Atom = List (Σ _ : Atom, Bool)` is definitionally equal to
`List (Σ v, (compiledClauseFactorGraph M support).stateSpace v)` since the compiled
factor graph sets `stateSpace _ := Bool`. This instance witnesses that unification. -/
noncomputable instance clauseWorldModel
    (M : GroundMLN Atom ClauseId)
    (support : Finset ClauseId) :
    BinaryWorldModel
      (ValuationWorldModel.WMState (compiledClauseFactorGraph M support))
      (ConstraintQuery Atom) :=
  have : ConstraintQuery Atom =
      List (Σ v, (compiledClauseFactorGraph M support).stateSpace v) := rfl
  this ▸ inferInstance

/-- The VE weight of the clause source equals the MLN query mass. -/
theorem clauseWM_weight_eq_queryMass
    (M : GroundMLN Atom ClauseId)
    (support : Finset ClauseId)
    (constraints : ConstraintQuery Atom) :
    ValuationWorldModel.weight (fg := compiledClauseFactorGraph M support)
      (W := clauseWMSource M support) constraints =
      (clauseMassSemantics M support).queryMass constraints := by
  classical
  unfold ValuationWorldModel.weight clauseWMSource clauseMassSemantics
  rw [← VariableElimination.weightOfConstraints_eq_list]
  exact weightOfConstraints_eq_queryMass M support constraints

/-- The total weight of the clause source equals the MLN total mass. -/
theorem clauseWM_total_eq_totalMass
    (M : GroundMLN Atom ClauseId)
    (support : Finset ClauseId) :
    ValuationWorldModel.total (fg := compiledClauseFactorGraph M support)
      (W := clauseWMSource M support) =
      (clauseMassSemantics M support).totalMass := by
  classical
  unfold ValuationWorldModel.total
  rw [clauseWM_weight_eq_queryMass]
  -- queryMass [] = totalMass: empty constraints are trivially satisfied
  unfold clauseMassSemantics
  simp only [CountableMLNSemantics.toMassSemantics]
  change CountableMLNSemantics.queryMass _ [] = CountableMLNSemantics.totalMass _
  unfold CountableMLNSemantics.queryMass CountableMLNSemantics.totalMass
  refine tsum_congr ?_
  intro w
  simp only [toCountableMLNSemantics]
  -- if (∀ c ∈ [], w c.1 = c.2) then worldWeight else 0 = worldWeight
  rw [if_pos]
  intro c hc; exact absurd hc List.not_mem_nil

/-- Source evidence from the clause WM matches the semantic mass evidence. -/
theorem clauseWM_sourceEvidence_eq_evidenceOfMasses
    (M : GroundMLN Atom ClauseId)
    (support : Finset ClauseId)
    (constraints : ConstraintQuery Atom) :
    ValuationWorldModel.sourceEvidence (fg := compiledClauseFactorGraph M support)
      (W := clauseWMSource M support) constraints =
      (clauseMassSemantics M support).evidenceOfMasses constraints := by
  unfold ValuationWorldModel.sourceEvidence MassSemantics.evidenceOfMasses
  rw [clauseWM_weight_eq_queryMass, clauseWM_total_eq_totalMass]

/-- BinaryEvidence from the singleton clause WM state matches the semantic mass evidence. -/
theorem clauseWM_evidence_eq_evidenceOfMasses
    (M : GroundMLN Atom ClauseId)
    (support : Finset ClauseId)
    (constraints : ConstraintQuery Atom) :
    BinaryWorldModel.evidence (clauseWMState M support) constraints =
      (clauseMassSemantics M support).evidenceOfMasses constraints := by
  show ValuationWorldModel.evidence
    (fg := compiledClauseFactorGraph M support)
    (clauseWMState M support) constraints = _
  unfold clauseWMState ValuationWorldModel.evidence
  simp [Multiset.map_singleton, Multiset.sum_singleton]
  exact clauseWM_sourceEvidence_eq_evidenceOfMasses M support constraints

/-- **Main theorem:** `queryStrength` on the clause WM state equals the MLN `queryProb`. -/
theorem clauseWM_queryStrength_eq_queryProb
    (M : GroundMLN Atom ClauseId)
    (support : Finset ClauseId)
    (q : ConstraintQuery Atom) :
    BinaryWorldModel.queryStrength (clauseWMState M support) q =
      (clauseMassSemantics M support).queryProb q :=
  queryStrength_eq_queryProb_of_evidence_eq
    (clauseWMState M support)
    (clauseMassSemantics M support)
    (clauseWM_evidence_eq_evidenceOfMasses M support)
    q

end Mettapedia.Logic.MarkovLogicClauseWorldModel
