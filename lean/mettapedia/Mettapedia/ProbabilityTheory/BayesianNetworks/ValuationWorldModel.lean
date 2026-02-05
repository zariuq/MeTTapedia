import Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination

/-!
# Canonical Semantic WM: Factorization + Marginalization

This module records the **semantic world-model** core as a factorized valuation:

* The WM state is an explicit **factor list**.
* Revision = add factors (at the state level).
* Queries are answered by **exact VE** on that factorization.

This is the canonical “WM = factorized valuation + marginalization” form,
independent of any PLN rule heuristics.
-/

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

open scoped Classical BigOperators

namespace ValuationWorldModel

variable {V K : Type*} [DecidableEq V]
variable {fg : FactorGraph V K}

/-- A semantic WM state is just a factorization (explicit factor list). -/
def WMState (fg : FactorGraph V K) : Type _ :=
  List (VariableElimination.Factor (fg := fg))

/-- Exact unnormalized weight for a constraint set from a WM factorization. -/
noncomputable def weight
    (W : WMState fg)
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [CommSemiring K] : K :=
  VariableElimination.weightOfConstraintsList (fg := fg) W constraints

/-- Total unnormalized weight (partition function of the WM state). -/
noncomputable def total
    (W : WMState fg)
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [CommSemiring K] : K :=
  weight (fg := fg) (W := W) []

end ValuationWorldModel

end Mettapedia.ProbabilityTheory.BayesianNetworks
