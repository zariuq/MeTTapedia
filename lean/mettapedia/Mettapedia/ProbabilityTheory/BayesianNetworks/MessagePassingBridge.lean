import Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassingLiterature
import Mettapedia.ProbabilityTheory.BayesianNetworks.ValuationBridge

/-!
# Local Bridge from BP Messages to the VE / Valuation Spine

This module packages the first **honest** bridge points between the abstract BP
equations and the existing exact-inference stack:

* unary-factor updates collapse to a local potential evaluation;
* singleton-other-scope ("pairwise leaf") updates collapse to a one-variable
  elimination sum;
* factor beliefs with unit incoming messages are exactly the VE local factors.

These are the reusable local facts we need before stating a full tree-exactness
theorem.
-/

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

namespace MessagePassing

variable {V K : Type*} [DecidableEq V]

section LocalBridge

variable {fg : FactorGraph V K}

/-- Unary local BP update: if a factor has no other variables besides `v`,
the factor-to-variable message is just that factor's potential at `x_v`. -/
theorem unaryFactor_localPotential_bridge
    [CommSemiring K] [∀ v, Fintype (fg.stateSpace v)]
    (μ : VarToFactorMsg fg) (f : fg.factors) (v : V) (hv : v ∈ fg.scope f)
    (hEmpty : (fg.scope f).erase v = ∅) :
    factorToVarUpdate (fg := fg) μ f v hv =
      fun x_v =>
        (VariableElimination.Factor.ofGraph (fg := fg) f).potential
          (VariableElimination.Factor.extend
            (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) f)
            v hv
            (emptyOtherScopeAssign (fg := fg) f v hEmpty)
            x_v) := by
  simpa [VariableElimination.Factor.ofGraph] using
    factorToVarUpdate_eq_potential_of_otherScopeEmpty
      (fg := fg) (μ := μ) (f := f) (v := v) hv hEmpty

/-- Pairwise leaf BP update: if `scope(f) \\ {v} = {u}`, then the
factor-to-variable message is exactly a one-variable elimination sum. -/
theorem pairwiseLeaf_localElimination_bridge
    [CommSemiring K] [∀ v, Fintype (fg.stateSpace v)]
    (μ : VarToFactorMsg fg) (f : fg.factors) (v u : V) (hv : v ∈ fg.scope f)
    (hSingle : (fg.scope f).erase v = {u}) :
    factorToVarUpdate (fg := fg) μ f v hv =
      fun x_v =>
        ∑ x_u : fg.stateSpace u,
          (VariableElimination.Factor.ofGraph (fg := fg) f).potential
            (VariableElimination.Factor.extend
              (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) f)
              v hv
              (singletonOtherScopeAssign (fg := fg) f v u hSingle x_u)
              x_v) *
            μ u f x_u := by
  simpa [VariableElimination.Factor.ofGraph] using
    factorToVarUpdate_eq_sum_of_otherScopeSingleton
      (fg := fg) (μ := μ) (f := f) (v := v) (u := u) hv hSingle

omit [DecidableEq V] in
/-- Unit-incoming factor beliefs are literally the concrete VE local factors. -/
theorem factorBelief_unit_messages_bridge
    [CommMonoid K] (f : fg.factors) :
    factorBelief (fg := fg) (unitVarToFactor (fg := fg)) f =
      (VariableElimination.Factor.ofGraph (fg := fg) f).potential :=
  factorBelief_unitVarToFactor_eq_ofGraph (fg := fg) f

end LocalBridge

end MessagePassing

end Mettapedia.ProbabilityTheory.BayesianNetworks
