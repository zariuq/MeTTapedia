import Mathlib.Data.Real.Basic
import Mettapedia.ProbabilityTheory.BayesianNetworks.ValuationAlgebra
import Mettapedia.ProbabilityTheory.BayesianNetworks.FactorGraph
import Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination
import Mettapedia.ProbabilityTheory.BayesianNetworks.ValuationBridge
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Interfaces
import Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative.ScaledMultRep

/-!
# Knuth–Skilling → Valuation Algebra Bridge

This module provides a **minimal** bridge from K&S regraduations to the
valuation-algebra value scale.

Key design choices:
- We **do not** assume probability normalization (e.g. Θ(ident)=0).
- We only use the additive representation from Appendix A.
- The multiplicative (tensor) side is optional and kept as a separate helper.

This supports the “KS semialgebra” regime: a valuation scale on ℝ without
committing to Kolmogorov normalization or complements.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Bridges.ValuationAlgebra

section Additive

variable {α : Type*} [LinearOrder α] {op : α → α → α}

/-- Regraduation map from an additive K&S representation. -/
def regrade (rep : Mettapedia.ProbabilityTheory.KnuthSkilling.AdditiveOrderIsoRep α op) :
    α → ℝ :=
  match rep with
  | ⟨Θ, _⟩ => fun x => Θ x

@[simp] theorem regrade_op
    (rep : Mettapedia.ProbabilityTheory.KnuthSkilling.AdditiveOrderIsoRep α op)
    (x y : α) :
    regrade rep (op x y) = regrade rep x + regrade rep y :=
  by
    cases rep with
    | mk Θ map_op =>
      simp [regrade, map_op]

/-- Regrade a valuation into ℝ using the K&S additive representation.

This is a **scale change**, not probability normalization. -/
def regradeValuation {V : Type*} {β : V → Type*}
    (rep : Mettapedia.ProbabilityTheory.KnuthSkilling.AdditiveOrderIsoRep α op)
    (φ : Mettapedia.ProbabilityTheory.BayesianNetworks.Valuation V β α) :
    Mettapedia.ProbabilityTheory.BayesianNetworks.Valuation V β ℝ :=
  { scope := φ.scope
    val := fun x => regrade rep (φ.val x) }

end Additive

/-! ## Factor-graph regraduation -/

section FactorGraph

variable {α : Type*} [LinearOrder α] {op : α → α → α}

def regradeFactorGraph {V : Type*}
    (rep : Mettapedia.ProbabilityTheory.KnuthSkilling.AdditiveOrderIsoRep α op)
    (fg : Mettapedia.ProbabilityTheory.BayesianNetworks.FactorGraph V α) :
    Mettapedia.ProbabilityTheory.BayesianNetworks.FactorGraph V ℝ :=
  { stateSpace := fg.stateSpace
    factors := fg.factors
    scope := fg.scope
    potential := fun f x => regrade rep (fg.potential f x) }

noncomputable def weightOfConstraintsKS {V : Type*}
    (rep : Mettapedia.ProbabilityTheory.KnuthSkilling.AdditiveOrderIsoRep α op)
    (fg : Mettapedia.ProbabilityTheory.BayesianNetworks.FactorGraph V α)
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [DecidableEq V]
    [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [Fintype fg.factors] : ℝ :=
  by
    classical
    let fg' := regradeFactorGraph (rep := rep) fg
    have instState : ∀ v, Fintype (fg'.stateSpace v) := by
      intro v
      simpa [fg', regradeFactorGraph] using (inferInstance : Fintype (fg.stateSpace v))
    have instDecEq : ∀ v, DecidableEq (fg'.stateSpace v) := by
      intro v
      simpa [fg', regradeFactorGraph] using (inferInstance : DecidableEq (fg.stateSpace v))
    have instFactors : Fintype fg'.factors := by
      simpa [fg', regradeFactorGraph] using (inferInstance : Fintype fg.factors)
    letI : ∀ v, Fintype (fg'.stateSpace v) := instState
    letI : ∀ v, DecidableEq (fg'.stateSpace v) := instDecEq
    letI : Fintype fg'.factors := instFactors
    exact
      Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination.weightOfConstraints
        (fg := fg') constraints

end FactorGraph

/-! ## VE correctness for regraded KS factors (via valuation bridge) -/

section VEBridge

open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.ValuationBridge

variable {α : Type*} [LinearOrder α] {op : α → α → α}

variable {V : Type*} [DecidableEq V]
variable (rep : Mettapedia.ProbabilityTheory.KnuthSkilling.AdditiveOrderIsoRep α op)
variable (fg : FactorGraph V α)

local instance regrade_state_fintype [∀ v, Fintype (fg.stateSpace v)] :
    ∀ v, Fintype ((regradeFactorGraph (rep := rep) fg).stateSpace v) := by
  intro v
  simpa [regradeFactorGraph] using (inferInstance : Fintype (fg.stateSpace v))

local instance regrade_factors_fintype [Fintype fg.factors] :
    Fintype (regradeFactorGraph (rep := rep) fg).factors := by
  simpa [regradeFactorGraph] using (inferInstance : Fintype fg.factors)

theorem ve_correct_regrade
    (order : List V)
    [Fintype V]
    [∀ v, Fintype (fg.stateSpace v)]
    [Fintype fg.factors] :
    toValuation (fg := regradeFactorGraph (rep := rep) fg)
        (VariableElimination.sumOutAll (fg := regradeFactorGraph (rep := rep) fg)
          (VariableElimination.combineAll (fg := regradeFactorGraph (rep := rep) fg)
            (VariableElimination.factorsOfGraph (fg := regradeFactorGraph (rep := rep) fg))) order) =
      combineAll (V := V) (β := fun v => fg.stateSpace v) (K := ℝ)
        (eliminateVars (V := V) (β := fun v => fg.stateSpace v) (K := ℝ)
          (toValuations (fg := regradeFactorGraph (rep := rep) fg)
            (VariableElimination.factorsOfGraph (fg := regradeFactorGraph (rep := rep) fg))) order) := by
  classical
  let fg' := regradeFactorGraph (rep := rep) fg
  -- Reuse the valuation-bridge VE correctness lemma on the regraded factor graph.
  simpa using
    (sumOutAll_combineAll_via_valuation
      (fg := fg')
      (fs := VariableElimination.factorsOfGraph (fg := fg')) (order := order))

/-! ## Direct KS-valued VE instantiation -/

noncomputable def ksVE
    (order : List V)
    [Fintype V]
    [∀ v, Fintype (fg.stateSpace v)]
    [Fintype fg.factors] :
    Mettapedia.ProbabilityTheory.BayesianNetworks.Valuation V (fun v => fg.stateSpace v) ℝ :=
  combineAll (V := V) (β := fun v => fg.stateSpace v) (K := ℝ)
    (eliminateVars (V := V) (β := fun v => fg.stateSpace v) (K := ℝ)
      (toValuations (fg := regradeFactorGraph (rep := rep) fg)
        (VariableElimination.factorsOfGraph (fg := regradeFactorGraph (rep := rep) fg))) order)

theorem ksVE_correct
    (order : List V)
    [Fintype V]
    [∀ v, Fintype (fg.stateSpace v)]
    [Fintype fg.factors] :
    toValuation (fg := regradeFactorGraph (rep := rep) fg)
        (VariableElimination.sumOutAll (fg := regradeFactorGraph (rep := rep) fg)
          (VariableElimination.combineAll (fg := regradeFactorGraph (rep := rep) fg)
            (VariableElimination.factorsOfGraph (fg := regradeFactorGraph (rep := rep) fg))) order) =
      ksVE (rep := rep) (fg := fg) (order := order) := by
  simpa [ksVE] using (ve_correct_regrade (rep := rep) (fg := fg) order)

end VEBridge

/-! ## Optional: scaled multiplication on the regraded scale

If a tensor operation admits a `ScaledMultRep`, the induced multiplication on ℝ
is scaled by the global constant `C`. This is the multiplicative counterpart of
`regrade` when interpreting tensor as a valuation-algebra `Mul`.
-/

section Multiplicative

open Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative

/-- Scaled multiplication on ℝ induced by a K&S tensor representation. -/
noncomputable def scaledMul {tensor : PosReal → PosReal → PosReal}
    (h : ScaledMultRep tensor) (x y : ℝ) : ℝ :=
  (x * y) / h.C

end Multiplicative

end Mettapedia.ProbabilityTheory.KnuthSkilling.Bridges.ValuationAlgebra
