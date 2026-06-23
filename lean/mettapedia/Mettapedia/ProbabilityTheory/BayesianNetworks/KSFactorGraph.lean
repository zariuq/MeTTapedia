import Mettapedia.ProbabilityTheory.BayesianNetworks.FactorGraph
import KnuthSkilling.Bridges.ValuationAlgebra

/-!
# KS‑Valued Factor Graphs (Bridge Wrapper)

This module provides a **small alias layer** that makes the K&S → valuation bridge
explicit for factor graphs.  It exposes end‑to‑end VE paths via `ksVE` and
`ksVE_correct`, without committing to probability normalization.
-/

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

open KnuthSkilling
open KnuthSkilling.Bridges.ValuationAlgebra

/-! ## Alias layer -/

-- The K&S → valuation bridge (`weightOfConstraintsKS`, `ksVE`, `Valuation`) is stated
-- over the standalone `KnuthSkilling` external's `_root_.ProbabilityTheory.BayesianNetworks`
-- types, NOT the local `Mettapedia.ProbabilityTheory.BayesianNetworks` ones.  Lean 4.31
-- resolves a bare `FactorGraph`/`Valuation` in this namespace to the local copies, so
-- this wrapper must name the external types with `_root_.`.
abbrev KSFactorGraphα (V : Type*) (α : Type*) := _root_.ProbabilityTheory.BayesianNetworks.FactorGraph V α

/-! ## End‑to‑end KS‑valued VE (via regrade) -/

noncomputable def ksWeightOfConstraints {V α : Type*} [LinearOrder α]
    {op : α → α → α}
    (rep : AdditiveOrderIsoRep α op)
    (fg : KSFactorGraphα V α)
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [DecidableEq V]
    [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [Fintype fg.factors] : ℝ :=
  weightOfConstraintsKS (rep := rep) (fg := fg) constraints

@[simp] theorem ksWeightOfConstraints_eq
    {V α : Type*} [LinearOrder α] {op : α → α → α}
    (rep : AdditiveOrderIsoRep α op)
    (fg : KSFactorGraphα V α)
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [DecidableEq V]
    [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [Fintype fg.factors] :
    ksWeightOfConstraints (rep := rep) (fg := fg) constraints =
      weightOfConstraintsKS (rep := rep) (fg := fg) constraints := by
  rfl

noncomputable def ksVE {V α : Type*} [LinearOrder α]
    {op : α → α → α}
    (rep : AdditiveOrderIsoRep α op)
    (fg : KSFactorGraphα V α) (order : List V)
    [Fintype V] [DecidableEq V]
    [∀ v, Fintype (fg.stateSpace v)]
    [Fintype fg.factors] :
    _root_.ProbabilityTheory.BayesianNetworks.Valuation V (fun v => fg.stateSpace v) ℝ :=
  Bridges.ValuationAlgebra.ksVE (rep := rep) (fg := fg) (order := order)

abbrev ksVE_correct {V α : Type*} [LinearOrder α]
    {op : α → α → α}
    (rep : AdditiveOrderIsoRep α op)
    (fg : KSFactorGraphα V α) (order : List V)
    [Fintype V] [DecidableEq V]
    [∀ v, Fintype (fg.stateSpace v)]
    [Fintype fg.factors] :=
  Bridges.ValuationAlgebra.ksVE_correct (rep := rep) (fg := fg) (order := order)

end Mettapedia.ProbabilityTheory.BayesianNetworks
