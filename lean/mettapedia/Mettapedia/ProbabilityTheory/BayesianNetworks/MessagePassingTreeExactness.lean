import Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassingBeliefExactness

/-!
# Tree-Exactness Mini-Family for Abstract Belief Propagation

This module collects the first coherent family of exactness theorems for small
tree fragments:

* fork-shaped variable beliefs fed by leaf factors,
* pairwise factor beliefs fed by leaf factors,
* variable beliefs fed by reusable two-factor subtrees,
* factor beliefs fed by reusable two-factor subtrees.

The purpose is not new mathematics, but a cleaner public shape for the current
exactness milestone.
-/

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

namespace MessagePassing.TreeExactness

variable {V K : Type*} [DecidableEq V]
variable {fg : FactorGraph V K}

private theorem variableBelief_normalized_of_exact
    {fgp : FactorGraph V ENNReal}
    [Fintype fgp.factors] [DecidableEq fgp.factors]
    [∀ v, Fintype (fgp.stateSpace v)]
    (μ : FactorToVarMsg fgp) (v : V)
    (φ : VariableElimination.Factor (fg := fgp))
    (hExact : ∀ x : fgp.FullConfig,
      variableBelief (fg := fgp) μ v (x v) =
        (VariableElimination.Factor.toValuation (φ := φ)).val x) :
    ∀ x : fgp.FullConfig,
      let z :=
        ∑ val : fgp.stateSpace v,
          (VariableElimination.Factor.toValuation (φ := φ)).val
            (Mettapedia.ProbabilityTheory.BayesianNetworks.update
              (V := V) (β := fun u => fgp.stateSpace u) x v val)
      (if (∑ val : fgp.stateSpace v, variableBelief (fg := fgp) μ v val) = 0 then
        0
      else
        variableBelief (fg := fgp) μ v (x v) /
          (∑ val : fgp.stateSpace v, variableBelief (fg := fgp) μ v val)) =
      (if z = 0 then
        0
      else
        (VariableElimination.Factor.toValuation (φ := φ)).val x / z) := by
  intro x
  have hNum :
      variableBelief (fg := fgp) μ v (x v) =
        (VariableElimination.Factor.toValuation (φ := φ)).val x := hExact x
  have hPoint :
      ∀ val : fgp.stateSpace v,
        variableBelief (fg := fgp) μ v val =
          (VariableElimination.Factor.toValuation (φ := φ)).val
            (Mettapedia.ProbabilityTheory.BayesianNetworks.update
              (V := V) (β := fun u => fgp.stateSpace u) x v val) := by
    intro val
    simpa [Mettapedia.ProbabilityTheory.BayesianNetworks.update] using
      hExact
        (Mettapedia.ProbabilityTheory.BayesianNetworks.update
          (V := V) (β := fun u => fgp.stateSpace u) x v val)
  have hDen :
      (∑ val : fgp.stateSpace v, variableBelief (fg := fgp) μ v val) =
        ∑ val : fgp.stateSpace v,
          (VariableElimination.Factor.toValuation (φ := φ)).val
            (Mettapedia.ProbabilityTheory.BayesianNetworks.update
              (V := V) (β := fun u => fgp.stateSpace u) x v val) := by
    refine Finset.sum_congr rfl ?_
    intro val _
    exact hPoint val
  simp [hNum, hDen]

private theorem factorBelief_normalized_of_exact
    {fgp : FactorGraph V ENNReal}
    [Fintype fgp.factors] [DecidableEq fgp.factors]
    [∀ v, Fintype (fgp.stateSpace v)] [∀ v, Nonempty (fgp.stateSpace v)]
    (μ : VarToFactorMsg fgp) (h : fgp.factors)
    (φ : VariableElimination.Factor (fg := fgp))
    (hExact : ∀ x : fgp.FullConfig,
      factorBelief (fg := fgp) μ h (fgp.restrictToScope h x) =
        (VariableElimination.Factor.toValuation (φ := φ)).val x) :
    ∀ x : fgp.FullConfig,
      let exactAt := Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassing.localFactorValue
        (fg := fgp) h φ
      let z :=
        ∑ a : VariableElimination.FactorGraph.Assign (fg := fgp) (fgp.scope h), exactAt a
      (if (∑ a : VariableElimination.FactorGraph.Assign (fg := fgp) (fgp.scope h),
            factorBelief (fg := fgp) μ h a) = 0 then
        0
      else
        factorBelief (fg := fgp) μ h (fgp.restrictToScope h x) /
          (∑ a : VariableElimination.FactorGraph.Assign (fg := fgp) (fgp.scope h),
            factorBelief (fg := fgp) μ h a)) =
      (if z = 0 then
        0
      else
        exactAt (fgp.restrictToScope h x) / z) := by
  intro x
  have hPoint :
      ∀ a : VariableElimination.FactorGraph.Assign (fg := fgp) (fgp.scope h),
        factorBelief (fg := fgp) μ h a =
          Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassing.localFactorValue
            (fg := fgp) h φ a := by
    intro a
    let xa := extendScopeAssign
      (fg := fgp) h
      (Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassing.arbitraryFullConfig
        (fg := fgp)) a
    simpa [Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassing.localFactorValue,
      Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassing.arbitraryFullConfig,
      xa, restrictToScope_extendScopeAssign] using
      hExact xa
  have hNum :
      factorBelief (fg := fgp) μ h (fgp.restrictToScope h x) =
        Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassing.localFactorValue
          (fg := fgp) h φ (fgp.restrictToScope h x) := by
    exact hPoint (fgp.restrictToScope h x)
  have hDen :
      (∑ a : VariableElimination.FactorGraph.Assign (fg := fgp) (fgp.scope h),
          factorBelief (fg := fgp) μ h a) =
        ∑ a : VariableElimination.FactorGraph.Assign (fg := fgp) (fgp.scope h),
          Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassing.localFactorValue
            (fg := fgp) h φ a := by
    refine Finset.sum_congr rfl ?_
    intro a _
    exact hPoint a
  simp [hNum, hDen,
    Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassing.localFactorValue]

theorem leafFork_variableBelief_exact
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (f g : fg.factors) (u v w : V)
    (hvf : v ∈ fg.scope f) (hLeafF : (fg.scope f).erase v = {u})
    (hvg : v ∈ fg.scope g) (hLeafG : (fg.scope g).erase v = {w})
    (hfg : f ≠ g)
    (hNbrs : FactorGraph.variableNeighborsFinset fg v = {f, g}) :
    ∀ x : fg.FullConfig,
      variableBelief
        (fg := fg)
        ((runSyncRounds (fg := fg) 1 (initState (fg := fg))).factorToVar)
        v
        (x v) =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.mul (fg := fg)
          (leafEliminatedFactor (fg := fg) f u)
          (leafEliminatedFactor (fg := fg) g w))).val x :=
  twoLeaf_variableBelief_exact
    (fg := fg) (f := f) (g := g) (u := u) (v := v) (w := w)
    hvf hLeafF hvg hLeafG hfg hNbrs

theorem leafFork_variableBelief_exact_incident
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (f g : fg.factors) (u v w : V)
    (hvf : v ∈ fg.scope f) (hLeafF : (fg.scope f).erase v = {u})
    (hvg : v ∈ fg.scope g) (hLeafG : (fg.scope g).erase v = {w})
    (hfg : f ≠ g)
    (hNbrs : FactorGraph.variableNeighborsFinset fg v = {f, g}) :
    ∀ x : fg.FullConfig,
      variableBelief
        (fg := fg)
        ((IncidentMessageState.toTotal (fg := fg)
          (runSyncRoundsIncident (fg := fg) 1 (initIncidentState (fg := fg)))).factorToVar)
        v
        (x v) =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.mul (fg := fg)
          (leafEliminatedFactor (fg := fg) f u)
          (leafEliminatedFactor (fg := fg) g w))).val x := by
  intro x
  have hFactor :
      (IncidentMessageState.toTotal (fg := fg)
        (runSyncRoundsIncident (fg := fg) 1 (initIncidentState (fg := fg)))).factorToVar =
      (runSyncRounds (fg := fg) 1 (initState (fg := fg))).factorToVar := by
    have hState :=
      congrArg MessageState.factorToVar
        (toTotal_runSyncRoundsIncident_eq_runSyncRounds_toTotal
          (fg := fg) 1 (initIncidentState (fg := fg)))
    rw [initIncidentState_toTotal] at hState
    exact hState
  simpa [hFactor] using
    leafFork_variableBelief_exact
      (fg := fg) (f := f) (g := g) (u := u) (v := v) (w := w)
      hvf hLeafF hvg hLeafG hfg hNbrs x

theorem twoLeaf_factorBelief_exact
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (f g h : fg.factors) (u w v z : V)
    (hwf : w ∈ fg.scope f) (hLeafF : (fg.scope f).erase w = {u})
    (hvg : v ∈ fg.scope g) (hPairG : (fg.scope g).erase v = {w})
    (hvh : v ∈ fg.scope h) (hLeafH : (fg.scope h).erase v = {z})
    (hfg : f ≠ g) (hgh : h ≠ g)
    (hNbrsW : FactorGraph.variableNeighborsFinset fg w = {f, g})
    (hNbrsV : FactorGraph.variableNeighborsFinset fg v = {h, g}) :
    ∀ x : fg.FullConfig,
      factorBelief
        (fg := fg)
        ((runSyncRounds (fg := fg) 2 (initState (fg := fg))).varToFactor)
        g
        (fg.restrictToScope g x) =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.mul (fg := fg)
          (VariableElimination.Factor.mul (fg := fg)
            (VariableElimination.Factor.ofGraph (fg := fg) g)
            (leafEliminatedFactor (fg := fg) f u))
          (leafEliminatedFactor (fg := fg) h z))).val x :=
  twoSidedLeaf_factorBelief_exact
    (fg := fg) (f := f) (g := g) (h := h) (u := u) (w := w) (v := v) (z := z)
    hwf hLeafF hvg hPairG hvh hLeafH hfg hgh hNbrsW hNbrsV

theorem twoLeaf_factorBelief_exact_incident
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (f g h : fg.factors) (u w v z : V)
    (hwf : w ∈ fg.scope f) (hLeafF : (fg.scope f).erase w = {u})
    (hvg : v ∈ fg.scope g) (hPairG : (fg.scope g).erase v = {w})
    (hvh : v ∈ fg.scope h) (hLeafH : (fg.scope h).erase v = {z})
    (hfg : f ≠ g) (hgh : h ≠ g)
    (hNbrsW : FactorGraph.variableNeighborsFinset fg w = {f, g})
    (hNbrsV : FactorGraph.variableNeighborsFinset fg v = {h, g}) :
    ∀ x : fg.FullConfig,
      factorBelief
        (fg := fg)
        ((IncidentMessageState.toTotal (fg := fg)
          (runSyncRoundsIncident (fg := fg) 2 (initIncidentState (fg := fg)))).varToFactor)
        g
        (fg.restrictToScope g x) =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.mul (fg := fg)
          (VariableElimination.Factor.mul (fg := fg)
            (VariableElimination.Factor.ofGraph (fg := fg) g)
            (leafEliminatedFactor (fg := fg) f u))
          (leafEliminatedFactor (fg := fg) h z))).val x := by
  intro x
  have hVar :
      (IncidentMessageState.toTotal (fg := fg)
        (runSyncRoundsIncident (fg := fg) 2 (initIncidentState (fg := fg)))).varToFactor =
      (runSyncRounds (fg := fg) 2 (initState (fg := fg))).varToFactor := by
    have hState :=
      congrArg MessageState.varToFactor
        (toTotal_runSyncRoundsIncident_eq_runSyncRounds_toTotal
          (fg := fg) 2 (initIncidentState (fg := fg)))
    rw [initIncidentState_toTotal] at hState
    exact hState
  simpa [hVar] using
    twoLeaf_factorBelief_exact
      (fg := fg) (f := f) (g := g) (h := h) (u := u) (w := w) (v := v) (z := z)
      hwf hLeafF hvg hPairG hvh hLeafH hfg hgh hNbrsW hNbrsV x

theorem twoSubtree_variableBelief_exact
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (f g h j : fg.factors) (u w v y z : V)
    (hwf : w ∈ fg.scope f) (hLeafF : (fg.scope f).erase w = {u})
    (hvg : v ∈ fg.scope g) (hLeafG : (fg.scope g).erase v = {w})
    (hzh : z ∈ fg.scope h) (hLeafH : (fg.scope h).erase z = {y})
    (hvj : v ∈ fg.scope j) (hLeafJ : (fg.scope j).erase v = {z})
    (hfg : f ≠ g) (hhj : h ≠ j) (hgj : g ≠ j)
    (hNbrsW : FactorGraph.variableNeighborsFinset fg w = {f, g})
    (hNbrsZ : FactorGraph.variableNeighborsFinset fg z = {h, j})
    (hNbrsV : FactorGraph.variableNeighborsFinset fg v = {g, j}) :
    ∀ x : fg.FullConfig,
      variableBelief
        (fg := fg)
        ((runSyncRounds (fg := fg) 3 (initState (fg := fg))).factorToVar)
        v
        (x v) =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.mul (fg := fg)
          (VariableElimination.Factor.sumOut
            (φ := twoFactorSubtreeFactor (fg := fg) f g u) w)
          (VariableElimination.Factor.sumOut
            (φ := twoFactorSubtreeFactor (fg := fg) h j y) z))).val x :=
  Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassing.twoSubtree_variableBelief_exact
    (fg := fg) (f := f) (g := g) (h := h) (j := j)
    (u := u) (w := w) (v := v) (y := y) (z := z)
    hwf hLeafF hvg hLeafG hzh hLeafH hvj hLeafJ hfg hhj hgj hNbrsW hNbrsZ hNbrsV

theorem twoSubtree_variableBelief_exact_incident
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (f g h j : fg.factors) (u w v y z : V)
    (hwf : w ∈ fg.scope f) (hLeafF : (fg.scope f).erase w = {u})
    (hvg : v ∈ fg.scope g) (hLeafG : (fg.scope g).erase v = {w})
    (hzh : z ∈ fg.scope h) (hLeafH : (fg.scope h).erase z = {y})
    (hvj : v ∈ fg.scope j) (hLeafJ : (fg.scope j).erase v = {z})
    (hfg : f ≠ g) (hhj : h ≠ j) (hgj : g ≠ j)
    (hNbrsW : FactorGraph.variableNeighborsFinset fg w = {f, g})
    (hNbrsZ : FactorGraph.variableNeighborsFinset fg z = {h, j})
    (hNbrsV : FactorGraph.variableNeighborsFinset fg v = {g, j}) :
    ∀ x : fg.FullConfig,
      variableBelief
        (fg := fg)
        ((IncidentMessageState.toTotal (fg := fg)
          (runSyncRoundsIncident (fg := fg) 3 (initIncidentState (fg := fg)))).factorToVar)
        v
        (x v) =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.mul (fg := fg)
          (VariableElimination.Factor.sumOut
            (φ := twoFactorSubtreeFactor (fg := fg) f g u) w)
          (VariableElimination.Factor.sumOut
            (φ := twoFactorSubtreeFactor (fg := fg) h j y) z))).val x := by
  intro x
  have hFactor :
      (IncidentMessageState.toTotal (fg := fg)
        (runSyncRoundsIncident (fg := fg) 3 (initIncidentState (fg := fg)))).factorToVar =
      (runSyncRounds (fg := fg) 3 (initState (fg := fg))).factorToVar := by
    have hState :=
      congrArg MessageState.factorToVar
        (toTotal_runSyncRoundsIncident_eq_runSyncRounds_toTotal
          (fg := fg) 3 (initIncidentState (fg := fg)))
    rw [initIncidentState_toTotal] at hState
    exact hState
  simpa [hFactor] using
    twoSubtree_variableBelief_exact
      (fg := fg) (f := f) (g := g) (h := h) (j := j)
      (u := u) (w := w) (v := v) (y := y) (z := z)
      hwf hLeafF hvg hLeafG hzh hLeafH hvj hLeafJ hfg hhj hgj hNbrsW hNbrsZ hNbrsV x

section NormalizedIncident

variable {fg : FactorGraph V ENNReal}

theorem twoSubtree_variableBelief_exact_normalized_incident
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)]
    (f g h j : fg.factors) (u w v y z : V)
    (hwf : w ∈ fg.scope f) (hLeafF : (fg.scope f).erase w = {u})
    (hvg : v ∈ fg.scope g) (hLeafG : (fg.scope g).erase v = {w})
    (hzh : z ∈ fg.scope h) (hLeafH : (fg.scope h).erase z = {y})
    (hvj : v ∈ fg.scope j) (hLeafJ : (fg.scope j).erase v = {z})
    (hfg : f ≠ g) (hhj : h ≠ j) (hgj : g ≠ j)
    (hNbrsW : FactorGraph.variableNeighborsFinset fg w = {f, g})
    (hNbrsZ : FactorGraph.variableNeighborsFinset fg z = {h, j})
    (hNbrsV : FactorGraph.variableNeighborsFinset fg v = {g, j}) :
    ∀ x : fg.FullConfig,
      let μ := (IncidentMessageState.toTotal (fg := fg)
        (runSyncRoundsIncident (fg := fg) 3 (initIncidentState (fg := fg)))).factorToVar
      let φ := VariableElimination.Factor.mul (fg := fg)
        (VariableElimination.Factor.sumOut
          (φ := twoFactorSubtreeFactor (fg := fg) f g u) w)
        (VariableElimination.Factor.sumOut
          (φ := twoFactorSubtreeFactor (fg := fg) h j y) z)
      let zsum :=
        ∑ val : fg.stateSpace v,
          (VariableElimination.Factor.toValuation (φ := φ)).val
            (Mettapedia.ProbabilityTheory.BayesianNetworks.update
              (V := V) (β := fun u => fg.stateSpace u) x v val)
      (if (∑ val : fg.stateSpace v, variableBelief (fg := fg) μ v val) = 0 then
        0
      else
        variableBelief (fg := fg) μ v (x v) /
          (∑ val : fg.stateSpace v, variableBelief (fg := fg) μ v val)) =
      (if zsum = 0 then
        0
      else
        (VariableElimination.Factor.toValuation (φ := φ)).val x / zsum) := by
  intro x
  exact variableBelief_normalized_of_exact
    (μ := (IncidentMessageState.toTotal (fg := fg)
      (runSyncRoundsIncident (fg := fg) 3 (initIncidentState (fg := fg)))).factorToVar)
    (v := v)
    (φ := VariableElimination.Factor.mul (fg := fg)
      (VariableElimination.Factor.sumOut
        (φ := twoFactorSubtreeFactor (fg := fg) f g u) w)
      (VariableElimination.Factor.sumOut
        (φ := twoFactorSubtreeFactor (fg := fg) h j y) z))
    (hExact := by
      intro x
      exact twoSubtree_variableBelief_exact_incident
        (fg := fg) (f := f) (g := g) (h := h) (j := j)
        (u := u) (w := w) (v := v) (y := y) (z := z)
        hwf hLeafF hvg hLeafG hzh hLeafH hvj hLeafJ hfg hhj hgj hNbrsW hNbrsZ hNbrsV x)
    x

end NormalizedIncident

theorem twoSubtree_factorBelief_exact
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (f g k p q : fg.factors) (u w v y t z : V)
    (hwf : w ∈ fg.scope f) (hLeafF : (fg.scope f).erase w = {u})
    (hvg : v ∈ fg.scope g) (hLeafG : (fg.scope g).erase v = {w})
    (hvk : v ∈ fg.scope k)
    (htp : t ∈ fg.scope p) (hLeafP : (fg.scope p).erase t = {y})
    (hzq : z ∈ fg.scope q) (hLeafQ : (fg.scope q).erase z = {t})
    (hzk : z ∈ fg.scope k) (hPairK : (fg.scope k).erase z = {v})
    (hfg : f ≠ g) (hgk : g ≠ k) (hpq : p ≠ q) (hqk : q ≠ k)
    (hNbrsW : FactorGraph.variableNeighborsFinset fg w = {f, g})
    (hNbrsV : FactorGraph.variableNeighborsFinset fg v = {g, k})
    (hNbrsT : FactorGraph.variableNeighborsFinset fg t = {p, q})
    (hNbrsZ : FactorGraph.variableNeighborsFinset fg z = {q, k}) :
    ∀ x : fg.FullConfig,
      factorBelief
        (fg := fg)
        ((runSyncRounds (fg := fg) 4 (initState (fg := fg))).varToFactor)
        k
        (fg.restrictToScope k x) =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.mul (fg := fg)
          (VariableElimination.Factor.mul (fg := fg)
            (VariableElimination.Factor.ofGraph (fg := fg) k)
            (VariableElimination.Factor.sumOut
              (φ := twoFactorSubtreeFactor (fg := fg) f g u) w))
          (VariableElimination.Factor.sumOut
            (φ := twoFactorSubtreeFactor (fg := fg) p q y) t))).val x :=
  Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassing.twoSubtree_factorBelief_exact
    (fg := fg) (f := f) (g := g) (k := k) (p := p) (q := q)
    (u := u) (w := w) (v := v) (y := y) (t := t) (z := z)
    hwf hLeafF hvg hLeafG hvk htp hLeafP hzq hLeafQ hzk hPairK
    hfg hgk hpq hqk hNbrsW hNbrsV hNbrsT hNbrsZ

theorem twoSubtree_factorBelief_exact_incident
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (f g k p q : fg.factors) (u w v y t z : V)
    (hwf : w ∈ fg.scope f) (hLeafF : (fg.scope f).erase w = {u})
    (hvg : v ∈ fg.scope g) (hLeafG : (fg.scope g).erase v = {w})
    (hvk : v ∈ fg.scope k)
    (htp : t ∈ fg.scope p) (hLeafP : (fg.scope p).erase t = {y})
    (hzq : z ∈ fg.scope q) (hLeafQ : (fg.scope q).erase z = {t})
    (hzk : z ∈ fg.scope k) (hPairK : (fg.scope k).erase z = {v})
    (hfg : f ≠ g) (hgk : g ≠ k) (hpq : p ≠ q) (hqk : q ≠ k)
    (hNbrsW : FactorGraph.variableNeighborsFinset fg w = {f, g})
    (hNbrsV : FactorGraph.variableNeighborsFinset fg v = {g, k})
    (hNbrsT : FactorGraph.variableNeighborsFinset fg t = {p, q})
    (hNbrsZ : FactorGraph.variableNeighborsFinset fg z = {q, k}) :
    ∀ x : fg.FullConfig,
      factorBelief
        (fg := fg)
        ((IncidentMessageState.toTotal (fg := fg)
          (runSyncRoundsIncident (fg := fg) 4 (initIncidentState (fg := fg)))).varToFactor)
        k
        (fg.restrictToScope k x) =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.mul (fg := fg)
          (VariableElimination.Factor.mul (fg := fg)
            (VariableElimination.Factor.ofGraph (fg := fg) k)
            (VariableElimination.Factor.sumOut
              (φ := twoFactorSubtreeFactor (fg := fg) f g u) w))
          (VariableElimination.Factor.sumOut
            (φ := twoFactorSubtreeFactor (fg := fg) p q y) t))).val x := by
  intro x
  have hVar :
      (IncidentMessageState.toTotal (fg := fg)
        (runSyncRoundsIncident (fg := fg) 4 (initIncidentState (fg := fg)))).varToFactor =
      (runSyncRounds (fg := fg) 4 (initState (fg := fg))).varToFactor := by
    have hState :=
      congrArg MessageState.varToFactor
        (toTotal_runSyncRoundsIncident_eq_runSyncRounds_toTotal
          (fg := fg) 4 (initIncidentState (fg := fg)))
    rw [initIncidentState_toTotal] at hState
    exact hState
  simpa [hVar] using
    twoSubtree_factorBelief_exact
      (fg := fg) (f := f) (g := g) (k := k) (p := p) (q := q)
      (u := u) (w := w) (v := v) (y := y) (t := t) (z := z)
      hwf hLeafF hvg hLeafG hvk htp hLeafP hzq hLeafQ hzk hPairK
      hfg hgk hpq hqk hNbrsW hNbrsV hNbrsT hNbrsZ x

section NormalizedIncident

variable {fg : FactorGraph V ENNReal}

theorem twoSubtree_factorBelief_exact_normalized_incident
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [∀ v, Nonempty (fg.stateSpace v)]
    (f g k p q : fg.factors) (u w v y t z : V)
    (hwf : w ∈ fg.scope f) (hLeafF : (fg.scope f).erase w = {u})
    (hvg : v ∈ fg.scope g) (hLeafG : (fg.scope g).erase v = {w})
    (hvk : v ∈ fg.scope k)
    (htp : t ∈ fg.scope p) (hLeafP : (fg.scope p).erase t = {y})
    (hzq : z ∈ fg.scope q) (hLeafQ : (fg.scope q).erase z = {t})
    (hzk : z ∈ fg.scope k) (hPairK : (fg.scope k).erase z = {v})
    (hfg : f ≠ g) (hgk : g ≠ k) (hpq : p ≠ q) (hqk : q ≠ k)
    (hNbrsW : FactorGraph.variableNeighborsFinset fg w = {f, g})
    (hNbrsV : FactorGraph.variableNeighborsFinset fg v = {g, k})
    (hNbrsT : FactorGraph.variableNeighborsFinset fg t = {p, q})
    (hNbrsZ : FactorGraph.variableNeighborsFinset fg z = {q, k}) :
    ∀ x : fg.FullConfig,
      let μ := (IncidentMessageState.toTotal (fg := fg)
        (runSyncRoundsIncident (fg := fg) 4 (initIncidentState (fg := fg)))).varToFactor
      let φ := VariableElimination.Factor.mul (fg := fg)
        (VariableElimination.Factor.mul (fg := fg)
          (VariableElimination.Factor.ofGraph (fg := fg) k)
          (VariableElimination.Factor.sumOut
            (φ := twoFactorSubtreeFactor (fg := fg) f g u) w))
        (VariableElimination.Factor.sumOut
          (φ := twoFactorSubtreeFactor (fg := fg) p q y) t)
      let exactAt := Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassing.localFactorValue
        (fg := fg) k φ
      let zsum :=
        ∑ a : VariableElimination.FactorGraph.Assign (fg := fg) (fg.scope k), exactAt a
      (if (∑ a : VariableElimination.FactorGraph.Assign (fg := fg) (fg.scope k),
            factorBelief (fg := fg) μ k a) = 0 then
        0
      else
        factorBelief (fg := fg) μ k (fg.restrictToScope k x) /
          (∑ a : VariableElimination.FactorGraph.Assign (fg := fg) (fg.scope k),
            factorBelief (fg := fg) μ k a)) =
      (if zsum = 0 then
        0
      else
        exactAt (fg.restrictToScope k x) / zsum) := by
  intro x
  exact factorBelief_normalized_of_exact
    (μ := (IncidentMessageState.toTotal (fg := fg)
      (runSyncRoundsIncident (fg := fg) 4 (initIncidentState (fg := fg)))).varToFactor)
    (h := k)
    (φ := VariableElimination.Factor.mul (fg := fg)
      (VariableElimination.Factor.mul (fg := fg)
        (VariableElimination.Factor.ofGraph (fg := fg) k)
        (VariableElimination.Factor.sumOut
          (φ := twoFactorSubtreeFactor (fg := fg) f g u) w))
      (VariableElimination.Factor.sumOut
        (φ := twoFactorSubtreeFactor (fg := fg) p q y) t))
    (hExact := by
      intro x
      exact twoSubtree_factorBelief_exact_incident
        (fg := fg) (f := f) (g := g) (k := k) (p := p) (q := q)
        (u := u) (w := w) (v := v) (y := y) (t := t) (z := z)
        hwf hLeafF hvg hLeafG hvk htp hLeafP hzq hLeafQ hzk hPairK
        hfg hgk hpq hqk hNbrsW hNbrsV hNbrsT hNbrsZ x)
    x

end NormalizedIncident

end MessagePassing.TreeExactness

end Mettapedia.ProbabilityTheory.BayesianNetworks
