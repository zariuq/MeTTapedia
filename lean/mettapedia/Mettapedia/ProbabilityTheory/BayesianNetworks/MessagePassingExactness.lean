import Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassingBridge

/-!
# Tiny Exactness Theorems for Abstract Belief Propagation

This module starts cashing out the abstract BP core into exact-inference facts on
small tree-shaped fragments.

The first result is the minimal nontrivial case: a three-node factor-graph tree
`u — f — v`, where `f` is a pairwise factor. After one synchronous round from
the neutral message state, the BP message `f -> v` agrees exactly with
eliminating `u` from the factor by VE.
-/

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

namespace MessagePassing

variable {V K : Type*} [DecidableEq V]

section TinyTree

variable {fg : FactorGraph V K}

/-- Tiny tree exactness, first step: for a pairwise factor `f` whose other scope
relative to `v` is the singleton `{u}`, the first synchronous BP round from the
neutral state sends to `v` exactly the VE `sumOut` of `u` from `f`. -/
theorem pairwiseFactor_syncRound_init_exact
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (f : fg.factors) (v u : V) (hv : v ∈ fg.scope f)
    (hSingle : (fg.scope f).erase v = {u}) :
    ∀ x : fg.FullConfig,
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.sumOut
          (φ := VariableElimination.Factor.ofGraph (fg := fg) f) u)).val x =
        (syncRound (fg := fg) (initState (fg := fg))).factorToVar v f (x v) := by
  intro x
  have huErase : u ∈ (fg.scope f).erase v := by
    simp [hSingle]
  have hu : u ∈ fg.scope f := (Finset.mem_erase.mp huErase).2
  have hLocal :=
    pairwiseLeaf_sumOut_bridge
      (fg := fg) (μ := unitVarToFactor (fg := fg))
      (f := f) (v := v) (u := u) hv hSingle x
  have hLeft :
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.sumOut
          (φ := pairwiseIncomingFactor (fg := fg) (unitVarToFactor (fg := fg)) f u hu) u)).val x =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.sumOut
          (φ := VariableElimination.Factor.ofGraph (fg := fg) f) u)).val x := by
    simp [pairwiseIncomingFactor, unitVarToFactor, VariableElimination.Factor.ofGraph]
  calc
    (VariableElimination.Factor.toValuation
      (φ := VariableElimination.Factor.sumOut
        (φ := VariableElimination.Factor.ofGraph (fg := fg) f) u)).val x
        =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.sumOut
          (φ := pairwiseIncomingFactor (fg := fg) (unitVarToFactor (fg := fg)) f u hu) u)).val x := by
            symm
            exact hLeft
    _ = factorToVarUpdate
          (fg := fg) (unitVarToFactor (fg := fg)) f v hv (x v) := hLocal
    _ = (syncRound (fg := fg) (initState (fg := fg))).factorToVar v f (x v) := by
          simp [syncRound, initState, hv]

end TinyTree

section TwoFactorChain

variable {fg : FactorGraph V K}

private theorem otherFactorNeighbors_eq_singleton_of_variableNeighbors_pair
    [Fintype fg.factors] [DecidableEq fg.factors]
    (w : V) (f g : fg.factors) (hfg : f ≠ g)
    (hNbrs : FactorGraph.variableNeighborsFinset fg w = {f, g}) :
    FactorGraph.otherFactorNeighbors fg w g = {f} := by
  classical
  rw [FactorGraph.otherFactorNeighbors, hNbrs]
  ext a
  constructor
  · intro ha
    rcases Finset.mem_erase.mp ha with ⟨hag, ha⟩
    simp at ha
    cases ha with
    | inl haf => simp [haf]
    | inr hag' => exact (hag hag').elim
  · intro ha
    have haf : a = f := by simpa using ha
    refine Finset.mem_erase.mpr ?_
    constructor
    · simpa [haf] using hfg
    · simp [haf]

private theorem varToFactorUpdate_eq_single_incoming
    [Fintype fg.factors] [DecidableEq fg.factors] [CommMonoid K]
    (μ : FactorToVarMsg fg) (w : V) (f g : fg.factors)
    (hwg : w ∈ fg.scope g)
    (hSingle : FactorGraph.otherFactorNeighbors fg w g = {f}) :
    varToFactorUpdate (fg := fg) μ w g hwg = μ w f := by
  funext x_w
  rw [varToFactorUpdate, hSingle]
  change ∏ h : { g_1 : fg.factors // g_1 ∈ ({f} : Finset fg.factors) }, μ w h.1 x_w = μ w f x_w
  simp

/-- In the two-factor chain `u - f - w - g`, after two synchronous rounds from
the neutral state, the message `w -> g` is exactly the VE elimination of the
leaf factor `f` into `w`. This is the first point where information has really
propagated across an intermediate variable. -/
theorem twoFactorChain_varToFactor_twoRounds_exact
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (f g : fg.factors) (u w : V)
    (hwf : w ∈ fg.scope f) (hLeafF : (fg.scope f).erase w = {u})
    (hwg : w ∈ fg.scope g) (hfg : f ≠ g)
    (hNbrs : FactorGraph.variableNeighborsFinset fg w = {f, g}) :
    ∀ x : fg.FullConfig,
      (runSyncRounds (fg := fg) 2 (initState (fg := fg))).varToFactor w g (x w) =
        (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.sumOut
            (φ := VariableElimination.Factor.ofGraph (fg := fg) f) u)).val x := by
  intro x
  let σ₁ := syncRound (fg := fg) (initState (fg := fg))
  have hSingle :
      FactorGraph.otherFactorNeighbors fg w g = {f} :=
    otherFactorNeighbors_eq_singleton_of_variableNeighbors_pair
      (fg := fg) (w := w) (f := f) (g := g) hfg hNbrs
  have hVar :
      varToFactorUpdate (fg := fg) σ₁.factorToVar w g hwg = σ₁.factorToVar w f := by
    exact varToFactorUpdate_eq_single_incoming
      (fg := fg) (μ := σ₁.factorToVar) (w := w) (f := f) (g := g) hwg hSingle
  have hPairwise :=
    pairwiseFactor_syncRound_init_exact
      (fg := fg) (f := f) (v := w) (u := u) hwf hLeafF x
  calc
    (runSyncRounds (fg := fg) 2 (initState (fg := fg))).varToFactor w g (x w)
        = (syncRound (fg := fg) σ₁).varToFactor w g (x w) := by
            simp [σ₁, runSyncRounds]
    _ = varToFactorUpdate (fg := fg) σ₁.factorToVar w g hwg (x w) := by
          simp [syncRound, hwg]
    _ = σ₁.factorToVar w f (x w) := by
          simpa using congrFun hVar (x w)
    _ = (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.sumOut
            (φ := VariableElimination.Factor.ofGraph (fg := fg) f) u)).val x := by
          simpa [σ₁] using hPairwise.symm

/-- Two-factor chain exactness: in `u - f - w - g - v`, after three
synchronous rounds from the neutral state, the message `g -> v` is exactly what
you get by first eliminating the leaf factor `f` into a unary message on `w`,
then using that unary message in the pairwise update across `g`. -/
theorem twoFactorChain_factorToVar_threeRounds_exact
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (f g : fg.factors) (u w v : V)
    (hwf : w ∈ fg.scope f) (hLeafF : (fg.scope f).erase w = {u})
    (hvg : v ∈ fg.scope g) (hLeafG : (fg.scope g).erase v = {w})
    (hfg : f ≠ g)
    (hNbrs : FactorGraph.variableNeighborsFinset fg w = {f, g}) :
    ∀ x : fg.FullConfig,
      (runSyncRounds (fg := fg) 3 (initState (fg := fg))).factorToVar v g (x v) =
        ∑ x_w : fg.stateSpace w,
          fg.potential g
            (VariableElimination.Factor.extend
              (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) g)
              v hvg
              (singletonOtherScopeAssign (fg := fg) g v w hLeafG x_w)
              (x v)) *
            (VariableElimination.Factor.toValuation
              (φ := VariableElimination.Factor.sumOut
                (φ := VariableElimination.Factor.ofGraph (fg := fg) f) u)).val
              (Function.update x w x_w) := by
  intro x
  let σ₂ := runSyncRounds (fg := fg) 2 (initState (fg := fg))
  have hwg : w ∈ fg.scope g := by
    have hwErase : w ∈ (fg.scope g).erase v := by
      simp [hLeafG]
    exact (Finset.mem_erase.mp hwErase).2
  have hLocal :=
    congrFun
      (pairwiseLeaf_localElimination_bridge
        (fg := fg) (μ := σ₂.varToFactor) (f := g) (v := v) (u := w) hvg hLeafG)
      (x v)
  calc
    (runSyncRounds (fg := fg) 3 (initState (fg := fg))).factorToVar v g (x v)
        = factorToVarUpdate (fg := fg) σ₂.varToFactor g v hvg (x v) := by
            simp [σ₂, runSyncRounds_succ, syncRound, hvg]
    _ = ∑ x_w : fg.stateSpace w,
          fg.potential g
            (VariableElimination.Factor.extend
              (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) g)
              v hvg
              (singletonOtherScopeAssign (fg := fg) g v w hLeafG x_w)
              (x v)) *
            σ₂.varToFactor w g x_w := by
          simpa using! hLocal
    _ = ∑ x_w : fg.stateSpace w,
          fg.potential g
            (VariableElimination.Factor.extend
              (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) g)
              v hvg
              (singletonOtherScopeAssign (fg := fg) g v w hLeafG x_w)
              (x v)) *
            (VariableElimination.Factor.toValuation
              (φ := VariableElimination.Factor.sumOut
                (φ := VariableElimination.Factor.ofGraph (fg := fg) f) u)).val
              (Function.update x w x_w) := by
          apply Fintype.sum_congr
          intro x_w
          have hProp :=
            twoFactorChain_varToFactor_twoRounds_exact
              (fg := fg) (f := f) (g := g) (u := u) (w := w)
              hwf hLeafF
              hwg
              hfg hNbrs
              (Function.update x w x_w)
          simpa using! congrArg
            (fun z =>
              fg.potential g
                (VariableElimination.Factor.extend
                  (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) g)
                  v hvg
                  (singletonOtherScopeAssign (fg := fg) g v w hLeafG x_w)
                  (x v)) * z)
            hProp

/-- The three-round chain theorem repackaged at the actual VE factor layer:
the propagated subtree message is `sumOut` of the product of the local factor
`g` with the already-eliminated leaf factor from `f`. -/
theorem twoFactorChain_factorToVar_threeRounds_sumOut_mul_exact
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (f g : fg.factors) (u w v : V)
    (hwf : w ∈ fg.scope f) (hLeafF : (fg.scope f).erase w = {u})
    (hvg : v ∈ fg.scope g) (hLeafG : (fg.scope g).erase v = {w})
    (hfg : f ≠ g)
    (hNbrs : FactorGraph.variableNeighborsFinset fg w = {f, g}) :
    ∀ x : fg.FullConfig,
      (runSyncRounds (fg := fg) 3 (initState (fg := fg))).factorToVar v g (x v) =
        (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.sumOut
            (φ := VariableElimination.Factor.mul (fg := fg)
              (VariableElimination.Factor.ofGraph (fg := fg) g)
              (VariableElimination.Factor.sumOut
                (φ := VariableElimination.Factor.ofGraph (fg := fg) f) u))
            w)).val x := by
  intro x
  let leaf : VariableElimination.Factor (fg := fg) :=
    VariableElimination.Factor.sumOut
      (φ := VariableElimination.Factor.ofGraph (fg := fg) f) u
  let χ : VariableElimination.Factor (fg := fg) :=
    VariableElimination.Factor.mul (fg := fg)
      (VariableElimination.Factor.ofGraph (fg := fg) g) leaf
  have hwg : w ∈ fg.scope g := by
    have hwErase : w ∈ (fg.scope g).erase v := by
      simp [hLeafG]
    exact (Finset.mem_erase.mp hwErase).2
  have hvw : v ≠ w := by
    have hwErase : w ∈ (fg.scope g).erase v := by
      simp [hLeafG]
    exact Ne.symm (Finset.mem_erase.mp hwErase).1
  have hwχ : w ∈ χ.scope := by
    simp [χ, leaf, VariableElimination.Factor.mul, VariableElimination.Factor.ofGraph, hwg]
  have hUpdateEq :
      Mettapedia.ProbabilityTheory.BayesianNetworks.update
          (V := V) (β := fun z => fg.stateSpace z) x w
          =
        Function.update x w := by
    funext x_w z
    classical
    by_cases h : z = w
    · subst z
      simp [Mettapedia.ProbabilityTheory.BayesianNetworks.update, Function.update]
    · simp [Mettapedia.ProbabilityTheory.BayesianNetworks.update, Function.update, h]
  have hPotentialG :
      ∀ x_w : fg.stateSpace w,
        (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.ofGraph (fg := fg) g)).val
            (Mettapedia.ProbabilityTheory.BayesianNetworks.update
              (V := V) (β := fun z => fg.stateSpace z) x w x_w) =
          fg.potential g
            (VariableElimination.Factor.extend
              (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) g)
              v hvg
              (singletonOtherScopeAssign (fg := fg) g v w hLeafG x_w)
              (x v)) := by
    intro x_w
    have hAssign :
        (fun z hz =>
          Mettapedia.ProbabilityTheory.BayesianNetworks.update
            (V := V) (β := fun z => fg.stateSpace z) x w x_w z) =
          VariableElimination.Factor.extend
            (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) g)
            v hvg
            (singletonOtherScopeAssign (fg := fg) g v w hLeafG x_w)
            (x v) := by
      funext z hz
      by_cases hzv : z = v
      · subst z
        calc
          Mettapedia.ProbabilityTheory.BayesianNetworks.update
              (V := V) (β := fun z => fg.stateSpace z) x w x_w v
              = x v := by
                  simp [Mettapedia.ProbabilityTheory.BayesianNetworks.update, hvw]
          _ = VariableElimination.Factor.extend
                (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) g)
                v hvg
                (singletonOtherScopeAssign (fg := fg) g v w hLeafG x_w)
                (x v) v hvg := by
                  symm
                  simpa using
                    (VariableElimination.Factor.extend_apply_eq
                      (φ := VariableElimination.Factor.ofGraph (fg := fg) g)
                      (v := v) (hv := hvg)
                      (x := singletonOtherScopeAssign (fg := fg) g v w hLeafG x_w)
                      (val := x v))
      · have hzw : z = w := by
          have hzErase : z ∈ (fg.scope g).erase v := Finset.mem_erase.mpr ⟨hzv, hz⟩
          simpa [hLeafG] using hzErase
        subst z
        calc
          Mettapedia.ProbabilityTheory.BayesianNetworks.update
              (V := V) (β := fun z => fg.stateSpace z) x w x_w w
              = x_w := by
                  simp [Mettapedia.ProbabilityTheory.BayesianNetworks.update]
          _ = VariableElimination.Factor.extend
                (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) g)
                v hvg
                (singletonOtherScopeAssign (fg := fg) g v w hLeafG x_w)
                (x v) w hwg := by
                  symm
                  simpa [singletonOtherScopeAssign] using
                    (VariableElimination.Factor.extend_apply_ne
                      (φ := VariableElimination.Factor.ofGraph (fg := fg) g)
                      (v := v) (hv := hvg)
                      (x := singletonOtherScopeAssign (fg := fg) g v w hLeafG x_w)
                      (val := x v) (u := w) (hu := hwg) (Ne.symm hvw))
    have := congrArg (fg.potential g) hAssign
    simpa [VariableElimination.Factor.toValuation, VariableElimination.Factor.ofGraph] using this
  have hCombine :
      ∀ x_w : fg.stateSpace w,
        (Mettapedia.ProbabilityTheory.BayesianNetworks.combine
          (φ := VariableElimination.Factor.toValuation
            (φ := VariableElimination.Factor.ofGraph (fg := fg) g))
          (ψ := VariableElimination.Factor.toValuation (φ := leaf))).val
            (Mettapedia.ProbabilityTheory.BayesianNetworks.update
              (V := V) (β := fun z => fg.stateSpace z) x w x_w) =
          fg.potential g
            (VariableElimination.Factor.extend
              (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) g)
              v hvg
              (singletonOtherScopeAssign (fg := fg) g v w hLeafG x_w)
              (x v)) *
            (VariableElimination.Factor.toValuation (φ := leaf)).val
              (Mettapedia.ProbabilityTheory.BayesianNetworks.update
                (V := V) (β := fun z => fg.stateSpace z) x w x_w) := by
    intro x_w
    simp [Mettapedia.ProbabilityTheory.BayesianNetworks.combine, hPotentialG x_w]
  calc
    (runSyncRounds (fg := fg) 3 (initState (fg := fg))).factorToVar v g (x v)
        = ∑ x_w : fg.stateSpace w,
            fg.potential g
              (VariableElimination.Factor.extend
                (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) g)
                v hvg
                (singletonOtherScopeAssign (fg := fg) g v w hLeafG x_w)
                (x v)) *
              (VariableElimination.Factor.toValuation (φ := leaf)).val
                (Mettapedia.ProbabilityTheory.BayesianNetworks.update
                  (V := V) (β := fun z => fg.stateSpace z) x w x_w) := by
          calc
            (runSyncRounds (fg := fg) 3 (initState (fg := fg))).factorToVar v g (x v)
                = ∑ x_w : fg.stateSpace w,
                    fg.potential g
                      (VariableElimination.Factor.extend
                        (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) g)
                        v hvg
                        (singletonOtherScopeAssign (fg := fg) g v w hLeafG x_w)
                        (x v)) *
                      (VariableElimination.Factor.toValuation (φ := leaf)).val
                        (Function.update x w x_w) := by
                    simpa [leaf] using
                      twoFactorChain_factorToVar_threeRounds_exact
                        (fg := fg) (f := f) (g := g) (u := u) (w := w) (v := v)
                        hwf hLeafF hvg hLeafG hfg hNbrs x
            _ = ∑ x_w : fg.stateSpace w,
                  fg.potential g
                    (VariableElimination.Factor.extend
                      (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) g)
                      v hvg
                      (singletonOtherScopeAssign (fg := fg) g v w hLeafG x_w)
                      (x v)) *
                    (VariableElimination.Factor.toValuation (φ := leaf)).val
                      (Mettapedia.ProbabilityTheory.BayesianNetworks.update
                        (V := V) (β := fun z => fg.stateSpace z) x w x_w) := by
                  apply Fintype.sum_congr
                  intro x_w
                  simp [hUpdateEq]
    _ = ∑ x_w : fg.stateSpace w,
          (Mettapedia.ProbabilityTheory.BayesianNetworks.combine
            (φ := VariableElimination.Factor.toValuation
              (φ := VariableElimination.Factor.ofGraph (fg := fg) g))
            (ψ := VariableElimination.Factor.toValuation (φ := leaf))).val
              (Mettapedia.ProbabilityTheory.BayesianNetworks.update
                (V := V) (β := fun z => fg.stateSpace z) x w x_w) := by
          apply Fintype.sum_congr
          intro x_w
          symm
          exact hCombine x_w
    _ =
      (Mettapedia.ProbabilityTheory.BayesianNetworks.sumOut
        (φ := Mettapedia.ProbabilityTheory.BayesianNetworks.combine
          (φ := VariableElimination.Factor.toValuation
            (φ := VariableElimination.Factor.ofGraph (fg := fg) g))
          (ψ := VariableElimination.Factor.toValuation (φ := leaf)))
        w).val x := by
          have hwCombine :
              w ∈
                (Mettapedia.ProbabilityTheory.BayesianNetworks.combine
                  (φ := VariableElimination.Factor.toValuation
                    (φ := VariableElimination.Factor.ofGraph (fg := fg) g))
                  (ψ := VariableElimination.Factor.toValuation (φ := leaf))).scope := by
            exact Finset.mem_union.mpr <| Or.inl <|
              (by simpa [VariableElimination.Factor.toValuation, VariableElimination.Factor.ofGraph] using hwg)
          symm
          simp [Mettapedia.ProbabilityTheory.BayesianNetworks.sumOut, hwCombine]
    _ =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.sumOut (φ := χ) w)).val x := by
          symm
          exact congrArg (fun ψ => ψ.val x)
            (VariableElimination.Factor.toValuation_sumOut (φ := χ) (v := w))
    _ =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.sumOut
          (φ := VariableElimination.Factor.mul (fg := fg)
            (VariableElimination.Factor.ofGraph (fg := fg) g)
            (VariableElimination.Factor.sumOut
              (φ := VariableElimination.Factor.ofGraph (fg := fg) f) u))
          w)).val x := by
            rfl

end TwoFactorChain

end MessagePassing

end Mettapedia.ProbabilityTheory.BayesianNetworks
