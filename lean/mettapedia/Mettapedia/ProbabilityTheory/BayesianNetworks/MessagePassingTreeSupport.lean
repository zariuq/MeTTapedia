import Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassingExactness

/-!
# Tree-Support Objects for Abstract Belief Propagation

This module packages the current local and chain exactness results into a small
set of **named subtree factors** and **reusable message theorems**. The goal is
to give later tree-induction proofs stable objects to talk about:

* eliminate a leaf factor into its parent variable;
* combine that eliminated leaf subtree with the parent factor;
* express the propagated BP message as `sumOut` of the combined subtree factor.
-/

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

namespace MessagePassing

variable {V K : Type*} [DecidableEq V]

section TreeSupport

variable {fg : FactorGraph V K}

/-- If `w` has exactly the two factor neighbors `{f, g}`, then the neighbors of
`w` other than `g` are exactly `{f}`. -/
theorem otherFactorNeighbors_eq_singleton_of_variableNeighbors_pair
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

/-- If the only incoming factor neighbor of `w` besides `g` is `f`, then the
variable-to-factor update toward `g` is just the single incoming message from
`f`. -/
theorem varToFactorUpdate_eq_single_incoming
    [Fintype fg.factors] [DecidableEq fg.factors] [CommMonoid K]
    (μ : FactorToVarMsg fg) (w : V) (f g : fg.factors)
    (hwg : w ∈ fg.scope g)
    (hSingle : FactorGraph.otherFactorNeighbors fg w g = {f}) :
    varToFactorUpdate (fg := fg) μ w g hwg = μ w f := by
  funext x_w
  rw [varToFactorUpdate, hSingle]
  change ∏ h : { g_1 : fg.factors // g_1 ∈ ({f} : Finset fg.factors) }, μ w h.1 x_w = μ w f x_w
  simp

/-- If the only incoming factor neighbor of `v` besides `h` is `g`, and the
incoming message from `g` is already exact as a subtree factor valuation, then
the next variable-to-factor message toward `h` is that same exact subtree
factor valuation. -/
theorem varToFactor_of_exactIncomingFactor
    [Fintype fg.factors] [DecidableEq fg.factors] [CommMonoid K]
    (μ : FactorToVarMsg fg) (v : V) (g h : fg.factors)
    (hvh : v ∈ fg.scope h)
    (hSingle : FactorGraph.otherFactorNeighbors fg v h = {g})
    (ψ : VariableElimination.Factor (fg := fg))
    (hIncoming : ∀ x : fg.FullConfig,
      μ v g (x v) = (VariableElimination.Factor.toValuation (φ := ψ)).val x) :
    ∀ x : fg.FullConfig,
      varToFactorUpdate (fg := fg) μ v h hvh (x v) =
        (VariableElimination.Factor.toValuation (φ := ψ)).val x := by
  intro x
  rw [varToFactorUpdate_eq_single_incoming (fg := fg) (μ := μ) (w := v) (f := g) (g := h) hvh hSingle]
  exact hIncoming x

/-- The exact VE factor obtained by eliminating the leaf variable `u` from the
leaf factor `f`. -/
noncomputable def leafEliminatedFactor
    [∀ v, Fintype (fg.stateSpace v)] [AddCommMonoid K]
    (f : fg.factors) (u : V) : VariableElimination.Factor (fg := fg) :=
  VariableElimination.Factor.sumOut
    (φ := VariableElimination.Factor.ofGraph (fg := fg) f) u

/-- The combined two-factor subtree factor for a chain `u - f - w - g`: first
eliminate `u` from `f`, then multiply the resulting unary factor into `g`. -/
noncomputable def twoFactorSubtreeFactor
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (f g : fg.factors) (u : V) : VariableElimination.Factor (fg := fg) :=
  VariableElimination.Factor.mul (fg := fg)
    (VariableElimination.Factor.ofGraph (fg := fg) g)
    (leafEliminatedFactor (fg := fg) f u)

/-- The combined three-factor subtree factor for the chain `u - f - w - g - v - h`:
first eliminate the leaf variable `u` from `f`, combine the result into `g`,
then eliminate the separator `w` and combine that unary factor into `h`. -/
noncomputable def threeFactorSubtreeFactor
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (f g h : fg.factors) (u w : V) : VariableElimination.Factor (fg := fg) :=
  VariableElimination.Factor.mul (fg := fg)
    (VariableElimination.Factor.ofGraph (fg := fg) h)
    (VariableElimination.Factor.sumOut
      (φ := twoFactorSubtreeFactor (fg := fg) f g u) w)

/-- Exact subtree packaged as a variable-to-factor message into a parent factor. -/
structure ExactVarToFactorSubtree
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (v : V) (f : fg.factors) where
  rounds : Nat
  factor : VariableElimination.Factor (fg := fg)
  exact :
    ∀ x : fg.FullConfig,
      (runSyncRounds (fg := fg) rounds (initState (fg := fg))).varToFactor v f (x v) =
        (VariableElimination.Factor.toValuation (φ := factor)).val x

/-- Exact subtree packaged as a factor-to-variable message into a parent variable. -/
structure ExactFactorToVarSubtree
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (v : V) (f : fg.factors) where
  rounds : Nat
  factor : VariableElimination.Factor (fg := fg)
  exact :
    ∀ x : fg.FullConfig,
      (runSyncRounds (fg := fg) rounds (initState (fg := fg))).factorToVar v f (x v) =
        (VariableElimination.Factor.toValuation (φ := factor)).val x


/-- Reusable leaf-to-parent variable-message theorem: in `u - f - w - g`, after
two synchronous rounds from the neutral state, the message `w -> g` is exactly
the eliminated leaf subtree factor. -/
theorem leafToParent_varMessage_exact
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (f g : fg.factors) (u w : V)
    (hwf : w ∈ fg.scope f) (hLeafF : (fg.scope f).erase w = {u})
    (hwg : w ∈ fg.scope g) (hfg : f ≠ g)
    (hNbrs : FactorGraph.variableNeighborsFinset fg w = {f, g}) :
    ∀ x : fg.FullConfig,
      (runSyncRounds (fg := fg) 2 (initState (fg := fg))).varToFactor w g (x w) =
        (VariableElimination.Factor.toValuation
          (φ := leafEliminatedFactor (fg := fg) f u)).val x := by
  intro x
  simpa [leafEliminatedFactor] using
    twoFactorChain_varToFactor_twoRounds_exact
      (fg := fg) (f := f) (g := g) (u := u) (w := w)
      hwf hLeafF hwg hfg hNbrs x

/-- Incident-edge-indexed form of `leafToParent_varMessage_exact`. -/
theorem leafToParent_varMessage_exact_incident
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (f g : fg.factors) (u w : V)
    (hwf : w ∈ fg.scope f) (hLeafF : (fg.scope f).erase w = {u})
    (hwg : w ∈ fg.scope g) (hfg : f ≠ g)
    (hNbrs : FactorGraph.variableNeighborsFinset fg w = {f, g}) :
    ∀ x : fg.FullConfig,
      (runSyncRoundsIncident (fg := fg) 2 (initIncidentState (fg := fg))).varToFactor
          ⟨w, g, hwg⟩ (x w) =
        (VariableElimination.Factor.toValuation
          (φ := leafEliminatedFactor (fg := fg) f u)).val x := by
  intro x
  have hBridge :
      (IncidentMessageState.toTotal (fg := fg)
        (runSyncRoundsIncident (fg := fg) 2 (initIncidentState (fg := fg)))).varToFactor w g (x w) =
      (runSyncRounds (fg := fg) 2
        (IncidentMessageState.toTotal (fg := fg) (initIncidentState (fg := fg)))).varToFactor
          w g (x w) :=
    congrArg (fun σ => σ.varToFactor w g (x w))
      (toTotal_runSyncRoundsIncident_eq_runSyncRounds_toTotal
        (fg := fg) (n := 2) (σ := initIncidentState (fg := fg)))
  calc
    (runSyncRoundsIncident (fg := fg) 2 (initIncidentState (fg := fg))).varToFactor
        ⟨w, g, hwg⟩ (x w)
        =
      (IncidentMessageState.toTotal (fg := fg)
        (runSyncRoundsIncident (fg := fg) 2 (initIncidentState (fg := fg)))).varToFactor
          w g (x w) := by
            simp [IncidentMessageState.toTotal, IncidentVarToFactorMsg.toTotal, hwg]
    _ = (runSyncRounds (fg := fg) 2
          (IncidentMessageState.toTotal (fg := fg) (initIncidentState (fg := fg)))).varToFactor
            w g (x w) := hBridge
    _ = (runSyncRounds (fg := fg) 2 (initState (fg := fg))).varToFactor w g (x w) := by
          simp [initIncidentState_toTotal]
    _ =
      (VariableElimination.Factor.toValuation
        (φ := leafEliminatedFactor (fg := fg) f u)).val x := by
          exact leafToParent_varMessage_exact
            (fg := fg) (f := f) (g := g) (u := u) (w := w)
            hwf hLeafF hwg hfg hNbrs x

/-- Reusable leaf-to-parent factor-message theorem: in `u - f - w - g - v`,
after three synchronous rounds from the neutral state, the message `g -> v` is
exactly `sumOut` of the combined two-factor subtree through the separator
variable `w`. -/
theorem leafToParent_subtreeMessage_exact
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
            (φ := twoFactorSubtreeFactor (fg := fg) f g u) w)).val x := by
  intro x
  simpa [leafEliminatedFactor, twoFactorSubtreeFactor] using
    twoFactorChain_factorToVar_threeRounds_sumOut_mul_exact
      (fg := fg) (f := f) (g := g) (u := u) (w := w) (v := v)
      hwf hLeafF hvg hLeafG hfg hNbrs x

/-- Incident-edge-indexed form of `leafToParent_subtreeMessage_exact`. -/
theorem leafToParent_subtreeMessage_exact_incident
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (f g : fg.factors) (u w v : V)
    (hwf : w ∈ fg.scope f) (hLeafF : (fg.scope f).erase w = {u})
    (hvg : v ∈ fg.scope g) (hLeafG : (fg.scope g).erase v = {w})
    (hfg : f ≠ g)
    (hNbrs : FactorGraph.variableNeighborsFinset fg w = {f, g}) :
    ∀ x : fg.FullConfig,
      (runSyncRoundsIncident (fg := fg) 3 (initIncidentState (fg := fg))).factorToVar
          ⟨v, g, hvg⟩ (x v) =
        (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.sumOut
            (φ := twoFactorSubtreeFactor (fg := fg) f g u) w)).val x := by
  intro x
  have hBridge :
      (IncidentMessageState.toTotal (fg := fg)
        (runSyncRoundsIncident (fg := fg) 3 (initIncidentState (fg := fg)))).factorToVar v g (x v) =
      (runSyncRounds (fg := fg) 3
        (IncidentMessageState.toTotal (fg := fg) (initIncidentState (fg := fg)))).factorToVar
          v g (x v) :=
    congrArg (fun σ => σ.factorToVar v g (x v))
      (toTotal_runSyncRoundsIncident_eq_runSyncRounds_toTotal
        (fg := fg) (n := 3) (σ := initIncidentState (fg := fg)))
  calc
    (runSyncRoundsIncident (fg := fg) 3 (initIncidentState (fg := fg))).factorToVar
        ⟨v, g, hvg⟩ (x v)
        =
      (IncidentMessageState.toTotal (fg := fg)
        (runSyncRoundsIncident (fg := fg) 3 (initIncidentState (fg := fg)))).factorToVar
          v g (x v) := by
            simp [IncidentMessageState.toTotal, IncidentFactorToVarMsg.toTotal, hvg]
    _ = (runSyncRounds (fg := fg) 3
          (IncidentMessageState.toTotal (fg := fg) (initIncidentState (fg := fg)))).factorToVar
            v g (x v) := hBridge
    _ = (runSyncRounds (fg := fg) 3 (initState (fg := fg))).factorToVar v g (x v) := by
          simp [initIncidentState_toTotal]
    _ =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.sumOut
          (φ := twoFactorSubtreeFactor (fg := fg) f g u) w)).val x := by
          exact leafToParent_subtreeMessage_exact
            (fg := fg) (f := f) (g := g) (u := u) (w := w) (v := v)
            hwf hLeafF hvg hLeafG hfg hNbrs x

/-- Reusable recursive subtree theorem: in `u - f - w - g - v - h`, after four
synchronous rounds from the neutral state, the variable-to-factor message
`v -> h` is exactly the eliminated two-factor subtree arriving through `v`. -/
theorem twoFactorSubtreeToParent_varMessage_exact
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (f g h : fg.factors) (u w v : V)
    (hwf : w ∈ fg.scope f) (hLeafF : (fg.scope f).erase w = {u})
    (hvg : v ∈ fg.scope g) (hLeafG : (fg.scope g).erase v = {w})
    (hvh : v ∈ fg.scope h) (hfg : f ≠ g) (hgh : g ≠ h)
    (hNbrsW : FactorGraph.variableNeighborsFinset fg w = {f, g})
    (hNbrsV : FactorGraph.variableNeighborsFinset fg v = {g, h}) :
    ∀ x : fg.FullConfig,
      (runSyncRounds (fg := fg) 4 (initState (fg := fg))).varToFactor v h (x v) =
        (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.sumOut
            (φ := twoFactorSubtreeFactor (fg := fg) f g u) w)).val x := by
  intro x
  let σ₃ := runSyncRounds (fg := fg) 3 (initState (fg := fg))
  have hSingle :
      FactorGraph.otherFactorNeighbors fg v h = {g} :=
    otherFactorNeighbors_eq_singleton_of_variableNeighbors_pair
      (fg := fg) (w := v) (f := g) (g := h) hgh hNbrsV
  have hVar :
      varToFactorUpdate (fg := fg) σ₃.factorToVar v h hvh = σ₃.factorToVar v g := by
    exact varToFactorUpdate_eq_single_incoming
      (fg := fg) (μ := σ₃.factorToVar) (w := v) (f := g) (g := h) hvh hSingle
  have hSubtree :=
    leafToParent_subtreeMessage_exact
      (fg := fg) (f := f) (g := g) (u := u) (w := w) (v := v)
      hwf hLeafF hvg hLeafG hfg hNbrsW x
  calc
    (runSyncRounds (fg := fg) 4 (initState (fg := fg))).varToFactor v h (x v)
        = (syncRound (fg := fg) σ₃).varToFactor v h (x v) := by
            simp [σ₃, runSyncRounds]
    _ = varToFactorUpdate (fg := fg) σ₃.factorToVar v h hvh (x v) := by
          simp [syncRound, hvh]
    _ = σ₃.factorToVar v g (x v) := by
          simpa using congrFun hVar (x v)
    _ = (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.sumOut
            (φ := twoFactorSubtreeFactor (fg := fg) f g u) w)).val x := by
          simpa [σ₃] using hSubtree

/-- Incident-edge-indexed form of `twoFactorSubtreeToParent_varMessage_exact`. -/
theorem twoFactorSubtreeToParent_varMessage_exact_incident
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (f g h : fg.factors) (u w v : V)
    (hwf : w ∈ fg.scope f) (hLeafF : (fg.scope f).erase w = {u})
    (hvg : v ∈ fg.scope g) (hLeafG : (fg.scope g).erase v = {w})
    (hvh : v ∈ fg.scope h) (hfg : f ≠ g) (hgh : g ≠ h)
    (hNbrsW : FactorGraph.variableNeighborsFinset fg w = {f, g})
    (hNbrsV : FactorGraph.variableNeighborsFinset fg v = {g, h}) :
    ∀ x : fg.FullConfig,
      (runSyncRoundsIncident (fg := fg) 4 (initIncidentState (fg := fg))).varToFactor
          ⟨v, h, hvh⟩ (x v) =
        (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.sumOut
            (φ := twoFactorSubtreeFactor (fg := fg) f g u) w)).val x := by
  intro x
  have hBridge :
      (IncidentMessageState.toTotal (fg := fg)
        (runSyncRoundsIncident (fg := fg) 4 (initIncidentState (fg := fg)))).varToFactor v h (x v) =
      (runSyncRounds (fg := fg) 4
        (IncidentMessageState.toTotal (fg := fg) (initIncidentState (fg := fg)))).varToFactor
          v h (x v) :=
    congrArg (fun σ => σ.varToFactor v h (x v))
      (toTotal_runSyncRoundsIncident_eq_runSyncRounds_toTotal
        (fg := fg) (n := 4) (σ := initIncidentState (fg := fg)))
  calc
    (runSyncRoundsIncident (fg := fg) 4 (initIncidentState (fg := fg))).varToFactor
        ⟨v, h, hvh⟩ (x v)
        =
      (IncidentMessageState.toTotal (fg := fg)
        (runSyncRoundsIncident (fg := fg) 4 (initIncidentState (fg := fg)))).varToFactor
          v h (x v) := by
            simp [IncidentMessageState.toTotal, IncidentVarToFactorMsg.toTotal, hvh]
    _ = (runSyncRounds (fg := fg) 4
          (IncidentMessageState.toTotal (fg := fg) (initIncidentState (fg := fg)))).varToFactor
            v h (x v) := hBridge
    _ = (runSyncRounds (fg := fg) 4 (initState (fg := fg))).varToFactor v h (x v) := by
          simp [initIncidentState_toTotal]
    _ =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.sumOut
          (φ := twoFactorSubtreeFactor (fg := fg) f g u) w)).val x := by
          exact twoFactorSubtreeToParent_varMessage_exact
            (fg := fg) (f := f) (g := g) (h := h) (u := u) (w := w) (v := v)
            hwf hLeafF hvg hLeafG hvh hfg hgh hNbrsW hNbrsV x

/-- Generic recursive extension step: if the incoming message `v -> h` already
agrees with the valuation semantics of an exact subtree factor `ψ`, and `h` is
pairwise with variables `{z, v}`, then one more factor-to-variable step across
`h` is exactly `sumOut` of `ofGraph h * ψ` through the separator variable `v`.

This is the reusable semantic step behind longer tree exactness proofs. -/
theorem pairwiseLeaf_factorToVar_of_exactIncoming
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (μ : VarToFactorMsg fg) (h : fg.factors) (z v : V)
    (hzh : z ∈ fg.scope h) (hLeafH : (fg.scope h).erase z = {v})
    (ψ : VariableElimination.Factor (fg := fg))
    (hIncoming : ∀ x : fg.FullConfig,
      μ v h (x v) = (VariableElimination.Factor.toValuation (φ := ψ)).val x) :
    ∀ x : fg.FullConfig,
      factorToVarUpdate (fg := fg) μ h z hzh (x z) =
        (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.sumOut
            (φ := VariableElimination.Factor.mul (fg := fg)
              (VariableElimination.Factor.ofGraph (fg := fg) h) ψ)
            v)).val x := by
  intro x
  let χ : VariableElimination.Factor (fg := fg) :=
    VariableElimination.Factor.mul (fg := fg)
      (VariableElimination.Factor.ofGraph (fg := fg) h) ψ
  have hvh : v ∈ fg.scope h := by
    have hvErase : v ∈ (fg.scope h).erase z := by
      simp [hLeafH]
    exact (Finset.mem_erase.mp hvErase).2
  have hvz : v ≠ z := by
    have hvErase : v ∈ (fg.scope h).erase z := by
      simp [hLeafH]
    exact (Finset.mem_erase.mp hvErase).1
  have hLocal :=
    congrFun
      (pairwiseLeaf_localElimination_bridge
        (fg := fg) (μ := μ) (f := h) (v := z) (u := v) hzh hLeafH)
      (x z)
  have hPotentialH :
      ∀ x_v : fg.stateSpace v,
        (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.ofGraph (fg := fg) h)).val
            (Mettapedia.ProbabilityTheory.BayesianNetworks.update
              (V := V) (β := fun y => fg.stateSpace y) x v x_v) =
          fg.potential h
            (VariableElimination.Factor.extend
              (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) h)
              z hzh
              (singletonOtherScopeAssign (fg := fg) h z v hLeafH x_v)
              (x z)) := by
    intro x_v
    have hAssign :
        (fun y hy =>
          Mettapedia.ProbabilityTheory.BayesianNetworks.update
            (V := V) (β := fun t => fg.stateSpace t) x v x_v y) =
          VariableElimination.Factor.extend
            (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) h)
            z hzh
            (singletonOtherScopeAssign (fg := fg) h z v hLeafH x_v)
            (x z) := by
      funext y hy
      by_cases hyz : y = z
      · subst y
        have hzy : z ≠ v := Ne.symm hvz
        calc
          Mettapedia.ProbabilityTheory.BayesianNetworks.update
              (V := V) (β := fun t => fg.stateSpace t) x v x_v z
              = x z := by
                  simp [Mettapedia.ProbabilityTheory.BayesianNetworks.update, hzy]
          _ = VariableElimination.Factor.extend
                (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) h)
                z hzh
                (singletonOtherScopeAssign (fg := fg) h z v hLeafH x_v)
                (x z) z hzh := by
                  symm
                  simpa using
                    (VariableElimination.Factor.extend_apply_eq
                      (φ := VariableElimination.Factor.ofGraph (fg := fg) h)
                      (v := z) (hv := hzh)
                      (x := singletonOtherScopeAssign (fg := fg) h z v hLeafH x_v)
                      (val := x z))
      · have hyv : y = v := by
          have hyErase : y ∈ (fg.scope h).erase z := Finset.mem_erase.mpr ⟨hyz, hy⟩
          simpa [hLeafH] using hyErase
        subst y
        calc
          Mettapedia.ProbabilityTheory.BayesianNetworks.update
              (V := V) (β := fun t => fg.stateSpace t) x v x_v v
              = x_v := by
                  simp [Mettapedia.ProbabilityTheory.BayesianNetworks.update]
          _ = VariableElimination.Factor.extend
                (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) h)
                z hzh
                (singletonOtherScopeAssign (fg := fg) h z v hLeafH x_v)
                (x z) v hvh := by
                  symm
                  simpa [singletonOtherScopeAssign] using
                    (VariableElimination.Factor.extend_apply_ne
                      (φ := VariableElimination.Factor.ofGraph (fg := fg) h)
                      (v := z) (hv := hzh)
                      (x := singletonOtherScopeAssign (fg := fg) h z v hLeafH x_v)
                      (val := x z) (u := v) (hu := hvh) hvz)
    have := congrArg (fg.potential h) hAssign
    simpa [VariableElimination.Factor.toValuation, VariableElimination.Factor.ofGraph] using this
  have hCombine :
      ∀ x_v : fg.stateSpace v,
        (Mettapedia.ProbabilityTheory.BayesianNetworks.combine
          (φ := VariableElimination.Factor.toValuation
            (φ := VariableElimination.Factor.ofGraph (fg := fg) h))
          (ψ := VariableElimination.Factor.toValuation (φ := ψ))).val
            (Mettapedia.ProbabilityTheory.BayesianNetworks.update
              (V := V) (β := fun y => fg.stateSpace y) x v x_v) =
          fg.potential h
            (VariableElimination.Factor.extend
              (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) h)
              z hzh
              (singletonOtherScopeAssign (fg := fg) h z v hLeafH x_v)
              (x z)) *
          (VariableElimination.Factor.toValuation (φ := ψ)).val
            (Mettapedia.ProbabilityTheory.BayesianNetworks.update
              (V := V) (β := fun y => fg.stateSpace y) x v x_v) := by
    intro x_v
    simp [Mettapedia.ProbabilityTheory.BayesianNetworks.combine, hPotentialH x_v]
  have hMulVal :
      Mettapedia.ProbabilityTheory.BayesianNetworks.combine
        (φ := VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.ofGraph (fg := fg) h))
        (ψ := VariableElimination.Factor.toValuation (φ := ψ)) =
      VariableElimination.Factor.toValuation (φ := χ) := by
    simpa [χ] using
      (VariableElimination.Factor.toValuation_mul
        (φ := VariableElimination.Factor.ofGraph (fg := fg) h)
        (ψ := ψ)).symm
  calc
    factorToVarUpdate (fg := fg) μ h z hzh (x z)
        = ∑ x_v : fg.stateSpace v,
            fg.potential h
              (VariableElimination.Factor.extend
                (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) h)
                z hzh
                (singletonOtherScopeAssign (fg := fg) h z v hLeafH x_v)
                (x z)) *
              μ v h x_v := by
            simpa using! hLocal
    _ = ∑ x_v : fg.stateSpace v,
          fg.potential h
            (VariableElimination.Factor.extend
              (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) h)
              z hzh
              (singletonOtherScopeAssign (fg := fg) h z v hLeafH x_v)
              (x z)) *
            (VariableElimination.Factor.toValuation (φ := ψ)).val
              (Mettapedia.ProbabilityTheory.BayesianNetworks.update
                (V := V) (β := fun y => fg.stateSpace y) x v x_v) := by
          apply Fintype.sum_congr
          intro x_v
          have hProp :=
            hIncoming
              (Mettapedia.ProbabilityTheory.BayesianNetworks.update
                (V := V) (β := fun y => fg.stateSpace y) x v x_v)
          simpa [Mettapedia.ProbabilityTheory.BayesianNetworks.update] using
            congrArg
              (fun t =>
                fg.potential h
                  (VariableElimination.Factor.extend
                    (fg := fg) (φ := VariableElimination.Factor.ofGraph (fg := fg) h)
                    z hzh
                    (singletonOtherScopeAssign (fg := fg) h z v hLeafH x_v)
                    (x z)) * t)
              hProp
    _ = ∑ x_v : fg.stateSpace v,
          (Mettapedia.ProbabilityTheory.BayesianNetworks.combine
            (φ := VariableElimination.Factor.toValuation
              (φ := VariableElimination.Factor.ofGraph (fg := fg) h))
            (ψ := VariableElimination.Factor.toValuation (φ := ψ))).val
              (Mettapedia.ProbabilityTheory.BayesianNetworks.update
                (V := V) (β := fun y => fg.stateSpace y) x v x_v) := by
          apply Fintype.sum_congr
          intro x_v
          symm
          exact hCombine x_v
    _ =
      (Mettapedia.ProbabilityTheory.BayesianNetworks.sumOut
        (φ := Mettapedia.ProbabilityTheory.BayesianNetworks.combine
          (φ := VariableElimination.Factor.toValuation
            (φ := VariableElimination.Factor.ofGraph (fg := fg) h))
          (ψ := VariableElimination.Factor.toValuation (φ := ψ)))
        v).val x := by
          have hvCombine :
              v ∈
                (Mettapedia.ProbabilityTheory.BayesianNetworks.combine
                  (φ := VariableElimination.Factor.toValuation
                    (φ := VariableElimination.Factor.ofGraph (fg := fg) h))
                  (ψ := VariableElimination.Factor.toValuation (φ := ψ))).scope := by
            exact Finset.mem_union.mpr <| Or.inl <|
              (by
                simpa [VariableElimination.Factor.toValuation, VariableElimination.Factor.ofGraph] using hvh)
          symm
          simp [Mettapedia.ProbabilityTheory.BayesianNetworks.sumOut, hvCombine]
    _ =
      (Mettapedia.ProbabilityTheory.BayesianNetworks.sumOut
        (φ := VariableElimination.Factor.toValuation (φ := χ)) v).val x := by
          simp [hMulVal]
    _ =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.sumOut (φ := χ) v)).val x := by
          symm
          exact congrArg (fun η => η.val x)
            (VariableElimination.Factor.toValuation_sumOut (φ := χ) (v := v))
    _ =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.sumOut
          (φ := VariableElimination.Factor.mul (fg := fg)
            (VariableElimination.Factor.ofGraph (fg := fg) h) ψ)
          v)).val x := by
            rfl

/-- Base exact subtree object for the first leaf-to-parent variable message. -/
noncomputable def leafExactVarToFactorSubtree
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (f g : fg.factors) (u w : V)
    (hwf : w ∈ fg.scope f) (hLeafF : (fg.scope f).erase w = {u})
    (hwg : w ∈ fg.scope g) (hfg : f ≠ g)
    (hNbrs : FactorGraph.variableNeighborsFinset fg w = {f, g}) :
    ExactVarToFactorSubtree (fg := fg) w g where
  rounds := 2
  factor := leafEliminatedFactor (fg := fg) f u
  exact := leafToParent_varMessage_exact
    (fg := fg) (f := f) (g := g) (u := u) (w := w)
    hwf hLeafF hwg hfg hNbrs

/-- Promote an exact variable-to-factor subtree message across one pairwise
factor edge. -/
noncomputable def ExactVarToFactorSubtree.promoteAcrossPairwiseFactor
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    {v : V} {h : fg.factors}
    (T : ExactVarToFactorSubtree (fg := fg) v h)
    (z : V) (hzh : z ∈ fg.scope h) (hLeafH : (fg.scope h).erase z = {v}) :
    ExactFactorToVarSubtree (fg := fg) z h where
  rounds := T.rounds + 1
  factor :=
    VariableElimination.Factor.sumOut
      (φ := VariableElimination.Factor.mul (fg := fg)
        (VariableElimination.Factor.ofGraph (fg := fg) h) T.factor)
      v
  exact := by
    intro x
    let σ := runSyncRounds (fg := fg) T.rounds (initState (fg := fg))
    have hStep :=
      pairwiseLeaf_factorToVar_of_exactIncoming
        (fg := fg) (μ := σ.varToFactor) (h := h) (z := z) (v := v)
        hzh hLeafH T.factor (by
          intro y
          simpa [σ] using T.exact y)
    calc
      (runSyncRounds (fg := fg) (T.rounds + 1) (initState (fg := fg))).factorToVar z h (x z)
          = (syncRound (fg := fg) σ).factorToVar z h (x z) := by
              simpa [σ, runSyncRounds] using
                congrArg (fun st => st.factorToVar z h (x z))
                  (Function.iterate_succ_apply' (f := syncRound (fg := fg)) T.rounds
                    (initState (fg := fg)))
      _ = factorToVarUpdate (fg := fg) σ.varToFactor h z hzh (x z) := by
            simp [syncRound, hzh]
      _ = (VariableElimination.Factor.toValuation
            (φ := VariableElimination.Factor.sumOut
              (φ := VariableElimination.Factor.mul (fg := fg)
                (VariableElimination.Factor.ofGraph (fg := fg) h) T.factor)
              v)).val x := by
            simpa [σ] using hStep x

/-- Promote an exact factor-to-variable subtree message across one variable
edge with a unique incoming subtree on the other side. -/
noncomputable def ExactFactorToVarSubtree.promoteAcrossVariable
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    {v : V} {g : fg.factors}
    (T : ExactFactorToVarSubtree (fg := fg) v g)
    (h : fg.factors) (hvh : v ∈ fg.scope h)
    (hSingle : FactorGraph.otherFactorNeighbors fg v h = {g}) :
    ExactVarToFactorSubtree (fg := fg) v h where
  rounds := T.rounds + 1
  factor := T.factor
  exact := by
    intro x
    let σ := runSyncRounds (fg := fg) T.rounds (initState (fg := fg))
    have hStep :=
      varToFactor_of_exactIncomingFactor
        (fg := fg) (μ := σ.factorToVar) (v := v) (g := g) (h := h)
        hvh hSingle T.factor (by
          intro y
          simpa [σ] using T.exact y)
    calc
      (runSyncRounds (fg := fg) (T.rounds + 1) (initState (fg := fg))).varToFactor v h (x v)
          = (syncRound (fg := fg) σ).varToFactor v h (x v) := by
              simpa [σ, runSyncRounds] using
                congrArg (fun st => st.varToFactor v h (x v))
                  (Function.iterate_succ_apply' (f := syncRound (fg := fg)) T.rounds
                    (initState (fg := fg)))
      _ = varToFactorUpdate (fg := fg) σ.factorToVar v h hvh (x v) := by
            simp [syncRound, hvh]
      _ = (VariableElimination.Factor.toValuation (φ := T.factor)).val x := by
            simpa [σ] using hStep x

/-- Reusable recursive factor-message theorem: in
`u - f - w - g - v - h - z`, after five synchronous rounds from the neutral
state, the factor-to-variable message `h -> z` is exactly `sumOut` of the
three-factor subtree through the separator variable `v`. -/
theorem threeFactorSubtreeToParent_factorMessage_exact
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (f g h : fg.factors) (u w v z : V)
    (hwf : w ∈ fg.scope f) (hLeafF : (fg.scope f).erase w = {u})
    (hvg : v ∈ fg.scope g) (hLeafG : (fg.scope g).erase v = {w})
    (hzh : z ∈ fg.scope h) (hLeafH : (fg.scope h).erase z = {v})
    (hfg : f ≠ g) (hgh : g ≠ h)
    (hNbrsW : FactorGraph.variableNeighborsFinset fg w = {f, g})
    (hNbrsV : FactorGraph.variableNeighborsFinset fg v = {g, h}) :
    ∀ x : fg.FullConfig,
      (runSyncRounds (fg := fg) 5 (initState (fg := fg))).factorToVar z h (x z) =
        (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.sumOut
            (φ := threeFactorSubtreeFactor (fg := fg) f g h u w) v)).val x := by
  intro x
  have hvh : v ∈ fg.scope h := by
    have hvErase : v ∈ (fg.scope h).erase z := by
      simp [hLeafH]
    exact (Finset.mem_erase.mp hvErase).2
  have hwg : w ∈ fg.scope g := by
    have hwErase : w ∈ (fg.scope g).erase v := by
      simp [hLeafG]
    exact (Finset.mem_erase.mp hwErase).2
  have hSingleV :
      FactorGraph.otherFactorNeighbors fg v h = {g} :=
    otherFactorNeighbors_eq_singleton_of_variableNeighbors_pair
      (fg := fg) (w := v) (f := g) (g := h) hgh hNbrsV
  let T₀ : ExactVarToFactorSubtree (fg := fg) w g :=
    leafExactVarToFactorSubtree
      (fg := fg) (f := f) (g := g) (u := u) (w := w)
      hwf hLeafF hwg hfg hNbrsW
  let T₁ : ExactFactorToVarSubtree (fg := fg) v g :=
    ExactVarToFactorSubtree.promoteAcrossPairwiseFactor
      (fg := fg) T₀ v hvg hLeafG
  let T₂ : ExactVarToFactorSubtree (fg := fg) v h :=
    ExactFactorToVarSubtree.promoteAcrossVariable
      (fg := fg) T₁ h hvh hSingleV
  let T₃ : ExactFactorToVarSubtree (fg := fg) z h :=
    ExactVarToFactorSubtree.promoteAcrossPairwiseFactor
      (fg := fg) T₂ z hzh hLeafH
  have hRounds : T₃.rounds = 5 := by
    simp [T₀, T₁, T₂, T₃, leafExactVarToFactorSubtree,
      ExactVarToFactorSubtree.promoteAcrossPairwiseFactor,
      ExactFactorToVarSubtree.promoteAcrossVariable]
  have hFactor :
      T₃.factor =
        VariableElimination.Factor.sumOut
          (φ := threeFactorSubtreeFactor (fg := fg) f g h u w) v := by
    simp [T₀, T₁, T₂, T₃, leafExactVarToFactorSubtree,
      ExactVarToFactorSubtree.promoteAcrossPairwiseFactor,
      ExactFactorToVarSubtree.promoteAcrossVariable,
      leafEliminatedFactor, twoFactorSubtreeFactor, threeFactorSubtreeFactor]
  calc
    (runSyncRounds (fg := fg) 5 (initState (fg := fg))).factorToVar z h (x z)
        = (runSyncRounds (fg := fg) T₃.rounds (initState (fg := fg))).factorToVar z h (x z) := by
            simp [hRounds]
    _ = (VariableElimination.Factor.toValuation (φ := T₃.factor)).val x := by
          exact T₃.exact x
    _ =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.sumOut
          (φ := threeFactorSubtreeFactor (fg := fg) f g h u w) v)).val x := by
            simp [hFactor]

/-- If `u` has `f` as its only factor neighbor, then the synchronous
variable-to-factor message `u -> f` stays identically `1` at every round. -/
theorem runSyncRounds_varToFactor_eq_one_of_variableNeighbors_eq_singleton
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (u : V) (f : fg.factors) (huf : u ∈ fg.scope f)
    (hLeafU : FactorGraph.variableNeighborsFinset fg u = {f}) :
    ∀ rounds : Nat, ∀ x_u : fg.stateSpace u,
      (runSyncRounds (fg := fg) rounds (initState (fg := fg))).varToFactor u f x_u = 1 := by
  intro rounds x_u
  induction rounds with
  | zero =>
      simp [runSyncRounds, initState, unitVarToFactor]
  | succ n ih =>
      let σ := runSyncRounds (fg := fg) n (initState (fg := fg))
      calc
        (runSyncRounds (fg := fg) (n + 1) (initState (fg := fg))).varToFactor u f x_u
            = (syncRound (fg := fg) σ).varToFactor u f x_u := by
                simpa [σ, runSyncRounds] using
                  congrArg (fun st => st.varToFactor u f x_u)
                    (Function.iterate_succ_apply'
                      (f := syncRound (fg := fg)) n (initState (fg := fg)))
        _ = varToFactorUpdate (fg := fg) σ.factorToVar u f huf x_u := by
              simp [syncRound, huf]
        _ = 1 := by
              have hOne :=
                varToFactorUpdate_eq_one_of_variableNeighbors_eq_singleton
                  (fg := fg) (μ := σ.factorToVar) (v := u) (f := f) huf hLeafU
              simpa using congrFun hOne x_u

/-- Stable exact subtree packaged as a variable-to-factor message into a parent
factor: once the message becomes exact, it stays exact at every later round. -/
structure StableExactVarToFactorSubtree
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (v : V) (f : fg.factors) where
  readyAt : Nat
  factor : VariableElimination.Factor (fg := fg)
  exact_after :
    ∀ rounds : Nat, readyAt ≤ rounds → ∀ x : fg.FullConfig,
      (runSyncRounds (fg := fg) rounds (initState (fg := fg))).varToFactor v f (x v) =
        (VariableElimination.Factor.toValuation (φ := factor)).val x

/-- Stable exact subtree packaged as a factor-to-variable message into a parent
variable: once the message becomes exact, it stays exact at every later round. -/
structure StableExactFactorToVarSubtree
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (v : V) (f : fg.factors) where
  readyAt : Nat
  factor : VariableElimination.Factor (fg := fg)
  exact_after :
    ∀ rounds : Nat, readyAt ≤ rounds → ∀ x : fg.FullConfig,
      (runSyncRounds (fg := fg) rounds (initState (fg := fg))).factorToVar v f (x v) =
        (VariableElimination.Factor.toValuation (φ := factor)).val x

/-- Promote a stable exact variable-to-factor subtree message across one
pairwise factor edge. The result becomes exact one synchronous round later and
stays exact thereafter. -/
noncomputable def StableExactVarToFactorSubtree.promoteAcrossPairwiseFactor
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    {v : V} {h : fg.factors}
    (T : StableExactVarToFactorSubtree (fg := fg) v h)
    (z : V) (hzh : z ∈ fg.scope h) (hLeafH : (fg.scope h).erase z = {v}) :
    StableExactFactorToVarSubtree (fg := fg) z h where
  readyAt := T.readyAt + 1
  factor :=
    VariableElimination.Factor.sumOut
      (φ := VariableElimination.Factor.mul (fg := fg)
        (VariableElimination.Factor.ofGraph (fg := fg) h) T.factor)
      v
  exact_after := by
    intro rounds hReady x
    cases rounds with
    | zero =>
        cases hReady
    | succ n =>
        let σ := runSyncRounds (fg := fg) n (initState (fg := fg))
        have hReady' : T.readyAt ≤ n := Nat.le_of_succ_le_succ hReady
        have hStep :=
          pairwiseLeaf_factorToVar_of_exactIncoming
            (fg := fg) (μ := σ.varToFactor) (h := h) (z := z) (v := v)
            hzh hLeafH T.factor (by
              intro y
              simpa [σ] using T.exact_after n hReady' y)
        calc
          (runSyncRounds (fg := fg) (n + 1) (initState (fg := fg))).factorToVar z h (x z)
              = (syncRound (fg := fg) σ).factorToVar z h (x z) := by
                  simpa [σ, runSyncRounds] using
                    congrArg (fun st => st.factorToVar z h (x z))
                      (Function.iterate_succ_apply'
                        (f := syncRound (fg := fg)) n (initState (fg := fg)))
          _ = factorToVarUpdate (fg := fg) σ.varToFactor h z hzh (x z) := by
                simp [syncRound, hzh]
          _ = (VariableElimination.Factor.toValuation
                (φ := VariableElimination.Factor.sumOut
                  (φ := VariableElimination.Factor.mul (fg := fg)
                    (VariableElimination.Factor.ofGraph (fg := fg) h) T.factor)
                  v)).val x := by
                simpa [σ] using hStep x

/-- Promote a stable exact factor-to-variable subtree message across one
variable edge with a unique incoming subtree on the other side. The result
becomes exact one synchronous round later and stays exact thereafter. -/
noncomputable def StableExactFactorToVarSubtree.promoteAcrossVariable
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    {v : V} {g : fg.factors}
    (T : StableExactFactorToVarSubtree (fg := fg) v g)
    (h : fg.factors) (hvh : v ∈ fg.scope h)
    (hSingle : FactorGraph.otherFactorNeighbors fg v h = {g}) :
    StableExactVarToFactorSubtree (fg := fg) v h where
  readyAt := T.readyAt + 1
  factor := T.factor
  exact_after := by
    intro rounds hReady x
    cases rounds with
    | zero =>
        cases hReady
    | succ n =>
        let σ := runSyncRounds (fg := fg) n (initState (fg := fg))
        have hReady' : T.readyAt ≤ n := Nat.le_of_succ_le_succ hReady
        have hStep :=
          varToFactor_of_exactIncomingFactor
            (fg := fg) (μ := σ.factorToVar) (v := v) (g := g) (h := h)
            hvh hSingle T.factor (by
              intro y
              simpa [σ] using T.exact_after n hReady' y)
        calc
          (runSyncRounds (fg := fg) (n + 1) (initState (fg := fg))).varToFactor v h (x v)
              = (syncRound (fg := fg) σ).varToFactor v h (x v) := by
                  simpa [σ, runSyncRounds] using
                    congrArg (fun st => st.varToFactor v h (x v))
                      (Function.iterate_succ_apply'
                        (f := syncRound (fg := fg)) n (initState (fg := fg)))
          _ = varToFactorUpdate (fg := fg) σ.factorToVar v h hvh (x v) := by
                simp [syncRound, hvh]
          _ = (VariableElimination.Factor.toValuation (φ := T.factor)).val x := by
                simpa [σ] using hStep x

/-- Stable base factor-to-variable subtree for a pairwise leaf factor whose
other variable `u` is itself a leaf variable of the whole graph. -/
noncomputable def leafStableFactorToVarSubtree
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (f : fg.factors) (w u : V)
    (hwf : w ∈ fg.scope f) (hLeafF : (fg.scope f).erase w = {u})
    (hLeafU : FactorGraph.variableNeighborsFinset fg u = {f}) :
    StableExactFactorToVarSubtree (fg := fg) w f where
  readyAt := 1
  factor :=
    VariableElimination.Factor.sumOut
      (φ := VariableElimination.Factor.mul (fg := fg)
        (VariableElimination.Factor.ofGraph (fg := fg) f)
        (VariableElimination.oneFactor (fg := fg)))
      u
  exact_after := by
    intro rounds hReady x
    have huErase : u ∈ (fg.scope f).erase w := by
      simp [hLeafF]
    have huf : u ∈ fg.scope f := (Finset.mem_erase.mp huErase).2
    cases rounds with
    | zero =>
        cases hReady
    | succ n =>
        let σ := runSyncRounds (fg := fg) n (initState (fg := fg))
        have hIncoming :
            ∀ y : fg.FullConfig,
              σ.varToFactor u f (y u) =
                (VariableElimination.Factor.toValuation
                  (φ := VariableElimination.oneFactor (fg := fg))).val y := by
          intro y
          calc
            σ.varToFactor u f (y u) = 1 := by
              simpa [σ] using
                runSyncRounds_varToFactor_eq_one_of_variableNeighbors_eq_singleton
                  (fg := fg) (u := u) (f := f) huf hLeafU n (y u)
            _ =
              (VariableElimination.Factor.toValuation
                (φ := VariableElimination.oneFactor (fg := fg))).val y := by
                  simp [VariableElimination.Factor.toValuation, VariableElimination.oneFactor]
        have hStep :=
          pairwiseLeaf_factorToVar_of_exactIncoming
            (fg := fg) (μ := σ.varToFactor) (h := f) (z := w) (v := u)
            hwf hLeafF (VariableElimination.oneFactor (fg := fg)) hIncoming
        calc
          (runSyncRounds (fg := fg) (n + 1) (initState (fg := fg))).factorToVar w f (x w)
              = (syncRound (fg := fg) σ).factorToVar w f (x w) := by
                  simpa [σ, runSyncRounds] using
                    congrArg (fun st => st.factorToVar w f (x w))
                      (Function.iterate_succ_apply'
                        (f := syncRound (fg := fg)) n (initState (fg := fg)))
          _ = factorToVarUpdate (fg := fg) σ.varToFactor f w hwf (x w) := by
                simp [syncRound, hwf]
          _ = (VariableElimination.Factor.toValuation
                (φ := VariableElimination.Factor.sumOut
                  (φ := VariableElimination.Factor.mul (fg := fg)
                    (VariableElimination.Factor.ofGraph (fg := fg) f)
                    (VariableElimination.oneFactor (fg := fg)))
                  u)).val x := by
                simpa [σ] using hStep x

/-- Stable base variable-to-factor subtree for the first leaf-to-parent
propagation step in a genuine leaf chain. -/
noncomputable def leafStableVarToFactorSubtree
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (f g : fg.factors) (u w : V)
    (hwf : w ∈ fg.scope f) (hLeafF : (fg.scope f).erase w = {u})
    (hwg : w ∈ fg.scope g) (hfg : f ≠ g)
    (hNbrs : FactorGraph.variableNeighborsFinset fg w = {f, g})
    (hLeafU : FactorGraph.variableNeighborsFinset fg u = {f}) :
    StableExactVarToFactorSubtree (fg := fg) w g :=
  StableExactFactorToVarSubtree.promoteAcrossVariable
    (fg := fg)
    (T := leafStableFactorToVarSubtree
      (fg := fg) (f := f) (w := w) (u := u) hwf hLeafF hLeafU)
    g
    hwg
    (otherFactorNeighbors_eq_singleton_of_variableNeighbors_pair
      (fg := fg) (w := w) (f := f) (g := g) hfg hNbrs)

mutual

/-- Recursive stable attached subtree ending in a variable-to-factor message. -/
inductive StableAttachedVarToFactorTree
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K] :
    V → fg.factors → Sort _
  | promoteVariable
      {v : V} {g : fg.factors}
      (T : StableAttachedFactorToVarTree v g)
      (h : fg.factors) (hvh : v ∈ fg.scope h)
      (hSingle : FactorGraph.otherFactorNeighbors fg v h = {g}) :
      StableAttachedVarToFactorTree v h

/-- Recursive stable attached subtree ending in a factor-to-variable message. -/
inductive StableAttachedFactorToVarTree
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K] :
    V → fg.factors → Sort _
  | leaf
      (f : fg.factors) (w u : V)
      (hwf : w ∈ fg.scope f) (hLeafF : (fg.scope f).erase w = {u})
      (hLeafU : FactorGraph.variableNeighborsFinset fg u = {f}) :
      StableAttachedFactorToVarTree w f
  | promoteAcrossPairwise
      {v : V} {h : fg.factors}
      (T : StableAttachedVarToFactorTree v h)
      (z : V) (hzh : z ∈ fg.scope h) (hLeafH : (fg.scope h).erase z = {v}) :
      StableAttachedFactorToVarTree z h

end

mutual

/-- Interpret a recursive attached subtree as a stable exact variable-to-factor
message package. -/
noncomputable def StableAttachedVarToFactorTree.toStable
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    {v : V} {f : fg.factors}
    : StableAttachedVarToFactorTree v f → StableExactVarToFactorSubtree (fg := fg) v f
  | .promoteVariable T hParent hvh hSingle =>
      StableExactFactorToVarSubtree.promoteAcrossVariable
        (fg := fg) (T := T.toStable) hParent hvh hSingle

/-- Interpret a recursive attached subtree as a stable exact factor-to-variable
message package. -/
noncomputable def StableAttachedFactorToVarTree.toStable
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    {v : V} {f : fg.factors}
    : StableAttachedFactorToVarTree v f → StableExactFactorToVarSubtree (fg := fg) v f
  | .leaf fBase wBase uBase hwf hLeafF hLeafU =>
      leafStableFactorToVarSubtree
        (fg := fg) (f := fBase) (w := wBase) (u := uBase) hwf hLeafF hLeafU
  | .promoteAcrossPairwise T zChild hzh hLeafH =>
      StableExactVarToFactorSubtree.promoteAcrossPairwiseFactor
        (fg := fg) (T := T.toStable) zChild hzh hLeafH

end

/-- Readiness round of a recursive attached variable-to-factor subtree. -/
noncomputable def StableAttachedVarToFactorTree.readyAt
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    {v : V} {f : fg.factors}
    (T : StableAttachedVarToFactorTree v f) : Nat :=
  T.toStable.readyAt

/-- Exact eliminated factor carried by a recursive attached variable-to-factor
subtree. -/
noncomputable def StableAttachedVarToFactorTree.factor
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    {v : V} {f : fg.factors}
    (T : StableAttachedVarToFactorTree v f) :
    VariableElimination.Factor (fg := fg) :=
  T.toStable.factor

/-- Readiness round of a recursive attached factor-to-variable subtree. -/
noncomputable def StableAttachedFactorToVarTree.readyAt
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    {v : V} {f : fg.factors}
    (T : StableAttachedFactorToVarTree v f) : Nat :=
  T.toStable.readyAt

/-- Exact eliminated factor carried by a recursive attached factor-to-variable
subtree. -/
noncomputable def StableAttachedFactorToVarTree.factor
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    {v : V} {f : fg.factors}
    (T : StableAttachedFactorToVarTree v f) :
    VariableElimination.Factor (fg := fg) :=
  T.toStable.factor

/-- General upward-message exactness for recursive attached variable-to-factor
subtrees. -/
theorem StableAttachedVarToFactorTree.upwardMessage_exact
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    {v : V} {f : fg.factors}
    (T : StableAttachedVarToFactorTree v f) :
    ∀ rounds : Nat, T.readyAt ≤ rounds → ∀ x : fg.FullConfig,
      (runSyncRounds (fg := fg) rounds (initState (fg := fg))).varToFactor v f (x v) =
        (VariableElimination.Factor.toValuation (φ := T.factor)).val x := by
  intro rounds hReady x
  exact T.toStable.exact_after rounds hReady x

/-- General upward-message exactness for recursive attached factor-to-variable
subtrees. -/
theorem StableAttachedFactorToVarTree.upwardMessage_exact
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    {v : V} {f : fg.factors}
    (T : StableAttachedFactorToVarTree v f) :
    ∀ rounds : Nat, T.readyAt ≤ rounds → ∀ x : fg.FullConfig,
      (runSyncRounds (fg := fg) rounds (initState (fg := fg))).factorToVar v f (x v) =
        (VariableElimination.Factor.toValuation (φ := T.factor)).val x := by
  intro rounds hReady x
  exact T.toStable.exact_after rounds hReady x

end TreeSupport

end MessagePassing

end Mettapedia.ProbabilityTheory.BayesianNetworks
