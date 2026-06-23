import Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassingTreeSupport
import Mettapedia.ProbabilityTheory.BayesianNetworks.VEBridge

/-!
# First Belief-Exactness Theorems for Abstract Belief Propagation

This module upgrades the message-exactness spine to the first exactness results
for beliefs themselves on small tree fragments.
-/

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

open scoped Classical BigOperators

namespace MessagePassing

variable {V K : Type*} [DecidableEq V]

section BeliefExactness

variable {fg : FactorGraph V K}

/-- Incoming exact subtree factors for all factor neighbors of a variable node,
packed as a list in the neighbor finset order. -/
noncomputable def incomingFactorListAtVar
    [Fintype fg.factors]
    (v : V)
    (ψ : (f : {f : fg.factors // f ∈ FactorGraph.variableNeighborsFinset fg v}) →
      VariableElimination.Factor (fg := fg)) :
    List (VariableElimination.Factor (fg := fg)) :=
  ((FactorGraph.variableNeighborsFinset fg v).attach.toList.map ψ)

/-- Incoming exact subtree factors for all variables in a factor scope, packed
as a list in scope order. -/
noncomputable def incomingFactorListAtFactor
    (h : fg.factors)
    (ψ : (u : {u : V // u ∈ fg.scope h}) →
      VariableElimination.Factor (fg := fg)) :
    List (VariableElimination.Factor (fg := fg)) :=
  ((fg.scope h).attach.toList.map ψ)

/-- Extend a local assignment on the scope of `h` to a full configuration by
using `x` outside the scope. -/
noncomputable def extendScopeAssign
    (h : fg.factors) (x : fg.FullConfig)
    (a : VariableElimination.FactorGraph.Assign (fg := fg) (fg.scope h)) :
    fg.FullConfig :=
  fun v =>
    by
      classical
      by_cases hv : v ∈ fg.scope h
      · exact a v hv
      · exact x v

theorem restrictToScope_extendScopeAssign
    (h : fg.factors) (x : fg.FullConfig)
    (a : VariableElimination.FactorGraph.Assign (fg := fg) (fg.scope h)) :
    fg.restrictToScope h (extendScopeAssign (fg := fg) h x a) = a := by
  funext v
  funext hv
  simp [FactorGraph.restrictToScope, extendScopeAssign, hv]

/-- A canonical ambient full configuration, available when every variable state
space is nonempty. This is used only to package genuinely local factor-scope
values without threading an arbitrary ambient `x` through theorem statements. -/
noncomputable def arbitraryFullConfig
    [∀ v, Nonempty (fg.stateSpace v)] :
    fg.FullConfig :=
  fun v => Classical.choice (inferInstance : Nonempty (fg.stateSpace v))

/-- Evaluate a factor valuation on a local assignment to the scope of `h`,
using an arbitrary ambient configuration outside the scope. When an exactness
theorem identifies the valuation with a factor belief at `h`, this value is
independent of the chosen ambient extension. -/
noncomputable def localFactorValue
    [∀ v, Nonempty (fg.stateSpace v)]
    (h : fg.factors) (φ : VariableElimination.Factor (fg := fg)) :
    VariableElimination.FactorGraph.Assign (fg := fg) (fg.scope h) → K :=
  fun a =>
    (VariableElimination.Factor.toValuation (φ := φ)).val
      (extendScopeAssign (fg := fg) h (arbitraryFullConfig (fg := fg)) a)

private theorem scope_eq_pair_of_erase_eq_singleton
    (f : fg.factors) (v u : V)
    (hv : v ∈ fg.scope f) (hSingle : (fg.scope f).erase v = {u}) :
    fg.scope f = {v, u} := by
  ext x
  constructor
  · intro hx
    by_cases hxv : x = v
    · simp [hxv]
    · have hxErase : x ∈ (fg.scope f).erase v := Finset.mem_erase.mpr ⟨hxv, hx⟩
      have hxu : x = u := by simpa [hSingle] using hxErase
      simp [hxu]
  · intro hx
    simp at hx
    rcases hx with hx | hx
    · simpa [hx] using hv
    · subst x
      have huErase : u ∈ (fg.scope f).erase v := by
        rw [hSingle]
        simp
      exact (Finset.mem_erase.mp huErase).2

/-- Generic variable-belief exactness: if every incoming factor-to-variable
message at `v` already agrees with the valuation semantics of an exact subtree
factor, then the variable belief is exactly the valuation of the combined
incoming factor list. -/
theorem variableBelief_of_exactIncoming
    [Fintype fg.factors] [CommSemiring K]
    (μ : FactorToVarMsg fg) (v : V)
    (ψ : (f : {f : fg.factors // f ∈ FactorGraph.variableNeighborsFinset fg v}) →
      VariableElimination.Factor (fg := fg))
    (hIncoming : ∀ f : {f : fg.factors // f ∈ FactorGraph.variableNeighborsFinset fg v},
      ∀ x : fg.FullConfig,
        μ v f.1 (x v) = (VariableElimination.Factor.toValuation (φ := ψ f)).val x) :
    ∀ x : fg.FullConfig,
      variableBelief (fg := fg) μ v (x v) =
        (VariableElimination.Factor.toValuation
          (φ := VariableElimination.combineAll (fg := fg)
            (incomingFactorListAtVar (fg := fg) v ψ))).val x := by
  intro x
  have hProd :
      variableBelief (fg := fg) μ v (x v) =
        (((FactorGraph.variableNeighborsFinset fg v).attach.toList.map
          (fun f => μ v f.1 (x v))).prod) := by
    symm
    simpa [variableBelief] using
      (Finset.prod_map_toList
        (s := (FactorGraph.variableNeighborsFinset fg v).attach)
        (f := fun f => μ v f.1 (x v)))
  have hMap :
      ((FactorGraph.variableNeighborsFinset fg v).attach.toList.map
          (fun f => μ v f.1 (x v))) =
        ((incomingFactorListAtVar (fg := fg) v ψ).map
          (fun φ =>
            φ.potential
              (VariableElimination.FactorGraph.fullAssign (fg := fg) x φ.scope))) := by
    unfold incomingFactorListAtVar
    induction ((FactorGraph.variableNeighborsFinset fg v).attach.toList) with
    | nil =>
        rfl
    | cons f fs ih =>
        simp [ih]
        simpa [VariableElimination.Factor.toValuation] using! hIncoming f x
  have hCombine :
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.combineAll (fg := fg)
          (incomingFactorListAtVar (fg := fg) v ψ))).val x =
        ((incomingFactorListAtVar (fg := fg) v ψ).map
          (fun φ =>
            φ.potential
              (VariableElimination.FactorGraph.fullAssign (fg := fg) x φ.scope))).prod := by
    simpa [VariableElimination.Factor.toValuation] using!
      VariableElimination.combineAll_potential_fullAssign
        (fg := fg) (fs := incomingFactorListAtVar (fg := fg) v ψ) x
  calc
    variableBelief (fg := fg) μ v (x v)
        = (((FactorGraph.variableNeighborsFinset fg v).attach.toList.map
            (fun f => μ v f.1 (x v))).prod) := hProd
    _ = ((incomingFactorListAtVar (fg := fg) v ψ).map
          (fun φ =>
            φ.potential
              (VariableElimination.FactorGraph.fullAssign (fg := fg) x φ.scope))).prod := by
          simp [hMap]
    _ = (VariableElimination.Factor.toValuation
          (φ := VariableElimination.combineAll (fg := fg)
            (incomingFactorListAtVar (fg := fg) v ψ))).val x := by
          exact hCombine.symm

/-- Generic factor-belief exactness: if every incoming variable-to-factor
message at `h` already agrees with the valuation semantics of an exact subtree
factor, then the factor belief is exactly the valuation of the local factor
combined with all incoming subtree factors. -/
theorem factorBelief_of_exactIncoming
    [CommSemiring K]
    (μ : VarToFactorMsg fg) (h : fg.factors)
    (ψ : (u : {u : V // u ∈ fg.scope h}) →
      VariableElimination.Factor (fg := fg))
    (hIncoming : ∀ u : {u : V // u ∈ fg.scope h},
      ∀ x : fg.FullConfig,
        μ u.1 h (x u.1) = (VariableElimination.Factor.toValuation (φ := ψ u)).val x) :
    ∀ x : fg.FullConfig,
      factorBelief (fg := fg) μ h (fg.restrictToScope h x) =
        (VariableElimination.Factor.toValuation
          (φ := VariableElimination.combineAll (fg := fg)
            (VariableElimination.Factor.ofGraph (fg := fg) h ::
              incomingFactorListAtFactor (fg := fg) h ψ))).val x := by
  intro x
  have hProd :
      factorBelief (fg := fg) μ h (fg.restrictToScope h x) =
        fg.potential h (fg.restrictToScope h x) *
          (((fg.scope h).attach.toList.map fun u => μ u.1 h (x u.1)).prod) := by
    have hList :
        (∏ u ∈ (fg.scope h).attach, μ u.1 h ((fg.restrictToScope h x) u.1 u.2)) =
          (((fg.scope h).attach.toList.map fun u => μ u.1 h (x u.1)).prod) := by
      simpa [FactorGraph.restrictToScope] using
        (Finset.prod_map_toList
          (s := (fg.scope h).attach)
          (f := fun u => μ u.1 h (x u.1))).symm
    calc
      factorBelief (fg := fg) μ h (fg.restrictToScope h x)
          = fg.potential h (fg.restrictToScope h x) *
              ∏ u ∈ (fg.scope h).attach, μ u.1 h ((fg.restrictToScope h x) u.1 u.2) := by
                rfl
      _ = fg.potential h (fg.restrictToScope h x) *
            (((fg.scope h).attach.toList.map fun u => μ u.1 h (x u.1)).prod) := by
            rw [hList]
  have hMap :
      ((fg.scope h).attach.toList.map fun u => μ u.1 h (x u.1)) =
        ((incomingFactorListAtFactor (fg := fg) h ψ).map
          (fun φ =>
            φ.potential
              (VariableElimination.FactorGraph.fullAssign (fg := fg) x φ.scope))) := by
    unfold incomingFactorListAtFactor
    induction ((fg.scope h).attach.toList) with
    | nil =>
        rfl
    | cons u us ih =>
        simp [ih]
        simpa [VariableElimination.Factor.toValuation] using! hIncoming u x
  have hCombine :
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.combineAll (fg := fg)
          (VariableElimination.Factor.ofGraph (fg := fg) h ::
            incomingFactorListAtFactor (fg := fg) h ψ))).val x =
        ((VariableElimination.Factor.ofGraph (fg := fg) h ::
            incomingFactorListAtFactor (fg := fg) h ψ).map
          (fun φ =>
            φ.potential
              (VariableElimination.FactorGraph.fullAssign (fg := fg) x φ.scope))).prod := by
    simpa [VariableElimination.Factor.toValuation] using!
      VariableElimination.combineAll_potential_fullAssign
        (fg := fg)
        (fs := VariableElimination.Factor.ofGraph (fg := fg) h ::
          incomingFactorListAtFactor (fg := fg) h ψ)
        x
  calc
    factorBelief (fg := fg) μ h (fg.restrictToScope h x)
        = fg.potential h (fg.restrictToScope h x) *
            (((fg.scope h).attach.toList.map fun u => μ u.1 h (x u.1)).prod) := hProd
    _ = fg.potential h (fg.restrictToScope h x) *
          ((incomingFactorListAtFactor (fg := fg) h ψ).map
            (fun φ =>
              φ.potential
                (VariableElimination.FactorGraph.fullAssign (fg := fg) x φ.scope))).prod := by
          rw [hMap]
    _ = fg.potential h
          (VariableElimination.FactorGraph.fullAssign (fg := fg) x (fg.scope h)) *
          ((incomingFactorListAtFactor (fg := fg) h ψ).map
            (fun φ =>
              φ.potential
                (VariableElimination.FactorGraph.fullAssign (fg := fg) x φ.scope))).prod := by
          rfl
    _ = ((VariableElimination.Factor.ofGraph (fg := fg) h ::
          incomingFactorListAtFactor (fg := fg) h ψ).map
            (fun φ =>
              φ.potential
                (VariableElimination.FactorGraph.fullAssign (fg := fg) x φ.scope))).prod := by
          simp [VariableElimination.Factor.ofGraph]
    _ = (VariableElimination.Factor.toValuation
          (φ := VariableElimination.combineAll (fg := fg)
            (VariableElimination.Factor.ofGraph (fg := fg) h ::
              incomingFactorListAtFactor (fg := fg) h ψ))).val x := by
          exact hCombine.symm

/-- Generic variable-belief exactness from arbitrary stable exact incoming
factor-to-variable subtree messages. -/
theorem variableBelief_of_stableIncoming
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (rounds : Nat) (v : V)
    (T : (f : {f : fg.factors // f ∈ FactorGraph.variableNeighborsFinset fg v}) →
      StableExactFactorToVarSubtree (fg := fg) v f.1)
    (hReady : ∀ f, (T f).readyAt ≤ rounds) :
    ∀ x : fg.FullConfig,
      variableBelief
        (fg := fg)
        ((runSyncRounds (fg := fg) rounds (initState (fg := fg))).factorToVar)
        v
        (x v) =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.combineAll (fg := fg)
          (incomingFactorListAtVar (fg := fg) v (fun f => (T f).factor)))).val x := by
  intro x
  exact variableBelief_of_exactIncoming
    (fg := fg)
    (μ := (runSyncRounds (fg := fg) rounds (initState (fg := fg))).factorToVar)
    (v := v)
    (ψ := fun f => (T f).factor)
    (hIncoming := by
      intro f y
      exact (T f).exact_after rounds (hReady f) y)
    x

/-- Generic factor-belief exactness from arbitrary stable exact incoming
variable-to-factor subtree messages. -/
theorem factorBelief_of_stableIncoming
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (rounds : Nat) (h : fg.factors)
    (T : (u : {u : V // u ∈ fg.scope h}) →
      StableExactVarToFactorSubtree (fg := fg) u.1 h)
    (hReady : ∀ u, (T u).readyAt ≤ rounds) :
    ∀ x : fg.FullConfig,
      factorBelief
        (fg := fg)
        ((runSyncRounds (fg := fg) rounds (initState (fg := fg))).varToFactor)
        h
        (fg.restrictToScope h x) =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.combineAll (fg := fg)
          (VariableElimination.Factor.ofGraph (fg := fg) h ::
            incomingFactorListAtFactor (fg := fg) h (fun u => (T u).factor)))).val x := by
  intro x
  exact factorBelief_of_exactIncoming
    (fg := fg)
    (μ := (runSyncRounds (fg := fg) rounds (initState (fg := fg))).varToFactor)
    (h := h)
    (ψ := fun u => (T u).factor)
    (hIncoming := by
      intro u y
      exact (T u).exact_after rounds (hReady u) y)
    x

/-- Generic variable-belief exactness from arbitrary recursive attached
factor-to-variable subtrees. -/
theorem variableBelief_of_attachedIncoming
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (rounds : Nat) (v : V)
    (T : (f : {f : fg.factors // f ∈ FactorGraph.variableNeighborsFinset fg v}) →
      StableAttachedFactorToVarTree v f.1)
    (hReady : ∀ f, (T f).readyAt ≤ rounds) :
    ∀ x : fg.FullConfig,
      variableBelief
        (fg := fg)
        ((runSyncRounds (fg := fg) rounds (initState (fg := fg))).factorToVar)
        v
        (x v) =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.combineAll (fg := fg)
          (incomingFactorListAtVar (fg := fg) v (fun f => (T f).factor)))).val x := by
  intro x
  exact variableBelief_of_stableIncoming
    (fg := fg) (rounds := rounds) (v := v)
    (T := fun f => (T f).toStable)
    (hReady := fun f => hReady f)
    x

/-- Generic factor-belief exactness from arbitrary recursive attached
variable-to-factor subtrees. -/
theorem factorBelief_of_attachedIncoming
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (rounds : Nat) (h : fg.factors)
    (T : (u : {u : V // u ∈ fg.scope h}) →
      StableAttachedVarToFactorTree u.1 h)
    (hReady : ∀ u, (T u).readyAt ≤ rounds) :
    ∀ x : fg.FullConfig,
      factorBelief
        (fg := fg)
        ((runSyncRounds (fg := fg) rounds (initState (fg := fg))).varToFactor)
        h
        (fg.restrictToScope h x) =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.combineAll (fg := fg)
          (VariableElimination.Factor.ofGraph (fg := fg) h ::
            incomingFactorListAtFactor (fg := fg) h (fun u => (T u).factor)))).val x := by
  intro x
  exact factorBelief_of_stableIncoming
    (fg := fg) (rounds := rounds) (h := h)
    (T := fun u => (T u).toStable)
    (hReady := fun u => hReady u)
    x

/-- Incident-edge-indexed variable-belief exactness from arbitrary stable exact
incoming factor-to-variable subtree messages. This states the same result as
`variableBelief_of_stableIncoming`, but phrased against the schedule-layer
incident message state. -/
theorem variableBelief_of_stableIncoming_incident
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (rounds : Nat) (v : V)
    (T : (f : {f : fg.factors // f ∈ FactorGraph.variableNeighborsFinset fg v}) →
      StableExactFactorToVarSubtree (fg := fg) v f.1)
    (hReady : ∀ f, (T f).readyAt ≤ rounds) :
    ∀ x : fg.FullConfig,
      variableBelief
        (fg := fg)
        ((IncidentMessageState.toTotal (fg := fg)
          (runSyncRoundsIncident (fg := fg) rounds (initIncidentState (fg := fg)))).factorToVar)
        v
        (x v) =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.combineAll (fg := fg)
          (incomingFactorListAtVar (fg := fg) v (fun f => (T f).factor)))).val x := by
  intro x
  have hState :
      IncidentMessageState.toTotal (fg := fg)
        (runSyncRoundsIncident (fg := fg) rounds (initIncidentState (fg := fg))) =
      runSyncRounds (fg := fg) rounds (initState (fg := fg)) := by
    simpa [initIncidentState_toTotal] using
      toTotal_runSyncRoundsIncident_eq_runSyncRounds_toTotal
        (fg := fg) rounds (initIncidentState (fg := fg))
  have hFactor :
      (IncidentMessageState.toTotal (fg := fg)
        (runSyncRoundsIncident (fg := fg) rounds (initIncidentState (fg := fg)))).factorToVar =
      (runSyncRounds (fg := fg) rounds (initState (fg := fg))).factorToVar := by
    simpa using congrArg MessageState.factorToVar hState
  simpa [hFactor] using
    variableBelief_of_stableIncoming
      (fg := fg) (rounds := rounds) (v := v) (T := T) (hReady := hReady) x

/-- Incident-edge-indexed factor-belief exactness from arbitrary stable exact
incoming variable-to-factor subtree messages. -/
theorem factorBelief_of_stableIncoming_incident
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (rounds : Nat) (h : fg.factors)
    (T : (u : {u : V // u ∈ fg.scope h}) →
      StableExactVarToFactorSubtree (fg := fg) u.1 h)
    (hReady : ∀ u, (T u).readyAt ≤ rounds) :
    ∀ x : fg.FullConfig,
      factorBelief
        (fg := fg)
        ((IncidentMessageState.toTotal (fg := fg)
          (runSyncRoundsIncident (fg := fg) rounds (initIncidentState (fg := fg)))).varToFactor)
        h
        (fg.restrictToScope h x) =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.combineAll (fg := fg)
          (VariableElimination.Factor.ofGraph (fg := fg) h ::
            incomingFactorListAtFactor (fg := fg) h (fun u => (T u).factor)))).val x := by
  intro x
  have hState :
      IncidentMessageState.toTotal (fg := fg)
        (runSyncRoundsIncident (fg := fg) rounds (initIncidentState (fg := fg))) =
      runSyncRounds (fg := fg) rounds (initState (fg := fg)) := by
    simpa [initIncidentState_toTotal] using
      toTotal_runSyncRoundsIncident_eq_runSyncRounds_toTotal
        (fg := fg) rounds (initIncidentState (fg := fg))
  have hVar :
      (IncidentMessageState.toTotal (fg := fg)
        (runSyncRoundsIncident (fg := fg) rounds (initIncidentState (fg := fg)))).varToFactor =
      (runSyncRounds (fg := fg) rounds (initState (fg := fg))).varToFactor := by
    simpa using congrArg MessageState.varToFactor hState
  simpa [hVar] using
    factorBelief_of_stableIncoming
      (fg := fg) (rounds := rounds) (h := h) (T := T) (hReady := hReady) x

/-- Incident-edge-indexed variable-belief exactness from arbitrary recursive
attached factor-to-variable subtrees. -/
theorem variableBelief_of_attachedIncoming_incident
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (rounds : Nat) (v : V)
    (T : (f : {f : fg.factors // f ∈ FactorGraph.variableNeighborsFinset fg v}) →
      StableAttachedFactorToVarTree v f.1)
    (hReady : ∀ f, (T f).readyAt ≤ rounds) :
    ∀ x : fg.FullConfig,
      variableBelief
        (fg := fg)
        ((IncidentMessageState.toTotal (fg := fg)
          (runSyncRoundsIncident (fg := fg) rounds (initIncidentState (fg := fg)))).factorToVar)
        v
        (x v) =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.combineAll (fg := fg)
          (incomingFactorListAtVar (fg := fg) v (fun f => (T f).factor)))).val x := by
  intro x
  exact variableBelief_of_stableIncoming_incident
    (fg := fg) (rounds := rounds) (v := v)
    (T := fun f => (T f).toStable)
    (hReady := fun f => hReady f)
    x

/-- Incident-edge-indexed factor-belief exactness from arbitrary recursive
attached variable-to-factor subtrees. -/
theorem factorBelief_of_attachedIncoming_incident
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (rounds : Nat) (h : fg.factors)
    (T : (u : {u : V // u ∈ fg.scope h}) →
      StableAttachedVarToFactorTree u.1 h)
    (hReady : ∀ u, (T u).readyAt ≤ rounds) :
    ∀ x : fg.FullConfig,
      factorBelief
        (fg := fg)
        ((IncidentMessageState.toTotal (fg := fg)
          (runSyncRoundsIncident (fg := fg) rounds (initIncidentState (fg := fg)))).varToFactor)
        h
        (fg.restrictToScope h x) =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.combineAll (fg := fg)
          (VariableElimination.Factor.ofGraph (fg := fg) h ::
            incomingFactorListAtFactor (fg := fg) h (fun u => (T u).factor)))).val x := by
  intro x
  exact factorBelief_of_stableIncoming_incident
    (fg := fg) (rounds := rounds) (h := h)
    (T := fun u => (T u).toStable)
    (hReady := fun u => hReady u)
    x

/-- Normalized variable-belief corollary for recursive attached incoming
subtrees over the probability semiring. This states that once the incoming
subtrees are exact, the BP belief normalized over the states of `v` matches the
corresponding normalized exact local factor valuation. -/
theorem variableBelief_of_attachedIncoming_normalized
    {fgp : FactorGraph V ENNReal}
    [Fintype fgp.factors] [DecidableEq fgp.factors]
    [∀ v, Fintype (fgp.stateSpace v)]
    (rounds : Nat) (v : V)
    (T : (f : {f : fgp.factors // f ∈ FactorGraph.variableNeighborsFinset fgp v}) →
      StableAttachedFactorToVarTree (fg := fgp) v f.1)
    (hReady : ∀ f, (T f).readyAt ≤ rounds) :
    ∀ x : fgp.FullConfig,
      let μ := (runSyncRounds (fg := fgp) rounds (initState (fg := fgp))).factorToVar
      let φ := VariableElimination.combineAll (fg := fgp)
        (incomingFactorListAtVar (fg := fgp) v (fun f => (T f).factor))
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
  let μ := (runSyncRounds (fg := fgp) rounds (initState (fg := fgp))).factorToVar
  let φ := VariableElimination.combineAll (fg := fgp)
    (incomingFactorListAtVar (fg := fgp) v (fun f => (T f).factor))
  have hNum :
      variableBelief (fg := fgp) μ v (x v) =
        (VariableElimination.Factor.toValuation (φ := φ)).val x := by
    simpa [μ, φ] using
      variableBelief_of_attachedIncoming
        (fg := fgp) (rounds := rounds) (v := v) (T := T) (hReady := hReady) x
  have hPoint :
      ∀ val : fgp.stateSpace v,
        variableBelief (fg := fgp) μ v val =
          (VariableElimination.Factor.toValuation (φ := φ)).val
            (Mettapedia.ProbabilityTheory.BayesianNetworks.update
              (V := V) (β := fun u => fgp.stateSpace u) x v val) := by
    intro val
    simpa [μ, φ, Mettapedia.ProbabilityTheory.BayesianNetworks.update] using
      variableBelief_of_attachedIncoming
        (fg := fgp) (rounds := rounds) (v := v) (T := T) (hReady := hReady)
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
  simp [hNum, hDen, μ, φ]

/-- Incident-edge-indexed normalized variable-belief corollary for recursive
attached incoming subtrees over the probability semiring. -/
theorem variableBelief_of_attachedIncoming_normalized_incident
    {fgp : FactorGraph V ENNReal}
    [Fintype fgp.factors] [DecidableEq fgp.factors]
    [∀ v, Fintype (fgp.stateSpace v)]
    (rounds : Nat) (v : V)
    (T : (f : {f : fgp.factors // f ∈ FactorGraph.variableNeighborsFinset fgp v}) →
      StableAttachedFactorToVarTree (fg := fgp) v f.1)
    (hReady : ∀ f, (T f).readyAt ≤ rounds) :
    ∀ x : fgp.FullConfig,
      let μ := (IncidentMessageState.toTotal (fg := fgp)
        (runSyncRoundsIncident (fg := fgp) rounds (initIncidentState (fg := fgp)))).factorToVar
      let φ := VariableElimination.combineAll (fg := fgp)
        (incomingFactorListAtVar (fg := fgp) v (fun f => (T f).factor))
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
  have hFactor :
      (IncidentMessageState.toTotal (fg := fgp)
        (runSyncRoundsIncident (fg := fgp) rounds (initIncidentState (fg := fgp)))).factorToVar =
      (runSyncRounds (fg := fgp) rounds (initState (fg := fgp))).factorToVar := by
    have hState :=
      congrArg MessageState.factorToVar
        (toTotal_runSyncRoundsIncident_eq_runSyncRounds_toTotal
          (fg := fgp) rounds (initIncidentState (fg := fgp)))
    rw [initIncidentState_toTotal] at hState
    exact hState
  simpa [hFactor] using
    variableBelief_of_attachedIncoming_normalized
      (fgp := fgp) (rounds := rounds) (v := v) (T := T) (hReady := hReady) x

/-- Normalized factor-belief corollary for recursive attached incoming
subtrees over the probability semiring. The exact local factor is evaluated on
full configurations extending each scope assignment by a fixed ambient
configuration `x`. This keeps the statement honest without assuming extra scope
lemmas beyond the current exactness spine. -/
theorem factorBelief_of_attachedIncoming_normalized
    {fgp : FactorGraph V ENNReal}
    [Fintype fgp.factors] [DecidableEq fgp.factors]
    [∀ v, Fintype (fgp.stateSpace v)]
    (rounds : Nat) (h : fgp.factors)
    (T : (u : {u : V // u ∈ fgp.scope h}) →
      StableAttachedVarToFactorTree (fg := fgp) u.1 h)
    (hReady : ∀ u, (T u).readyAt ≤ rounds) :
    ∀ x : fgp.FullConfig,
      let μ := (runSyncRounds (fg := fgp) rounds (initState (fg := fgp))).varToFactor
      let φ := VariableElimination.combineAll (fg := fgp)
        (VariableElimination.Factor.ofGraph (fg := fgp) h ::
          incomingFactorListAtFactor (fg := fgp) h (fun u => (T u).factor))
      let exactAt :=
        fun a : VariableElimination.FactorGraph.Assign (fg := fgp) (fgp.scope h) =>
          (VariableElimination.Factor.toValuation (φ := φ)).val
            (extendScopeAssign (fg := fgp) h x a)
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
  let μ := (runSyncRounds (fg := fgp) rounds (initState (fg := fgp))).varToFactor
  let φ := VariableElimination.combineAll (fg := fgp)
    (VariableElimination.Factor.ofGraph (fg := fgp) h ::
      incomingFactorListAtFactor (fg := fgp) h (fun u => (T u).factor))
  let exactAt :=
    fun a : VariableElimination.FactorGraph.Assign (fg := fgp) (fgp.scope h) =>
      (VariableElimination.Factor.toValuation (φ := φ)).val
        (extendScopeAssign (fg := fgp) h x a)
  have hNum :
      factorBelief (fg := fgp) μ h (fgp.restrictToScope h x) =
        exactAt (fgp.restrictToScope h x) := by
    let xh := extendScopeAssign (fg := fgp) h x (fgp.restrictToScope h x)
    simpa [μ, φ, exactAt, xh, restrictToScope_extendScopeAssign] using
      factorBelief_of_attachedIncoming
        (fg := fgp) (rounds := rounds) (h := h) (T := T) (hReady := hReady) xh
  have hPoint :
      ∀ a : VariableElimination.FactorGraph.Assign (fg := fgp) (fgp.scope h),
        factorBelief (fg := fgp) μ h a = exactAt a := by
    intro a
    let xa := extendScopeAssign (fg := fgp) h x a
    simpa [μ, φ, exactAt, xa, restrictToScope_extendScopeAssign] using
      factorBelief_of_attachedIncoming
        (fg := fgp) (rounds := rounds) (h := h) (T := T) (hReady := hReady) xa
  have hDen :
      (∑ a : VariableElimination.FactorGraph.Assign (fg := fgp) (fgp.scope h),
          factorBelief (fg := fgp) μ h a) =
        ∑ a : VariableElimination.FactorGraph.Assign (fg := fgp) (fgp.scope h), exactAt a := by
    refine Finset.sum_congr rfl ?_
    intro a _
    exact hPoint a
  simp [hNum, hDen, μ, φ, exactAt]

/-- Incident-edge-indexed normalized factor-belief corollary for recursive
attached incoming subtrees over the probability semiring. -/
theorem factorBelief_of_attachedIncoming_normalized_incident
    {fgp : FactorGraph V ENNReal}
    [Fintype fgp.factors] [DecidableEq fgp.factors]
    [∀ v, Fintype (fgp.stateSpace v)]
    (rounds : Nat) (h : fgp.factors)
    (T : (u : {u : V // u ∈ fgp.scope h}) →
      StableAttachedVarToFactorTree (fg := fgp) u.1 h)
    (hReady : ∀ u, (T u).readyAt ≤ rounds) :
    ∀ x : fgp.FullConfig,
      let μ := (IncidentMessageState.toTotal (fg := fgp)
        (runSyncRoundsIncident (fg := fgp) rounds (initIncidentState (fg := fgp)))).varToFactor
      let φ := VariableElimination.combineAll (fg := fgp)
        (VariableElimination.Factor.ofGraph (fg := fgp) h ::
          incomingFactorListAtFactor (fg := fgp) h (fun u => (T u).factor))
      let exactAt :=
        fun a : VariableElimination.FactorGraph.Assign (fg := fgp) (fgp.scope h) =>
          (VariableElimination.Factor.toValuation (φ := φ)).val
            (extendScopeAssign (fg := fgp) h x a)
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
  have hVar :
      (IncidentMessageState.toTotal (fg := fgp)
        (runSyncRoundsIncident (fg := fgp) rounds (initIncidentState (fg := fgp)))).varToFactor =
      (runSyncRounds (fg := fgp) rounds (initState (fg := fgp))).varToFactor := by
    have hState :=
      congrArg MessageState.varToFactor
        (toTotal_runSyncRoundsIncident_eq_runSyncRounds_toTotal
          (fg := fgp) rounds (initIncidentState (fg := fgp)))
    rw [initIncidentState_toTotal] at hState
    exact hState
  simpa [hVar] using
    factorBelief_of_attachedIncoming_normalized
      (fgp := fgp) (rounds := rounds) (h := h) (T := T) (hReady := hReady) x

/-- Stronger normalized factor-belief corollary for recursive attached incoming
subtrees over the probability semiring, under nonempty state spaces. The exact
local factor family is packaged as a genuinely local function on assignments to
`scope h`, so the statement no longer depends on an ambient extension `x`
outside that scope. -/
theorem factorBelief_of_attachedIncoming_normalized_local
    {fgp : FactorGraph V ENNReal}
    [Fintype fgp.factors] [DecidableEq fgp.factors]
    [∀ v, Fintype (fgp.stateSpace v)] [∀ v, Nonempty (fgp.stateSpace v)]
    (rounds : Nat) (h : fgp.factors)
    (T : (u : {u : V // u ∈ fgp.scope h}) →
      StableAttachedVarToFactorTree (fg := fgp) u.1 h)
    (hReady : ∀ u, (T u).readyAt ≤ rounds) :
    ∀ x : fgp.FullConfig,
      let μ := (runSyncRounds (fg := fgp) rounds (initState (fg := fgp))).varToFactor
      let φ := VariableElimination.combineAll (fg := fgp)
        (VariableElimination.Factor.ofGraph (fg := fgp) h ::
          incomingFactorListAtFactor (fg := fgp) h (fun u => (T u).factor))
      let exactAt := localFactorValue (fg := fgp) h φ
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
  let μ := (runSyncRounds (fg := fgp) rounds (initState (fg := fgp))).varToFactor
  let φ := VariableElimination.combineAll (fg := fgp)
    (VariableElimination.Factor.ofGraph (fg := fgp) h ::
      incomingFactorListAtFactor (fg := fgp) h (fun u => (T u).factor))
  let exactAt := localFactorValue (fg := fgp) h φ
  have hPoint :
      ∀ a : VariableElimination.FactorGraph.Assign (fg := fgp) (fgp.scope h),
        factorBelief (fg := fgp) μ h a = exactAt a := by
    intro a
    let xa := extendScopeAssign
      (fg := fgp) h (arbitraryFullConfig (fg := fgp)) a
    simpa [μ, φ, exactAt, xa, localFactorValue, arbitraryFullConfig,
      restrictToScope_extendScopeAssign] using
      factorBelief_of_attachedIncoming
        (fg := fgp) (rounds := rounds) (h := h) (T := T) (hReady := hReady) xa
  have hNum :
      factorBelief (fg := fgp) μ h (fgp.restrictToScope h x) =
        exactAt (fgp.restrictToScope h x) := by
    exact hPoint (fgp.restrictToScope h x)
  have hDen :
      (∑ a : VariableElimination.FactorGraph.Assign (fg := fgp) (fgp.scope h),
          factorBelief (fg := fgp) μ h a) =
        ∑ a : VariableElimination.FactorGraph.Assign (fg := fgp) (fgp.scope h), exactAt a := by
    refine Finset.sum_congr rfl ?_
    intro a _
    exact hPoint a
  simp [hNum, hDen, μ, φ, exactAt]

/-- Incident-edge-indexed version of
`factorBelief_of_attachedIncoming_normalized_local`. -/
theorem factorBelief_of_attachedIncoming_normalized_incident_local
    {fgp : FactorGraph V ENNReal}
    [Fintype fgp.factors] [DecidableEq fgp.factors]
    [∀ v, Fintype (fgp.stateSpace v)] [∀ v, Nonempty (fgp.stateSpace v)]
    (rounds : Nat) (h : fgp.factors)
    (T : (u : {u : V // u ∈ fgp.scope h}) →
      StableAttachedVarToFactorTree (fg := fgp) u.1 h)
    (hReady : ∀ u, (T u).readyAt ≤ rounds) :
    ∀ x : fgp.FullConfig,
      let μ := (IncidentMessageState.toTotal (fg := fgp)
        (runSyncRoundsIncident (fg := fgp) rounds (initIncidentState (fg := fgp)))).varToFactor
      let φ := VariableElimination.combineAll (fg := fgp)
        (VariableElimination.Factor.ofGraph (fg := fgp) h ::
          incomingFactorListAtFactor (fg := fgp) h (fun u => (T u).factor))
      let exactAt := localFactorValue (fg := fgp) h φ
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
  have hVar :
      (IncidentMessageState.toTotal (fg := fgp)
        (runSyncRoundsIncident (fg := fgp) rounds (initIncidentState (fg := fgp)))).varToFactor =
      (runSyncRounds (fg := fgp) rounds (initState (fg := fgp))).varToFactor := by
    have hState :=
      congrArg MessageState.varToFactor
        (toTotal_runSyncRoundsIncident_eq_runSyncRounds_toTotal
          (fg := fgp) rounds (initIncidentState (fg := fgp)))
    rw [initIncidentState_toTotal] at hState
    exact hState
  simpa [hVar] using
    factorBelief_of_attachedIncoming_normalized_local
      (fgp := fgp) (rounds := rounds) (h := h) (T := T) (hReady := hReady) x

/-- Local pairwise factor-belief exactness: if a pairwise factor `h` has scope
`{z, v}` and the two incoming variable-to-factor messages already agree with
exact subtree factors `ψ` and `χ`, then the factor belief at `h` is exactly the
valuation semantics of `ofGraph h * ψ * χ`. -/
theorem pairwiseFactorBelief_of_exactIncoming
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (μ : VarToFactorMsg fg) (h : fg.factors) (v z : V)
    (hzh : z ∈ fg.scope h) (hPair : (fg.scope h).erase z = {v})
    (ψ χ : VariableElimination.Factor (fg := fg))
    (hV : ∀ x : fg.FullConfig,
      μ v h (x v) = (VariableElimination.Factor.toValuation (φ := ψ)).val x)
    (hZ : ∀ x : fg.FullConfig,
      μ z h (x z) = (VariableElimination.Factor.toValuation (φ := χ)).val x) :
    ∀ x : fg.FullConfig,
      factorBelief (fg := fg) μ h (fg.restrictToScope h x) =
        (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.mul (fg := fg)
            (VariableElimination.Factor.mul (fg := fg)
              (VariableElimination.Factor.ofGraph (fg := fg) h) ψ)
            χ)).val x := by
  intro x
  have hvh : v ∈ fg.scope h := by
    have hvErase : v ∈ (fg.scope h).erase z := by simp [hPair]
    exact (Finset.mem_erase.mp hvErase).2
  have hScope : fg.scope h = {z, v} := by
    exact scope_eq_pair_of_erase_eq_singleton (fg := fg) h z v hzh hPair
  have hzv : z ≠ v := by
    have hvErase : v ∈ (fg.scope h).erase z := by simp [hPair]
    exact (Finset.mem_erase.mp hvErase).1 |> Ne.symm
  have hBel :
      factorBelief (fg := fg) μ h (fg.restrictToScope h x) =
        fg.potential h (fg.restrictToScope h x) *
          (μ v h (x v) * μ z h (x z)) := by
    have hAttach :
        (fg.scope h).attach = {⟨v, hvh⟩, ⟨z, hzh⟩} := by
      ext a
      constructor
      · intro ha
        have ha' : a.1 = z ∨ a.1 = v := by
          simpa [hScope] using a.2
        rcases ha' with rfl | rfl <;> simp
      · intro ha
        rcases Finset.mem_insert.mp ha with hEq | hEq
        · subst hEq
          simp
        · simp at hEq
          subst hEq
          simp
    rw [factorBelief, hAttach, Finset.prod_insert]
    · rw [Finset.prod_singleton]
      simp [FactorGraph.restrictToScope]
    · intro hEq
      simp at hEq
      exact hzv hEq.symm
  have hMul1 :
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.mul (fg := fg)
          (VariableElimination.Factor.ofGraph (fg := fg) h)
          ψ)).val x =
        fg.potential h (fg.restrictToScope h x) *
          (VariableElimination.Factor.toValuation
            (φ := ψ)).val x := by
    simpa [VariableElimination.Factor.ofGraph] using! congrArg
      (fun η => η.val x)
      (VariableElimination.Factor.toValuation_mul
        (φ := VariableElimination.Factor.ofGraph (fg := fg) h)
        (ψ := ψ))
  have hMul2 :
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.mul (fg := fg)
          (VariableElimination.Factor.mul (fg := fg)
            (VariableElimination.Factor.ofGraph (fg := fg) h) ψ)
          χ)).val x =
        (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.mul (fg := fg)
            (VariableElimination.Factor.ofGraph (fg := fg) h)
            ψ)).val x *
        (VariableElimination.Factor.toValuation
          (φ := χ)).val x := by
    simpa using! congrArg
      (fun η => η.val x)
      (VariableElimination.Factor.toValuation_mul
        (φ := VariableElimination.Factor.mul (fg := fg)
          (VariableElimination.Factor.ofGraph (fg := fg) h) ψ)
        (ψ := χ))
  calc
    factorBelief (fg := fg) μ h (fg.restrictToScope h x)
        = fg.potential h (fg.restrictToScope h x) * (μ v h (x v) * μ z h (x z)) := hBel
    _ = fg.potential h (fg.restrictToScope h x) *
        ((VariableElimination.Factor.toValuation (φ := ψ)).val x *
         (VariableElimination.Factor.toValuation (φ := χ)).val x) := by
          rw [hV x, hZ x]
    _ = fg.potential h (fg.restrictToScope h x) *
        (VariableElimination.Factor.toValuation (φ := ψ)).val x *
        (VariableElimination.Factor.toValuation (φ := χ)).val x := by
          ring
    _ = (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.mul (fg := fg)
            (VariableElimination.Factor.ofGraph (fg := fg) h)
            ψ)).val x *
        (VariableElimination.Factor.toValuation (φ := χ)).val x := by
          rw [← hMul1]
    _ = (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.mul (fg := fg)
            (VariableElimination.Factor.mul (fg := fg)
              (VariableElimination.Factor.ofGraph (fg := fg) h) ψ)
            χ)).val x := by
          exact hMul2.symm

/-- Once two incoming stable exact factor-to-variable subtree messages at a
variable node `v` are both past their readiness rounds, the variable belief is
exactly the product of their subtree factors. -/
theorem twoStableIncoming_variableBelief_exact
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (rounds : Nat) (v : V) (f g : fg.factors)
    (hNbrs : FactorGraph.variableNeighborsFinset fg v = {f, g})
    (hfg : f ≠ g)
    (Tf : StableExactFactorToVarSubtree v f)
    (Tg : StableExactFactorToVarSubtree v g)
    (hTf : Tf.readyAt ≤ rounds) (hTg : Tg.readyAt ≤ rounds) :
    ∀ x : fg.FullConfig,
      variableBelief
        (fg := fg)
        ((runSyncRounds (fg := fg) rounds (initState (fg := fg))).factorToVar)
        v
        (x v) =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.mul (fg := fg) Tf.factor Tg.factor)).val x := by
  intro x
  have hfMem : f ∈ FactorGraph.variableNeighborsFinset fg v := by
    simp [hNbrs]
  have hgMem : g ∈ FactorGraph.variableNeighborsFinset fg v := by
    simp [hNbrs]
  have hvf : v ∈ fg.scope f :=
    (FactorGraph.mem_variableNeighborsFinset_iff (fg := fg) v f).mp hfMem
  have hvg : v ∈ fg.scope g :=
    (FactorGraph.mem_variableNeighborsFinset_iff (fg := fg) v g).mp hgMem
  have hAttach :
      (FactorGraph.variableNeighborsFinset fg v).attach = {⟨f, hfMem⟩, ⟨g, hgMem⟩} := by
    ext a
    constructor
    · intro ha
      have ha' : a.1 = f ∨ a.1 = g := by
        simpa [hNbrs] using a.2
      rcases ha' with rfl | rfl <;> simp
    · intro ha
      rcases Finset.mem_insert.mp ha with hEq | hEq
      · subst hEq
        simp
      · simp at hEq
        subst hEq
        simp
  have hBel :
      variableBelief
        (fg := fg)
        ((runSyncRounds (fg := fg) rounds (initState (fg := fg))).factorToVar)
        v
        (x v) =
      (runSyncRounds (fg := fg) rounds (initState (fg := fg))).factorToVar v f (x v) *
      (runSyncRounds (fg := fg) rounds (initState (fg := fg))).factorToVar v g (x v) := by
    rw [variableBelief, hAttach, Finset.prod_insert]
    · simp
    · intro hEq
      simp at hEq
      exact hfg hEq
  have hMul :
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.mul (fg := fg) Tf.factor Tg.factor)).val x =
      (VariableElimination.Factor.toValuation (φ := Tf.factor)).val x *
      (VariableElimination.Factor.toValuation (φ := Tg.factor)).val x := by
    simpa using! congrArg
      (fun η => η.val x)
      (VariableElimination.Factor.toValuation_mul
        (φ := Tf.factor) (ψ := Tg.factor))
  calc
    variableBelief
        (fg := fg)
        ((runSyncRounds (fg := fg) rounds (initState (fg := fg))).factorToVar)
        v
        (x v)
        =
      (runSyncRounds (fg := fg) rounds (initState (fg := fg))).factorToVar v f (x v) *
      (runSyncRounds (fg := fg) rounds (initState (fg := fg))).factorToVar v g (x v) := hBel
    _ =
      (VariableElimination.Factor.toValuation (φ := Tf.factor)).val x *
      (VariableElimination.Factor.toValuation (φ := Tg.factor)).val x := by
        rw [Tf.exact_after rounds hTf x, Tg.exact_after rounds hTg x]
    _ =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.mul (fg := fg) Tf.factor Tg.factor)).val x := by
          exact hMul.symm

/-- Once two incoming stable exact variable-to-factor subtree messages at a
pairwise factor node are both past their readiness rounds, the factor belief is
exactly the product of the local factor with those two subtree factors. -/
theorem pairwiseFactorBelief_of_stableIncoming
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (rounds : Nat) (h : fg.factors) (v z : V)
    (hzh : z ∈ fg.scope h) (hPair : (fg.scope h).erase z = {v})
    (Tv : StableExactVarToFactorSubtree v h)
    (Tz : StableExactVarToFactorSubtree z h)
    (hTv : Tv.readyAt ≤ rounds) (hTz : Tz.readyAt ≤ rounds) :
    ∀ x : fg.FullConfig,
      factorBelief
        (fg := fg)
        ((runSyncRounds (fg := fg) rounds (initState (fg := fg))).varToFactor)
        h
        (fg.restrictToScope h x) =
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.mul (fg := fg)
          (VariableElimination.Factor.mul (fg := fg)
            (VariableElimination.Factor.ofGraph (fg := fg) h)
            Tv.factor)
          Tz.factor)).val x := by
  intro x
  exact pairwiseFactorBelief_of_exactIncoming
    (fg := fg)
    (μ := (runSyncRounds (fg := fg) rounds (initState (fg := fg))).varToFactor)
    (h := h) (v := v) (z := z) hzh hPair Tv.factor Tz.factor
    (fun y => Tv.exact_after rounds hTv y)
    (fun y => Tz.exact_after rounds hTz y)
    x

/-- Exact variable belief on the smallest nontrivial fork-shaped tree fragment:
if `v` has exactly two pairwise leaf factors `f` and `g`, then after one
synchronous round from the neutral state, the variable belief at `v` is exactly
the product of the two eliminated leaf factors. -/
theorem twoLeaf_variableBelief_exact
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
          (leafEliminatedFactor (fg := fg) g w))).val x := by
  intro x
  let σ₁ := runSyncRounds (fg := fg) 1 (initState (fg := fg))
  have hF :=
    pairwiseFactor_syncRound_init_exact
      (fg := fg) (f := f) (v := v) (u := u) hvf hLeafF x
  have hG :=
    pairwiseFactor_syncRound_init_exact
      (fg := fg) (f := g) (v := v) (u := w) hvg hLeafG x
  have hBel :
      variableBelief (fg := fg) σ₁.factorToVar v (x v) =
        σ₁.factorToVar v f (x v) * σ₁.factorToVar v g (x v) := by
    have hfmem : f ∈ FactorGraph.variableNeighborsFinset fg v := by
      rw [hNbrs]
      simp
    have hgmem : g ∈ FactorGraph.variableNeighborsFinset fg v := by
      rw [hNbrs]
      simp
    have hAttach :
        (FactorGraph.variableNeighborsFinset fg v).attach =
          {⟨f, hfmem⟩, ⟨g, hgmem⟩} := by
      ext a
      constructor
      · intro ha
        have ha' : a.1 = f ∨ a.1 = g := by
          simpa [hNbrs] using a.2
        rcases ha' with rfl | rfl <;> simp
      · intro ha
        rcases Finset.mem_insert.mp ha with h | h
        · subst h
          simp
        · simp at h
          subst h
          simp
    rw [variableBelief, hAttach, Finset.prod_insert]
    · rw [Finset.prod_singleton]
    · simp [Subtype.mk.injEq, hfg]
  have hF' :
      σ₁.factorToVar v f (x v) =
        (VariableElimination.Factor.toValuation
          (φ := leafEliminatedFactor (fg := fg) f u)).val x := by
    simpa [σ₁, runSyncRounds, leafEliminatedFactor] using hF.symm
  have hG' :
      σ₁.factorToVar v g (x v) =
        (VariableElimination.Factor.toValuation
          (φ := leafEliminatedFactor (fg := fg) g w)).val x := by
    simpa [σ₁, runSyncRounds, leafEliminatedFactor] using hG.symm
  have hMul :
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.mul (fg := fg)
          (leafEliminatedFactor (fg := fg) f u)
          (leafEliminatedFactor (fg := fg) g w))).val x =
        (VariableElimination.Factor.toValuation
          (φ := leafEliminatedFactor (fg := fg) f u)).val x *
        (VariableElimination.Factor.toValuation
          (φ := leafEliminatedFactor (fg := fg) g w)).val x := by
    simpa using! congrArg
      (fun ψ => ψ.val x)
      (VariableElimination.Factor.toValuation_mul
        (φ := leafEliminatedFactor (fg := fg) f u)
        (ψ := leafEliminatedFactor (fg := fg) g w))
  calc
    variableBelief
        (fg := fg)
        ((runSyncRounds (fg := fg) 1 (initState (fg := fg))).factorToVar)
        v
        (x v)
        = σ₁.factorToVar v f (x v) * σ₁.factorToVar v g (x v) := hBel
    _ = (VariableElimination.Factor.toValuation
          (φ := leafEliminatedFactor (fg := fg) f u)).val x *
        (VariableElimination.Factor.toValuation
          (φ := leafEliminatedFactor (fg := fg) g w)).val x := by
          rw [hF', hG']
    _ = (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.mul (fg := fg)
            (leafEliminatedFactor (fg := fg) f u)
            (leafEliminatedFactor (fg := fg) g w))).val x := by
          exact hMul.symm

/-- Exact factor belief on the smallest nontrivial two-sided tree fragment: if
the pairwise factor `g` has one leaf subtree on each side, then after two
synchronous rounds from the neutral state, the factor belief at `g` is exactly
the product of the local factor with the two eliminated leaf factors. -/
theorem twoSidedLeaf_factorBelief_exact
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
          (leafEliminatedFactor (fg := fg) h z))).val x := by
  intro x
  let σ₂ := runSyncRounds (fg := fg) 2 (initState (fg := fg))
  have hwg : w ∈ fg.scope g := by
    have hwErase : w ∈ (fg.scope g).erase v := by simp [hPairG]
    exact (Finset.mem_erase.mp hwErase).2
  have hwg_scope : fg.scope g = {v, w} := by
    exact scope_eq_pair_of_erase_eq_singleton (fg := fg) g v w hvg hPairG
  have hvg' : v ∈ fg.scope g := hvg
  have hLeft :=
    twoFactorChain_varToFactor_twoRounds_exact
      (fg := fg) (f := f) (g := g) (u := u) (w := w)
      hwf hLeafF hwg hfg hNbrsW x
  have hRight :=
    twoFactorChain_varToFactor_twoRounds_exact
      (fg := fg) (f := h) (g := g) (u := z) (w := v)
      hvh hLeafH hvg' hgh hNbrsV x
  have hBel :
      factorBelief (fg := fg) σ₂.varToFactor g (fg.restrictToScope g x) =
        fg.potential g (fg.restrictToScope g x) *
          (σ₂.varToFactor w g (x w) * σ₂.varToFactor v g (x v)) := by
    have hwmem : w ∈ fg.scope g := hwg
    have hvmem : v ∈ fg.scope g := hvg
    have hwv : w ≠ v := by
      have hwErase : w ∈ (fg.scope g).erase v := by simp [hPairG]
      exact (Finset.mem_erase.mp hwErase).1
    have hAttach :
        (fg.scope g).attach = {⟨w, hwmem⟩, ⟨v, hvmem⟩} := by
      ext a
      constructor
      · intro ha
        have ha' : a.1 = v ∨ a.1 = w := by
          simpa [hwg_scope] using a.2
        rcases ha' with rfl | rfl <;> simp
      · intro ha
        rcases Finset.mem_insert.mp ha with h | h
        · subst h
          simp
        · simp at h
          subst h
          simp
    rw [factorBelief, hAttach, Finset.prod_insert]
    · rw [Finset.prod_singleton]
      simp [FactorGraph.restrictToScope]
    · simp [hwv]
  have hMul1 :
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.mul (fg := fg)
          (VariableElimination.Factor.ofGraph (fg := fg) g)
          (leafEliminatedFactor (fg := fg) f u))).val x =
        fg.potential g (fg.restrictToScope g x) *
          (VariableElimination.Factor.toValuation
            (φ := leafEliminatedFactor (fg := fg) f u)).val x := by
    simpa [VariableElimination.Factor.ofGraph] using! congrArg
      (fun ψ => ψ.val x)
      (VariableElimination.Factor.toValuation_mul
        (φ := VariableElimination.Factor.ofGraph (fg := fg) g)
        (ψ := leafEliminatedFactor (fg := fg) f u))
  have hMul2 :
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.mul (fg := fg)
          (VariableElimination.Factor.mul (fg := fg)
            (VariableElimination.Factor.ofGraph (fg := fg) g)
            (leafEliminatedFactor (fg := fg) f u))
          (leafEliminatedFactor (fg := fg) h z))).val x =
        (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.mul (fg := fg)
            (VariableElimination.Factor.ofGraph (fg := fg) g)
            (leafEliminatedFactor (fg := fg) f u))).val x *
        (VariableElimination.Factor.toValuation
          (φ := leafEliminatedFactor (fg := fg) h z)).val x := by
    simpa using! congrArg
      (fun ψ => ψ.val x)
      (VariableElimination.Factor.toValuation_mul
        (φ := VariableElimination.Factor.mul (fg := fg)
          (VariableElimination.Factor.ofGraph (fg := fg) g)
          (leafEliminatedFactor (fg := fg) f u))
        (ψ := leafEliminatedFactor (fg := fg) h z))
  calc
    factorBelief
        (fg := fg)
        ((runSyncRounds (fg := fg) 2 (initState (fg := fg))).varToFactor)
        g
        (fg.restrictToScope g x)
        =
      fg.potential g (fg.restrictToScope g x) *
        (σ₂.varToFactor w g (x w) * σ₂.varToFactor v g (x v)) := hBel
    _ = fg.potential g (fg.restrictToScope g x) *
        ((VariableElimination.Factor.toValuation
          (φ := leafEliminatedFactor (fg := fg) f u)).val x *
         (VariableElimination.Factor.toValuation
          (φ := leafEliminatedFactor (fg := fg) h z)).val x) := by
          rw [hLeft, hRight]
          simp [leafEliminatedFactor]
    _ = fg.potential g (fg.restrictToScope g x) *
        (VariableElimination.Factor.toValuation
          (φ := leafEliminatedFactor (fg := fg) f u)).val x *
        (VariableElimination.Factor.toValuation
          (φ := leafEliminatedFactor (fg := fg) h z)).val x := by
          ring
    _ = (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.mul (fg := fg)
            (VariableElimination.Factor.ofGraph (fg := fg) g)
            (leafEliminatedFactor (fg := fg) f u))).val x *
        (VariableElimination.Factor.toValuation
          (φ := leafEliminatedFactor (fg := fg) h z)).val x := by
          rw [← hMul1]
    _ = (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.mul (fg := fg)
            (VariableElimination.Factor.mul (fg := fg)
              (VariableElimination.Factor.ofGraph (fg := fg) g)
              (leafEliminatedFactor (fg := fg) f u))
            (leafEliminatedFactor (fg := fg) h z))).val x := by
          exact hMul2.symm

/-- Exact variable belief on the first fragment with two reusable attached
subtrees: if `v` receives one incoming message from the two-factor subtree
`u - f - w - g - v` and one from the two-factor subtree `y - h - z - j - v`,
then after three synchronous rounds from the neutral state its variable belief
is exactly the product of those two eliminated subtree factors. -/
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
            (φ := twoFactorSubtreeFactor (fg := fg) h j y) z))).val x := by
  intro x
  let σ₃ := runSyncRounds (fg := fg) 3 (initState (fg := fg))
  have hLeft :=
    leafToParent_subtreeMessage_exact
      (fg := fg) (f := f) (g := g) (u := u) (w := w) (v := v)
      hwf hLeafF hvg hLeafG hfg hNbrsW x
  have hRight :=
    leafToParent_subtreeMessage_exact
      (fg := fg) (f := h) (g := j) (u := y) (w := z) (v := v)
      hzh hLeafH hvj hLeafJ hhj hNbrsZ x
  have hBel :
      variableBelief (fg := fg) σ₃.factorToVar v (x v) =
        σ₃.factorToVar v g (x v) * σ₃.factorToVar v j (x v) := by
    have hgmem : g ∈ FactorGraph.variableNeighborsFinset fg v := by
      rw [hNbrsV]
      simp
    have hjmem : j ∈ FactorGraph.variableNeighborsFinset fg v := by
      rw [hNbrsV]
      simp
    have hAttach :
        (FactorGraph.variableNeighborsFinset fg v).attach =
          {⟨g, hgmem⟩, ⟨j, hjmem⟩} := by
      ext a
      constructor
      · intro ha
        have ha' : a.1 = g ∨ a.1 = j := by
          simpa [hNbrsV] using a.2
        rcases ha' with rfl | rfl <;> simp
      · intro ha
        rcases Finset.mem_insert.mp ha with hEq | hEq
        · subst hEq
          simp
        · simp at hEq
          subst hEq
          simp
    rw [variableBelief, hAttach, Finset.prod_insert]
    · rw [Finset.prod_singleton]
    · simp [Subtype.mk.injEq, hgj]
  have hMul :
      (VariableElimination.Factor.toValuation
        (φ := VariableElimination.Factor.mul (fg := fg)
          (VariableElimination.Factor.sumOut
            (φ := twoFactorSubtreeFactor (fg := fg) f g u) w)
          (VariableElimination.Factor.sumOut
            (φ := twoFactorSubtreeFactor (fg := fg) h j y) z))).val x =
        (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.sumOut
            (φ := twoFactorSubtreeFactor (fg := fg) f g u) w)).val x *
        (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.sumOut
            (φ := twoFactorSubtreeFactor (fg := fg) h j y) z)).val x := by
    simpa using! congrArg
      (fun ψ => ψ.val x)
      (VariableElimination.Factor.toValuation_mul
        (φ := VariableElimination.Factor.sumOut
          (φ := twoFactorSubtreeFactor (fg := fg) f g u) w)
        (ψ := VariableElimination.Factor.sumOut
          (φ := twoFactorSubtreeFactor (fg := fg) h j y) z))
  calc
    variableBelief
        (fg := fg)
        ((runSyncRounds (fg := fg) 3 (initState (fg := fg))).factorToVar)
        v
        (x v)
        = σ₃.factorToVar v g (x v) * σ₃.factorToVar v j (x v) := hBel
    _ = (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.sumOut
            (φ := twoFactorSubtreeFactor (fg := fg) f g u) w)).val x *
        (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.sumOut
            (φ := twoFactorSubtreeFactor (fg := fg) h j y) z)).val x := by
          rw [hLeft, hRight]
    _ = (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.mul (fg := fg)
            (VariableElimination.Factor.sumOut
              (φ := twoFactorSubtreeFactor (fg := fg) f g u) w)
            (VariableElimination.Factor.sumOut
              (φ := twoFactorSubtreeFactor (fg := fg) h j y) z))).val x := by
          exact hMul.symm

/-- Exact factor belief on the first fragment with two reusable attached
two-factor subtrees, one arriving through each variable of the central
pairwise factor `k`. -/
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
            (φ := twoFactorSubtreeFactor (fg := fg) p q y) t))).val x := by
  intro x
  let σ₄ := runSyncRounds (fg := fg) 4 (initState (fg := fg))
  have hLeft :
      σ₄.varToFactor v k (x v) =
        (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.sumOut
            (φ := twoFactorSubtreeFactor (fg := fg) f g u) w)).val x := by
    simpa [σ₄] using
      twoFactorSubtreeToParent_varMessage_exact
        (fg := fg) (f := f) (g := g) (h := k) (u := u) (w := w) (v := v)
        hwf hLeafF hvg hLeafG hvk hfg hgk hNbrsW hNbrsV x
  have hRight :
      σ₄.varToFactor z k (x z) =
        (VariableElimination.Factor.toValuation
          (φ := VariableElimination.Factor.sumOut
            (φ := twoFactorSubtreeFactor (fg := fg) p q y) t)).val x := by
    simpa [σ₄] using
      twoFactorSubtreeToParent_varMessage_exact
        (fg := fg) (f := p) (g := q) (h := k) (u := y) (w := t) (v := z)
        htp hLeafP hzq hLeafQ hzk hpq hqk hNbrsT hNbrsZ x
  exact pairwiseFactorBelief_of_exactIncoming
    (fg := fg)
    (μ := σ₄.varToFactor) (h := k) (v := v) (z := z)
    hzk hPairK
    (ψ := VariableElimination.Factor.sumOut
      (φ := twoFactorSubtreeFactor (fg := fg) f g u) w)
    (χ := VariableElimination.Factor.sumOut
      (φ := twoFactorSubtreeFactor (fg := fg) p q y) t)
    (hV := by
      intro x'
      simpa [σ₄] using
        twoFactorSubtreeToParent_varMessage_exact
          (fg := fg) (f := f) (g := g) (h := k) (u := u) (w := w) (v := v)
          hwf hLeafF hvg hLeafG hvk hfg hgk hNbrsW hNbrsV x')
    (hZ := by
      intro x'
      simpa [σ₄] using
        twoFactorSubtreeToParent_varMessage_exact
          (fg := fg) (f := p) (g := q) (h := k) (u := y) (w := t) (v := z)
          htp hLeafP hzq hLeafQ hzk hpq hqk hNbrsT hNbrsZ x')
    x

end BeliefExactness

end MessagePassing

end Mettapedia.ProbabilityTheory.BayesianNetworks
