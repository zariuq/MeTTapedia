import Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassing

/-!
# Schedules for Abstract Belief Propagation

This layer adds **execution structure** on top of the algebraic BP core:

* synchronous rounds,
* single-edge asynchronous updates,
* finite asynchronous schedules.

The core equations remain in `MessagePassing.lean`; this file only specifies how
to apply them over time.
-/

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

namespace MessagePassing

variable {V K : Type*} [DecidableEq V]

/-- An incident variable-factor pair in the factor graph. -/
structure IncidentEdge (fg : FactorGraph V K) where
  v : V
  f : fg.factors
  incident : v ∈ fg.scope f

/-- Variable-to-factor messages indexed only by true incident edges. -/
abbrev IncidentVarToFactorMsg (fg : FactorGraph V K) : Type _ :=
  ∀ e : IncidentEdge fg, fg.stateSpace e.v → K

/-- Factor-to-variable messages indexed only by true incident edges. -/
abbrev IncidentFactorToVarMsg (fg : FactorGraph V K) : Type _ :=
  ∀ e : IncidentEdge fg, fg.stateSpace e.v → K

namespace IncidentVarToFactorMsg

/-- Extend an incident-edge-indexed message family to the total-function core by
using the neutral value on non-incident pairs. -/
def toTotal {fg : FactorGraph V K} [One K] (μ : IncidentVarToFactorMsg fg) :
    VarToFactorMsg fg :=
  fun v f x =>
    by
      by_cases hv : v ∈ fg.scope f
      · exact μ ⟨v, f, hv⟩ x
      · exact 1

end IncidentVarToFactorMsg

namespace IncidentFactorToVarMsg

/-- Extend an incident-edge-indexed message family to the total-function core by
using the neutral value on non-incident pairs. -/
def toTotal {fg : FactorGraph V K} [One K] (μ : IncidentFactorToVarMsg fg) :
    FactorToVarMsg fg :=
  fun v f x =>
    by
      by_cases hv : v ∈ fg.scope f
      · exact μ ⟨v, f, hv⟩ x
      · exact 1

end IncidentFactorToVarMsg

namespace VarToFactorMsg

/-- Restrict a total message family to its meaningful incident edges. -/
def restrictIncident {fg : FactorGraph V K} (μ : VarToFactorMsg fg) :
    IncidentVarToFactorMsg fg :=
  fun e => μ e.v e.f

end VarToFactorMsg

namespace FactorToVarMsg

/-- Restrict a total message family to its meaningful incident edges. -/
def restrictIncident {fg : FactorGraph V K} (μ : FactorToVarMsg fg) :
    IncidentFactorToVarMsg fg :=
  fun e => μ e.v e.f

end FactorToVarMsg

/-- Incident-edge-indexed mutable state. This is a schedule-layer prototype
that stays definitionally aligned with the existing total-function core. -/
structure IncidentMessageState (fg : FactorGraph V K) where
  varToFactor : IncidentVarToFactorMsg fg
  factorToVar : IncidentFactorToVarMsg fg

/-- A mutable state of both message families. -/
structure MessageState (fg : FactorGraph V K) where
  varToFactor : VarToFactorMsg fg
  factorToVar : FactorToVarMsg fg

omit [DecidableEq V] in
@[ext] theorem MessageState.ext {fg : FactorGraph V K} {σ τ : MessageState fg}
    (hVar : σ.varToFactor = τ.varToFactor)
    (hFactor : σ.factorToVar = τ.factorToVar) : σ = τ := by
  cases σ
  cases τ
  cases hVar
  cases hFactor
  rfl

namespace IncidentMessageState

/-- Forget the incident-edge indexing by extending with neutral values on
non-incident pairs. -/
def toTotal {fg : FactorGraph V K} [One K] (σ : IncidentMessageState fg) :
    MessageState fg where
  varToFactor := IncidentVarToFactorMsg.toTotal σ.varToFactor
  factorToVar := IncidentFactorToVarMsg.toTotal σ.factorToVar

end IncidentMessageState

/-- Neutral message state. -/
def initState {fg : FactorGraph V K} [One K] : MessageState fg where
  varToFactor := unitVarToFactor (fg := fg)
  factorToVar := unitFactorToVar (fg := fg)

/-- Neutral incident-edge-indexed message state. -/
def initIncidentState {fg : FactorGraph V K} [One K] : IncidentMessageState fg where
  varToFactor := fun _ _ => 1
  factorToVar := fun _ _ => 1

/-- One synchronous BP round: update every directed message from the previous
state. -/
noncomputable def syncRound {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (σ : MessageState fg) : MessageState fg where
  varToFactor := fun v f x =>
    if hv : v ∈ fg.scope f then
      varToFactorUpdate (fg := fg) σ.factorToVar v f hv x
    else
      1
  factorToVar := fun v f x =>
    if hv : v ∈ fg.scope f then
      factorToVarUpdate (fg := fg) σ.varToFactor f v hv x
    else
      1

/-- One synchronous round on incident-edge-indexed messages, delegated to the
existing total-function update equations. -/
noncomputable def syncRoundIncident {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (σ : IncidentMessageState fg) : IncidentMessageState fg where
  varToFactor := fun e =>
    varToFactorUpdate (fg := fg)
      (IncidentFactorToVarMsg.toTotal σ.factorToVar) e.v e.f e.incident
  factorToVar := fun e =>
    factorToVarUpdate (fg := fg)
      (IncidentVarToFactorMsg.toTotal σ.varToFactor) e.f e.v e.incident

@[simp] theorem syncRoundIncident_varToFactor
    {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (σ : IncidentMessageState fg) (e : IncidentEdge fg) (x : fg.stateSpace e.v) :
    (syncRoundIncident (fg := fg) σ).varToFactor e x =
      varToFactorUpdate (fg := fg)
        (IncidentFactorToVarMsg.toTotal σ.factorToVar) e.v e.f e.incident x := rfl

@[simp] theorem syncRoundIncident_factorToVar
    {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (σ : IncidentMessageState fg) (e : IncidentEdge fg) (x : fg.stateSpace e.v) :
    (syncRoundIncident (fg := fg) σ).factorToVar e x =
      factorToVarUpdate (fg := fg)
        (IncidentVarToFactorMsg.toTotal σ.varToFactor) e.f e.v e.incident x := rfl

/-- Repeat synchronous rounds for `n` steps. -/
noncomputable def runSyncRounds {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (n : Nat) (σ : MessageState fg) : MessageState fg :=
  Nat.iterate (syncRound (fg := fg)) n σ

/-- Repeat synchronous rounds on the incident-edge-indexed schedule prototype. -/
noncomputable def runSyncRoundsIncident {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (n : Nat) (σ : IncidentMessageState fg) : IncidentMessageState fg :=
  Nat.iterate (syncRoundIncident (fg := fg)) n σ

/-- A single asynchronous update target. -/
inductive AsyncUpdate (fg : FactorGraph V K) where
  | varToFactor : IncidentEdge fg → AsyncUpdate fg
  | factorToVar : IncidentEdge fg → AsyncUpdate fg

/-- Update just one variable-to-factor message, leaving the rest unchanged. -/
noncomputable def updateVarToFactorAt {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors] [CommSemiring K]
    (σ : MessageState fg) (e : IncidentEdge fg) : MessageState fg where
  varToFactor := fun v f x =>
    by
      by_cases hvEq : v = e.v
      · subst hvEq
        by_cases hfEq : f = e.f
        · subst hfEq
          exact varToFactorUpdate (fg := fg) σ.factorToVar e.v e.f e.incident x
        · exact σ.varToFactor e.v f x
      · exact σ.varToFactor v f x
  factorToVar := σ.factorToVar

/-- Update just one factor-to-variable message, leaving the rest unchanged. -/
noncomputable def updateFactorToVarAt {fg : FactorGraph V K}
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (σ : MessageState fg) (e : IncidentEdge fg) : MessageState fg where
  varToFactor := σ.varToFactor
  factorToVar := fun v f x =>
    by
      by_cases hvEq : v = e.v
      · subst hvEq
        by_cases hfEq : f = e.f
        · subst hfEq
          exact factorToVarUpdate (fg := fg) σ.varToFactor e.f e.v e.incident x
        · exact σ.factorToVar e.v f x
      · exact σ.factorToVar v f x

/-- Apply one asynchronous update. -/
noncomputable def applyAsyncUpdate {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (σ : MessageState fg) : AsyncUpdate fg → MessageState fg
  | .varToFactor e => updateVarToFactorAt (fg := fg) σ e
  | .factorToVar e => updateFactorToVarAt (fg := fg) σ e

/-- Run a finite asynchronous schedule. -/
noncomputable def runAsyncSchedule {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (σ : MessageState fg) (sched : List (AsyncUpdate fg)) : MessageState fg :=
  sched.foldl (fun st upd => applyAsyncUpdate (fg := fg) st upd) σ

/-- Incident-edge-indexed variable-to-factor asynchronous update. -/
noncomputable def updateVarToFactorAtIncident {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors] [CommSemiring K]
    (σ : IncidentMessageState fg) (e : IncidentEdge fg) : IncidentMessageState fg where
  varToFactor :=
    VarToFactorMsg.restrictIncident
      (fg := fg) (updateVarToFactorAt (fg := fg)
        (IncidentMessageState.toTotal (fg := fg) σ) e).varToFactor
  factorToVar := σ.factorToVar

/-- Incident-edge-indexed factor-to-variable asynchronous update. -/
noncomputable def updateFactorToVarAtIncident {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (σ : IncidentMessageState fg) (e : IncidentEdge fg) : IncidentMessageState fg where
  varToFactor := σ.varToFactor
  factorToVar :=
    FactorToVarMsg.restrictIncident
      (fg := fg) (updateFactorToVarAt (fg := fg)
        (IncidentMessageState.toTotal (fg := fg) σ) e).factorToVar

/-- Apply one asynchronous update on the incident-edge schedule prototype. -/
noncomputable def applyAsyncUpdateIncident {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (σ : IncidentMessageState fg) : AsyncUpdate fg → IncidentMessageState fg
  | .varToFactor e => updateVarToFactorAtIncident (fg := fg) σ e
  | .factorToVar e => updateFactorToVarAtIncident (fg := fg) σ e

/-- Run a finite asynchronous schedule on the incident-edge-indexed prototype. -/
noncomputable def runAsyncScheduleIncident {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (σ : IncidentMessageState fg) (sched : List (AsyncUpdate fg)) : IncidentMessageState fg :=
  sched.foldl (fun st upd => applyAsyncUpdateIncident (fg := fg) st upd) σ

@[simp] theorem updateVarToFactorAtIncident_factorToVar
    {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors] [CommSemiring K]
    (σ : IncidentMessageState fg) (e : IncidentEdge fg) :
    (updateVarToFactorAtIncident (fg := fg) σ e).factorToVar = σ.factorToVar := rfl

@[simp] theorem updateFactorToVarAtIncident_varToFactor
    {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (σ : IncidentMessageState fg) (e : IncidentEdge fg) :
    (updateFactorToVarAtIncident (fg := fg) σ e).varToFactor = σ.varToFactor := rfl

@[simp] theorem updateVarToFactorAtIncident_varToFactor_self
    {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors] [CommSemiring K]
    (σ : IncidentMessageState fg) (e : IncidentEdge fg) (x : fg.stateSpace e.v) :
    (updateVarToFactorAtIncident (fg := fg) σ e).varToFactor e x =
      varToFactorUpdate (fg := fg)
        ((IncidentMessageState.toTotal (fg := fg) σ).factorToVar) e.v e.f e.incident x := by
  simp [updateVarToFactorAtIncident, VarToFactorMsg.restrictIncident,
    updateVarToFactorAt, IncidentMessageState.toTotal]

@[simp] theorem updateFactorToVarAtIncident_factorToVar_self
    {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (σ : IncidentMessageState fg) (e : IncidentEdge fg) (x : fg.stateSpace e.v) :
    (updateFactorToVarAtIncident (fg := fg) σ e).factorToVar e x =
      factorToVarUpdate (fg := fg)
        ((IncidentMessageState.toTotal (fg := fg) σ).varToFactor) e.f e.v e.incident x := by
  simp [updateFactorToVarAtIncident, FactorToVarMsg.restrictIncident,
    updateFactorToVarAt, IncidentMessageState.toTotal]

private theorem updateVarToFactorAt_toTotal_neutral
    {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors] [CommSemiring K]
    (σ : IncidentMessageState fg) (e : IncidentEdge fg) :
    ∀ v f (x : fg.stateSpace v), v ∉ fg.scope f →
      (updateVarToFactorAt (fg := fg) (IncidentMessageState.toTotal (fg := fg) σ) e).varToFactor v f x = 1 := by
  intro v f x hv
  unfold updateVarToFactorAt
  by_cases hve : v = e.v
  · subst hve
    by_cases hfe : f = e.f
    · subst hfe
      exact (hv e.incident).elim
    · simp [IncidentMessageState.toTotal, IncidentVarToFactorMsg.toTotal, hv, hfe]
  · simp [IncidentMessageState.toTotal, IncidentVarToFactorMsg.toTotal, hv, hve]

private theorem updateFactorToVarAt_toTotal_neutral
    {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (σ : IncidentMessageState fg) (e : IncidentEdge fg) :
    ∀ v f (x : fg.stateSpace v), v ∉ fg.scope f →
      (updateFactorToVarAt (fg := fg) (IncidentMessageState.toTotal (fg := fg) σ) e).factorToVar v f x = 1 := by
  intro v f x hv
  unfold updateFactorToVarAt
  by_cases hve : v = e.v
  · subst hve
    by_cases hfe : f = e.f
    · subst hfe
      exact (hv e.incident).elim
    · simp [IncidentMessageState.toTotal, IncidentFactorToVarMsg.toTotal, hv, hfe]
  · simp [IncidentMessageState.toTotal, IncidentFactorToVarMsg.toTotal, hv, hve]

@[simp] theorem runSyncRounds_zero {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (σ : MessageState fg) :
    runSyncRounds (fg := fg) 0 σ = σ := rfl

@[simp] theorem initIncidentState_toTotal {fg : FactorGraph V K} [One K] :
    IncidentMessageState.toTotal (fg := fg) (initIncidentState (fg := fg)) =
      initState (fg := fg) := by
  apply MessageState.ext
  · funext v
    funext f
    funext x
    by_cases hv : v ∈ fg.scope f <;>
      simp [IncidentMessageState.toTotal, initIncidentState, initState,
        IncidentVarToFactorMsg.toTotal, hv, unitVarToFactor]
  · funext v
    funext f
    funext x
    by_cases hv : v ∈ fg.scope f <;>
      simp [IncidentMessageState.toTotal, initIncidentState, initState,
        IncidentFactorToVarMsg.toTotal, hv, unitFactorToVar]

@[simp] theorem toTotal_syncRoundIncident_eq_syncRound_toTotal {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (σ : IncidentMessageState fg) :
    IncidentMessageState.toTotal (fg := fg) (syncRoundIncident (fg := fg) σ) =
      syncRound (fg := fg) (IncidentMessageState.toTotal (fg := fg) σ) := by
  apply MessageState.ext
  · funext v
    funext f
    funext x
    by_cases hv : v ∈ fg.scope f
    · unfold IncidentMessageState.toTotal syncRoundIncident syncRound
      simp [IncidentVarToFactorMsg.toTotal, hv]
    · unfold IncidentMessageState.toTotal syncRoundIncident syncRound
      simp [IncidentVarToFactorMsg.toTotal, hv]
  · funext v
    funext f
    funext x
    by_cases hv : v ∈ fg.scope f
    · unfold IncidentMessageState.toTotal syncRoundIncident syncRound
      simp [IncidentFactorToVarMsg.toTotal, hv]
    · unfold IncidentMessageState.toTotal syncRoundIncident syncRound
      simp [IncidentFactorToVarMsg.toTotal, hv]

@[simp] theorem runSyncRounds_succ {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (n : Nat) (σ : MessageState fg) :
    runSyncRounds (fg := fg) (n + 1) σ =
      runSyncRounds (fg := fg) n (syncRound (fg := fg) σ) := by
  change (syncRound (fg := fg))^[n + 1] σ =
    (syncRound (fg := fg))^[n] ((syncRound (fg := fg)) σ)
  exact Function.iterate_succ_apply (f := syncRound (fg := fg)) n σ

@[simp] theorem runSyncRoundsIncident_zero {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (σ : IncidentMessageState fg) :
    runSyncRoundsIncident (fg := fg) 0 σ = σ := rfl

@[simp] theorem runSyncRoundsIncident_succ {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (n : Nat) (σ : IncidentMessageState fg) :
    runSyncRoundsIncident (fg := fg) (n + 1) σ =
      runSyncRoundsIncident (fg := fg) n (syncRoundIncident (fg := fg) σ) := by
  change (syncRoundIncident (fg := fg))^[n + 1] σ =
    (syncRoundIncident (fg := fg))^[n] ((syncRoundIncident (fg := fg)) σ)
  exact Function.iterate_succ_apply (f := syncRoundIncident (fg := fg)) n σ

theorem toTotal_runSyncRoundsIncident_eq_runSyncRounds_toTotal {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (n : Nat) (σ : IncidentMessageState fg) :
    IncidentMessageState.toTotal (fg := fg) (runSyncRoundsIncident (fg := fg) n σ) =
      runSyncRounds (fg := fg) n (IncidentMessageState.toTotal (fg := fg) σ) := by
  induction n generalizing σ with
  | zero =>
      simp [runSyncRoundsIncident, runSyncRounds]
  | succ n ih =>
      simpa [runSyncRoundsIncident_succ, runSyncRounds_succ,
        toTotal_syncRoundIncident_eq_syncRound_toTotal]
        using ih (σ := syncRoundIncident (fg := fg) σ)

@[simp] theorem toTotal_updateVarToFactorAtIncident_eq_updateVarToFactorAt_toTotal
    {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors] [CommSemiring K]
    (σ : IncidentMessageState fg) (e : IncidentEdge fg) :
    IncidentMessageState.toTotal (fg := fg) (updateVarToFactorAtIncident (fg := fg) σ e) =
      updateVarToFactorAt (fg := fg) (IncidentMessageState.toTotal (fg := fg) σ) e := by
  apply MessageState.ext
  · funext v
    funext f
    funext x
    by_cases hv : v ∈ fg.scope f
    · simp [IncidentMessageState.toTotal, updateVarToFactorAtIncident,
        VarToFactorMsg.restrictIncident, IncidentVarToFactorMsg.toTotal, hv]
    · calc
        (IncidentMessageState.toTotal (fg := fg)
          (updateVarToFactorAtIncident (fg := fg) σ e)).varToFactor v f x = 1 := by
            simp [IncidentMessageState.toTotal, updateVarToFactorAtIncident,
              IncidentVarToFactorMsg.toTotal, hv]
        _ = (updateVarToFactorAt (fg := fg)
              (IncidentMessageState.toTotal (fg := fg) σ) e).varToFactor v f x := by
            symm
            exact updateVarToFactorAt_toTotal_neutral (fg := fg) (σ := σ) (e := e) v f x hv
  · funext v
    funext f
    funext x
    by_cases hv : v ∈ fg.scope f
    · simp [IncidentMessageState.toTotal, updateVarToFactorAtIncident,
        IncidentFactorToVarMsg.toTotal, hv, updateVarToFactorAt]
    · simp [IncidentMessageState.toTotal, updateVarToFactorAtIncident,
        IncidentFactorToVarMsg.toTotal, hv,
        updateVarToFactorAt]

@[simp] theorem toTotal_updateFactorToVarAtIncident_eq_updateFactorToVarAt_toTotal
    {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (σ : IncidentMessageState fg) (e : IncidentEdge fg) :
    IncidentMessageState.toTotal (fg := fg) (updateFactorToVarAtIncident (fg := fg) σ e) =
      updateFactorToVarAt (fg := fg) (IncidentMessageState.toTotal (fg := fg) σ) e := by
  apply MessageState.ext
  · funext v
    funext f
    funext x
    by_cases hv : v ∈ fg.scope f
    · simp [IncidentMessageState.toTotal, updateFactorToVarAtIncident,
        IncidentVarToFactorMsg.toTotal, hv, updateFactorToVarAt]
    · simp [IncidentMessageState.toTotal, updateFactorToVarAtIncident,
        IncidentVarToFactorMsg.toTotal, hv, updateFactorToVarAt]
  · funext v
    funext f
    funext x
    by_cases hv : v ∈ fg.scope f
    · simp [IncidentMessageState.toTotal, updateFactorToVarAtIncident,
        FactorToVarMsg.restrictIncident, IncidentFactorToVarMsg.toTotal, hv]
    · calc
        (IncidentMessageState.toTotal (fg := fg)
          (updateFactorToVarAtIncident (fg := fg) σ e)).factorToVar v f x = 1 := by
            simp [IncidentMessageState.toTotal, updateFactorToVarAtIncident,
              IncidentFactorToVarMsg.toTotal, hv]
        _ = (updateFactorToVarAt (fg := fg)
              (IncidentMessageState.toTotal (fg := fg) σ) e).factorToVar v f x := by
            symm
            exact updateFactorToVarAt_toTotal_neutral (fg := fg) (σ := σ) (e := e) v f x hv

@[simp] theorem toTotal_applyAsyncUpdateIncident_eq_applyAsyncUpdate_toTotal
    {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (σ : IncidentMessageState fg) (upd : AsyncUpdate fg) :
    IncidentMessageState.toTotal (fg := fg) (applyAsyncUpdateIncident (fg := fg) σ upd) =
      applyAsyncUpdate (fg := fg) (IncidentMessageState.toTotal (fg := fg) σ) upd := by
  cases upd with
  | varToFactor e =>
      exact by
        simp [applyAsyncUpdateIncident, applyAsyncUpdate,
          toTotal_updateVarToFactorAtIncident_eq_updateVarToFactorAt_toTotal]
  | factorToVar e =>
      exact by
        simp [applyAsyncUpdateIncident, applyAsyncUpdate,
          toTotal_updateFactorToVarAtIncident_eq_updateFactorToVarAt_toTotal]

@[simp] theorem runAsyncScheduleIncident_nil {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (σ : IncidentMessageState fg) :
    runAsyncScheduleIncident (fg := fg) σ [] = σ := rfl

@[simp] theorem runAsyncScheduleIncident_cons {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (σ : IncidentMessageState fg) (upd : AsyncUpdate fg) (sched : List (AsyncUpdate fg)) :
    runAsyncScheduleIncident (fg := fg) σ (upd :: sched) =
      runAsyncScheduleIncident (fg := fg) (applyAsyncUpdateIncident (fg := fg) σ upd) sched := by
  simp [runAsyncScheduleIncident]

theorem toTotal_runAsyncScheduleIncident_eq_runAsyncSchedule_toTotal
    {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (σ : IncidentMessageState fg) (sched : List (AsyncUpdate fg)) :
    IncidentMessageState.toTotal (fg := fg) (runAsyncScheduleIncident (fg := fg) σ sched) =
      runAsyncSchedule (fg := fg) (IncidentMessageState.toTotal (fg := fg) σ) sched := by
  induction sched generalizing σ with
  | nil =>
      simp [runAsyncScheduleIncident, runAsyncSchedule]
  | cons upd sched ih =>
      simpa [runAsyncScheduleIncident_cons, runAsyncSchedule,
        toTotal_applyAsyncUpdateIncident_eq_applyAsyncUpdate_toTotal] using
        ih (σ := applyAsyncUpdateIncident (fg := fg) σ upd)

@[simp] theorem runAsyncSchedule_nil {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (σ : MessageState fg) :
    runAsyncSchedule (fg := fg) σ [] = σ := rfl

@[simp] theorem runAsyncSchedule_cons {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (σ : MessageState fg) (upd : AsyncUpdate fg) (sched : List (AsyncUpdate fg)) :
    runAsyncSchedule (fg := fg) σ (upd :: sched) =
      runAsyncSchedule (fg := fg) (applyAsyncUpdate (fg := fg) σ upd) sched := by
  simp [runAsyncSchedule]

end MessagePassing

end Mettapedia.ProbabilityTheory.BayesianNetworks
