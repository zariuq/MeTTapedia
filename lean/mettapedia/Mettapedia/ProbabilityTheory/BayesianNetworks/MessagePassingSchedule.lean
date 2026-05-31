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

/-- A mutable state of both message families. -/
structure MessageState (fg : FactorGraph V K) where
  varToFactor : VarToFactorMsg fg
  factorToVar : FactorToVarMsg fg

/-- Neutral message state. -/
def initState {fg : FactorGraph V K} [One K] : MessageState fg where
  varToFactor := unitVarToFactor (fg := fg)
  factorToVar := unitFactorToVar (fg := fg)

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

/-- Repeat synchronous rounds for `n` steps. -/
noncomputable def runSyncRounds {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (n : Nat) (σ : MessageState fg) : MessageState fg :=
  Nat.iterate (syncRound (fg := fg)) n σ

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

@[simp] theorem runSyncRounds_zero {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (σ : MessageState fg) :
    runSyncRounds (fg := fg) 0 σ = σ := rfl

@[simp] theorem runSyncRounds_succ {fg : FactorGraph V K}
    [Fintype fg.factors] [DecidableEq fg.factors]
    [∀ v, Fintype (fg.stateSpace v)] [CommSemiring K]
    (n : Nat) (σ : MessageState fg) :
    runSyncRounds (fg := fg) (n + 1) σ =
      runSyncRounds (fg := fg) n (syncRound (fg := fg) σ) := by
  change (syncRound (fg := fg))^[n + 1] σ =
    (syncRound (fg := fg))^[n] ((syncRound (fg := fg)) σ)
  exact Function.iterate_succ_apply (f := syncRound (fg := fg)) n σ

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
