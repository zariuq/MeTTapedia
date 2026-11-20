import Mettapedia.ProbabilityTheory.StochasticInference.Finite

/-!
# Exact invariances of an identified factor readout

Permuting fixed likelihood factors preserves their evidence semantics.
Admitting an event as a hard indicator is redundant whenever the current
support entails it.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.StochasticInference.State

open Mettapedia.ProbabilityTheory.BayesianNetworks.ExecutableFactorTable (Config Table)

variable {n : Nat} {domains : Fin n → Nat} {Id : Type*}

theorem expectationMasses_of_weight_eq (first second : State Id domains)
    (positive : ∀ v, 0 < domains v) (schedule : Schedule n) (payoff : Table domains)
    (agree : ∀ x, first.unnormalized positive x = second.unnormalized positive x) :
    first.expectationMasses positive schedule payoff = second.expectationMasses positive schedule payoff := by
  simp only [expectationMasses_exact, agree]

theorem probability_of_table_permutation (first second : State Id domains)
    (positive : ∀ v, 0 < domains v) (schedule : Schedule n) (event : Event domains)
    (permutation : first.tables.Perm second.tables) :
    first.probability? positive schedule event = second.probability? positive schedule event := by
  unfold probability? probabilityMasses
  rw [expectationMasses_of_weight_eq first second positive schedule event.table]
  intro x
  exact (permutation.map (fun t => t.value domains positive x)).prod_eq

theorem entailed_observation_weight [DecidableEq Id] (state next : State Id domains)
    (id : Id) (event : Event domains) (fresh : state.ledger.lookup id = none)
    (recorded : state.observe id event.asPotential = .ok (.recorded, next))
    (positive : ∀ v, 0 < domains v)
    (entailed : ∀ x : Config domains, 0 < state.unnormalized positive x → event.holds positive x = true)
    (world : Config domains) :
    next.unnormalized positive world = state.unnormalized positive world := by
  rw [fresh_observation state id event.asPotential fresh next recorded]
  by_cases empty : state.unnormalized positive world = 0
  · rw [empty, zero_mul]
  · have possible := lt_of_le_of_ne (state.unnormalized_nonneg positive world) (Ne.symm empty)
    change _ * event.value positive world = _
    simp [event.value_eq_indicator, entailed world possible]

theorem entailed_observation_probability [DecidableEq Id] (state next : State Id domains)
    (id : Id) (event : Event domains) (fresh : state.ledger.lookup id = none)
    (recorded : state.observe id event.asPotential = .ok (.recorded, next))
    (positive : ∀ v, 0 < domains v)
    (entailed : ∀ x : Config domains, 0 < state.unnormalized positive x → event.holds positive x = true)
    (schedule : Schedule n) (query : Event domains) :
    next.probability? positive schedule query = state.probability? positive schedule query := by
  unfold probability? probabilityMasses
  rw [expectationMasses_of_weight_eq next state positive schedule query.table
    (entailed_observation_weight state next id event fresh recorded positive entailed)]

end Mettapedia.ProbabilityTheory.StochasticInference.State
