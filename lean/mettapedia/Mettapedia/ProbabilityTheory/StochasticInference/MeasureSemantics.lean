import Mettapedia.ProbabilityTheory.StochasticInference.Finite
import Mettapedia.PLN.WorldModel.BayesianObservationLedger
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Finite factor states as Bayesian measures

The counting measure on assignments is scored by the state weight.
The executable evidence step is density updating. Numerator and normalizer
are the measure of the query set and of all assignments.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.StochasticInference.MeasureSemantics

open MeasureTheory
open Mettapedia.ProbabilityTheory.BayesianNetworks.ExecutableFactorTable (Config)
open Mettapedia.PLN.WorldModel

open scoped ENNReal

variable {n : Nat} {domains : Fin n → Nat} {Id : Type*}
variable [MeasurableSpace (Config domains)] [MeasurableSingletonClass (Config domains)]

noncomputable def denote (state : State Id domains) (positive : ∀ v, 0 < domains v) :
    Measure (Config domains) :=
  Measure.count.withDensity (fun x => ENNReal.ofReal (state.unnormalized positive x : ℝ))

theorem observe_denote [DecidableEq Id] (state : State Id domains) (positive : ∀ v, 0 < domains v)
    (id : Id) (likelihood : Potential domains) (fresh : state.ledger.lookup id = none)
    (next : State Id domains) (observed : state.observe id likelihood = .ok (.recorded, next)) :
    denote next positive = (denote state positive).withDensity
      (fun x => ENNReal.ofReal (likelihood.table.value domains positive x : ℝ)) := by
  rw [denote, denote, ← withDensity_mul _ (measurable_of_countable _) (measurable_of_countable _)]
  congr 1
  funext x
  rw [state.fresh_observation id likelihood fresh next observed, Rat.cast_mul,
    ENNReal.ofReal_mul (Rat.cast_nonneg.mpr (state.unnormalized_nonneg positive x))]
  rfl

private theorem cast_sum {X : Type*} [Fintype X] (w : X → ℚ) (nonneg : ∀ x, 0 ≤ w x) :
    ENNReal.ofReal ((∑ x, w x : ℚ) : ℝ) = ∑ x, ENNReal.ofReal (w x : ℝ) := by
  rw [Rat.cast_sum, ENNReal.ofReal_sum_of_nonneg]
  exact fun x _ => Rat.cast_nonneg.mpr (nonneg x)

theorem denote_mass (state : State Id domains) (positive : ∀ v, 0 < domains v) (schedule : Schedule n)
    (event : Event domains) :
    let result := state.probabilityMasses positive schedule event
    (denote state positive) {x | event.holds positive x = true} = ENNReal.ofReal (result.joint : ℝ) ∧
      (denote state positive) Set.univ = ENNReal.ofReal (result.evidence : ℝ) := by
  let query : Set (Config domains) := {x | event.holds positive x = true}
  have measurableQuery : MeasurableSet query := query.to_countable.measurableSet
  dsimp only
  rw [state.probabilityMasses_exact]
  constructor
  · change (denote state positive) query = _
    rw [denote, withDensity_apply _ measurableQuery, ← lintegral_indicator measurableQuery,
      lintegral_count, tsum_fintype, cast_sum]
    · apply Finset.sum_congr rfl
      intro x _
      by_cases inside : event.holds positive x = true
      · simp [Set.indicator_of_mem (show x ∈ query from inside), inside]
      · simp [Set.indicator_of_notMem (show x ∉ query from inside), inside]
    · intro x
      split
      · exact state.unnormalized_nonneg positive x
      · exact le_rfl
  · rw [denote, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count,
      tsum_fintype, cast_sum _ (state.unnormalized_nonneg positive)]

theorem posterior_agrees (state : State Id domains) (positive : ∀ v, 0 < domains v)
    (schedule : Schedule n) (event : Event domains) (answer : ℚ)
    (answered : state.probability? positive schedule event = some answer) :
    BayesianObservationLedger.normalize (denote state positive) {x | event.holds positive x = true} =
      ENNReal.ofReal (answer : ℝ) := by
  let result := state.probabilityMasses positive schedule event
  change result.posterior? = some answer at answered
  unfold BayesianNetworks.ScopedFactorReadout.Masses.posterior? at answered
  split at answered
  · rename_i supported
    have value := Option.some.inj answered
    subst answer
    have masses := denote_mass state positive schedule event
    rw [BayesianObservationLedger.normalize, Measure.smul_apply, smul_eq_mul,
      masses.1, masses.2, mul_comm, ← div_eq_mul_inv]
    rw [Rat.cast_div, ENNReal.ofReal_div_of_pos (Rat.cast_pos.mpr supported)]
  · contradiction

end Mettapedia.ProbabilityTheory.StochasticInference.MeasureSemantics
