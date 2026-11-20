import Mettapedia.Computability.BitGenerator
import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.Basic

/-! # Prefix probabilities of one-way bit generators -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Computability.BitGenerator.Generator

open MeasureTheory Filter
open scoped ENNReal

open Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet

variable {State Symbol : Type*} [Fintype Symbol]

/-- The probability of each emitted prefix under fair input. Sibling events
are disjoint, and their union can leave out tapes that emit nothing further. -/
def semimeasure (program : BitGenerator.Generator State Symbol) : Semimeasure Symbol where
  toFun history := coinMeasure (program.event history)
  superadditive' history := by
    classical
    let children : Symbol → Set CantorSpace := fun next => program.event (history ++ [next])
    have disjoint : Set.PairwiseDisjoint (↑(Finset.univ : Finset Symbol)) children := by
      intro first _ second _ distinct
      apply program.event_disjoint (by simp)
      simpa using distinct
    have measured : coinMeasure (⋃ next ∈ (Finset.univ : Finset Symbol), children next) =
        ∑ next : Symbol, coinMeasure (children next) :=
      measure_biUnion_finset disjoint (fun next _ => program.measurable_event (history ++ [next]))
    rw [← measured]
    apply measure_mono
    intro tape member
    obtain ⟨next, member⟩ := Set.mem_iUnion.mp member
    obtain ⟨_, member⟩ := Set.mem_iUnion.mp member
    exact program.event_mono (List.prefix_append history [next]) member
  root_le_one' := by simp

@[simp] theorem semimeasure_apply (program : BitGenerator.Generator State Symbol) (history : List Symbol) :
    program.semimeasure history = coinMeasure (program.event history) := rfl

@[simp] theorem semimeasure_nil (program : BitGenerator.Generator State Symbol) :
    program.semimeasure [] = 1 := by
  simp

variable [DecidableEq State] [DecidableEq Symbol]

theorem stageMass_le (program : BitGenerator.Generator State Symbol) (history : List Symbol) (stage : Nat) :
    ENNReal.ofReal (program.stageMass history stage : ℝ) ≤ program.semimeasure history := by
  rw [program.stageMass_eq_fraction, ← (program.run_readsPrefix history).coinMeasure_stageSet_eq_fraction]
  apply measure_mono
  rw [← program.outputSet_eq_event]
  exact (program.run history).stageSet_subset_outputSet 1 stage

theorem toReal_stageMass_tendsto (program : BitGenerator.Generator State Symbol) (history : List Symbol) :
    Tendsto (fun stage => (program.stageMass history stage : ℝ)) atTop
      (nhds (program.semimeasure history).toReal) := by
  have convergence := (ENNReal.tendsto_toReal (program.semimeasure.ne_top history)).comp
    (program.stageMass_tendsto history)
  convert convergence using 1
  funext stage
  exact (ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (by
    unfold stageMass
    exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)))).symm

end Mettapedia.Computability.BitGenerator.Generator
