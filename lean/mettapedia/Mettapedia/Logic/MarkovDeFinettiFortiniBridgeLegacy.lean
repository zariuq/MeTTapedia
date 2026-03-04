import Mettapedia.Logic.MarkovDeFinettiFortiniBridgeCrux

/-!
# Markov de Finetti Fortini Bridge: Legacy Surface

This module exists for migration compatibility.
Prefer `Mettapedia.Logic.MarkovDeFinettiFortiniBridgeCanonical`.
-/

noncomputable section

namespace Mettapedia.Logic
namespace MarkovDeFinettiHard

open MeasureTheory
open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovDeFinettiRecurrence

@[deprecated fortiniSuccessorMatrixInvarianceTheorem_of_canonicalAssumptions_minimal (since := "2026-03-03")]
theorem fortiniSuccessorMatrixInvarianceTheorem_legacy
    (hPEBridge : SuccessorMatrixPE_of_markovExchangeable_recurrent k)
    (hBuildFromPE : ExistsBuiltRowKernel_of_successorMatrixPE k) :
    FortiniSuccessorMatrixInvarianceTheorem k :=
  fortiniSuccessorMatrixInvarianceTheorem_of_canonicalAssumptions
    (k := k) hPEBridge hBuildFromPE

@[deprecated fortini_and_solomonoff_of_canonicalAssumptions_minimal (since := "2026-03-03")]
theorem fortini_and_solomonoff_legacy
    (hPEBridge : SuccessorMatrixPE_of_markovExchangeable_recurrent k)
    (hBuildFromPE : ExistsBuiltRowKernel_of_successorMatrixPE k)
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hμLSC :
      Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.LowerSemicomputablePrefixMeasure
        (α := Fin k) μ) :
    (∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi) ∧
    (∀ n : ℕ,
      ∃ c : ENNReal, c ≠ 0 ∧
        Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.Dominates
          (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin k)) μ c ∧
        Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.FiniteHorizon.relEntropy μ
          (Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂
            (α := Fin k)) n ≤
          Real.log (1 / c.toReal)) :=
  fortini_and_solomonoff_of_canonicalAssumptions
    (k := k) hPEBridge hBuildFromPE μ hμ hrec hμLSC

end MarkovDeFinettiHard
end Mettapedia.Logic
