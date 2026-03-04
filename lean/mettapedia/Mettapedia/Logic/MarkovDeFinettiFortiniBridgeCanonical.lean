import Mettapedia.Logic.MarkovDeFinettiFortiniBridgeCore

/-!
# Markov de Finetti Fortini Bridge: Canonical Surface

This file is the default *public* Fortini surface.
It intentionally avoids importing `...BridgeCrux`.

Canonical target: prove the literature-facing theorem directly from
Markov exchangeability + recurrence assumptions.

Any bridge-style decomposition below is an optional fallback route and is
explicitly marked as such.
-/

noncomputable section

namespace Mettapedia.Logic
namespace MarkovDeFinettiHard

open MeasureTheory
open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovDeFinettiRecurrence

/-- Canonical public theorem shape (literature-facing). -/
abbrev FortiniCanonicalRepresentationTheorem (k : ℕ) : Prop :=
  ∀ μ : FiniteAlphabet.PrefixMeasure (Fin k),
    MarkovExchangeablePrefixMeasure (k := k) μ →
    MarkovRecurrentPrefixMeasure (k := k) μ →
      ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
        ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi

/-- Optional fallback assumption:
extract an extension law from recurrent Markov exchangeable prefix law. -/
abbrev FortiniOptionalPEBridgeAssumption (k : ℕ) : Prop :=
  ∀ μ : FiniteAlphabet.PrefixMeasure (Fin k),
    MarkovExchangeablePrefixMeasure (k := k) μ →
    MarkovRecurrentPrefixMeasure (k := k) μ →
      ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
        (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))

/-- Optional fallback assumption:
construct representation on the extracted extension law. -/
abbrev FortiniOptionalKernelBridgeAssumption (k : ℕ) : Prop :=
  ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (P : Measure (ℕ → Fin k)),
      IsProbabilityMeasure P →
      MarkovExchangeablePrefixMeasure (k := k) μ →
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) →
      MarkovRecurrentPrefixMeasure (k := k) μ →
      ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
        ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi

/-- Optional fallback composition route.
Not the primary canonical proof target. -/
theorem fortiniSuccessorMatrixInvarianceTheorem_via_optionalBridge
    (hPEBridge : FortiniOptionalPEBridgeAssumption k)
    (hKernelBridge : FortiniOptionalKernelBridgeAssumption k) :
    FortiniCanonicalRepresentationTheorem k := by
  intro μ hμ hrec
  rcases hPEBridge μ hμ hrec with ⟨P, hP, hExt⟩
  exact hKernelBridge μ P hP hμ hExt hrec

/-- Optional fallback composition route (Fortini + Solomonoff). -/
theorem fortini_and_solomonoff_via_optionalBridge
    (hPEBridge : FortiniOptionalPEBridgeAssumption k)
    (hKernelBridge : FortiniOptionalKernelBridgeAssumption k)
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
by
  refine ⟨?_, ?_⟩
  · exact
      (fortiniSuccessorMatrixInvarianceTheorem_via_optionalBridge
        (k := k) hPEBridge hKernelBridge) μ hμ hrec
  · exact
      (markovExchangeable_summary_and_solomonoff_regret
        (k := k) (μ := μ) hμ hμLSC).2

/-- Backward-compatible alias for previous naming on the optional route. -/
@[deprecated fortiniSuccessorMatrixInvarianceTheorem_via_optionalBridge (since := "2026-03-03")]
theorem fortiniSuccessorMatrixInvarianceTheorem_canonical
    (hPEBridge : FortiniOptionalPEBridgeAssumption k)
    (hKernelBridge : FortiniOptionalKernelBridgeAssumption k) :
    FortiniCanonicalRepresentationTheorem k :=
  fortiniSuccessorMatrixInvarianceTheorem_via_optionalBridge
    (k := k) hPEBridge hKernelBridge

/-- Backward-compatible alias for previous naming on the optional route. -/
@[deprecated fortini_and_solomonoff_via_optionalBridge (since := "2026-03-03")]
theorem fortini_and_solomonoff_canonical
    (hPEBridge : FortiniOptionalPEBridgeAssumption k)
    (hKernelBridge : FortiniOptionalKernelBridgeAssumption k)
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
  fortini_and_solomonoff_via_optionalBridge
    (k := k) hPEBridge hKernelBridge μ hμ hrec hμLSC

end MarkovDeFinettiHard
end Mettapedia.Logic
