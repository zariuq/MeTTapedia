import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.SolomonoffBridge

/-!
# Competitor Bounds (Finite Alphabet): Hook B meets M₂

This file is the finite-alphabet analogue of `UniversalPrediction/CompetitorBounds.lean`.

It packages the key composition step:

* `M₂` (the concrete Solomonoff-style universal mixture over LSC semimeasures on `Word α`)
  dominates any lower-semicomputable competitor `η`, and
* dominance implies the standard “best expert + complexity” KL-regret inequality.

Here we keep the bound in the generic `log(1/c)` form, since the finite-alphabet development
currently exposes the dominance constant as an explicit code weight (rather than a `Kpf`).
-/

namespace Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet

open scoped Classical BigOperators ENNReal

open Mettapedia.Computability.Hutter
open FiniteHorizon

namespace SolomonoffBridge

open Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.SolomonoffBridge

variable {α : Type*} [Fintype α] [Primcodable α]

/-- **Universal competitiveness** (finite alphabet, Solomonoff mixture `M₂`):

If `η` is lower semicomputable, then `M₂` incurs at most an additive `log(1/c)` KL-regret
relative to `η`, for some explicit dominance constant `c > 0`.

This is the theorem-grade form needed by Hook B: once a hyperprior mixture (or any other
tractable predictor) is shown lower semicomputable, `M₂` competes with it automatically.
-/
theorem relEntropy_le_competitor_add_log_inv_M₂
    (μ η : PrefixMeasure α)
    (hη : LowerSemicomputablePrefixMeasure (α := α) η)
    (hη0 : ∀ x : Word α, η x ≠ 0)
    (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧
      relEntropy μ (M₂ (α := α)) n ≤
        relEntropy μ η.toSemimeasure n + Real.log (1 / c.toReal) := by
  -- Get a dominance constant for `η` from the concrete Levin/Hutter enumeration theorem.
  obtain ⟨c, hc0, hdom, _hbound⟩ :=
    (LSCSemimeasureEnumeration.relEntropy_le_log_inv_of_LSC
      (E := HutterEnumerationTheoremSemimeasure.lscSemimeasureEnumeration (α := α))
      (μ := η) hη n)
  -- Convert dominance into a best-expert bound for an arbitrary true environment `μ`.
  refine ⟨c, hc0, ?_⟩
  exact
    relEntropy_le_add_log_inv_of_dominates_right
      (μ := μ) (ξ := (M₂ (α := α))) (η := η)
      (hdom := by simpa [M₂] using hdom) (hc0 := hc0) (hη0 := hη0) n

end SolomonoffBridge

end Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet

