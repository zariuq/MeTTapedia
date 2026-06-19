import Mettapedia.Logic.RavenAbduction
import Mettapedia.Logic.PLNAlgorithmicAbductionBridge

/-!
# Raven Abduction as Prior-Weighted Explanation Scoring

`RavenAbduction.lean` is the book-facing worked example: base rates dominate a
common feature, while a discriminating feature can flip the best explanation.

This file welds that example to the generic WM-PLN abduction-ranking surface:
the unnormalized hypothesis score is exactly `priorWeightedPoint`.  It does not
claim interval tightness for the Raven example; the robust interval-ranking
discipline remains in `PLNAlgorithmicAbductionBridge`.
-/

namespace Mettapedia.Logic.PLN

namespace RavenAbductionBridge

open Mettapedia.Logic.RavenAbduction

/-- The single-feature Raven score is the generic prior-weighted point score. -/
theorem scoreBlack_eq_priorWeightedPoint (h : Hypothesis) :
    scoreBlack h = priorWeightedPoint h.prior h.likeBlack := rfl

/-- The two-feature Raven score is the same generic prior-weighted point score,
with the feature likelihoods multiplied into the point component. -/
theorem scoreBlackCroak_eq_priorWeightedPoint (h : Hypothesis) :
    scoreBlackCroak h =
      priorWeightedPoint h.prior (h.likeBlack * h.likeCroak) := by
  simp [scoreBlackCroak, priorWeightedPoint]
  ring

/-- The book's `Black`-only abduction example, read through the generic
prior-weighted point surface: Crow wins because the common feature does not
overcome the base-rate prior. -/
theorem raven_crow_black_priorWeightedPoint :
    priorWeightedPoint raven.prior raven.likeBlack <
      priorWeightedPoint crow.prior crow.likeBlack := by
  simpa [scoreBlack_eq_priorWeightedPoint] using crow_best_on_black

/-- Adding the discriminating `Croaks` feature flips the prior-weighted
explanation score to Raven. -/
theorem raven_crow_blackCroak_priorWeightedPoint :
    priorWeightedPoint crow.prior (crow.likeBlack * crow.likeCroak) <
      priorWeightedPoint raven.prior (raven.likeBlack * raven.likeCroak) := by
  simpa [scoreBlackCroak_eq_priorWeightedPoint] using raven_best_on_black_and_croak

/-- Concrete value canary for the book example. -/
theorem ravenAbduction_priorWeightedPoint_values_canary :
    priorWeightedPoint raven.prior raven.likeBlack = (99 / 5000 : ℝ) ∧
      priorWeightedPoint crow.prior crow.likeBlack = (19 / 200 : ℝ) ∧
      priorWeightedPoint raven.prior (raven.likeBlack * raven.likeCroak) =
        (891 / 50000 : ℝ) ∧
      priorWeightedPoint crow.prior (crow.likeBlack * crow.likeCroak) =
        (19 / 20000 : ℝ) := by
  norm_num [priorWeightedPoint, raven, crow]

/-- The book's non-monotone best-explanation flip transported to the generic
prior-weighted point surface. -/
theorem ravenAbduction_priorWeightedPoint_flip_canary :
    priorWeightedPoint raven.prior raven.likeBlack <
        priorWeightedPoint crow.prior crow.likeBlack ∧
      priorWeightedPoint crow.prior (crow.likeBlack * crow.likeCroak) <
        priorWeightedPoint raven.prior (raven.likeBlack * raven.likeCroak) :=
  ⟨raven_crow_black_priorWeightedPoint, raven_crow_blackCroak_priorWeightedPoint⟩

end RavenAbductionBridge

end Mettapedia.Logic.PLN
