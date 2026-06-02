import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# RavenAbduction — abduction as inference to the best explanation, and base-rate dilution

Companion to `RavenAsymmetricInduction`. Where **induction** *learns* the
conditionals (`P(black|raven)=1`, `P(raven|black)=R/(R+M)`), **abduction** *uses*
them: observe a bird's features and hypothesize which species best explains them.

We model the (unnormalized) abductive posterior of a hypothesis `h` given features as

  `score(h) = prior(h) · ∏ᵢ P(featureᵢ | h)`,

so the **best explanation** is the hypothesis with the largest score (normalization
cancels in comparisons). The point of the example:

* From a **single common feature** (`Black`) the most plausible species is the
  *common* one — base rates dominate, because `Black` barely discriminates. This is
  the abductive face of `strength_blackRaven`: `P(raven|black)` is small.
* A **discriminating feature** (`Croaks`) can overturn the base-rate disadvantage,
  so the best explanation is **non-monotone in evidence**.

`sorry`-free, `axiom`-free.
-/

namespace Mettapedia.Logic.RavenAbduction

/-- A species hypothesis: prior plausibility and per-feature likelihoods
`P(feature | species)`. -/
structure Hypothesis where
  prior : ℝ
  likeBlack : ℝ
  likeCroak : ℝ

/-- Unnormalized abductive posterior from the single feature `Black`:
`prior · P(Black | h)`. -/
def scoreBlack (h : Hypothesis) : ℝ := h.prior * h.likeBlack

/-- Unnormalized abductive posterior from `Black` and `Croaks`:
`prior · P(Black | h) · P(Croaks | h)`. -/
def scoreBlackCroak (h : Hypothesis) : ℝ := h.prior * h.likeBlack * h.likeCroak

theorem scoreBlackCroak_eq (h : Hypothesis) :
    scoreBlackCroak h = scoreBlack h * h.likeCroak := rfl

/-! ## General theory -/

/-- **Base rates dominate a non-discriminating feature.** If two hypotheses are
equally good at the shared feature `Black`, the a-priori more plausible one is the
better single-feature explanation — even if it is the "wrong" answer. -/
theorem base_rate_dominates_shared_feature (r c : Hypothesis)
    (hlike : r.likeBlack = c.likeBlack) (hpos : 0 < c.likeBlack)
    (hprior : r.prior < c.prior) :
    scoreBlack r < scoreBlack c := by
  unfold scoreBlack
  rw [hlike]
  exact mul_lt_mul_of_pos_right hprior hpos

/-- **A discriminating feature flips the best explanation iff it overturns the gap.**
Hypothesis `r` is the better explanation of `Black ∧ Croaks` exactly when its
`Croaks`-weighted single-feature score beats `c`'s — which can happen even when `r`
lost on `Black` alone. -/
theorem better_with_croak_iff (r c : Hypothesis) :
    scoreBlackCroak c < scoreBlackCroak r ↔
      scoreBlack c * c.likeCroak < scoreBlack r * r.likeCroak := by
  rw [scoreBlackCroak_eq, scoreBlackCroak_eq]

/-! ## Concrete worked example: raven vs. crow -/

/-- A raven: rare, almost always black, croaks. -/
def raven : Hypothesis := ⟨0.02, 0.99, 0.90⟩
/-- A crow: more common, usually black, essentially never croaks (it caws). -/
def crow : Hypothesis := ⟨0.10, 0.95, 0.01⟩

/-- **`Black` alone ⇒ the common species wins** (`Crow`), by base-rate dilution. -/
theorem crow_best_on_black : scoreBlack raven < scoreBlack crow := by
  unfold scoreBlack raven crow; norm_num

/-- **`Black ∧ Croaks` ⇒ the discriminating feature flips it to `Raven`.** -/
theorem raven_best_on_black_and_croak :
    scoreBlackCroak crow < scoreBlackCroak raven := by
  unfold scoreBlackCroak crow raven; norm_num

/-- **The best explanation is non-monotone in evidence.** `Crow` best explains
`Black` alone, yet `Raven` best explains `Black ∧ Croaks`. This is the abductive
face of the raven asymmetry: one common feature under-determines the explanation;
a discriminating feature decides it. -/
theorem best_explanation_flips :
    scoreBlack raven < scoreBlack crow ∧
      scoreBlackCroak crow < scoreBlackCroak raven :=
  ⟨crow_best_on_black, raven_best_on_black_and_croak⟩

end Mettapedia.Logic.RavenAbduction
