import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.Model
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank-budget reachability for consolidation

A rank-`r` adapter update is modeled operationally: its matrix must factor
through the `r`-dimensional bottleneck `Fin r → ℝ`.  This is not a definition
in terms of rank.  The main theorem proves that such a factorization exists
exactly when the required matrix rank fits the budget.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation

/-- A matrix update is reachable with budget `r` when it factors through an
`r`-dimensional adapter bottleneck. -/
def RankBudgetReachable {Row Column : Type*} [Fintype Column]
    (r : ℕ) (required : Matrix Row Column ℝ) : Prop :=
  ∃ left : Matrix Row (Fin r) ℝ, ∃ right : Matrix (Fin r) Column ℝ,
    left * right = required

/-- Factorization through an `r`-dimensional adapter is equivalent to the
usable rank test `required.rank ≤ r`. -/
theorem rankBudgetReachable_iff_rank_le
    {Row Column : Type*} [Fintype Row] [Fintype Column]
    [DecidableEq Column]
    (r : ℕ) (required : Matrix Row Column ℝ) :
    RankBudgetReachable r required ↔ required.rank ≤ r := by
  classical
  constructor
  · rintro ⟨left, right, rfl⟩
    exact (Matrix.rank_mul_le_left left right).trans (by
      simpa using left.rank_le_card_width)
  · intro hrank
    let effect : (Column → ℝ) →ₗ[ℝ] (Row → ℝ) := required.mulVecLin
    have hdimension :
        Module.finrank ℝ (LinearMap.range effect) ≤
          Module.finrank ℝ (Fin r → ℝ) := by
      simpa [Matrix.rank, effect] using hrank
    obtain ⟨embed, hembed⟩ :=
      finrank_le_iff_exists_linearMap.mp hdimension
    have hembedKer : LinearMap.ker embed = ⊥ :=
      LinearMap.ker_eq_bot.mpr hembed
    let rightMap : (Column → ℝ) →ₗ[ℝ] (Fin r → ℝ) :=
      embed.comp effect.rangeRestrict
    let leftMap : (Fin r → ℝ) →ₗ[ℝ] (Row → ℝ) :=
      (LinearMap.range effect).subtype.comp embed.leftInverse
    refine ⟨LinearMap.toMatrix' leftMap, LinearMap.toMatrix' rightMap, ?_⟩
    rw [← LinearMap.toMatrix'_comp]
    rw [← LinearMap.toMatrix'_toLin' required]
    congr 1
    ext value row
    simp only [leftMap, rightMap, LinearMap.comp_apply]
    rw [LinearMap.leftInverse_apply_of_inj hembedKer]
    rfl

/-- Full input-width budget reaches every update matrix. -/
theorem fullWidthBudget_reachable
    {Row Column : Type*} [Fintype Row] [Fintype Column]
    [DecidableEq Column]
    (required : Matrix Row Column ℝ) :
    RankBudgetReachable (Fintype.card Column) required := by
  rw [rankBudgetReachable_iff_rank_le]
  exact required.rank_le_card_width

/-- Any update whose rank exceeds the adapter budget is unreachable. -/
theorem rank_gt_budget_not_reachable
    {Row Column : Type*} [Fintype Row] [Fintype Column]
    [DecidableEq Column]
    {r : ℕ} {required : Matrix Row Column ℝ}
    (hrank : r < required.rank) :
    ¬ RankBudgetReachable r required := by
  rw [rankBudgetReachable_iff_rank_le]
  omega

/-- If every slow update lies within rank budget `r`, a faster effect whose
rank exceeds `r` cannot be faithfully consolidated. -/
theorem rankBudget_precludes_faithfulConsolidation
    {Slow Fast Row Column : Type*}
    [AddCommMonoid Slow] [Module ℝ Slow]
    [AddCommMonoid Fast] [Module ℝ Fast]
    [Fintype Row] [Fintype Column] [DecidableEq Column]
    (model : LinearEffectModel Slow Fast (Matrix Row Column ℝ))
    (r : ℕ) (slow : Slow) (fast : Fast)
    (hbudget : ∀ delta, RankBudgetReachable r (model.slowEffect delta))
    (hrank : r < (model.fastEffect fast).rank) :
    ¬ ∃ delta : Slow, FaithfulConsolidation model slow fast delta := by
  rintro ⟨delta, hfaithful⟩
  have heffect :=
    (faithfulConsolidation_iff_effect_eq model slow fast delta).1 hfaithful
  have hle :=
    (rankBudgetReachable_iff_rank_le r (model.slowEffect delta)).1
      (hbudget delta)
  rw [heffect] at hle
  omega

/-! ## Positive and negative fixtures -/

/-- When slow updates can be arbitrary matrices, the fast matrix itself is a
faithful full-rank consolidation delta. -/
noncomputable def fullMatrixEffectModel (Row Column : Type*)
    [Fintype Column] :
    LinearEffectModel (Matrix Row Column ℝ) (Matrix Row Column ℝ)
      (Matrix Row Column ℝ) where
  slowEffect := LinearMap.id
  fastEffect := LinearMap.id

theorem fullMatrixEffectModel_faithful
    {Row Column : Type*} [Fintype Column]
    (slow fast : Matrix Row Column ℝ) :
    FaithfulConsolidation (fullMatrixEffectModel Row Column) slow fast fast := by
  rw [faithfulConsolidation_iff_effect_eq]
  rfl

/-- A fixed rank-one update space: only the first output row can change. -/
noncomputable def firstRowMatrixMap :
    Matrix (Fin 1) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ where
  toFun input row column := if row = 0 then input 0 column else 0
  map_add' left right := by
    ext row column
    fin_cases row <;> simp
  map_smul' scalar input := by
    ext row column
    fin_cases row <;> simp

/-- Every matrix in the first-row update space factors through one adapter
dimension. -/
theorem firstRowMatrixMap_rankOne_reachable
    (input : Matrix (Fin 1) (Fin 2) ℝ) :
    RankBudgetReachable 1 (firstRowMatrixMap input) := by
  let left : Matrix (Fin 2) (Fin 1) ℝ :=
    fun row _ => if row = 0 then 1 else 0
  refine ⟨left, input, ?_⟩
  ext row column
  fin_cases row <;>
    simp [Matrix.mul_apply, left, firstRowMatrixMap]

/-- A rank-one adapter update space facing a full two-dimensional fast state. -/
noncomputable def rankOneSlowFullFastModel :
    LinearEffectModel (Matrix (Fin 1) (Fin 2) ℝ)
      (Matrix (Fin 2) (Fin 2) ℝ) (Matrix (Fin 2) (Fin 2) ℝ) where
  slowEffect := firstRowMatrixMap
  fastEffect := LinearMap.id

/-- The two-dimensional identity context has rank two. -/
theorem identityMatrixTwo_rank :
    (1 : Matrix (Fin 2) (Fin 2) ℝ).rank = 2 := by
  simp

/-- Negative fixture: rank-one adapter updates cannot faithfully consolidate
the rank-two identity context effect. -/
theorem rankOneAdapter_identityContext_no_faithfulConsolidation
    (slow : Matrix (Fin 1) (Fin 2) ℝ) :
    ¬ ∃ delta : Matrix (Fin 1) (Fin 2) ℝ,
      FaithfulConsolidation rankOneSlowFullFastModel slow
        (1 : Matrix (Fin 2) (Fin 2) ℝ) delta := by
  apply rankBudget_precludes_faithfulConsolidation
    rankOneSlowFullFastModel 1 slow (1 : Matrix (Fin 2) (Fin 2) ℝ)
  · exact firstRowMatrixMap_rankOne_reachable
  · norm_num [rankOneSlowFullFastModel, identityMatrixTwo_rank]

#print axioms rankBudgetReachable_iff_rank_le
#print axioms fullWidthBudget_reachable
#print axioms rankBudget_precludes_faithfulConsolidation
#print axioms rankOneAdapter_identityContext_no_faithfulConsolidation

end Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation
