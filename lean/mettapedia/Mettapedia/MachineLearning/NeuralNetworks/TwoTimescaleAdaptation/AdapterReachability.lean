import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.RankReachability
import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.OnlineRegret

/-!
# Frozen-parent adapter reachability

For a frozen nonlinear parent, first-order adapter behavior is controlled by
Jacobians.  This file formalizes that local model: old outputs must remain in
the kernel of the old-output Jacobian, while the current loss must have a
nonzero component along that kernel.  The main equivalence constructs the sign
of an improving update instead of assuming one.

The final bridge reuses the existing operational rank-factorization theorem for
matrix-valued adapter effects.  No claim is made beyond the Jacobian-local
scope for a nonlinear trained network.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation

/-- Jacobian-local view of a finite adapter attached to a frozen parent. -/
structure FrozenAdapterJacobianModel
    (OldOutput Adapter : Type*) [Fintype Adapter] where
  oldJacobian : Matrix OldOutput Adapter ℝ
  currentGradient : Adapter → ℝ

section JacobianLocal

variable {OldOutput Adapter : Type*}
  [Fintype Adapter]

/-- The update leaves every old output unchanged to first order. -/
def PreservesOldOutputs
    (model : FrozenAdapterJacobianModel OldOutput Adapter)
    (update : Adapter → ℝ) : Prop :=
  model.oldJacobian.mulVec update = 0

/-- The update is a strict first-order descent direction for the current loss. -/
def StrictlyImprovesCurrentLoss
    (model : FrozenAdapterJacobianModel OldOutput Adapter)
    (update : Adapter → ℝ) : Prop :=
  model.currentGradient ⬝ᵥ update < 0

/-- The current gradient has a nonzero useful component in the kernel of the
old-output Jacobian. -/
def HasUsefulOldOutputKernelDirection
    (model : FrozenAdapterJacobianModel OldOutput Adapter) : Prop :=
  ∃ direction : Adapter → ℝ,
    PreservesOldOutputs model direction ∧
      model.currentGradient ⬝ᵥ direction ≠ 0

/-- Exact reachability criterion: preserving old outputs while improving the
current loss is possible iff the old-output kernel contains a direction with
nonzero current-gradient pairing. -/
theorem exists_preserving_strictImprovement_iff_usefulKernelDirection
    (model : FrozenAdapterJacobianModel OldOutput Adapter) :
    (∃ update : Adapter → ℝ,
      PreservesOldOutputs model update ∧
        StrictlyImprovesCurrentLoss model update) ↔
      HasUsefulOldOutputKernelDirection model := by
  constructor
  · rintro ⟨update, hpreserves, himproves⟩
    exact ⟨update, hpreserves, ne_of_lt himproves⟩
  · rintro ⟨direction, hpreserves, huseful⟩
    by_cases hnegative : model.currentGradient ⬝ᵥ direction < 0
    · exact ⟨direction, hpreserves, hnegative⟩
    · have hpositive : 0 < model.currentGradient ⬝ᵥ direction :=
        lt_of_le_of_ne (le_of_not_gt hnegative) (Ne.symm huseful)
      refine ⟨-direction, ?_, ?_⟩
      · unfold PreservesOldOutputs at hpreserves ⊢
        rw [Matrix.mulVec_neg, hpreserves]
        simp
      · unfold StrictlyImprovesCurrentLoss
        rw [dotProduct_neg]
        linarith

/-- Equivalent negative form: if the gradient annihilates the entire old
output kernel, strict retention-compatible plasticity is impossible. -/
theorem no_preserving_strictImprovement_iff_kernelAnnihilated
    (model : FrozenAdapterJacobianModel OldOutput Adapter) :
    (¬ ∃ update : Adapter → ℝ,
      PreservesOldOutputs model update ∧
        StrictlyImprovesCurrentLoss model update) ↔
      ∀ direction, PreservesOldOutputs model direction →
        model.currentGradient ⬝ᵥ direction = 0 := by
  rw [exists_preserving_strictImprovement_iff_usefulKernelDirection]
  unfold HasUsefulOldOutputKernelDirection
  constructor
  · intro hnone direction hpreserves
    by_contra hnonzero
    exact hnone ⟨direction, hpreserves, hnonzero⟩
  · rintro hannihilates ⟨direction, hpreserves, hnonzero⟩
    exact hnonzero (hannihilates direction hpreserves)

end JacobianLocal

/-! ## Concrete useful-kernel and exhausted-kernel fixtures -/

noncomputable def oneOldTwoAdapterJacobian : Matrix (Fin 1) (Fin 2) ℝ :=
  fun _ adapter => if adapter = 0 then 1 else 0

noncomputable def secondAdapterCurrentGradient : Fin 2 → ℝ :=
  fun adapter => if adapter = 1 then 1 else 0

noncomputable def usefulSecondAdapterUpdate : Fin 2 → ℝ :=
  fun adapter => if adapter = 1 then -1 else 0

noncomputable def usefulKernelFixture :
    FrozenAdapterJacobianModel (Fin 1) (Fin 2) where
  oldJacobian := oneOldTwoAdapterJacobian
  currentGradient := secondAdapterCurrentGradient

theorem usefulKernelFixture_preserves_and_improves_positive_example :
    PreservesOldOutputs usefulKernelFixture usefulSecondAdapterUpdate ∧
      StrictlyImprovesCurrentLoss usefulKernelFixture usefulSecondAdapterUpdate := by
  constructor
  · funext old
    fin_cases old
    simp [usefulKernelFixture, oneOldTwoAdapterJacobian,
      usefulSecondAdapterUpdate, Matrix.mulVec, dotProduct]
  · norm_num [StrictlyImprovesCurrentLoss, usefulKernelFixture,
      secondAdapterCurrentGradient, usefulSecondAdapterUpdate,
      dotProduct, Fin.sum_univ_two]

noncomputable def identityOldOutputFixture
    (currentGradient : Fin 2 → ℝ) :
    FrozenAdapterJacobianModel (Fin 2) (Fin 2) where
  oldJacobian := 1
  currentGradient := currentGradient

theorem identityOldOutputFixture_preservation_forces_zero
    (currentGradient update : Fin 2 → ℝ)
    (hpreserves : PreservesOldOutputs
      (identityOldOutputFixture currentGradient) update) :
    update = 0 := by
  unfold PreservesOldOutputs identityOldOutputFixture at hpreserves
  simpa using hpreserves

/-- Negative fixture: when the old-output Jacobian is injective, its kernel is
exhausted and exact old-output retention leaves no plastic direction. -/
theorem identityOldOutputFixture_no_strictPlasticity_negative_example
    (currentGradient : Fin 2 → ℝ) :
    ¬ ∃ update : Fin 2 → ℝ,
      PreservesOldOutputs (identityOldOutputFixture currentGradient) update ∧
        StrictlyImprovesCurrentLoss
          (identityOldOutputFixture currentGradient) update := by
  rintro ⟨update, hpreserves, himproves⟩
  have hzero := identityOldOutputFixture_preservation_forces_zero
    currentGradient update hpreserves
  subst update
  simp [StrictlyImprovesCurrentLoss] at himproves

/-! ## Bridge to operational adapter-rank reachability -/

/-- Matrix-valued Jacobian effects are implementable through an `r`-slot
adapter exactly when their matrix rank fits the adapter budget. -/
theorem frozenAdapterEffect_reachable_iff_rank_le
    {Row Column : Type*} [Fintype Row] [Fintype Column]
    [DecidableEq Column]
    (rankBudget : ℕ) (requiredEffect : Matrix Row Column ℝ) :
    RankBudgetReachable rankBudget requiredEffect ↔
      requiredEffect.rank ≤ rankBudget :=
  rankBudgetReachable_iff_rank_le rankBudget requiredEffect

theorem frozenAdapterEffect_rankExhausted_negative_example
    {Row Column : Type*} [Fintype Row] [Fintype Column]
    [DecidableEq Column]
    {rankBudget : ℕ} {requiredEffect : Matrix Row Column ℝ}
    (hexceeds : rankBudget < requiredEffect.rank) :
    ¬ RankBudgetReachable rankBudget requiredEffect :=
  rank_gt_budget_not_reachable hexceeds

end Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation
