import Mettapedia.Logic.PLNFirstOrder.Infinite
import Mettapedia.Logic.PLNIntuitionisticBridge

/-!
# Soundness Theorems for Arbitrary-Domain PLN Quantifiers

This module promotes the arbitrary-domain quantifier layer from
`PLNFirstOrder.Infinite` into a theorem surface parallel to the finite one,
without reintroducing any finiteness assumptions.
-/

namespace Mettapedia.Logic.PLNFirstOrder.Infinite

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Algebra.QuantaleWeakness
open Mettapedia.Logic.PLNQuantaleSemantics.PBit
open scoped ENNReal

variable {U : Type*}

/-- Arbitrary-domain universal quantification is weakness of the infinitary diagonal. -/
theorem main_theorem_1_forAll_is_weakness_inf
    (S : SatisfyingSetInf U) (μ : WeightFunctionInf U BinaryEvidence) :
    forAllEvalInf S μ = weaknessInf μ (SatisfyingSetInf.diagonal S) :=
  rfl

/-- Alias matching the finite soundness surface inside the infinitary namespace. -/
theorem main_theorem_1_forAll_is_weakness
    (S : SatisfyingSetInf U) (μ : WeightFunctionInf U BinaryEvidence) :
    forAllEvalInf S μ = weaknessInf μ (SatisfyingSetInf.diagonal S) :=
  main_theorem_1_forAll_is_weakness_inf S μ

/-- Goertzel's weakness bridge for arbitrary domains. -/
theorem forAll_is_weakness_of_diagonal
    (S : SatisfyingSetInf U) (μ : WeightFunctionInf U BinaryEvidence) :
    forAllEvalInf S μ = weaknessInf μ (SatisfyingSetInf.diagonal S) :=
  main_theorem_1_forAll_is_weakness_inf S μ

/-- Monotonicity in the weight function transports directly to the arbitrary-domain layer. -/
theorem main_theorem_2_monotonicity_inf
    (S : SatisfyingSetInf U)
    (μ₁ μ₂ : WeightFunctionInf U BinaryEvidence)
    (h : ∀ u, μ₁.μ u ≤ μ₂.μ u) :
    forAllEvalInf S μ₁ ≤ forAllEvalInf S μ₂ := by
  unfold forAllEvalInf weaknessInf
  apply sSup_le
  intro e he
  rcases he with ⟨uv, huv, rfl⟩
  have h1 := h uv.1
  have h2 := h uv.2
  have hmul : μ₁.μ uv.1 * μ₁.μ uv.2 ≤ μ₂.μ uv.1 * μ₂.μ uv.2 := by
    rw [BinaryEvidence.le_def] at h1 h2 ⊢
    constructor
    · simp only [BinaryEvidence.tensor_def]
      exact mul_le_mul' h1.1 h2.1
    · simp only [BinaryEvidence.tensor_def]
      exact mul_le_mul' h1.2 h2.2
  exact le_trans hmul (le_sSup ⟨uv, huv, rfl⟩)

/-- Alias matching the finite soundness surface inside the infinitary namespace. -/
theorem main_theorem_2_monotonicity
    (S : SatisfyingSetInf U)
    (μ₁ μ₂ : WeightFunctionInf U BinaryEvidence)
    (h : ∀ u, μ₁.μ u ≤ μ₂.μ u) :
    forAllEvalInf S μ₁ ≤ forAllEvalInf S μ₂ :=
  main_theorem_2_monotonicity_inf S μ₁ μ₂ h

/-- Weight monotonicity for arbitrary-domain universal quantification. -/
theorem forAllEvalInf_mono_weights
    (S : SatisfyingSetInf U)
    (μ₁ μ₂ : WeightFunctionInf U BinaryEvidence)
    (h : ∀ u, μ₁.μ u ≤ μ₂.μ u) :
    forAllEvalInf S μ₁ ≤ forAllEvalInf S μ₂ :=
  main_theorem_2_monotonicity_inf S μ₁ μ₂ h

/-- De Morgan duality for infinitary existential quantification. -/
theorem main_theorem_3_de_morgan_inf
    (S : SatisfyingSetInf U) (μ : WeightFunctionInf U BinaryEvidence) :
    thereExistsEvalInf S μ =
    BinaryEvidence.compl (forAllEvalInf (SatisfyingSetInf.neg S) μ) :=
  thereExistsEvalInf_deMorgan S μ

/-- Alias matching the finite soundness surface inside the infinitary namespace. -/
theorem main_theorem_3_de_morgan
    (S : SatisfyingSetInf U) (μ : WeightFunctionInf U BinaryEvidence) :
    thereExistsEvalInf S μ =
    BinaryEvidence.compl (forAllEvalInf (SatisfyingSetInf.neg S) μ) :=
  main_theorem_3_de_morgan_inf S μ

/-- Subset monotonicity of infinitary weakness. -/
theorem weaknessInf_mono_subset
    (μ : WeightFunctionInf U BinaryEvidence)
    (H₁ H₂ : Set (U × U))
    (h : H₁ ⊆ H₂) :
    weaknessInf μ H₁ ≤ weaknessInf μ H₂ :=
  weaknessInf_mono μ H₁ H₂ h

/-- Extensional infinitary `∀` remains below extensional infinitary `∃` on nonempty domains. -/
theorem main_theorem_4_extensional_order_inf
    [Nonempty U] (S : SatisfyingSetInf U) :
    forAllEvalExtInf S ≤ thereExistsEvalExtInf S :=
  forAllEvalExtInf_le_thereExistsEvalExtInf S

/-- Empty-domain vacuity for the extensional infinitary universal quantifier. -/
theorem forAllEvalExtInf_empty_eq_top
    [IsEmpty U] (S : SatisfyingSetInf U) :
    forAllEvalExtInf S = ⊤ :=
  forAllEvalExtInf_eq_top_of_isEmpty S

/-- Empty-domain vacuity for the extensional infinitary existential quantifier. -/
theorem thereExistsEvalExtInf_empty_eq_bot
    [IsEmpty U] (S : SatisfyingSetInf U) :
    thereExistsEvalExtInf S = ⊥ :=
  thereExistsEvalExtInf_eq_bot_of_isEmpty S

/-- Functoriality for arbitrary-domain quantifier evaluation. -/
theorem main_theorem_5_functoriality_inf
    {Q : Type*} [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q]
    (f : QuantaleHom BinaryEvidence Q)
    (S : SatisfyingSetInf U)
    (μ : WeightFunctionInf U BinaryEvidence) :
    f (forAllEvalInf S μ) =
    weaknessInf (WeightFunctionInf.map f μ) (SatisfyingSetInf.diagonal S) := by
  unfold forAllEvalInf weaknessInf
  rw [f.map_sSup']
  congr 1
  ext e
  simp only [Set.mem_image, Set.mem_setOf_eq, WeightFunctionInf.map_μ]
  constructor
  · intro he
    rcases he with ⟨e', ⟨uv, huv, he'⟩, rfl⟩
    exact ⟨uv, huv, by
      calc
        f (μ.μ uv.1) * f (μ.μ uv.2) = f (μ.μ uv.1 * μ.μ uv.2) := by
          symm
          exact f.map_mul' _ _
        _ = f e' := by rw [he']⟩
  · intro he
    rcases he with ⟨uv, huv, rfl⟩
    exact ⟨μ.μ uv.1 * μ.μ uv.2, ⟨uv, huv, rfl⟩, by rw [f.map_mul']⟩

/-- Alias matching the finite soundness surface inside the infinitary namespace. -/
theorem main_theorem_5_functoriality
    {Q : Type*} [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q]
    (f : QuantaleHom BinaryEvidence Q)
    (S : SatisfyingSetInf U)
    (μ : WeightFunctionInf U BinaryEvidence) :
    f (forAllEvalInf S μ) =
    weaknessInf (WeightFunctionInf.map f μ) (SatisfyingSetInf.diagonal S) :=
  main_theorem_5_functoriality_inf f S μ

/-- Dummett's axiom still holds pointwise over arbitrary domains. -/
theorem fo_dummett_pointwise_inf (P Q : SatisfyingSetInf U) (u : U) :
    (P.pred u ⇨ Q.pred u) ⊔ (Q.pred u ⇨ P.pred u) = ⊤ :=
  Mettapedia.Logic.PLNIntuitionisticBridge.evidence_dummett (P.pred u) (Q.pred u)

/-- Dummett's axiom also holds after infinitary universal quantification. -/
theorem fo_dummett_quantifiers_inf
    (P Q : SatisfyingSetInf U) (μ : WeightFunctionInf U BinaryEvidence) :
    (forAllEvalInf P μ ⇨ forAllEvalInf Q μ) ⊔
      (forAllEvalInf Q μ ⇨ forAllEvalInf P μ) = ⊤ :=
  Mettapedia.Logic.PLNIntuitionisticBridge.evidence_dummett (forAllEvalInf P μ)
    (forAllEvalInf Q μ)

/-- Constant-true sanity check for arbitrary-domain universal quantification. -/
theorem forAllEvalInf_constantTrue_eq_sup_all
    (μ : WeightFunctionInf U BinaryEvidence) :
    forAllEvalInf SatisfyingSetInf.constantTrue μ =
    sSup { e | ∃ (u : U) (v : U), e = μ.μ u * μ.μ v } :=
  forAllEvalInf_constantTrue μ

/-- Alias matching the finite weakness-connection surface inside the infinitary namespace. -/
theorem forAll_constantTrue_eq_sup_all
    (μ : WeightFunctionInf U BinaryEvidence) :
    forAllEvalInf SatisfyingSetInf.constantTrue μ =
    sSup { e | ∃ (u : U) (v : U), e = μ.μ u * μ.μ v } :=
  forAllEvalInf_constantTrue_eq_sup_all μ

/-- Constant-false sanity check for arbitrary-domain universal quantification. -/
theorem forAllEvalInf_constantFalse_eq_bot
    (μ : WeightFunctionInf U BinaryEvidence) :
    forAllEvalInf SatisfyingSetInf.constantFalse μ = ⊥ :=
  forAllEvalInf_constantFalse μ

/-- Alias matching the finite weakness-connection surface inside the infinitary namespace. -/
theorem forAll_constantFalse_eq_bot
    (μ : WeightFunctionInf U BinaryEvidence) :
    forAllEvalInf SatisfyingSetInf.constantFalse μ = ⊥ :=
  forAllEvalInf_constantFalse_eq_bot μ

end Mettapedia.Logic.PLNFirstOrder.Infinite
