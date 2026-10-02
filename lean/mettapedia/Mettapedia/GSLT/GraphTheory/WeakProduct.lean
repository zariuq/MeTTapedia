import Mettapedia.GSLT.GraphTheory.FactorInterpretation

/-!
# Canonical weak products of graph models

Bucciarelli–Salibra, §3 Definitions 5–6, first forms the injective partial
coding on a disjoint union and then completes every missing full input with
a fresh token. The resulting graph model retains both pure factor codes and
mixed supports. Its induced lambda theory is a lower bound of the factor
theories, by the actual interpreter comparison of §3.1 Proposition 13 and
Theorem 14. This is containment, not an intersection or idempotence claim.

A graph model is stratified, in the sense of §3.2, when it is the completion
of a proper partial pair; every weak product is (`WeakProduct.source_pair_proper`).
The semisensibility theorem for stratified models (§3.2 Theorem 29) is not
proved here.
-/

namespace Mettapedia.GSLT.GraphTheory

open Mettapedia.GSLT.Core

/-- The canonical completion of the source partial disjoint union. -/
noncomputable def WeakProduct (D₁ D₂ : GraphModel) : GraphModel :=
  PartialPair.Completion.graphModel (PartialPair.disjointUnion D₁ D₂)

notation:70 D₁ " ◇ " D₂ => WeakProduct D₁ D₂

namespace WeakProduct

open PartialPair

/-- The original left factor embeds into the completed carrier. -/
def leftEmbedding (D₁ D₂ : GraphModel) : D₁.Carrier ↪ (D₁ ◇ D₂).Carrier :=
  FactorFlattening.factorEmbed (FactorEmbedding.left D₁ D₂)

/-- The original right factor embeds into the completed carrier. -/
def rightEmbedding (D₁ D₂ : GraphModel) : D₂.Carrier ↪ (D₁ ◇ D₂).Carrier :=
  FactorFlattening.factorEmbed (FactorEmbedding.right D₁ D₂)

theorem left_ne_right (D₁ D₂ : GraphModel) (left : D₁.Carrier) (right : D₂.Carrier) :
    leftEmbedding D₁ D₂ left ≠ rightEmbedding D₁ D₂ right := by
  intro equality
  have original := (Completion.embed (disjointUnion D₁ D₂) 0).injective equality
  cases original

/-- Coding retains every pure left-factor input. -/
theorem code_left (D₁ D₂ : GraphModel) (support : Finset D₁.Carrier) (output : D₁.Carrier) :
    (D₁ ◇ D₂).code (support.map (leftEmbedding D₁ D₂)) (leftEmbedding D₁ D₂ output) =
      leftEmbedding D₁ D₂ (D₁.code support output) :=
  FactorInterpretation.code_factor (FactorEmbedding.left D₁ D₂) support output

/-- Coding retains every pure right-factor input. -/
theorem code_right (D₁ D₂ : GraphModel) (support : Finset D₂.Carrier) (output : D₂.Carrier) :
    (D₁ ◇ D₂).code (support.map (rightEmbedding D₁ D₂)) (rightEmbedding D₁ D₂ output) =
      rightEmbedding D₁ D₂ (D₂.code support output) :=
  FactorInterpretation.code_factor (FactorEmbedding.right D₁ D₂) support output

/-- A code in the left factor reflects its entire support and output. -/
theorem code_eq_left_iff (D₁ D₂ : GraphModel) (support : Finset (D₁ ◇ D₂).Carrier)
    (output : (D₁ ◇ D₂).Carrier) (token : D₁.Carrier) :
    (D₁ ◇ D₂).code support output = leftEmbedding D₁ D₂ token ↔
      ∃ (factorSupport : Finset D₁.Carrier) (factorOutput : D₁.Carrier),
        D₁.code factorSupport factorOutput = token ∧
        support = factorSupport.map (leftEmbedding D₁ D₂) ∧
        output = leftEmbedding D₁ D₂ factorOutput :=
  FactorInterpretation.code_eq_factor_iff (FactorEmbedding.left D₁ D₂) support output token

/-- A code in the right factor reflects its entire support and output. -/
theorem code_eq_right_iff (D₁ D₂ : GraphModel) (support : Finset (D₁ ◇ D₂).Carrier)
    (output : (D₁ ◇ D₂).Carrier) (token : D₂.Carrier) :
    (D₁ ◇ D₂).code support output = rightEmbedding D₁ D₂ token ↔
      ∃ (factorSupport : Finset D₂.Carrier) (factorOutput : D₂.Carrier),
        D₂.code factorSupport factorOutput = token ∧
        support = factorSupport.map (rightEmbedding D₁ D₂) ∧
        output = rightEmbedding D₁ D₂ factorOutput :=
  FactorInterpretation.code_eq_factor_iff (FactorEmbedding.right D₁ D₂) support output token

/-- Lift a factor environment through the left embedding. -/
def liftLeftEnv (D₁ D₂ : GraphModel) (environment : Env D₁) : Env (D₁ ◇ D₂) :=
  FactorInterpretation.liftEnv (FactorEmbedding.left D₁ D₂) environment

/-- Lift a factor environment through the right embedding. -/
def liftRightEnv (D₁ D₂ : GraphModel) (environment : Env D₂) : Env (D₁ ◇ D₂) :=
  FactorInterpretation.liftEnv (FactorEmbedding.right D₁ D₂) environment

/-- Actual left-factor interpretation is recovered from the lifted environment. -/
theorem interpret_left (D₁ D₂ : GraphModel) (term : LambdaTerm) (environment : Env D₁) :
    leftEmbedding D₁ D₂ ⁻¹' interpret (D₁ ◇ D₂) (liftLeftEnv D₁ D₂ environment) term =
      interpret D₁ environment term :=
  FactorInterpretation.interpret_lift_factor (FactorEmbedding.left D₁ D₂) term environment

/-- Actual right-factor interpretation is recovered from the lifted environment. -/
theorem interpret_right (D₁ D₂ : GraphModel) (term : LambdaTerm) (environment : Env D₂) :
    rightEmbedding D₁ D₂ ⁻¹' interpret (D₁ ◇ D₂) (liftRightEnv D₁ D₂ environment) term =
      interpret D₂ environment term :=
  FactorInterpretation.interpret_lift_factor (FactorEmbedding.right D₁ D₂) term environment

/-- Every valid equation of the weak product is valid in both factors. -/
theorem theory_inclusion (D₁ D₂ : GraphModel) :
    theoryOf (D₁ ◇ D₂) ⊆ theoryOf D₁ ∩ theoryOf D₂ := by
  intro equation valid
  exact ⟨FactorInterpretation.theory_subset_factor (FactorEmbedding.left D₁ D₂) valid,
    FactorInterpretation.theory_subset_factor (FactorEmbedding.right D₁ D₂) valid⟩

/-- The source partial union is proper: a mixed input is genuinely undefined.
Thus this weak product is a proper-partial-pair completion, as in source §3.2. -/
theorem source_pair_proper (D₁ D₂ : GraphModel) : (disjointUnion D₁ D₂).Proper := by
  classical
  exact disjointUnion_proper D₁ D₂ (Classical.arbitrary D₁.Carrier) (Classical.arbitrary D₂.Carrier)

end WeakProduct

end Mettapedia.GSLT.GraphTheory
