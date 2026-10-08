import Mettapedia.TypeTheory.ContextualSumComprehension
import Mettapedia.TypeTheory.ContextualModelTelescopes
import Mettapedia.TypeTheory.ContextualTypePresentationCast

/-!
# Dependent sum sections under substitution

The canonical sum lift commutes with supplied complete pair sections.
Combining this earned square with full-motive elimination substitution
preserves the complete dependent result value, including its annotation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSumSectionSubstitution

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualModelTelescopes ContextualSumComprehension ContextualTypeOperations
open ContextualProductComparison (selfExtend)

universe c s t m
variable {K : Cwf.{c, s, t, m}} {Γ Δ : K.Ctx}

theorem sumReindex_eq_extensionCast (sums : StableSums K) (σ : K.Sub Δ Γ)
    (A : K.Ty Γ) (B : K.Ty (K.ext Γ A)) :
    sumReindex sums σ A B =
      K.compS (TypeOver.extensionSubstitution σ (sums.operations.sigma A B))
        (ContextualTypePresentationCast.extensionCast
          (K := K) (sums.substitution.1 σ A B).symm) := rfl

theorem body_value_substitution (sums : StableSums K) (σ : K.Sub Δ Γ)
    (A : K.Ty Γ) (B : K.Ty (K.ext Γ A))
    (M : K.Ty (K.ext Γ (sums.operations.sigma A B)))
    (branch : K.Tm (K.ext (K.ext Γ A) B) (K.tySub M (pack sums A B))) :
    Value.substitute (⟨_, branch⟩ : Value K (K.ext (K.ext Γ A) B))
      (tupleReindex σ A B) = ⟨_, reindexBody sums σ A B M branch⟩ :=
  Sigma.ext (reindexBody_type sums σ A B M)
    (reindexBody_heq sums σ A B M branch).symm

theorem normalized_value_substitution (sums : StableSums K) (σ : K.Sub Δ Γ)
    (A : K.Ty Γ) (B : K.Ty (K.ext Γ A))
    (pair : K.Tm Γ (sums.operations.sigma A B)) :
    Value.substitute (⟨_, pair⟩ : Value K Γ) σ =
      ⟨_, normalize sums σ (K.tmSub pair σ)⟩ :=
  Sigma.ext (sums.substitution.1 σ A B) (normalize_heq sums σ (K.tmSub pair σ)).symm

theorem sumReindex_selfExtend (sums : StableSums K) (σ : K.Sub Δ Γ) (A : K.Ty Γ)
    (B : K.Ty (K.ext Γ A))
    (pair : K.Tm Γ (sums.operations.sigma A B)) :
    K.compS (sumReindex sums σ A B)
      (selfExtend K (normalize sums σ (K.tmSub pair σ))) =
      K.compS (selfExtend K pair) σ := by
  let newSum := sums.operations.sigma (K.tySub A σ)
    (K.tySub B (TypeOver.extensionSubstitution σ A))
  let newPair := normalize sums σ (K.tmSub pair σ)
  apply TypeOver.substitution_ext
  · rw [← K.comp_assoc, sumReindex_base, K.comp_assoc, wk_selfExtend,
      K.comp_id, ← K.comp_assoc, wk_selfExtend, K.id_comp]
  · have newTypes : K.tySub
        (K.tySub (sums.operations.sigma A B)
          (K.wk (sums.operations.sigma A B))) (sumReindex sums σ A B) =
        K.tySub newSum (K.wk newSum) := by
      rw [← K.tySub_comp, sumReindex_base, K.tySub_comp,
        sums.substitution.1]
    have oldTypes : K.tySub
        (K.tySub (sums.operations.sigma A B)
          (K.wk (sums.operations.sigma A B))) (selfExtend K pair) =
        sums.operations.sigma A B := by
      rw [← K.tySub_comp, wk_selfExtend, K.tySub_id]
    have left := (TypeOver.tmSub_comp_heq
      (K.vz (sums.operations.sigma A B)) (sumReindex sums σ A B)
      (selfExtend K newPair)).trans
      ((TypeOver.tmSub_heq newTypes (sumReindex_variable sums σ A B)
        (selfExtend K newPair)).trans
        ((vz_selfExtend newPair).trans (normalize_heq _ _ _)))
    have right := (TypeOver.tmSub_comp_heq
      (K.vz (sums.operations.sigma A B)) (selfExtend K pair) σ).trans
      (TypeOver.tmSub_heq oldTypes (vz_selfExtend pair) σ)
    exact left.trans right.symm

theorem eliminated_value_substitution (sums : StableSums K) (σ : K.Sub Δ Γ)
    (A : K.Ty Γ) (B : K.Ty (K.ext Γ A))
    (M : K.Ty (K.ext Γ (sums.operations.sigma A B)))
    (branch : K.Tm (K.ext (K.ext Γ A) B) (K.tySub M (pack sums A B)))
    (pair : K.Tm Γ (sums.operations.sigma A B)) :
    Value.substitute
      (⟨K.tySub M (selfExtend K pair),
        K.tmSub (eliminate sums A B M branch) (selfExtend K pair)⟩ : Value K Γ) σ =
      ⟨K.tySub (K.tySub M (sumReindex sums σ A B))
          (selfExtend K (normalize sums σ (K.tmSub pair σ))),
        K.tmSub (eliminate sums (K.tySub A σ)
          (K.tySub B (TypeOver.extensionSubstitution σ A))
          (K.tySub M (sumReindex sums σ A B)) (reindexBody sums σ A B M branch))
          (selfExtend K (normalize sums σ (K.tmSub pair σ)))⟩ := by
  apply Sigma.ext
  · change K.tySub (K.tySub M (selfExtend K pair)) σ = _
    rw [← K.tySub_comp, ← sumReindex_selfExtend sums σ A B pair, K.tySub_comp]
  · have original := (TypeOver.tmSub_comp_heq (eliminate sums A B M branch)
      (selfExtend K pair) σ).symm
    rw [← sumReindex_selfExtend sums σ A B pair] at original
    have throughLift := original.trans (TypeOver.tmSub_comp_heq (eliminate sums A B M branch)
      (sumReindex sums σ A B) (selfExtend K (normalize sums σ (K.tmSub pair σ))))
    rw [eliminate_substitution] at throughLift
    exact throughLift

end Mettapedia.TypeTheory.ContextualSumSectionSubstitution
