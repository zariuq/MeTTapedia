import Mettapedia.AutoBooks.Codex.Henkin1950.Semantics
import Mettapedia.Logic.HOL.Soundness

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL

/-!
Extensional soundness consequences for Henkin (1950).

The raw HOL soundness theorem already covers the base derivation calculus.
This file extends that semantic story to the extensional overlay under the
explicit model-side `EqAppArgSound` hypothesis isolated in `Semantics.lean`.
-/

/-- Open-formula soundness for the extensional overlay, assuming the ambient
paper-general model validates higher-order argument congruence. -/
theorem extensional_derivation_sound_of_eqAppArgSound
    {Γ : Ctx Atom} {Δ : List (Formula Γ)} {φ : Formula Γ}
    (d : ExtDerivation Primitive Δ φ) :
    ∀ {M : GeneralModel} {ρ : HenkinModel.Valuation M.toHenkinModel Γ},
      EqAppArgSound M →
      HenkinModel.ValuationAdmissible M.toHenkinModel ρ →
      Mettapedia.Logic.HOL.Soundness.SatisfiesHyps M.toHenkinModel ρ Δ →
      (HenkinModel.denote M.toHenkinModel φ ρ).down := by
  induction d with
  | hyp hmem =>
      intro M ρ _ hρ hΔ
      exact hΔ _ hmem
  | topI =>
      intro M ρ _ hρ hΔ
      simp
  | botE h ih =>
      intro M ρ hSound hρ hΔ
      exact False.elim (ih hSound hρ hΔ)
  | andI hφ hψ ihφ ihψ =>
      intro M ρ hSound hρ hΔ
      exact ⟨ihφ hSound hρ hΔ, ihψ hSound hρ hΔ⟩
  | andEL h ih =>
      intro M ρ hSound hρ hΔ
      exact (ih hSound hρ hΔ).1
  | andER h ih =>
      intro M ρ hSound hρ hΔ
      exact (ih hSound hρ hΔ).2
  | orIL h ih =>
      intro M ρ hSound hρ hΔ
      exact Or.inl (ih hSound hρ hΔ)
  | orIR h ih =>
      intro M ρ hSound hρ hΔ
      exact Or.inr (ih hSound hρ hΔ)
  | orE hor hφ hψ ihor ihφ ihψ =>
      intro M ρ hSound hρ hΔ
      rcases ihor hSound hρ hΔ with h | h
      · exact ihφ hSound hρ (by
          intro χ hχ
          rw [List.mem_cons] at hχ
          rcases hχ with rfl | hχ
          · simpa using h
          · exact hΔ _ hχ)
      · exact ihψ hSound hρ (by
          intro χ hχ
          rw [List.mem_cons] at hχ
          rcases hχ with rfl | hχ
          · simpa using h
          · exact hΔ _ hχ)
  | impI h ih =>
      intro M ρ hSound hρ hΔ hφ
      exact ih hSound hρ (by
        intro χ hχ
        rw [List.mem_cons] at hχ
        rcases hχ with rfl | hχ
        · simpa using hφ
        · exact hΔ _ hχ)
  | impE himp hφ ihimp ihφ =>
      intro M ρ hSound hρ hΔ
      exact (ihimp hSound hρ hΔ) (ihφ hSound hρ hΔ)
  | notI h ih =>
      intro M ρ hSound hρ hΔ hφ
      exact ih hSound hρ (by
        intro χ hχ
        rw [List.mem_cons] at hχ
        rcases hχ with rfl | hχ
        · simpa using hφ
        · exact hΔ _ hχ)
  | notE hnot hφ ihnot ihφ =>
      intro M ρ hSound hρ hΔ
      exact (ihnot hSound hρ hΔ) (ihφ hSound hρ hΔ)
  | allI h ih =>
      intro M ρ hSound hρ hΔ x hx
      exact ih hSound
        (HenkinModel.extend_admissible M.toHenkinModel hρ hx)
        (Mettapedia.Logic.HOL.Soundness.satisfies_weakenHyps M.toHenkinModel hΔ x)
  | allE t h ih =>
      intro M ρ hSound hρ hΔ
      have hall := ih hSound hρ hΔ
      have ht : M.toHenkinModel.adm _ (HenkinModel.denote M.toHenkinModel t ρ) :=
        HenkinModel.denote_admissible M.toHenkinModel hρ t
      exact (Mettapedia.Logic.HOL.Soundness.denote_instantiate M.toHenkinModel t _ ρ).mpr
        (hall _ ht)
  | exI t h ih =>
      intro M ρ hSound hρ hΔ
      refine ⟨HenkinModel.denote M.toHenkinModel t ρ,
        HenkinModel.denote_admissible M.toHenkinModel hρ t, ?_⟩
      exact (Mettapedia.Logic.HOL.Soundness.denote_instantiate M.toHenkinModel t _ ρ).mp
        (ih hSound hρ hΔ)
  | exE hex hbody ihex ihbody =>
      intro M ρ hSound hρ hΔ
      rcases ihex hSound hρ hΔ with ⟨x, hx, hφ⟩
      have hbody' :=
        ihbody hSound
          (HenkinModel.extend_admissible M.toHenkinModel hρ hx)
          (by
            intro χ hχ
            rw [List.mem_cons] at hχ
            rcases hχ with rfl | hχ
            · exact hφ
            · exact
                Mettapedia.Logic.HOL.Soundness.satisfies_weakenHyps
                  M.toHenkinModel hΔ x _ hχ)
      simpa using hbody'
  | eqRefl t =>
      intro M ρ hSound hρ hΔ
      exact
        HenkinModel.eqv_refl M.toHenkinModel
          (HenkinModel.denote_admissible M.toHenkinModel hρ t)
  | eqSymm h ih =>
      intro M ρ hSound hρ hΔ
      exact HenkinModel.eqv_symm M.toHenkinModel (ih hSound hρ hΔ)
  | eqTrans htu huv ihtu ihuv =>
      intro M ρ hSound hρ hΔ
      exact HenkinModel.eqv_trans M.toHenkinModel
        (ihtu hSound hρ hΔ) (ihuv hSound hρ hΔ)
  | eqPropI hpq hqp ihpq ihqp =>
      intro M ρ hSound hρ hΔ
      constructor
      · simpa [HenkinModel.denote, PreModel.denote] using ihpq hSound hρ hΔ
      · simpa [HenkinModel.denote, PreModel.denote] using ihqp hSound hρ hΔ
  | eqPropEL hpq ih =>
      intro M ρ hSound hρ hΔ
      have hEq := ih hSound hρ hΔ
      simp [HenkinModel.denote, PreModel.denote] at hEq ⊢
      exact hEq.mp
  | eqPropER hpq ih =>
      intro M ρ hSound hρ hΔ
      have hEq := ih hSound hρ hΔ
      simp [HenkinModel.denote, PreModel.denote] at hEq ⊢
      exact hEq.mpr
  | eqApp t h ih =>
      intro M ρ hSound hρ hΔ
      exact HenkinModel.eqv_arr_apply M.toHenkinModel
        (ih hSound hρ hΔ)
        (HenkinModel.denote_admissible M.toHenkinModel hρ t)
  | eqAppArg f h ih =>
      intro M ρ hSound hρ hΔ
      simpa [HenkinModel.denote, PreModel.denote] using
        hSound (HenkinModel.denote M.toHenkinModel f ρ)
          (HenkinModel.denote_admissible M.toHenkinModel hρ f)
          (HenkinModel.denote_admissible M.toHenkinModel hρ _)
          (HenkinModel.denote_admissible M.toHenkinModel hρ _)
          (ih hSound hρ hΔ)
  | eqLam h ih =>
      intro M ρ hSound hρ hΔ x hx
      simpa [HenkinModel.denote, PreModel.denote] using ih hSound
        (HenkinModel.extend_admissible M.toHenkinModel hρ hx)
        (Mettapedia.Logic.HOL.Soundness.satisfies_weakenHyps M.toHenkinModel hΔ x)
  | funExt h ih =>
      intro M ρ hSound hρ hΔ x hx
      simpa [HenkinModel.denote, PreModel.denote, HenkinModel.extend, PreModel.extend] using
        (ih hSound hρ hΔ x hx)
  | beta t u =>
      intro M ρ hSound hρ hΔ
      simpa [HenkinModel.denote, PreModel.denote] using
        HenkinModel.eqv_refl M.toHenkinModel
          (HenkinModel.denote_admissible M.toHenkinModel hρ
            (instantiate (Base := Atom) t u))
  | eta f =>
      intro M ρ hSound hρ hΔ x hx
      simpa [HenkinModel.denote, PreModel.denote, HenkinModel.extend, PreModel.extend] using
        (HenkinModel.eqv_refl M.toHenkinModel
          (M.toHenkinModel.app_mem
            (HenkinModel.denote_admissible M.toHenkinModel hρ f) hx))

/-- Closed-theory extensional provability is semantically sound in any
paper-general model satisfying `EqAppArgSound`. -/
theorem models_of_setProvable_of_eqAppArgSound
    {T : ClosedTheorySet} {φ : Sentence}
    (M : GeneralModel)
    (hSound : EqAppArgSound M)
    (hT : ∀ ψ : Sentence, ψ ∈ T → HenkinModel.models M.toHenkinModel ψ) :
    SetProvable T φ → HenkinModel.models M.toHenkinModel φ := by
  rintro ⟨Δ, hΔ, hφ⟩
  exact
    extensional_derivation_sound_of_eqAppArgSound hφ hSound
      (by
        intro τ v
        nomatch v)
      (by
        intro ψ hψ
        simpa [HenkinModel.models, PreModel.models, emptyValuation] using
          hT ψ (hΔ ψ hψ))

/-- Any closed theory satisfied in a paper-general model class where
`EqAppArgSound` uniformly holds is consistent in the extensional closed-theory
sense. -/
theorem consistent_of_satisfiable_of_eqAppArgSound
    (hSound : ∀ M : GeneralModel, EqAppArgSound M)
    {T : ClosedTheorySet} :
    Satisfiable T → Consistent T := by
  intro hSat hBot
  rcases hSat with ⟨M, hM⟩
  exact
    (HenkinModel.models_bot M.toHenkinModel) <|
      models_of_setProvable_of_eqAppArgSound M (hSound M) hM hBot

end Mettapedia.AutoBooks.Codex.Henkin1950
