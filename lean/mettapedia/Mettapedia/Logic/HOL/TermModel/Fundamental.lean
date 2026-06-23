import Mettapedia.Logic.HOL.TermModel.PreModelWrapper

/-!
# The fundamental lemma and `models ↔ membership`

The engine of completeness: for any term `t` and any **Rep-related** environment pair
(a semantic valuation `e` and a closed-term substitution `ρ` with `Rep (e v) (ρ v)`),
the denotation `⟦t⟧_e` is represented by `t[ρ]`.  Proved by structural induction on the
term — the type recursion lives only inside `Rep`/`Eqv`, so the prop-quantification trap
never appears.  The `eq` case uses the `Eqv`-realization coincidence; the `λ`-case uses
`beta` + `instantiate_subst_lift`; the `∀`/`∃` cases use `World.mem_all/ex_iff`.

The `prop` corollary at the empty environment is `models_iff_mem`.
-/

namespace Mettapedia.Logic.HOL
namespace ClosedTheorySet

open Mettapedia.Logic.HOL.WithParams
open scoped Classical

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

/-- **Equality coincidence.**  Semantic extensional equality of represented elements
matches provable equality of their representatives. -/
theorem eqv_rep_iff (M : World (WithParams Const))
    (hC : ∀ χ : ClosedFormula (WithParams Const),
      χ ∈ M.carrier ∨ (.not χ : ClosedFormula (WithParams Const)) ∈ M.carrier) :
    ∀ (τ : Ty Base) {d d' : Ty.denote (termCarrier M) τ}
      {t t' : ClosedTerm (WithParams Const) τ},
      Rep M τ d t → Rep M τ d' t' →
      (PreModel.Eqv (termPreModel M hC) τ d d' ↔
        (.eq t t' : ClosedFormula (WithParams Const)) ∈ M.carrier)
  | .prop, d, d', t, t', hd, hd' => by
      simp only [Rep] at hd hd'
      simp only [PreModel.Eqv]
      rw [hd, hd']
      exact ⟨fun h => eqProp_mem_of_iff M hC h, fun h => eqProp_mem_iff h⟩
  | .base b, d, d', t, t', hd, hd' => by
      simp only [Rep] at hd hd'
      simp only [PreModel.Eqv]
      rw [hd, hd']
      exact ⟨fun h => TermDom.mk_eq.mp (congrArg ULift.down h),
             fun h => congrArg ULift.up (TermDom.mk_eq.mpr h)⟩
  | .arr σ ρ, d, d', t, t', hd, hd' => by
      simp only [Rep] at hd hd'
      simp only [PreModel.Eqv]
      constructor
      · intro heqv
        refine eq_of_app_eq M (fun w => ?_)
        exact (eqv_rep_iff M hC ρ (hd (tval M σ w) w (rep_tval M hC w))
            (hd' (tval M σ w) w (rep_tval M hC w))).mp
          (heqv (tval M σ w) ⟨w, rep_tval M hC w⟩)
      · intro heq x hx
        obtain ⟨u, hu⟩ := hx
        exact (eqv_rep_iff M hC ρ (hd x u hu) (hd' x u hu)).mpr (World.eq_app_mem u heq)

/-- **Fundamental lemma.**  Denotation is represented by the substituted term, for
Rep-related environments. -/
theorem fundamental (M : World (WithParams Const))
    (hC : ∀ χ : ClosedFormula (WithParams Const),
      χ ∈ M.carrier ∨ (.not χ : ClosedFormula (WithParams Const)) ∈ M.carrier) :
    ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term (WithParams Const) Γ τ)
      (e : PreModel.Valuation (termPreModel M hC) Γ) (ρ : Subst (WithParams Const) Γ []),
      (∀ {σ : Ty Base} (v : Var Γ σ), Rep M σ (e v) (ρ v)) →
      Rep M τ (PreModel.denote (termPreModel M hC) t e) (subst ρ t)
  | _, _, .var v, e, ρ, h => by
      simpa only [PreModel.denote, subst] using h v
  | _, _, .const c, e, ρ, h => by
      simpa only [PreModel.denote, subst, termPreModel_constDen] using rep_tval M hC (.const c)
  | _, _, .app f a, e, ρ, h => by
      have ihf := fundamental M hC f e ρ h
      have iha := fundamental M hC a e ρ h
      simp only [Rep] at ihf
      simpa only [PreModel.denote, subst] using ihf _ _ iha
  | _, _, .lam t, e, ρ, h => by
      simp only [PreModel.denote, subst, Rep]
      intro d u hdu
      have hbeta : (.eq (.app (.lam (subst (Subst.lift (Base := Base) ρ) t)) u)
          (subst (extendEnv ρ u) t) : ClosedFormula (WithParams Const)) ∈ M.carrier := by
        have hb := ExtDerivation.beta (Const := WithParams Const)
          (Δ := ([] : ClosedTheory (WithParams Const))) (Base := Base)
          u (subst (Subst.lift (Base := Base) ρ) t)
        rw [instantiate_subst_lift ρ u t] at hb
        exact World.mem_of_provable (W := M)
          (provable_of_closedTheory (fun {ψ} hψ => by cases hψ) hb)
      refine Rep_respects_eq M _ (World.eq_symm_mem hbeta) ?_
      refine fundamental M hC t (PreModel.extend (termPreModel M hC) e d) (extendEnv ρ u) ?_
      intro σ' v
      cases v with
      | vz => exact hdu
      | vs w => exact h w
  | _, _, .top, e, ρ, h => by
      simp only [PreModel.denote, subst, Rep]
      exact iff_of_true trivial World.top_mem
  | _, _, .bot, e, ρ, h => by
      simp only [PreModel.denote, subst, Rep]
      exact iff_of_false not_false World.bot_not_mem
  | _, _, .and a b, e, ρ, h => by
      have iha := fundamental M hC a e ρ h
      have ihb := fundamental M hC b e ρ h
      simp only [Rep] at iha ihb ⊢
      simp only [PreModel.denote, subst]
      rw [iha, ihb]
      exact ⟨fun ⟨x, y⟩ => World.and_mem x y,
             fun hm => ⟨World.and_left_mem hm, World.and_right_mem hm⟩⟩
  | _, _, .or a b, e, ρ, h => by
      have iha := fundamental M hC a e ρ h
      have ihb := fundamental M hC b e ρ h
      simp only [Rep] at iha ihb ⊢
      simp only [PreModel.denote, subst]
      rw [iha, ihb]
      exact ⟨fun hm => hm.elim (fun x => World.or_left_mem x) (fun y => World.or_right_mem y),
             fun hm => M.prime_or hm⟩
  | _, _, .imp a b, e, ρ, h => by
      have iha := fundamental M hC a e ρ h
      have ihb := fundamental M hC b e ρ h
      simp only [Rep] at iha ihb ⊢
      simp only [PreModel.denote, subst]
      rw [iha, ihb]
      exact ⟨fun hm => imp_mem M hC hm, fun hm hx => World.mp hm hx⟩
  | _, _, .not a, e, ρ, h => by
      have iha := fundamental M hC a e ρ h
      simp only [Rep] at iha ⊢
      simp only [PreModel.denote, subst]
      rw [iha]
      exact (not_mem_iff M hC).symm
  | _, _, .eq s u, e, ρ, h => by
      simp only [PreModel.denote, subst, Rep]
      exact eqv_rep_iff M hC _ (fundamental M hC s e ρ h) (fundamental M hC u e ρ h)
  | _, _, .all φ, e, ρ, h => by
      simp only [PreModel.denote, subst, Rep]
      rw [World.mem_all_iff]
      constructor
      · intro hsem w
        have ih := fundamental M hC φ (PreModel.extend (termPreModel M hC) e (tval M _ w))
          (extendEnv ρ w) (by intro σ' v; cases v with | vz => exact rep_tval M hC w | vs y => exact h y)
        simp only [Rep] at ih
        rw [instantiate_subst_lift]
        exact ih.mp (hsem (tval M _ w) ⟨w, rep_tval M hC w⟩)
      · intro hmem x hx
        obtain ⟨u, hu⟩ := hx
        have ih := fundamental M hC φ (PreModel.extend (termPreModel M hC) e x)
          (extendEnv ρ u) (by intro σ' v; cases v with | vz => exact hu | vs y => exact h y)
        simp only [Rep] at ih
        refine ih.mpr ?_
        have := hmem u
        rwa [instantiate_subst_lift] at this
  | _, _, .ex φ, e, ρ, h => by
      simp only [PreModel.denote, subst, Rep]
      rw [World.mem_ex_iff]
      constructor
      · rintro ⟨x, hx, hsem⟩
        obtain ⟨u, hu⟩ := hx
        have ih := fundamental M hC φ (PreModel.extend (termPreModel M hC) e x)
          (extendEnv ρ u) (by intro σ' v; cases v with | vz => exact hu | vs y => exact h y)
        simp only [Rep] at ih
        exact ⟨u, by rw [instantiate_subst_lift]; exact ih.mp hsem⟩
      · rintro ⟨w, hw⟩
        refine ⟨tval M _ w, ⟨w, rep_tval M hC w⟩, ?_⟩
        have ih := fundamental M hC φ (PreModel.extend (termPreModel M hC) e (tval M _ w))
          (extendEnv ρ w) (by intro σ' v; cases v with | vz => exact rep_tval M hC w | vs y => exact h y)
        simp only [Rep] at ih
        rw [instantiate_subst_lift] at hw
        exact ih.mpr hw

/-- **`models ↔ membership`.**  A closed formula is satisfied by the canonical term
`PreModel` exactly when it belongs to the world. -/
theorem models_iff_mem (M : World (WithParams Const))
    (hC : ∀ χ : ClosedFormula (WithParams Const),
      χ ∈ M.carrier ∨ (.not χ : ClosedFormula (WithParams Const)) ∈ M.carrier)
    (φ : ClosedFormula (WithParams Const)) :
    (termPreModel M hC).models φ ↔ φ ∈ M.carrier := by
  have hf := fundamental M hC φ (fun v => nomatch v)
    (Subst.id (Base := Base) (Const := WithParams Const) (Γ := [])) (fun v => nomatch v)
  rw [subst_id] at hf
  exact hf

end ClosedTheorySet
end Mettapedia.Logic.HOL
