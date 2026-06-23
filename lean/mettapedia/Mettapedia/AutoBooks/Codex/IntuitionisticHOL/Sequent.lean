import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Terms
import Mettapedia.Logic.HOL.DerivationExtensionality

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Antecedent weakening along one context extension. -/
def weakenAntecedents (σ : Ty Base) (Δ : List (Formula Const Γ)) :
    List (Formula Const (σ :: Γ)) :=
  Δ.map (weaken (Base := Base) (σ := σ))

/-- Paper-facing sequent package. -/
structure Sequent (Const : Ty Base → Type v) (Γ : Ctx Base) where
  antecedents : List (Formula Const Γ)
  succedent : Formula Const Γ

/-- Cut-free sequent calculus for the initial soundness layer. -/
inductive Derivable (Const : Ty Base → Type v) :
    {Γ : Ctx Base} → List (Formula Const Γ) → Formula Const Γ → Prop where
  | ax {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
      φ ∈ Δ → Derivable Const Δ φ
  | topR {Γ : Ctx Base} {Δ : List (Formula Const Γ)} :
      Derivable Const Δ .top
  | botL {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
      Derivable Const (.bot :: Δ) φ
  | andL {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ χ : Formula Const Γ} :
      Derivable Const (φ :: ψ :: Δ) χ →
      Derivable Const (.and φ ψ :: Δ) χ
  | andR {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      Derivable Const Δ φ →
      Derivable Const Δ ψ →
      Derivable Const Δ (.and φ ψ)
  | orL {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ χ : Formula Const Γ} :
      Derivable Const (φ :: Δ) χ →
      Derivable Const (ψ :: Δ) χ →
      Derivable Const (.or φ ψ :: Δ) χ
  | orR₁ {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      Derivable Const Δ φ →
      Derivable Const Δ (.or φ ψ)
  | orR₂ {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      Derivable Const Δ ψ →
      Derivable Const Δ (.or φ ψ)
  | impL {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ χ : Formula Const Γ} :
      Derivable Const Δ φ →
      Derivable Const (ψ :: Δ) χ →
      Derivable Const (.imp φ ψ :: Δ) χ
  | impR {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      Derivable Const (φ :: Δ) ψ →
      Derivable Const Δ (.imp φ ψ)
  | allL {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {χ : Formula Const Γ}
      (t : Term Const Γ σ) :
      Derivable Const (instantiate (Base := Base) t φ :: Δ) χ →
      Derivable Const (.all φ :: Δ) χ
  | allR {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)} :
      Derivable Const (weakenAntecedents (Base := Base) (Const := Const) σ Δ) φ →
      Derivable Const Δ (.all φ)
  | exL {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {χ : Formula Const Γ} :
      Derivable Const
        (φ :: weakenAntecedents (Base := Base) (Const := Const) σ Δ)
        (weaken (Base := Base) (σ := σ) χ) →
      Derivable Const (.ex φ :: Δ) χ
  | exR {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)}
      (t : Term Const Γ σ) :
      Derivable Const Δ (instantiate (Base := Base) t φ) →
      Derivable Const Δ (.ex φ)
  | lam {Γ : Ctx Base}
      {Δ Δ' : List (Formula Const Γ)}
      {φ φ' : Formula Const Γ} :
      AntecedentsBetaEtaEq (Base := Base) (Const := Const) Δ Δ' →
      BetaEtaEq (Base := Base) (Const := Const) φ φ' →
      Derivable Const Δ' φ' →
      Derivable Const Δ φ

namespace Derivable

/-- Closed theorems are derivations from an empty antecedent. -/
abbrev Theorem (Const : Ty Base → Type v) (φ : ClosedFormula Const) : Prop :=
  Derivable Const ([] : List (ClosedFormula Const)) φ

theorem ext_weaken_head
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {χ φ : Formula Const Γ}
    (d : ExtDerivation Const Δ φ) :
    ExtDerivation Const (χ :: Δ) φ :=
  ExtDerivation.mono
    (Δ := Δ)
    (Δ' := χ :: Δ)
    (φ := φ)
    (by
      intro ξ hξ
      simp [hξ])
    d

theorem ext_discharge_head
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {χ φ : Formula Const Γ}
    (hχ : ExtDerivation Const Δ χ)
    (d : ExtDerivation Const (χ :: Δ) φ) :
    ExtDerivation Const Δ φ :=
  .impE (.impI d) hχ

theorem ext_botL
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ} :
    ExtDerivation Const (.bot :: Δ) φ :=
  .botE (.hyp (by simp))

theorem ext_andL
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {φ ψ χ : Formula Const Γ}
    (d : ExtDerivation Const (φ :: ψ :: Δ) χ) :
    ExtDerivation Const (.and φ ψ :: Δ) χ := by
  have hAnd : ExtDerivation Const (.and φ ψ :: Δ) (.and φ ψ) :=
    .hyp (by simp)
  have hφ : ExtDerivation Const (.and φ ψ :: Δ) φ :=
    .andEL hAnd
  have hψ : ExtDerivation Const (φ :: .and φ ψ :: Δ) ψ :=
    .andER (ext_weaken_head (χ := φ) hAnd)
  have d' : ExtDerivation Const (ψ :: φ :: .and φ ψ :: Δ) χ :=
    ExtDerivation.mono
      (Δ := φ :: ψ :: Δ)
      (Δ' := ψ :: φ :: .and φ ψ :: Δ)
      (φ := χ)
      (by
        intro ξ hξ
        simp at hξ ⊢
        rcases hξ with rfl | rfl | hξ
        · exact Or.inr <| Or.inl rfl
        · exact Or.inl rfl
        · exact Or.inr <| Or.inr <| Or.inr hξ)
      d
  have d'' : ExtDerivation Const (φ :: .and φ ψ :: Δ) χ :=
    ext_discharge_head hψ d'
  exact ext_discharge_head hφ d''

theorem ext_orL
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {φ ψ χ : Formula Const Γ}
    (hφ : ExtDerivation Const (φ :: Δ) χ)
    (hψ : ExtDerivation Const (ψ :: Δ) χ) :
    ExtDerivation Const (.or φ ψ :: Δ) χ := by
  have hOr : ExtDerivation Const (.or φ ψ :: Δ) (.or φ ψ) :=
    .hyp (by simp)
  have hφ' : ExtDerivation Const (φ :: .or φ ψ :: Δ) χ :=
    ExtDerivation.mono
      (Δ := φ :: Δ)
      (Δ' := φ :: .or φ ψ :: Δ)
      (φ := χ)
      (by
        intro ξ hξ
        simp at hξ ⊢
        rcases hξ with rfl | hξ
        · exact Or.inl rfl
        · exact Or.inr <| Or.inr hξ)
      hφ
  have hψ' : ExtDerivation Const (ψ :: .or φ ψ :: Δ) χ :=
    ExtDerivation.mono
      (Δ := ψ :: Δ)
      (Δ' := ψ :: .or φ ψ :: Δ)
      (φ := χ)
      (by
        intro ξ hξ
        simp at hξ ⊢
        rcases hξ with rfl | hξ
        · exact Or.inl rfl
        · exact Or.inr <| Or.inr hξ)
      hψ
  exact .orE hOr hφ' hψ'

theorem ext_impL
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {φ ψ χ : Formula Const Γ}
    (hφ : ExtDerivation Const Δ φ)
    (hψχ : ExtDerivation Const (ψ :: Δ) χ) :
    ExtDerivation Const (.imp φ ψ :: Δ) χ := by
  have hImp : ExtDerivation Const (.imp φ ψ :: Δ) (.imp φ ψ) :=
    .hyp (by simp)
  have hφ' : ExtDerivation Const (.imp φ ψ :: Δ) φ :=
    ext_weaken_head (χ := .imp φ ψ) hφ
  have hψ : ExtDerivation Const (.imp φ ψ :: Δ) ψ :=
    .impE hImp hφ'
  have hψχ' : ExtDerivation Const (ψ :: .imp φ ψ :: Δ) χ :=
    ExtDerivation.mono
      (Δ := ψ :: Δ)
      (Δ' := ψ :: .imp φ ψ :: Δ)
      (φ := χ)
      (by
        intro ξ hξ
        simp at hξ ⊢
        rcases hξ with rfl | hξ
        · exact Or.inl rfl
        · exact Or.inr <| Or.inr hξ)
      hψχ
  exact ext_discharge_head hψ hψχ'

theorem ext_allL
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {σ : Ty Base}
    {φ : Formula Const (σ :: Γ)}
    {χ : Formula Const Γ}
    (t : Term Const Γ σ)
    (d : ExtDerivation Const (instantiate (Base := Base) t φ :: Δ) χ) :
    ExtDerivation Const (.all φ :: Δ) χ := by
  have hAll : ExtDerivation Const (.all φ :: Δ) (.all φ) :=
    .hyp (by simp)
  have hInst : ExtDerivation Const (.all φ :: Δ) (instantiate (Base := Base) t φ) :=
    .allE t hAll
  have d' : ExtDerivation Const (instantiate (Base := Base) t φ :: .all φ :: Δ) χ :=
    ExtDerivation.mono
      (Δ := instantiate (Base := Base) t φ :: Δ)
      (Δ' := instantiate (Base := Base) t φ :: .all φ :: Δ)
      (φ := χ)
      (by
        intro ξ hξ
        simp at hξ ⊢
        rcases hξ with rfl | hξ
        · exact Or.inl rfl
        · exact Or.inr <| Or.inr hξ)
      d
  exact ext_discharge_head hInst d'

theorem ext_exL
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {σ : Ty Base}
    {φ : Formula Const (σ :: Γ)}
    {χ : Formula Const Γ}
    (d :
      ExtDerivation Const
        (φ :: weakenAntecedents (Base := Base) (Const := Const) σ Δ)
        (weaken (Base := Base) (Const := Const) (σ := σ) χ)) :
    ExtDerivation Const (.ex φ :: Δ) χ := by
  have hEx : ExtDerivation Const (.ex φ :: Δ) (.ex φ) :=
    .hyp (by simp)
  have d' :
      ExtDerivation Const
        (φ :: weakenAntecedents (Base := Base) (Const := Const) σ (.ex φ :: Δ))
        (weaken (Base := Base) (Const := Const) (σ := σ) χ) :=
    ExtDerivation.mono
      (Δ := φ :: weakenAntecedents (Base := Base) (Const := Const) σ Δ)
      (Δ' := φ :: weakenAntecedents (Base := Base) (Const := Const) σ (.ex φ :: Δ))
      (φ := weaken (Base := Base) (Const := Const) (σ := σ) χ)
      (by
        intro ξ hξ
        simp [weakenAntecedents] at hξ ⊢
        rcases hξ with rfl | hξ
        · exact Or.inl rfl
        · exact Or.inr <| Or.inr hξ)
      d
  simpa [weakenAntecedents] using (.exE hEx d')

theorem ext_topR
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)} :
    ExtDerivation Const Δ .top :=
  .topI

theorem ext_andR
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {φ ψ : Formula Const Γ}
    (hφ : ExtDerivation Const Δ φ)
    (hψ : ExtDerivation Const Δ ψ) :
    ExtDerivation Const Δ (.and φ ψ) :=
  .andI hφ hψ

theorem ext_orR₁
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {φ ψ : Formula Const Γ}
    (hφ : ExtDerivation Const Δ φ) :
    ExtDerivation Const Δ (.or φ ψ) :=
  .orIL hφ

theorem ext_orR₂
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {φ ψ : Formula Const Γ}
    (hψ : ExtDerivation Const Δ ψ) :
    ExtDerivation Const Δ (.or φ ψ) :=
  .orIR hψ

theorem ext_impR
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {φ ψ : Formula Const Γ}
    (d : ExtDerivation Const (φ :: Δ) ψ) :
    ExtDerivation Const Δ (.imp φ ψ) :=
  .impI d

theorem ext_allR
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {σ : Ty Base}
    {φ : Formula Const (σ :: Γ)}
    (d : ExtDerivation Const (weakenAntecedents (Base := Base) (Const := Const) σ Δ) φ) :
    ExtDerivation Const Δ (.all φ) := by
  simpa [weakenAntecedents, Mettapedia.Logic.HOL.weakenHyps,
    Mettapedia.Logic.HOL.weaken] using
    (.allI d)

theorem ext_exR
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {σ : Ty Base}
    {φ : Formula Const (σ :: Γ)}
    (t : Term Const Γ σ)
    (d : ExtDerivation Const Δ (instantiate (Base := Base) t φ)) :
    ExtDerivation Const Δ (.ex φ) :=
  .exI t d

theorem instantiate_head_rename_lift_weaken
    {Γ : Ctx Base}
    {σ : Ty Base}
    {τ : Ty Base}
    (t : Term Const (σ :: Γ) τ) :
    instantiate (Base := Base) (.var (.vz : Var (σ :: Γ) σ))
      (Mettapedia.Logic.HOL.rename
        (Rename.lift (Base := Base) (σ := σ)
          (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ))) t) = t := by
  unfold instantiate
  rw [Mettapedia.Logic.HOL.subst_rename]
  calc
    subst
        (fun {_τ} v =>
          (Subst.single (Base := Base) (Const := Const)
            (.var (.vz : Var (σ :: Γ) σ)))
            ((Rename.lift (Base := Base) (σ := σ)
              (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ))) v))
        t =
      subst (Subst.id (Base := Base) (Const := Const) (Γ := σ :: Γ)) t := by
        apply Mettapedia.Logic.HOL.subst_ext
        intro τ v
        cases v <;> rfl
    _ = t := Mettapedia.Logic.HOL.subst_id (Base := Base) (Const := Const)
      (Γ := σ :: Γ) t

theorem ext_formula_weaken
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ}
    {σ : Ty Base}
    (d : ExtDerivation Const Δ φ) :
    ExtDerivation Const
      (weakenAntecedents (Base := Base) (Const := Const) σ Δ)
      (weaken (Base := Base) (Const := Const) (σ := σ) φ) := by
  change ExtDerivation Const
    (List.map
      (fun ψ =>
        Mettapedia.Logic.HOL.rename
          (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ)) ψ)
      Δ)
    (Mettapedia.Logic.HOL.rename
      (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ)) φ)
  exact ExtDerivation.rename
    (Base := Base)
    (Const := Const)
    (ρ := Rename.weaken (Base := Base) (Γ := Γ) (σ := σ))
    d

theorem eq_andCongr
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {φ φ' ψ ψ' : Formula Const Γ}
    (hφ : ExtDerivation Const Δ (.eq φ φ'))
    (hψ : ExtDerivation Const Δ (.eq ψ ψ')) :
    ExtDerivation Const Δ (.eq (.and φ ψ) (.and φ' ψ')) := by
  apply ExtDerivation.eqPropI
  · apply ExtDerivation.impI
    have hφ' : ExtDerivation Const (.and φ ψ :: Δ) (.eq φ φ') :=
      ext_weaken_head (χ := .and φ ψ) hφ
    have hψ' : ExtDerivation Const (.and φ ψ :: Δ) (.eq ψ ψ') :=
      ext_weaken_head (χ := .and φ ψ) hψ
    have hAnd : ExtDerivation Const (.and φ ψ :: Δ) (.and φ ψ) :=
      .hyp (by simp)
    exact .andI
      (ExtDerivation.eqProp_mp_left hφ' (.andEL hAnd))
      (ExtDerivation.eqProp_mp_left hψ' (.andER hAnd))
  · apply ExtDerivation.impI
    have hφ' : ExtDerivation Const (.and φ' ψ' :: Δ) (.eq φ φ') :=
      ext_weaken_head (χ := .and φ' ψ') hφ
    have hψ' : ExtDerivation Const (.and φ' ψ' :: Δ) (.eq ψ ψ') :=
      ext_weaken_head (χ := .and φ' ψ') hψ
    have hAnd : ExtDerivation Const (.and φ' ψ' :: Δ) (.and φ' ψ') :=
      .hyp (by simp)
    exact .andI
      (ExtDerivation.eqProp_mp_right hφ' (.andEL hAnd))
      (ExtDerivation.eqProp_mp_right hψ' (.andER hAnd))

theorem eq_orCongr
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {φ φ' ψ ψ' : Formula Const Γ}
    (hφ : ExtDerivation Const Δ (.eq φ φ'))
    (hψ : ExtDerivation Const Δ (.eq ψ ψ')) :
    ExtDerivation Const Δ (.eq (.or φ ψ) (.or φ' ψ')) := by
  apply ExtDerivation.eqPropI
  · apply ExtDerivation.impI
    have hφ₀ : ExtDerivation Const (.or φ ψ :: Δ) (.eq φ φ') :=
      ext_weaken_head (χ := .or φ ψ) hφ
    have hψ₀ : ExtDerivation Const (.or φ ψ :: Δ) (.eq ψ ψ') :=
      ext_weaken_head (χ := .or φ ψ) hψ
    exact .orE
      (.hyp (by simp))
      (.orIL
        (ExtDerivation.eqProp_mp_left
          (ext_weaken_head (χ := φ) hφ₀)
          (.hyp (by simp))))
      (.orIR
        (ExtDerivation.eqProp_mp_left
          (ext_weaken_head (χ := ψ) hψ₀)
          (.hyp (by simp))))
  · apply ExtDerivation.impI
    have hφ₀ : ExtDerivation Const (.or φ' ψ' :: Δ) (.eq φ φ') :=
      ext_weaken_head (χ := .or φ' ψ') hφ
    have hψ₀ : ExtDerivation Const (.or φ' ψ' :: Δ) (.eq ψ ψ') :=
      ext_weaken_head (χ := .or φ' ψ') hψ
    exact .orE
      (.hyp (by simp))
      (.orIL
        (ExtDerivation.eqProp_mp_right
          (ext_weaken_head (χ := φ') hφ₀)
          (.hyp (by simp))))
      (.orIR
        (ExtDerivation.eqProp_mp_right
          (ext_weaken_head (χ := ψ') hψ₀)
          (.hyp (by simp))))

theorem eq_impCongr
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {φ φ' ψ ψ' : Formula Const Γ}
    (hφ : ExtDerivation Const Δ (.eq φ φ'))
    (hψ : ExtDerivation Const Δ (.eq ψ ψ')) :
    ExtDerivation Const Δ (.eq (.imp φ ψ) (.imp φ' ψ')) := by
  apply ExtDerivation.eqPropI
  · apply ExtDerivation.impI
    apply ExtDerivation.impI
    have hφ' : ExtDerivation Const (φ' :: .imp φ ψ :: Δ) (.eq φ φ') :=
      ext_weaken_head (χ := φ') (ext_weaken_head (χ := .imp φ ψ) hφ)
    have hψ' : ExtDerivation Const (φ' :: .imp φ ψ :: Δ) (.eq ψ ψ') :=
      ext_weaken_head (χ := φ') (ext_weaken_head (χ := .imp φ ψ) hψ)
    have hImp : ExtDerivation Const (φ' :: .imp φ ψ :: Δ) (.imp φ ψ) :=
      .hyp (by simp)
    have hφ₀ : ExtDerivation Const (φ' :: .imp φ ψ :: Δ) φ :=
      ExtDerivation.eqProp_mp_right hφ' (.hyp (by simp))
    have hψ₀ : ExtDerivation Const (φ' :: .imp φ ψ :: Δ) ψ :=
      .impE hImp hφ₀
    exact ExtDerivation.eqProp_mp_left hψ' hψ₀
  · apply ExtDerivation.impI
    apply ExtDerivation.impI
    have hφ' : ExtDerivation Const (φ :: .imp φ' ψ' :: Δ) (.eq φ φ') :=
      ext_weaken_head (χ := φ) (ext_weaken_head (χ := .imp φ' ψ') hφ)
    have hψ' : ExtDerivation Const (φ :: .imp φ' ψ' :: Δ) (.eq ψ ψ') :=
      ext_weaken_head (χ := φ) (ext_weaken_head (χ := .imp φ' ψ') hψ)
    have hImp : ExtDerivation Const (φ :: .imp φ' ψ' :: Δ) (.imp φ' ψ') :=
      .hyp (by simp)
    have hφ₀ : ExtDerivation Const (φ :: .imp φ' ψ' :: Δ) φ' :=
      ExtDerivation.eqProp_mp_left hφ' (.hyp (by simp))
    have hψ₀ : ExtDerivation Const (φ :: .imp φ' ψ' :: Δ) ψ' :=
      .impE hImp hφ₀
    exact ExtDerivation.eqProp_mp_right hψ' hψ₀

theorem eq_notCongr
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {φ φ' : Formula Const Γ}
    (hφ : ExtDerivation Const Δ (.eq φ φ')) :
    ExtDerivation Const Δ (.eq (.not φ) (.not φ')) := by
  apply ExtDerivation.eqPropI
  · apply ExtDerivation.impI
    apply ExtDerivation.notI
    have hφ' : ExtDerivation Const (φ' :: .not φ :: Δ) (.eq φ φ') :=
      ext_weaken_head (χ := φ') (ext_weaken_head (χ := .not φ) hφ)
    have hNot : ExtDerivation Const (φ' :: .not φ :: Δ) (.not φ) :=
      .hyp (by simp)
    have h₀ : ExtDerivation Const (φ' :: .not φ :: Δ) φ :=
      ExtDerivation.eqProp_mp_right hφ' (.hyp (by simp))
    exact .notE hNot h₀
  · apply ExtDerivation.impI
    apply ExtDerivation.notI
    have hφ' : ExtDerivation Const (φ :: .not φ' :: Δ) (.eq φ φ') :=
      ext_weaken_head (χ := φ) (ext_weaken_head (χ := .not φ') hφ)
    have hNot : ExtDerivation Const (φ :: .not φ' :: Δ) (.not φ') :=
      .hyp (by simp)
    have h₀ : ExtDerivation Const (φ :: .not φ' :: Δ) φ' :=
      ExtDerivation.eqProp_mp_left hφ' (.hyp (by simp))
    exact .notE hNot h₀

theorem eq_eqCongr
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {τ : Ty Base}
    {t t' u u' : Term Const Γ τ}
    (ht : ExtDerivation Const Δ (.eq t t'))
    (hu : ExtDerivation Const Δ (.eq u u')) :
    ExtDerivation Const Δ (.eq (.eq t u) (.eq t' u')) := by
  apply ExtDerivation.eqPropI
  · apply ExtDerivation.impI
    have ht' : ExtDerivation Const (.eq t u :: Δ) (.eq t t') :=
      ext_weaken_head (χ := .eq t u) ht
    have hu' : ExtDerivation Const (.eq t u :: Δ) (.eq u u') :=
      ext_weaken_head (χ := .eq t u) hu
    exact .eqTrans (.eqTrans (.eqSymm ht') (.hyp (by simp))) hu'
  · apply ExtDerivation.impI
    have ht' : ExtDerivation Const (.eq t' u' :: Δ) (.eq t t') :=
      ext_weaken_head (χ := .eq t' u') ht
    have hu' : ExtDerivation Const (.eq t' u' :: Δ) (.eq u u') :=
      ext_weaken_head (χ := .eq t' u') hu
    exact .eqTrans (.eqTrans ht' (.hyp (by simp))) (.eqSymm hu')

theorem eq_allCongr
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {σ : Ty Base}
    {φ φ' : Formula Const (σ :: Γ)}
    (hφ :
      ExtDerivation Const
        (weakenAntecedents (Base := Base) (Const := Const) σ Δ)
        (.eq φ φ')) :
    ExtDerivation Const Δ (.eq (.all φ) (.all φ')) := by
  apply ExtDerivation.eqPropI
  · apply ExtDerivation.impI
    apply ext_allR
    have hEq :
        ExtDerivation Const
          (weakenAntecedents (Base := Base) (Const := Const) σ (.all φ :: Δ))
          (.eq φ φ') := by
      simpa [weakenAntecedents] using
        ext_weaken_head
          (χ := weaken (Base := Base) (Const := Const) (σ := σ) (.all φ))
          hφ
    have hAll :
        ExtDerivation Const
          (weakenAntecedents (Base := Base) (Const := Const) σ (.all φ :: Δ))
          (weaken (Base := Base) (Const := Const) (σ := σ) (.all φ)) :=
      .hyp (by simp [weakenAntecedents])
    have hBody :
        ExtDerivation Const
          (weakenAntecedents (Base := Base) (Const := Const) σ (.all φ :: Δ))
          φ := by
      simpa [weakenAntecedents, instantiate_head_rename_lift_weaken] using
        (ExtDerivation.allE (.var (.vz : Var (σ :: Γ) σ)) hAll)
    exact ExtDerivation.eqProp_mp_left hEq hBody
  · apply ExtDerivation.impI
    apply ext_allR
    have hEq :
        ExtDerivation Const
          (weakenAntecedents (Base := Base) (Const := Const) σ (.all φ' :: Δ))
          (.eq φ φ') := by
      simpa [weakenAntecedents] using
        ext_weaken_head
          (χ := weaken (Base := Base) (Const := Const) (σ := σ) (.all φ'))
          hφ
    have hAll :
        ExtDerivation Const
          (weakenAntecedents (Base := Base) (Const := Const) σ (.all φ' :: Δ))
          (weaken (Base := Base) (Const := Const) (σ := σ) (.all φ')) :=
      .hyp (by simp [weakenAntecedents])
    have hBody :
        ExtDerivation Const
          (weakenAntecedents (Base := Base) (Const := Const) σ (.all φ' :: Δ))
          φ' := by
      simpa [weakenAntecedents, instantiate_head_rename_lift_weaken] using
        (ExtDerivation.allE (.var (.vz : Var (σ :: Γ) σ)) hAll)
    exact ExtDerivation.eqProp_mp_right hEq hBody

theorem eq_exCongr
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {σ : Ty Base}
    {φ φ' : Formula Const (σ :: Γ)}
    (hφ :
      ExtDerivation Const
        (weakenAntecedents (Base := Base) (Const := Const) σ Δ)
        (.eq φ φ')) :
    ExtDerivation Const Δ (.eq (.ex φ) (.ex φ')) := by
  apply ExtDerivation.eqPropI
  · apply ExtDerivation.impI
    apply ext_exL
    have hEq :
        ExtDerivation Const
          (φ :: weakenAntecedents (Base := Base) (Const := Const) σ Δ)
          (.eq φ φ') := by
      simpa [weakenAntecedents] using ext_weaken_head (χ := φ) hφ
    have hBody :
        ExtDerivation Const
          (φ :: weakenAntecedents (Base := Base) (Const := Const) σ Δ)
          φ' :=
      ExtDerivation.eqProp_mp_left hEq (.hyp (by simp [weakenAntecedents]))
    simpa [weakenAntecedents, Mettapedia.Logic.HOL.weaken,
      Mettapedia.Logic.HOL.rename] using
      (ext_exR
        (Base := Base)
        (Const := Const)
        (Δ := φ :: weakenAntecedents (Base := Base) (Const := Const) σ Δ)
        (σ := σ)
        (φ := Mettapedia.Logic.HOL.rename
          (Rename.lift (Base := Base) (σ := σ)
            (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ))) φ')
        (.var (.vz : Var (σ :: Γ) σ))
        (by
          simpa [instantiate_head_rename_lift_weaken] using hBody))
  · apply ExtDerivation.impI
    apply ext_exL
    have hEq :
        ExtDerivation Const
          (φ' :: weakenAntecedents (Base := Base) (Const := Const) σ Δ)
          (.eq φ φ') := by
      simpa [weakenAntecedents] using ext_weaken_head (χ := φ') hφ
    have hBody :
        ExtDerivation Const
          (φ' :: weakenAntecedents (Base := Base) (Const := Const) σ Δ)
          φ :=
      ExtDerivation.eqProp_mp_right hEq (.hyp (by simp [weakenAntecedents]))
    simpa [weakenAntecedents, Mettapedia.Logic.HOL.weaken,
      Mettapedia.Logic.HOL.rename] using
      (ext_exR
        (Base := Base)
        (Const := Const)
        (Δ := φ' :: weakenAntecedents (Base := Base) (Const := Const) σ Δ)
        (σ := σ)
        (φ := Mettapedia.Logic.HOL.rename
          (Rename.lift (Base := Base) (σ := σ)
            (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ))) φ)
        (.var (.vz : Var (σ :: Γ) σ))
        (by
          simpa [instantiate_head_rename_lift_weaken] using hBody))

theorem betaEtaEq_eq
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {τ : Ty Base}
    {t u : Term Const Γ τ}
    (h : BetaEtaEq (Base := Base) (Const := Const) t u) :
    ExtDerivation Const Δ (.eq t u) := by
  induction h with
  | refl t =>
      exact .eqRefl t
  | symm h ih =>
      exact .eqSymm (ih (Δ := Δ))
  | trans htu huv ihtu ihuv =>
      exact .eqTrans (ihtu (Δ := Δ)) (ihuv (Δ := Δ))
  | app hfg htu ihfg ihtu =>
      exact ExtDerivation.eqAppCongr (ihfg (Δ := Δ)) (ihtu (Δ := Δ))
  | lam h ih =>
      exact .eqLam (by
        simpa [weakenAntecedents, Mettapedia.Logic.HOL.weakenHyps] using
          ih
            (Δ := weakenAntecedents (Base := Base) (Const := Const) _ Δ))
  | and hφ hψ ihφ ihψ =>
      exact eq_andCongr (ihφ (Δ := Δ)) (ihψ (Δ := Δ))
  | or hφ hψ ihφ ihψ =>
      exact eq_orCongr (ihφ (Δ := Δ)) (ihψ (Δ := Δ))
  | imp hφ hψ ihφ ihψ =>
      exact eq_impCongr (ihφ (Δ := Δ)) (ihψ (Δ := Δ))
  | not hφ ihφ =>
      exact eq_notCongr (ihφ (Δ := Δ))
  | eq ht hu iht ihu =>
      exact eq_eqCongr (iht (Δ := Δ)) (ihu (Δ := Δ))
  | all hφ ihφ =>
      exact
        eq_allCongr
          (Δ := Δ)
          (ihφ
            (Δ := weakenAntecedents (Base := Base) (Const := Const) _ Δ))
  | ex hφ ihφ =>
      exact
        eq_exCongr
          (Δ := Δ)
          (ihφ
            (Δ := weakenAntecedents (Base := Base) (Const := Const) _ Δ))
  | beta t u =>
      exact .beta t u
  | eta f =>
      exact .eta f

theorem ext_hypSubst
    {Γ : Ctx Base}
    {Δ Δ' : List (Formula Const Γ)}
    {φ : Formula Const Γ}
    (hsub : ∀ {χ : Formula Const Γ}, χ ∈ Δ → ExtDerivation Const Δ' χ) :
    ExtDerivation Const Δ φ →
    ExtDerivation Const Δ' φ := by
  intro d
  induction d with
  | hyp hmem =>
      exact hsub hmem
  | topI =>
      exact .topI
  | botE h ih =>
      exact .botE (ih hsub)
  | andI hφ hψ ihφ ihψ =>
      exact .andI (ihφ hsub) (ihψ hsub)
  | andEL h ih =>
      exact .andEL (ih hsub)
  | andER h ih =>
      exact .andER (ih hsub)
  | orIL h ih =>
      exact .orIL (ih hsub)
  | orIR h ih =>
      exact .orIR (ih hsub)
  | orE hor hφ hψ ihor ihφ ihψ =>
      refine .orE (ihor hsub) ?_ ?_
      · exact ihφ (by
          intro χ hχ
          rw [List.mem_cons] at hχ
          rcases hχ with rfl | hχ
          · exact .hyp (by simp)
          · exact ext_weaken_head (χ := _) (hsub hχ))
      · exact ihψ (by
          intro χ hχ
          rw [List.mem_cons] at hχ
          rcases hχ with rfl | hχ
          · exact .hyp (by simp)
          · exact ext_weaken_head (χ := _) (hsub hχ))
  | impI h ih =>
      exact .impI (ih (by
        intro χ hχ
        rw [List.mem_cons] at hχ
        rcases hχ with rfl | hχ
        · exact .hyp (by simp)
        · exact ext_weaken_head (χ := _) (hsub hχ)))
  | impE himp hφ ihimp ihφ =>
      exact .impE (ihimp hsub) (ihφ hsub)
  | notI h ih =>
      exact .notI (ih (by
        intro χ hχ
        rw [List.mem_cons] at hχ
        rcases hχ with rfl | hχ
        · exact .hyp (by simp)
        · exact ext_weaken_head (χ := _) (hsub hχ)))
  | notE hnot hφ ihnot ihφ =>
      exact .notE (ihnot hsub) (ihφ hsub)
  | allI h ih =>
      rename_i σ body
      exact .allI (ih (by
        intro χ hχ
        rcases List.mem_map.mp hχ with ⟨ψ, hψ, rfl⟩
        exact ext_formula_weaken (σ := σ) (hsub hψ)))
  | allE t h ih =>
      exact .allE t (ih hsub)
  | exI t h ih =>
      exact .exI t (ih hsub)
  | exE hex hbody ihex ihbody =>
      rename_i σ body ψ
      refine .exE (ihex hsub) ?_
      exact ihbody (by
        intro χ hχ
        rw [List.mem_cons] at hχ
        rcases hχ with rfl | hχ
        · exact .hyp (by simp)
        · rcases List.mem_map.mp hχ with ⟨θ, hθ, rfl⟩
          exact ext_weaken_head (χ := body) (ext_formula_weaken (σ := σ) (hsub hθ)))
  | eqRefl t =>
      exact .eqRefl t
  | eqSymm h ih =>
      exact .eqSymm (ih hsub)
  | eqTrans htu huv ihtu ihuv =>
      exact .eqTrans (ihtu hsub) (ihuv hsub)
  | eqPropI hpq hqp ihpq ihqp =>
      exact .eqPropI (ihpq hsub) (ihqp hsub)
  | eqPropEL hpq ihpq =>
      exact .eqPropEL (ihpq hsub)
  | eqPropER hpq ihpq =>
      exact .eqPropER (ihpq hsub)
  | eqApp t h ih =>
      exact .eqApp t (ih hsub)
  | eqAppArg f h ih =>
      exact .eqAppArg f (ih hsub)
  | eqLam h ih =>
      rename_i σ τ t u
      exact .eqLam (ih (by
        intro χ hχ
        rcases List.mem_map.mp hχ with ⟨ψ, hψ, rfl⟩
        exact ext_formula_weaken (σ := σ) (hsub hψ)))
  | funExt h ih =>
      exact .funExt (ih hsub)
  | beta t u =>
      exact .beta t u
  | eta f =>
      exact .eta f

theorem antecedentsBetaEtaEq_hyp
    {Γ : Ctx Base}
    {Δ Δ' : List (Formula Const Γ)}
    (hΔ : AntecedentsBetaEtaEq (Base := Base) (Const := Const) Δ Δ')
    {χ : Formula Const Γ}
    (hχ : χ ∈ Δ') :
    ExtDerivation Const Δ χ := by
  induction hΔ generalizing χ with
  | nil =>
      cases hχ
  | @cons φ ψ tail tail' hφ hΔ ih =>
      rw [List.mem_cons] at hχ
      rcases hχ with rfl | hχ
      · have hEq : ExtDerivation Const (φ :: tail) (.eq φ χ) :=
          ext_weaken_head (Δ := tail) (χ := φ) (betaEtaEq_eq (Δ := tail) hφ)
        exact ExtDerivation.eqProp_mp_left hEq (.hyp (by simp))
      · exact ext_weaken_head (Δ := tail) (χ := φ) (ih hχ)

theorem antecedentsBetaEtaEq_transport
    {Γ : Ctx Base}
    {Δ Δ' : List (Formula Const Γ)}
    {φ : Formula Const Γ}
    (hΔ : AntecedentsBetaEtaEq (Base := Base) (Const := Const) Δ Δ') :
    ExtDerivation Const Δ' φ →
    ExtDerivation Const Δ φ :=
  ext_hypSubst (fun hχ => antecedentsBetaEtaEq_hyp hΔ hχ)

theorem toExtDerivation
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ} :
    Derivable Const Δ φ →
    ExtDerivation Const Δ φ := by
  intro d
  induction d with
  | ax h =>
      exact .hyp h
  | topR =>
      exact ext_topR
  | botL =>
      exact ext_botL
  | andL h ih =>
      exact ext_andL ih
  | andR hφ hψ ihφ ihψ =>
      exact ext_andR ihφ ihψ
  | orL hφ hψ ihφ ihψ =>
      exact ext_orL ihφ ihψ
  | orR₁ h ih =>
      exact ext_orR₁ ih
  | orR₂ h ih =>
      exact ext_orR₂ ih
  | impL hφ hψχ ihφ ihψχ =>
      exact ext_impL ihφ ihψχ
  | impR h ih =>
      exact ext_impR ih
  | allL t h ih =>
      exact ext_allL t ih
  | allR h ih =>
      exact ext_allR ih
  | exL h ih =>
      exact ext_exL ih
  | exR t h ih =>
      exact ext_exR t ih
  | lam hΔ hφ h ih =>
      rename_i Δ₀ Δ₁ φ ψ
      exact
        ExtDerivation.eqProp_mp_right
          (betaEtaEq_eq (Δ := Δ₀) hφ)
          (antecedentsBetaEtaEq_transport (Δ := Δ₀) (Δ' := Δ₁) hΔ ih)

end Derivable

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
