import Mettapedia.Logic.HOL.Syntax.Subst

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Weakening of assumption lists along a one-step context extension. -/
def weakenHyps (Δ : List (Formula Const Γ)) : List (Formula Const (σ :: Γ)) :=
  Δ.map (weaken (Base := Base) (σ := σ))

/-- A small typed natural-deduction core for HOL formulas in context. -/
inductive Derivation (Const : Ty Base → Type v) :
    {Γ : Ctx Base} → List (Formula Const Γ) → Formula Const Γ → Prop where
  | hyp {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
      φ ∈ Δ → Derivation Const Δ φ
  | topI {Γ : Ctx Base} {Δ : List (Formula Const Γ)} :
      Derivation Const Δ .top
  | botE {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
      Derivation Const Δ .bot → Derivation Const Δ φ
  | andI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      Derivation Const Δ φ → Derivation Const Δ ψ → Derivation Const Δ (.and φ ψ)
  | andEL {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      Derivation Const Δ (.and φ ψ) → Derivation Const Δ φ
  | andER {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      Derivation Const Δ (.and φ ψ) → Derivation Const Δ ψ
  | orIL {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      Derivation Const Δ φ → Derivation Const Δ (.or φ ψ)
  | orIR {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      Derivation Const Δ ψ → Derivation Const Δ (.or φ ψ)
  | orE {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ χ : Formula Const Γ} :
      Derivation Const Δ (.or φ ψ) →
      Derivation Const (φ :: Δ) χ →
      Derivation Const (ψ :: Δ) χ →
      Derivation Const Δ χ
  | impI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      Derivation Const (φ :: Δ) ψ → Derivation Const Δ (.imp φ ψ)
  | impE {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      Derivation Const Δ (.imp φ ψ) →
      Derivation Const Δ φ →
      Derivation Const Δ ψ
  | notI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ : Formula Const Γ} :
      Derivation Const (φ :: Δ) .bot → Derivation Const Δ (.not φ)
  | notE {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ : Formula Const Γ} :
      Derivation Const Δ (.not φ) →
      Derivation Const Δ φ →
      Derivation Const Δ .bot
  | allI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)} :
      Derivation Const (weakenHyps (Base := Base) (σ := σ) Δ) φ →
      Derivation Const Δ (.all φ)
  | allE {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)}
      (t : Term Const Γ σ) :
      Derivation Const Δ (.all φ) →
      Derivation Const Δ (instantiate (Base := Base) t φ)
  | exI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)}
      (t : Term Const Γ σ) :
      Derivation Const Δ (instantiate (Base := Base) t φ) →
      Derivation Const Δ (.ex φ)
  | exE {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {ψ : Formula Const Γ} :
      Derivation Const Δ (.ex φ) →
      Derivation Const (φ :: weakenHyps (Base := Base) (σ := σ) Δ)
        (weaken (Base := Base) (σ := σ) ψ) →
      Derivation Const Δ ψ
  | eqRefl {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {τ : Ty Base} (t : Term Const Γ τ) :
      Derivation Const Δ (.eq t t)
  | eqSymm {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {τ : Ty Base} {t u : Term Const Γ τ} :
      Derivation Const Δ (.eq t u) →
      Derivation Const Δ (.eq u t)
  | eqTrans {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {τ : Ty Base} {t u v : Term Const Γ τ} :
      Derivation Const Δ (.eq t u) →
      Derivation Const Δ (.eq u v) →
      Derivation Const Δ (.eq t v)
  | eqApp {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} {f g : Term Const Γ (σ ⇒ τ)} (t : Term Const Γ σ) :
      Derivation Const Δ (.eq f g) →
      Derivation Const Δ (.eq (.app f t) (.app g t))
  | eqLam {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} {t u : Term Const (σ :: Γ) τ} :
      Derivation Const (weakenHyps (Base := Base) (σ := σ) Δ) (.eq t u) →
      Derivation Const Δ (.eq (.lam t) (.lam u))
  | funExt {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} {f g : Term Const Γ (σ ⇒ τ)} :
      Derivation Const Δ
        (.all (.eq (.app (weaken (Base := Base) (σ := σ) f) (.var .vz))
                   (.app (weaken (Base := Base) (σ := σ) g) (.var .vz)))) →
      Derivation Const Δ (.eq f g)
  | beta {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} (t : Term Const Γ σ) (u : Term Const (σ :: Γ) τ) :
      Derivation Const Δ (.eq (.app (.lam u) t) (instantiate (Base := Base) t u))
  | eta {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} (f : Term Const Γ (σ ⇒ τ)) :
      Derivation Const Δ (.eq (.lam (.app (weaken (Base := Base) (σ := σ) f) (.var .vz))) f)

namespace Derivation

variable {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ ψ : Formula Const Γ}

/-- Closed theorems are derivations from no assumptions. -/
abbrev Theorem (Const : Ty Base → Type v) (φ : ClosedFormula Const) : Prop :=
  Derivation Const ([] : List (ClosedFormula Const)) φ

theorem imp_mp
    (hImp : Derivation Const Δ (.imp φ ψ))
    (hφ : Derivation Const Δ φ) :
    Derivation Const Δ ψ :=
  .impE hImp hφ

theorem not_bot_of
    (hNot : Derivation Const Δ (.not φ))
    (hφ : Derivation Const Δ φ) :
    Derivation Const Δ .bot :=
  .notE hNot hφ

theorem mono {Γ : Ctx Base} {Δ Δ' : List (Formula Const Γ)} {φ : Formula Const Γ}
    (hsub : ∀ {χ : Formula Const Γ}, χ ∈ Δ → χ ∈ Δ') :
    Derivation Const Δ φ → Derivation Const Δ' φ := by
  intro d
  induction d with
  | hyp hmem =>
      exact .hyp (hsub hmem)
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
          rw [List.mem_cons] at hχ ⊢
          rcases hχ with rfl | hχ
          · exact Or.inl rfl
          · exact Or.inr (hsub hχ))
      · exact ihψ (by
          intro χ hχ
          rw [List.mem_cons] at hχ ⊢
          rcases hχ with rfl | hχ
          · exact Or.inl rfl
          · exact Or.inr (hsub hχ))
  | impI h ih =>
      exact .impI (ih (by
        intro χ hχ
        rw [List.mem_cons] at hχ ⊢
        rcases hχ with rfl | hχ
        · exact Or.inl rfl
        · exact Or.inr (hsub hχ)))
  | impE himp hφ ihimp ihφ =>
      exact .impE (ihimp hsub) (ihφ hsub)
  | notI h ih =>
      exact .notI (ih (by
        intro χ hχ
        rw [List.mem_cons] at hχ ⊢
        rcases hχ with rfl | hχ
        · exact Or.inl rfl
        · exact Or.inr (hsub hχ)))
  | notE hnot hφ ihnot ihφ =>
      exact .notE (ihnot hsub) (ihφ hsub)
  | allI h ih =>
      exact .allI (ih (by
        intro χ hχ
        rcases List.mem_map.mp hχ with ⟨ψ, hψ, rfl⟩
        exact List.mem_map.mpr ⟨ψ, hsub hψ, rfl⟩))
  | allE t h ih =>
      exact .allE t (ih hsub)
  | exI t h ih =>
      exact .exI t (ih hsub)
  | exE hex hbody ihex ihbody =>
      refine .exE (ihex hsub) ?_
      exact ihbody (by
        intro χ hχ
        rw [List.mem_cons] at hχ ⊢
        rcases hχ with rfl | hχ
        · exact Or.inl rfl
        · rcases List.mem_map.mp hχ with ⟨ψ, hψ, rfl⟩
          exact Or.inr (List.mem_map.mpr ⟨ψ, hsub hψ, rfl⟩))
  | eqRefl t =>
      exact .eqRefl t
  | eqSymm h ih =>
      exact .eqSymm (ih hsub)
  | eqTrans htu huv ihtu ihuv =>
      exact .eqTrans (ihtu hsub) (ihuv hsub)
  | eqApp t h ih =>
      exact .eqApp t (ih hsub)
  | eqLam h ih =>
      exact .eqLam (ih (by
        intro χ hχ
        rcases List.mem_map.mp hχ with ⟨ψ, hψ, rfl⟩
        exact List.mem_map.mpr ⟨ψ, hsub hψ, rfl⟩))
  | funExt h ih =>
      exact .funExt (ih hsub)
  | beta t u =>
      exact .beta t u
  | eta f =>
      exact .eta f

theorem ofTheorem {φ : ClosedFormula Const} {Δ : List (ClosedFormula Const)}
    (d : Theorem Const φ) : Derivation Const Δ φ :=
  mono (Δ := []) (Δ' := Δ) (φ := φ) (by
    intro χ hχ
    nomatch hχ) d

theorem theorem_imp_refl (φ : ClosedFormula Const) :
    Theorem Const (.imp φ φ) :=
  .impI (.hyp (by simp))

theorem theorem_imp_top (φ : ClosedFormula Const) :
    Theorem Const (.imp φ .top) :=
  .impI .topI

theorem theorem_imp_trans {φ ψ χ : ClosedFormula Const}
    (hφψ : Theorem Const (.imp φ ψ))
    (hψχ : Theorem Const (.imp ψ χ)) :
    Theorem Const (.imp φ χ) := by
  refine .impI ?_
  have hψ : Derivation Const [φ] ψ :=
    .impE (ofTheorem (Δ := [φ]) hφψ) (.hyp (by simp))
  exact .impE (ofTheorem (Δ := [φ]) hψχ) hψ

end Derivation

end Mettapedia.Logic.HOL
