import Mettapedia.Logic.HOL.Semantics.HeytingHenkin
import Mettapedia.Logic.HOL.Syntax.ConstMap

namespace Mettapedia.Logic.HOL

universe u v w x

variable {Base : Type u}
variable {Const : Ty Base → Type v} {Const' : Ty Base → Type w}

namespace HeytingPreModel

/-- Restrict a Heyting premodel along a constant map. -/
def reduct
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (M : HeytingPreModel Base Const') :
    HeytingPreModel Base Const where
  Ω := M.Ω
  instFrame := M.instFrame
  Carrier := M.Carrier
  adm := M.adm
  base_mem := M.base_mem
  app_mem := M.app_mem
  constDen := fun c => M.constDen (f c)
  const_mem := by
    intro τ c
    exact M.const_mem (f c)
  baseEq := M.baseEq
  baseEq_refl := M.baseEq_refl
  baseEq_symm := M.baseEq_symm
  baseEq_trans := M.baseEq_trans

@[simp] theorem eqv_reduct
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (M : HeytingPreModel Base Const')
    {τ : Ty Base}
    {x y : Ty.denoteHeyting M.Carrier M.Ω τ} :
    Eqv (reduct f M) τ x y = Eqv M τ x y := by
  induction τ with
  | prop =>
      rfl
  | base b =>
      rfl
  | arr σ τ ihσ ihτ =>
      unfold Eqv allAdmissible
      apply congrArg sInf
      ext z
      constructor <;> intro hz
      · rcases hz with ⟨w, rfl⟩
        refine ⟨w, ?_⟩
        simpa using (ihτ (x := x w.1) (y := y w.1)).symm
      · rcases hz with ⟨w, rfl⟩
        refine ⟨w, ?_⟩
        simpa using (ihτ (x := x w.1) (y := y w.1))

@[simp] theorem denote_mapConst
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (M : HeytingPreModel Base Const') :
    ∀ {Γ : Ctx Base} {τ : Ty Base}
      (t : Term Const Γ τ) (ρ : Valuation M Γ),
      denote (reduct f M) t ρ = denote M (mapConst f t) ρ
  | _, _, .var v, ρ => rfl
  | _, _, .const c, ρ => rfl
  | _, _, .app g t, ρ => by
      change denote (reduct f M) g ρ (denote (reduct f M) t ρ) =
        denote M (.app (mapConst f g) (mapConst f t)) ρ
      rw [denote_mapConst f M g ρ, denote_mapConst f M t ρ]
      rfl
  | _, _, .lam t, ρ => by
      funext x
      simpa [denote] using denote_mapConst f M t (extend M ρ x)
  | _, _, .top, ρ => rfl
  | _, _, .bot, ρ => rfl
  | _, _, .and φ ψ, ρ => by
      change ((show M.Ω from denote (reduct f M) φ ρ) ⊓
          (show M.Ω from denote (reduct f M) ψ ρ)) =
        denote M (.and (mapConst f φ) (mapConst f ψ)) ρ
      rw [denote_mapConst f M φ ρ, denote_mapConst f M ψ ρ]
      rfl
  | _, _, .or φ ψ, ρ => by
      change ((show M.Ω from denote (reduct f M) φ ρ) ⊔
          (show M.Ω from denote (reduct f M) ψ ρ)) =
        denote M (.or (mapConst f φ) (mapConst f ψ)) ρ
      rw [denote_mapConst f M φ ρ, denote_mapConst f M ψ ρ]
      rfl
  | _, _, .imp φ ψ, ρ => by
      change ((show M.Ω from denote (reduct f M) φ ρ) ⇨
          (show M.Ω from denote (reduct f M) ψ ρ)) =
        denote M (.imp (mapConst f φ) (mapConst f ψ)) ρ
      rw [denote_mapConst f M φ ρ, denote_mapConst f M ψ ρ]
      rfl
  | _, _, .not φ, ρ => by
      change ((show M.Ω from denote (reduct f M) φ ρ) ⇨ (⊥ : M.Ω)) =
        denote M (.not (mapConst f φ)) ρ
      rw [denote_mapConst f M φ ρ]
      rfl
  | _, _, .eq t u, ρ => by
      change
        Eqv (reduct f M) _ (denote (reduct f M) t ρ) (denote (reduct f M) u ρ) =
          denote M (.eq (mapConst f t) (mapConst f u)) ρ
      rw [denote_mapConst f M t ρ, denote_mapConst f M u ρ, eqv_reduct]
      rfl
  | _, _, .all φ, ρ => by
      change
        allAdmissible (reduct f M) (fun x => denote (reduct f M) φ (extend (reduct f M) ρ x.1)) =
          allAdmissible M (fun x => denote M (mapConst f φ) (extend M ρ x.1))
      apply congrArg
      funext x
      simpa using denote_mapConst f M φ (extend M ρ x.1)
  | _, _, .ex φ, ρ => by
      change
        anyAdmissible (reduct f M) (fun x => denote (reduct f M) φ (extend (reduct f M) ρ x.1)) =
          anyAdmissible M (fun x => denote M (mapConst f φ) (extend M ρ x.1))
      apply congrArg
      funext x
      simpa using denote_mapConst f M φ (extend M ρ x.1)

@[simp] theorem denoteFormula_mapConst
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (M : HeytingPreModel Base Const')
    {Γ : Ctx Base}
    (φ : Formula Const Γ) (ρ : Valuation M Γ) :
    denoteFormula (reduct f M) φ ρ =
      denoteFormula M (mapConst f φ) ρ :=
  denote_mapConst f M φ ρ

@[simp] theorem contextDenote_mapConst
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (M : HeytingPreModel Base Const')
    {Γ : Ctx Base}
    (Δ : List (Formula Const Γ)) (ρ : Valuation M Γ) :
    contextDenote (reduct f M) Δ ρ =
      contextDenote M (Δ.map (mapConst f)) ρ := by
  induction Δ with
  | nil =>
      rfl
  | cons φ Δ ih =>
      rw [contextDenote_cons, List.map, contextDenote_cons, denoteFormula_mapConst]
      simpa using
        congrArg (fun acc => denoteFormula M (mapConst f φ) ρ ⊓ acc) ih

theorem modelsFrom_mapConst_iff
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (M : HeytingPreModel Base Const')
    {Γ : Ctx Base}
    (Δ : List (Formula Const Γ)) (φ : Formula Const Γ) (ρ : Valuation M Γ) :
    modelsFrom (reduct f M) Δ φ ρ ↔
      modelsFrom M (Δ.map (mapConst f)) (mapConst f φ) ρ := by
  simp [modelsFrom, contextDenote_mapConst, denoteFormula_mapConst]

  theorem models_mapClosedFormula_iff
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (M : HeytingPreModel Base Const')
    (φ : ClosedFormula Const) :
    models (reduct f M) φ ↔
      models M (mapClosedFormula f φ) := by
  change
    denoteFormula (reduct f M) φ (fun v => nomatch v) = ⊤ ↔
      denoteFormula M (mapConst (fun {τ} => f) φ) (fun v => nomatch v) = ⊤
  rw [denoteFormula_mapConst]
  rfl

end HeytingPreModel

namespace HeytingHenkinModel

/-- Restrict a Heyting-Henkin model along a constant map. -/
def reduct
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (M : HeytingHenkinModel Base Const') :
    HeytingHenkinModel Base Const where
  toHeytingPreModel := HeytingPreModel.reduct f M.toHeytingPreModel
  term_closed := by
    intro Γ τ t ρ hρ
    simpa using M.term_closed (mapConst f t) ρ hρ
  app_respects_eq := by
    intro σ τ g hg x y hx hy
    simpa [HeytingPreModel.eqv_reduct] using
      (M.app_respects_eq (σ := σ) (τ := τ) hg hx hy)

@[simp] theorem denote_mapConst
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (M : HeytingHenkinModel Base Const')
    {Γ : Ctx Base} {τ : Ty Base}
    (t : Term Const Γ τ) (ρ : Valuation M Γ) :
    denote (reduct f M) t ρ = denote M (mapConst f t) ρ :=
  HeytingPreModel.denote_mapConst f M.toHeytingPreModel t ρ

theorem modelsFrom_mapConst_iff
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (M : HeytingHenkinModel Base Const')
    {Γ : Ctx Base}
    (Δ : List (Formula Const Γ)) (φ : Formula Const Γ) (ρ : Valuation M Γ) :
    modelsFrom (reduct f M) Δ φ ρ ↔
      modelsFrom M (Δ.map (mapConst f)) (mapConst f φ) ρ :=
  HeytingPreModel.modelsFrom_mapConst_iff f M.toHeytingPreModel Δ φ ρ

theorem models_mapClosedFormula_iff
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (M : HeytingHenkinModel Base Const')
    (φ : ClosedFormula Const) :
    models (reduct f M) φ ↔
      models M (mapClosedFormula f φ) :=
  HeytingPreModel.models_mapClosedFormula_iff f M.toHeytingPreModel φ

end HeytingHenkinModel

end Mettapedia.Logic.HOL
