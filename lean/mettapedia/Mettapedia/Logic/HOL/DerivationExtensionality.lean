import Mettapedia.Logic.HOL.Derivation
import Mettapedia.Logic.HOL.Syntax.ConstMap

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u}
variable {Const : Ty Base → Type v} {Const' : Ty Base → Type w}

/--
An extensional overlay of the small HOL derivation core.

This keeps the original calculus in
`/home/zar/claude/lean-projects/mettapedia/Mettapedia/Logic/HOL/Derivation.lean`
intact, while adding the missing argument-congruence strength needed by standard
extensional HOL equality.
-/
inductive ExtDerivation (Const : Ty Base → Type v) :
    {Γ : Ctx Base} → List (Formula Const Γ) → Formula Const Γ → Prop where
  | hyp {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
      φ ∈ Δ → ExtDerivation Const Δ φ
  | topI {Γ : Ctx Base} {Δ : List (Formula Const Γ)} :
      ExtDerivation Const Δ .top
  | botE {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
      ExtDerivation Const Δ .bot → ExtDerivation Const Δ φ
  | andI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      ExtDerivation Const Δ φ → ExtDerivation Const Δ ψ →
        ExtDerivation Const Δ (.and φ ψ)
  | andEL {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      ExtDerivation Const Δ (.and φ ψ) → ExtDerivation Const Δ φ
  | andER {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      ExtDerivation Const Δ (.and φ ψ) → ExtDerivation Const Δ ψ
  | orIL {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      ExtDerivation Const Δ φ → ExtDerivation Const Δ (.or φ ψ)
  | orIR {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      ExtDerivation Const Δ ψ → ExtDerivation Const Δ (.or φ ψ)
  | orE {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ χ : Formula Const Γ} :
      ExtDerivation Const Δ (.or φ ψ) →
      ExtDerivation Const (φ :: Δ) χ →
      ExtDerivation Const (ψ :: Δ) χ →
      ExtDerivation Const Δ χ
  | impI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      ExtDerivation Const (φ :: Δ) ψ → ExtDerivation Const Δ (.imp φ ψ)
  | impE {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      ExtDerivation Const Δ (.imp φ ψ) →
      ExtDerivation Const Δ φ →
      ExtDerivation Const Δ ψ
  | notI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ : Formula Const Γ} :
      ExtDerivation Const (φ :: Δ) .bot → ExtDerivation Const Δ (.not φ)
  | notE {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ : Formula Const Γ} :
      ExtDerivation Const Δ (.not φ) →
      ExtDerivation Const Δ φ →
      ExtDerivation Const Δ .bot
  | allI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)} :
      ExtDerivation Const (weakenHyps (Base := Base) (σ := σ) Δ) φ →
      ExtDerivation Const Δ (.all φ)
  | allE {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)}
      (t : Term Const Γ σ) :
      ExtDerivation Const Δ (.all φ) →
      ExtDerivation Const Δ (instantiate (Base := Base) t φ)
  | exI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)}
      (t : Term Const Γ σ) :
      ExtDerivation Const Δ (instantiate (Base := Base) t φ) →
      ExtDerivation Const Δ (.ex φ)
  | exE {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {ψ : Formula Const Γ} :
      ExtDerivation Const Δ (.ex φ) →
      ExtDerivation Const (φ :: weakenHyps (Base := Base) (σ := σ) Δ)
        (weaken (Base := Base) (σ := σ) ψ) →
      ExtDerivation Const Δ ψ
  | eqRefl {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {τ : Ty Base} (t : Term Const Γ τ) :
      ExtDerivation Const Δ (.eq t t)
  | eqSymm {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {τ : Ty Base} {t u : Term Const Γ τ} :
      ExtDerivation Const Δ (.eq t u) →
      ExtDerivation Const Δ (.eq u t)
  | eqTrans {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {τ : Ty Base} {t u v : Term Const Γ τ} :
      ExtDerivation Const Δ (.eq t u) →
      ExtDerivation Const Δ (.eq u v) →
      ExtDerivation Const Δ (.eq t v)
  | eqPropI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {p q : Formula Const Γ} :
      ExtDerivation Const Δ (.imp p q) →
      ExtDerivation Const Δ (.imp q p) →
      ExtDerivation Const Δ (.eq p q)
  | eqPropEL {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {p q : Formula Const Γ} :
      ExtDerivation Const Δ (.eq p q) →
      ExtDerivation Const Δ (.imp p q)
  | eqPropER {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {p q : Formula Const Γ} :
      ExtDerivation Const Δ (.eq p q) →
      ExtDerivation Const Δ (.imp q p)
  | eqApp {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} {f g : Term Const Γ (σ ⇒ τ)} (t : Term Const Γ σ) :
      ExtDerivation Const Δ (.eq f g) →
      ExtDerivation Const Δ (.eq (.app f t) (.app g t))
  | eqAppArg {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} (f : Term Const Γ (σ ⇒ τ)) {t u : Term Const Γ σ} :
      ExtDerivation Const Δ (.eq t u) →
      ExtDerivation Const Δ (.eq (.app f t) (.app f u))
  | eqLam {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} {t u : Term Const (σ :: Γ) τ} :
      ExtDerivation Const (weakenHyps (Base := Base) (σ := σ) Δ) (.eq t u) →
      ExtDerivation Const Δ (.eq (.lam t) (.lam u))
  | funExt {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} {f g : Term Const Γ (σ ⇒ τ)} :
      ExtDerivation Const Δ
        (.all (.eq (.app (weaken (Base := Base) (σ := σ) f) (.var .vz))
                   (.app (weaken (Base := Base) (σ := σ) g) (.var .vz)))) →
      ExtDerivation Const Δ (.eq f g)
  | beta {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} (t : Term Const Γ σ) (u : Term Const (σ :: Γ) τ) :
      ExtDerivation Const Δ (.eq (.app (.lam u) t) (instantiate (Base := Base) t u))
  | eta {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} (f : Term Const Γ (σ ⇒ τ)) :
      ExtDerivation Const Δ (.eq (.lam (.app (weaken (Base := Base) (σ := σ) f) (.var .vz))) f)

namespace ExtDerivation

variable {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ ψ : Formula Const Γ}

abbrev Theorem (Const : Ty Base → Type v) (φ : ClosedFormula Const) : Prop :=
  ExtDerivation Const ([] : List (ClosedFormula Const)) φ

@[simp] theorem mapConst_weakenHyps
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (Δ : List (Formula Const Γ)) :
    weakenHyps
        (Base := Base)
        (Const := Const')
        (σ := σ)
        (Δ.map (Mettapedia.Logic.HOL.mapConst f)) =
      (weakenHyps (Base := Base) (Const := Const) (σ := σ) Δ).map
        (Mettapedia.Logic.HOL.mapConst f) := by
  simp [weakenHyps, List.map_map, Function.comp, Mettapedia.Logic.HOL.mapConst_weaken]

def ofBase {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    Derivation Const Δ φ → ExtDerivation Const Δ φ
  | .hyp h => .hyp h
  | .topI => .topI
  | .botE h => .botE (ofBase h)
  | .andI hφ hψ => .andI (ofBase hφ) (ofBase hψ)
  | .andEL h => .andEL (ofBase h)
  | .andER h => .andER (ofBase h)
  | .orIL h => .orIL (ofBase h)
  | .orIR h => .orIR (ofBase h)
  | .orE hor hφ hψ => .orE (ofBase hor) (ofBase hφ) (ofBase hψ)
  | .impI h => .impI (ofBase h)
  | .impE hφψ hφ => .impE (ofBase hφψ) (ofBase hφ)
  | .notI h => .notI (ofBase h)
  | .notE hnot hφ => .notE (ofBase hnot) (ofBase hφ)
  | .allI h => .allI (ofBase h)
  | .allE t h => .allE t (ofBase h)
  | .exI t h => .exI t (ofBase h)
  | .exE hex hbody => .exE (ofBase hex) (ofBase hbody)
  | .eqRefl t => .eqRefl t
  | .eqSymm h => .eqSymm (ofBase h)
  | .eqTrans htu huv => .eqTrans (ofBase htu) (ofBase huv)
  | .eqApp t h => .eqApp t (ofBase h)
  | .eqLam h => .eqLam (ofBase h)
  | .funExt h => .funExt (ofBase h)
  | .beta t u => .beta t u
  | .eta f => .eta f

theorem mapConst
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ) :
    ExtDerivation Const Δ φ →
      ExtDerivation Const'
        (Δ.map (Mettapedia.Logic.HOL.mapConst f))
        (Mettapedia.Logic.HOL.mapConst f φ) := by
  intro d
  induction d with
  | hyp hmem =>
      exact .hyp (List.mem_map.mpr ⟨_, hmem, rfl⟩)
  | topI =>
      exact .topI
  | botE h ih =>
      exact .botE ih
  | andI hφ hψ ihφ ihψ =>
      exact .andI ihφ ihψ
  | andEL h ih =>
      exact .andEL ih
  | andER h ih =>
      exact .andER ih
  | orIL h ih =>
      exact .orIL ih
  | orIR h ih =>
      exact .orIR ih
  | orE hor hφ hψ ihor ihφ ihψ =>
      exact .orE ihor ihφ ihψ
  | impI h ih =>
      exact .impI ih
  | impE hφψ hφ ihφψ ihφ =>
      exact .impE ihφψ ihφ
  | notI h ih =>
      exact .notI ih
  | notE hnot hφ ihnot ihφ =>
      exact .notE ihnot ihφ
  | allI h ih =>
      exact .allI (by
        simpa [mapConst_weakenHyps] using ih)
  | allE t h ih =>
      simpa [Mettapedia.Logic.HOL.mapConst_instantiate] using
        (.allE (Mettapedia.Logic.HOL.mapConst f t) ih)
  | exI t h ih =>
      rename_i Γ' Δ' σ body
      have ih' : ExtDerivation Const'
          (Δ'.map (Mettapedia.Logic.HOL.mapConst f))
          (instantiate (Base := Base)
            (Mettapedia.Logic.HOL.mapConst f t)
            (Mettapedia.Logic.HOL.mapConst f body)) := by
        simpa [Mettapedia.Logic.HOL.mapConst_instantiate] using ih
      exact .exI (Mettapedia.Logic.HOL.mapConst f t) ih'
  | exE hex hbody ihex ihbody =>
      exact .exE ihex (by
        simpa [mapConst_weakenHyps, Mettapedia.Logic.HOL.mapConst_weaken] using ihbody)
  | eqRefl t =>
      exact .eqRefl (Mettapedia.Logic.HOL.mapConst f t)
  | eqSymm h ih =>
      exact .eqSymm ih
  | eqTrans htu huv ihtu ihuv =>
      exact .eqTrans ihtu ihuv
  | eqPropI hpq hqp ihpq ihqp =>
      exact .eqPropI ihpq ihqp
  | eqPropEL hpq ihpq =>
      exact .eqPropEL ihpq
  | eqPropER hpq ihpq =>
      exact .eqPropER ihpq
  | eqApp t h ih =>
      exact .eqApp (Mettapedia.Logic.HOL.mapConst f t) ih
  | eqAppArg g h ih =>
      exact .eqAppArg (Mettapedia.Logic.HOL.mapConst f g) ih
  | eqLam h ih =>
      exact .eqLam (by
        simpa [mapConst_weakenHyps] using ih)
  | funExt h ih =>
      exact .funExt (by
        simpa [Mettapedia.Logic.HOL.mapConst, Mettapedia.Logic.HOL.mapConst_weaken] using ih)
  | beta t u =>
      simpa [Mettapedia.Logic.HOL.mapConst, Mettapedia.Logic.HOL.mapConst_instantiate] using
        (.beta (Mettapedia.Logic.HOL.mapConst f t)
          (Mettapedia.Logic.HOL.mapConst f u))
  | eta g =>
      simpa [Mettapedia.Logic.HOL.mapConst, Mettapedia.Logic.HOL.mapConst_weaken] using
        (.eta (Mettapedia.Logic.HOL.mapConst f g))

theorem closedTheory_mapConst
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (h : ExtDerivation Const Δ φ) :
    ExtDerivation Const'
      (Δ.map (Mettapedia.Logic.HOL.mapClosedFormula f))
      (Mettapedia.Logic.HOL.mapClosedFormula f φ) := by
  simpa [Mettapedia.Logic.HOL.mapClosedFormula] using
    (mapConst (Base := Base) (Const := Const) (Const' := Const')
      (Δ := Δ) (φ := φ) f h)

theorem theorem_mapConst
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    {φ : ClosedFormula Const}
    (h : Theorem Const φ) :
    Theorem Const' (Mettapedia.Logic.HOL.mapClosedFormula f φ) := by
  simpa [Theorem, Mettapedia.Logic.HOL.mapClosedFormula] using
    (mapConst (Base := Base) (Const := Const) (Const' := Const')
      (Δ := ([] : List (ClosedFormula Const))) (φ := φ) f h)

theorem imp_mp
    (hImp : ExtDerivation Const Δ (.imp φ ψ))
    (hφ : ExtDerivation Const Δ φ) :
    ExtDerivation Const Δ ψ :=
  .impE hImp hφ

theorem not_bot_of
    (hNot : ExtDerivation Const Δ (.not φ))
    (hφ : ExtDerivation Const Δ φ) :
    ExtDerivation Const Δ .bot :=
  .notE hNot hφ

theorem mono {Γ : Ctx Base} {Δ Δ' : List (Formula Const Γ)} {φ : Formula Const Γ}
    (hsub : ∀ {χ : Formula Const Γ}, χ ∈ Δ → χ ∈ Δ') :
    ExtDerivation Const Δ φ → ExtDerivation Const Δ' φ := by
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
    (d : Theorem Const φ) : ExtDerivation Const Δ φ :=
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
  have hψ : ExtDerivation Const [φ] ψ :=
    .impE (ofTheorem (Δ := [φ]) hφψ) (.hyp (by simp))
  exact .impE (ofTheorem (Δ := [φ]) hψχ) hψ

theorem eqProp_mp_left {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {p q : Formula Const Γ}
    (hpq : ExtDerivation Const Δ (.eq p q))
    (hp : ExtDerivation Const Δ p) :
    ExtDerivation Const Δ q :=
  .impE (.eqPropEL hpq) hp

theorem eqProp_mp_right {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {p q : Formula Const Γ}
    (hpq : ExtDerivation Const Δ (.eq p q))
    (hq : ExtDerivation Const Δ q) :
    ExtDerivation Const Δ p :=
  .impE (.eqPropER hpq) hq

theorem eqAppCongr {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {σ τ : Ty Base} {f g : Term Const Γ (σ ⇒ τ)} {t u : Term Const Γ σ}
    (hfg : ExtDerivation Const Δ (.eq f g))
    (htu : ExtDerivation Const Δ (.eq t u)) :
    ExtDerivation Const Δ (.eq (.app f t) (.app g u)) := by
  exact
    .eqTrans
      (.eqApp t hfg)
      (.eqAppArg g htu)

theorem eqAppCongrSelf {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {σ τ : Ty Base} {f : Term Const Γ (σ ⇒ τ)} {t u : Term Const Γ σ}
    (htu : ExtDerivation Const Δ (.eq t u)) :
    ExtDerivation Const Δ (.eq (.app f t) (.app f u)) :=
  .eqAppArg f htu

end ExtDerivation

end Mettapedia.Logic.HOL
