import Foundation.Logic.Semantics
import Mettapedia.Logic.HOL.Syntax.Closed

namespace Mettapedia.Logic.HOL

open LO

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

namespace Ty

/-- The ambient meta-level carrier associated to a simple HOL type. -/
def denote (Carrier : Base → Type (max (u + 1) w)) : Ty Base → Type (max (u + 1) w)
  | .prop => ULift.{max (u + 1) w, 0} Prop
  | .base b => Carrier b
  | .arr σ τ => denote Carrier σ → denote Carrier τ

end Ty

/-- A raw Henkin-style premodel: ambient carriers plus admissible quantifier domains. -/
structure PreModel (Base : Type u) (Const : Ty Base → Type v) where
  Carrier : Base → Type (max (u + 1) w)
  adm : (τ : Ty Base) → Ty.denote Carrier τ → Prop
  base_mem : ∀ b (x : Carrier b), adm (.base b) x
  prop_mem : ∀ p : ULift.{max (u + 1) w, 0} Prop, adm .prop p
  app_mem :
    ∀ {σ τ} {f : Ty.denote Carrier (σ ⇒ τ)} {x : Ty.denote Carrier σ},
      adm (σ ⇒ τ) f → adm σ x → adm τ (f x)
  constDen : {τ : Ty Base} → Const τ → Ty.denote Carrier τ
  const_mem : ∀ {τ : Ty Base} (c : Const τ), adm τ (constDen c)

namespace PreModel

/-- Typed valuations into the ambient carriers of a premodel. -/
abbrev Valuation (M : PreModel Base Const) (Γ : Ctx Base) :=
  ∀ {τ}, Var Γ τ → Ty.denote M.Carrier τ

/-- A valuation is admissible when each variable lands in the quantifier domain of its type. -/
def ValuationAdmissible (M : PreModel Base Const) {Γ : Ctx Base} (ρ : Valuation M Γ) : Prop :=
  ∀ {τ} (v : Var Γ τ), M.adm τ (ρ v)

/-- Extend a valuation by one element. -/
def extend (M : PreModel Base Const) {Γ : Ctx Base}
    (ρ : Valuation M Γ) (x : Ty.denote M.Carrier σ) : Valuation M (σ :: Γ)
  | _, .vz => x
  | _, .vs v => ρ v

theorem extend_admissible (M : PreModel Base Const) {Γ : Ctx Base}
    {ρ : Valuation M Γ} {x : Ty.denote M.Carrier σ}
    (hρ : ValuationAdmissible M ρ) (hx : M.adm σ x) :
    ValuationAdmissible M (extend M ρ x) := by
  intro τ v
  cases v with
  | vz =>
      simpa using hx
  | vs v =>
      exact hρ v

/-- Extensional typed equality, interpreted recursively on type. -/
def Eqv (M : PreModel Base Const) :
    (τ : Ty Base) → Ty.denote M.Carrier τ → Ty.denote M.Carrier τ → Prop
  | .prop, p, q => p.down ↔ q.down
  | .base _, x, y => x = y
  | .arr σ τ, f, g => ∀ x, M.adm σ x → Eqv M τ (f x) (g x)

@[simp] theorem eqv_prop (M : PreModel Base Const)
    {p q : ULift.{max (u + 1) w, 0} Prop} :
    Eqv M .prop p q ↔ (p.down ↔ q.down) := Iff.rfl

@[simp] theorem eqv_base (M : PreModel Base Const) {b : Base} {x y : M.Carrier b} :
    Eqv M (.base b) x y ↔ x = y := Iff.rfl

@[simp] theorem eqv_arr (M : PreModel Base Const) {σ τ : Ty Base}
    {f g : Ty.denote M.Carrier (σ ⇒ τ)} :
    Eqv M (σ ⇒ τ) f g ↔ ∀ x, M.adm σ x → Eqv M τ (f x) (g x) := Iff.rfl

theorem eqv_refl (M : PreModel Base Const) :
    ∀ {τ : Ty Base} {x : Ty.denote M.Carrier τ}, M.adm τ x → Eqv M τ x x
  | .prop, _, _ => by simp [Eqv]
  | .base _, _, _ => rfl
  | .arr σ τ, f, hf => by
      intro x hx
      exact eqv_refl M (M.app_mem hf hx)

/-- Denotation of terms in a premodel. Quantifiers range over admissible elements. -/
def denote (M : PreModel Base Const) :
    {Γ : Ctx Base} → {τ : Ty Base} → Term Const Γ τ → Valuation M Γ → Ty.denote M.Carrier τ
  | _, _, .var v, ρ => ρ v
  | _, _, .const c, _ => M.constDen c
  | _, _, .app f t, ρ => (denote M f ρ) (denote M t ρ)
  | _, _, .lam t, ρ => fun x => denote M t (extend M ρ x)
  | _, _, .top, _ => .up True
  | _, _, .bot, _ => .up False
  | _, _, .and φ ψ, ρ => .up ((denote M φ ρ).down ∧ (denote M ψ ρ).down)
  | _, _, .or φ ψ, ρ => .up ((denote M φ ρ).down ∨ (denote M ψ ρ).down)
  | _, _, .imp φ ψ, ρ => .up ((denote M φ ρ).down → (denote M ψ ρ).down)
  | _, _, .not φ, ρ => .up (¬ (denote M φ ρ).down)
  | _, _, .eq t u, ρ => .up (Eqv M _ (denote M t ρ) (denote M u ρ))
  | _, _, .all φ, ρ => .up (∀ x, M.adm _ x → (denote M φ (extend M ρ x)).down)
  | _, _, .ex φ, ρ => .up (∃ x, M.adm _ x ∧ (denote M φ (extend M ρ x)).down)

@[simp] theorem denote_var (M : PreModel Base Const) {Γ : Ctx Base} {τ : Ty Base}
    (ρ : Valuation M Γ) (v : Var Γ τ) :
    denote M (.var v : Term Const Γ τ) ρ = ρ v := rfl

@[simp] theorem denote_const (M : PreModel Base Const) {Γ : Ctx Base} {τ : Ty Base}
    (ρ : Valuation M Γ) (c : Const τ) :
    denote M (.const c : Term Const Γ τ) ρ = M.constDen c := rfl

@[simp] theorem denote_top (M : PreModel Base Const) {Γ : Ctx Base} (ρ : Valuation M Γ) :
    denote M (.top : Formula Const Γ) ρ = .up True := rfl

@[simp] theorem denote_bot (M : PreModel Base Const) {Γ : Ctx Base} (ρ : Valuation M Γ) :
    (denote M (.bot : Formula Const Γ) ρ).down ↔ False := Iff.rfl

@[simp] theorem denote_and (M : PreModel Base Const) {Γ : Ctx Base}
    (ρ : Valuation M Γ) (φ ψ : Formula Const Γ) :
    (denote M (.and φ ψ) ρ).down ↔ (denote M φ ρ).down ∧ (denote M ψ ρ).down := Iff.rfl

@[simp] theorem denote_or (M : PreModel Base Const) {Γ : Ctx Base}
    (ρ : Valuation M Γ) (φ ψ : Formula Const Γ) :
    (denote M (.or φ ψ) ρ).down ↔ (denote M φ ρ).down ∨ (denote M ψ ρ).down := Iff.rfl

@[simp] theorem denote_imp (M : PreModel Base Const) {Γ : Ctx Base}
    (ρ : Valuation M Γ) (φ ψ : Formula Const Γ) :
    (denote M (.imp φ ψ) ρ).down ↔ ((denote M φ ρ).down → (denote M ψ ρ).down) := Iff.rfl

@[simp] theorem denote_not (M : PreModel Base Const) {Γ : Ctx Base}
    (ρ : Valuation M Γ) (φ : Formula Const Γ) :
    (denote M (.not φ) ρ).down ↔ ¬ (denote M φ ρ).down := Iff.rfl

@[simp] theorem denote_all (M : PreModel Base Const) {Γ : Ctx Base} {σ : Ty Base}
    (ρ : Valuation M Γ) (φ : Formula Const (σ :: Γ)) :
    (denote M (.all φ) ρ).down ↔
      ∀ x : Ty.denote M.Carrier σ, M.adm σ x → (denote M φ (extend M ρ x)).down := Iff.rfl

@[simp] theorem denote_ex (M : PreModel Base Const) {Γ : Ctx Base} {σ : Ty Base}
    (ρ : Valuation M Γ) (φ : Formula Const (σ :: Γ)) :
    (denote M (.ex φ) ρ).down ↔
      ∃ x : Ty.denote M.Carrier σ, M.adm σ x ∧ (denote M φ (extend M ρ x)).down := Iff.rfl

/-- Satisfaction of a closed sentence in a premodel. -/
def models (M : PreModel Base Const) (φ : ClosedFormula Const) : Prop :=
  (denote M φ (fun v => nomatch v)).down

end PreModel

/-- A Henkin model is a premodel closed under denotations of all terms. -/
structure HenkinModel (Base : Type u) (Const : Ty Base → Type v) extends PreModel Base Const where
  term_closed :
    ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ) (ρ : PreModel.Valuation toPreModel Γ),
      PreModel.ValuationAdmissible toPreModel ρ →
        toPreModel.adm τ (PreModel.denote toPreModel t ρ)

namespace HenkinModel

abbrev Valuation (M : HenkinModel Base Const) (Γ : Ctx Base) := PreModel.Valuation M.toPreModel Γ

abbrev ValuationAdmissible (M : HenkinModel Base Const) {Γ : Ctx Base}
    (ρ : Valuation M Γ) : Prop :=
  PreModel.ValuationAdmissible M.toPreModel ρ

abbrev extend (M : HenkinModel Base Const) {Γ : Ctx Base}
    (ρ : Valuation M Γ) (x : Ty.denote M.Carrier σ) : Valuation M (σ :: Γ) :=
  PreModel.extend M.toPreModel ρ x

abbrev Eqv (M : HenkinModel Base Const) := PreModel.Eqv M.toPreModel

abbrev denote (M : HenkinModel Base Const) {Γ : Ctx Base} {τ : Ty Base}
    (t : Term Const Γ τ) (ρ : Valuation M Γ) : Ty.denote M.Carrier τ :=
  PreModel.denote M.toPreModel t ρ

abbrev models (M : HenkinModel Base Const) (φ : ClosedFormula Const) : Prop :=
  PreModel.models M.toPreModel φ

theorem extend_admissible (M : HenkinModel Base Const) {Γ : Ctx Base}
    {ρ : Valuation M Γ} {x : Ty.denote M.Carrier σ}
    (hρ : ValuationAdmissible M ρ) (hx : M.adm σ x) :
    ValuationAdmissible M (extend M ρ x) :=
  PreModel.extend_admissible M.toPreModel hρ hx

theorem denote_admissible (M : HenkinModel Base Const) {Γ : Ctx Base} {τ : Ty Base}
    {ρ : Valuation M Γ} (hρ : ValuationAdmissible M ρ) (t : Term Const Γ τ) :
    M.adm τ (denote M t ρ) :=
  M.term_closed t ρ hρ

/-- Standard models are the special case where every ambient value is admissible. -/
def standard
    (Carrier : Base → Type (max (u + 1) w))
    (constDen : {τ : Ty Base} → Const τ → Ty.denote Carrier τ) :
    HenkinModel Base Const where
  Carrier := Carrier
  adm := fun _ _ => True
  base_mem := by intro _ _; trivial
  prop_mem := by intro _; trivial
  app_mem := by intro _ _ _ _ _ _; trivial
  constDen := constDen
  const_mem := by intro _ _; trivial
  term_closed := by intro _ _ _ _ _; trivial

instance : LO.Semantics (HenkinModel Base Const) (ClosedFormula Const) where
  Models M φ := models M φ

theorem models_top (M : HenkinModel Base Const) :
    models M (.top : ClosedFormula Const) := by
  simp [models, PreModel.models, PreModel.denote]

theorem models_bot (M : HenkinModel Base Const) :
    ¬ models M (.bot : ClosedFormula Const) := by
  simp [models, PreModel.models, PreModel.denote]

@[simp] theorem models_and (M : HenkinModel Base Const) {φ ψ : ClosedFormula Const} :
    models M (.and φ ψ) ↔ models M φ ∧ models M ψ := by
  simp [models, PreModel.models, PreModel.denote]

@[simp] theorem models_or (M : HenkinModel Base Const) {φ ψ : ClosedFormula Const} :
    models M (.or φ ψ) ↔ models M φ ∨ models M ψ := by
  simp [models, PreModel.models, PreModel.denote]

@[simp] theorem models_imp (M : HenkinModel Base Const) {φ ψ : ClosedFormula Const} :
    models M (.imp φ ψ) ↔ (models M φ → models M ψ) := by
  simp [models, PreModel.models, PreModel.denote]

@[simp] theorem models_not (M : HenkinModel Base Const) {φ : ClosedFormula Const} :
    models M (.not φ) ↔ ¬ models M φ := by
  simp [models, PreModel.models, PreModel.denote]

@[simp] theorem eqv_refl (M : HenkinModel Base Const) {τ : Ty Base} {x : Ty.denote M.Carrier τ}
    (hx : M.adm τ x) : Eqv M τ x x :=
  PreModel.eqv_refl M.toPreModel hx

end HenkinModel

end Mettapedia.Logic.HOL
