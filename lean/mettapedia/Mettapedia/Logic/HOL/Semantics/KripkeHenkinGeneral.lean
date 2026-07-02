import Mettapedia.Logic.HOL.Syntax.Closed
import Mettapedia.Logic.HOL.Derivation
import Mettapedia.Logic.HOL.DerivationExtensionality
import Mettapedia.Logic.HOL.LindenbaumSet

/-!
# Kripke-Henkin general models

Kripke semantics for the EM-free extensional calculus in the Henkin
general-model style of `Semantics/Henkin.lean`: ambient carriers, a
world-indexed monotone admissibility predicate (growing quantifier domains
over constant ambient carriers), world-indexed extensional equality, and a
denotation function whose propositional layer is Kripke-monotone.

This interface complements the substitutional `KripkeHenkin` class: models
here interpret quantifiers over their own admissible domains, so concrete
(e.g. finite-frame, full-function-space) countermodels can be built by
structural recursion, while term-generated canonical models arise as the
instance whose admissible elements are (denotations of) closed terms.
-/

namespace Mettapedia.Logic.HOL

universe u v x

variable {Base : Type u} {Const : Ty Base → Type v}

namespace Ty

/-- Ambient Kripke carriers: propositions are world-indexed, functions are
full meta-level function spaces, base types are world-independent carriers.
Monotonicity of propositional values is imposed by admissibility, not here. -/
def denoteK (Carrier : Base → Type x) (World : Type x) : Ty Base → Type x
  | .prop => World → Prop
  | .base b => Carrier b
  | .arr σ τ => denoteK Carrier World σ → denoteK Carrier World τ

end Ty

/-- A Kripke-Henkin premodel: a preordered set of worlds, ambient carriers,
a world-indexed monotone admissibility predicate carving out the quantifier
domains, and interpretations of constants.  Propositional admissible values
are required to be upward closed. -/
structure KripkePreModel (Base : Type u) (Const : Ty Base → Type v) where
  World : Type x
  le : World → World → Prop
  le_refl : ∀ W, le W W
  le_trans : ∀ {U V W}, le U V → le V W → le U W
  Carrier : Base → Type x
  baseEq : World → (b : Base) → Carrier b → Carrier b → Prop
  baseEq_mono :
    ∀ {U V : World} {b : Base} {d e : Carrier b},
      le U V → baseEq U b d e → baseEq V b d e
  baseEq_refl : ∀ (W : World) (b : Base) (d : Carrier b), baseEq W b d d
  baseEq_symm :
    ∀ {W : World} {b : Base} {d e : Carrier b},
      baseEq W b d e → baseEq W b e d
  baseEq_trans :
    ∀ {W : World} {b : Base} {d e k : Carrier b},
      baseEq W b d e → baseEq W b e k → baseEq W b d k
  adm : World → (τ : Ty Base) → Ty.denoteK Carrier World τ → Prop
  adm_mono :
    ∀ {U V : World} {τ : Ty Base} {d : Ty.denoteK Carrier World τ},
      le U V → adm U τ d → adm V τ d
  prop_adm_upset :
    ∀ {W : World} {S : Ty.denoteK Carrier World .prop},
      adm W .prop S → ∀ {U V : World}, le U V → S U → S V
  base_mem : ∀ (W : World) (b : Base) (d : Carrier b), adm W (.base b) d
  app_mem :
    ∀ {W : World} {σ τ : Ty Base}
      {f : Ty.denoteK Carrier World (σ ⇒ τ)} {d : Ty.denoteK Carrier World σ},
      adm W (σ ⇒ τ) f → adm W σ d → adm W τ (f d)
  constDen : {τ : Ty Base} → Const τ → Ty.denoteK Carrier World τ
  const_mem : ∀ (W : World) {τ : Ty Base} (c : Const τ), adm W τ (constDen c)

namespace KripkePreModel

variable (M : KripkePreModel Base Const)

/-- Typed valuations into the ambient Kripke carriers. -/
abbrev Valuation (Γ : Ctx Base) :=
  ∀ {τ}, Var Γ τ → Ty.denoteK M.Carrier M.World τ

/-- A valuation is admissible at a world when each variable lands in the
admissible domain of its type there. -/
def ValuationAdm {Γ : Ctx Base} (W : M.World) (ρ : M.Valuation Γ) : Prop :=
  ∀ {τ} (v : Var Γ τ), M.adm W τ (ρ v)

/-- Extend a valuation by one element. -/
def extend {Γ : Ctx Base} {σ : Ty Base} (ρ : M.Valuation Γ)
    (d : Ty.denoteK M.Carrier M.World σ) : M.Valuation (σ :: Γ) := fun v =>
  match v with
  | .vz => d
  | .vs v => ρ v

@[simp] theorem extend_vz {Γ : Ctx Base} {σ : Ty Base} (ρ : M.Valuation Γ)
    (d : Ty.denoteK M.Carrier M.World σ) :
    M.extend ρ d Var.vz = d := rfl

@[simp] theorem extend_vs {Γ : Ctx Base} {σ τ : Ty Base} (ρ : M.Valuation Γ)
    (d : Ty.denoteK M.Carrier M.World σ) (v : Var Γ τ) :
    M.extend ρ d (Var.vs v) = ρ v := rfl

theorem valuationAdm_mono {Γ : Ctx Base} {U V : M.World} {ρ : M.Valuation Γ}
    (hUV : M.le U V) (hρ : M.ValuationAdm U ρ) : M.ValuationAdm V ρ :=
  fun v => M.adm_mono hUV (hρ v)

theorem extend_adm {Γ : Ctx Base} {σ : Ty Base} {W : M.World} {ρ : M.Valuation Γ}
    {d : Ty.denoteK M.Carrier M.World σ}
    (hρ : M.ValuationAdm W ρ) (hd : M.adm W σ d) :
    M.ValuationAdm W (M.extend ρ d) := by
  intro τ v
  cases v with
  | vz => exact hd
  | vs v => exact hρ v

/-- World-indexed extensional equality, recursive on type.  At propositions it
is agreement at all future worlds; at functions it is extensional agreement on
admissible arguments at all future worlds. -/
def EqvK : (W : M.World) → (τ : Ty Base) →
    Ty.denoteK M.Carrier M.World τ → Ty.denoteK M.Carrier M.World τ → Prop
  | W, .prop, S, T => ∀ V, M.le W V → (S V ↔ T V)
  | W, .base b, d, e => M.baseEq W b d e
  | W, .arr σ τ, f, g =>
      ∀ V, M.le W V → ∀ d, M.adm V σ d → EqvK V τ (f d) (g d)

@[simp] theorem eqvK_prop {W : M.World} {S T : Ty.denoteK M.Carrier M.World .prop} :
    M.EqvK W .prop S T ↔ ∀ V, M.le W V → (S V ↔ T V) := Iff.rfl

@[simp] theorem eqvK_base {W : M.World} {b : Base} {d e : M.Carrier b} :
    M.EqvK W (.base b) d e ↔ M.baseEq W b d e := Iff.rfl

@[simp] theorem eqvK_arr {W : M.World} {σ τ : Ty Base}
    {f g : Ty.denoteK M.Carrier M.World (σ ⇒ τ)} :
    M.EqvK W (σ ⇒ τ) f g ↔
      ∀ V, M.le W V → ∀ d, M.adm V σ d → M.EqvK V τ (f d) (g d) := Iff.rfl

theorem eqvK_mono {τ : Ty Base} {U V : M.World}
    {d e : Ty.denoteK M.Carrier M.World τ}
    (hUV : M.le U V) (h : M.EqvK U τ d e) : M.EqvK V τ d e := by
  cases τ with
  | prop => exact fun V' hV' => h V' (M.le_trans hUV hV')
  | base b => exact M.baseEq_mono hUV h
  | arr σ τ => exact fun V' hV' => h V' (M.le_trans hUV hV')

theorem eqvK_refl : ∀ {τ : Ty Base} {W : M.World}
    {d : Ty.denoteK M.Carrier M.World τ}, M.adm W τ d → M.EqvK W τ d d
  | .prop, _, _, _ => fun _ _ => Iff.rfl
  | .base _, W, d, _ => M.baseEq_refl W _ d
  | .arr _ _, _, _, hf => fun _V hV _d hd =>
      eqvK_refl (M.app_mem (M.adm_mono hV hf) hd)

theorem eqvK_symm : ∀ {τ : Ty Base} {W : M.World}
    {d e : Ty.denoteK M.Carrier M.World τ},
    M.EqvK W τ d e → M.EqvK W τ e d
  | .prop, _, _, _, h => fun V hV => (h V hV).symm
  | .base _, _, _, _, h => M.baseEq_symm h
  | .arr _ _, _, _, _, h => fun V hV d hd =>
      eqvK_symm (h V hV d hd)

theorem eqvK_trans : ∀ {τ : Ty Base} {W : M.World}
    {d e k : Ty.denoteK M.Carrier M.World τ},
    M.EqvK W τ d e → M.EqvK W τ e k → M.EqvK W τ d k
  | .prop, _, _, _, _, h₁, h₂ => fun V hV => (h₁ V hV).trans (h₂ V hV)
  | .base _, _, _, _, _, h₁, h₂ => M.baseEq_trans h₁ h₂
  | .arr _ _, _, _, _, _, h₁, h₂ => fun V hV d hd =>
      eqvK_trans (h₁ V hV d hd) (h₂ V hV d hd)

/-- Denotation of terms.  The propositional layer uses the Kripke clauses:
implication, negation, and universal quantification look at all future worlds;
quantifiers range over the admissible domain at the relevant world. -/
def denote : {Γ : Ctx Base} → {τ : Ty Base} →
    Term Const Γ τ → M.Valuation Γ → Ty.denoteK M.Carrier M.World τ
  | _, _, .var v, ρ => ρ v
  | _, _, .const c, _ => M.constDen c
  | _, _, .app f t, ρ => (denote f ρ) (denote t ρ)
  | _, _, .lam t, ρ => fun d => denote t (M.extend ρ d)
  | _, _, .top, _ => fun _ => True
  | _, _, .bot, _ => fun _ => False
  | _, _, .and φ ψ, ρ => fun W => denote φ ρ W ∧ denote ψ ρ W
  | _, _, .or φ ψ, ρ => fun W => denote φ ρ W ∨ denote ψ ρ W
  | _, _, .imp φ ψ, ρ => fun W => ∀ V, M.le W V → denote φ ρ V → denote ψ ρ V
  | _, _, .not φ, ρ => fun W => ∀ V, M.le W V → ¬ denote φ ρ V
  | _, _, .eq t u, ρ => fun W => M.EqvK W _ (denote t ρ) (denote u ρ)
  | _, _, .all φ, ρ => fun W =>
      ∀ V, M.le W V → ∀ d, M.adm V _ d → denote φ (M.extend ρ d) V
  | _, _, .ex φ, ρ => fun W =>
      ∃ d, M.adm W _ d ∧ denote φ (M.extend ρ d) W

@[simp] theorem denote_var {Γ : Ctx Base} {τ : Ty Base}
    (ρ : M.Valuation Γ) (v : Var Γ τ) :
    M.denote (.var v : Term Const Γ τ) ρ = ρ v := rfl

@[simp] theorem denote_const {Γ : Ctx Base} {τ : Ty Base}
    (ρ : M.Valuation Γ) (c : Const τ) :
    M.denote (.const c : Term Const Γ τ) ρ = M.constDen c := rfl

@[simp] theorem denote_app {Γ : Ctx Base} {σ τ : Ty Base}
    (ρ : M.Valuation Γ) (f : Term Const Γ (σ ⇒ τ)) (t : Term Const Γ σ) :
    M.denote (.app f t) ρ = (M.denote f ρ) (M.denote t ρ) := rfl

@[simp] theorem denote_lam {Γ : Ctx Base} {σ τ : Ty Base}
    (ρ : M.Valuation Γ) (t : Term Const (σ :: Γ) τ) :
    M.denote (.lam t) ρ = fun d => M.denote t (M.extend ρ d) := rfl

@[simp] theorem denote_top {Γ : Ctx Base} (ρ : M.Valuation Γ) (W : M.World) :
    M.denote (.top : Formula Const Γ) ρ W ↔ True := Iff.rfl

@[simp] theorem denote_bot {Γ : Ctx Base} (ρ : M.Valuation Γ) (W : M.World) :
    M.denote (.bot : Formula Const Γ) ρ W ↔ False := Iff.rfl

@[simp] theorem denote_and {Γ : Ctx Base} (ρ : M.Valuation Γ)
    (φ ψ : Formula Const Γ) (W : M.World) :
    M.denote (.and φ ψ) ρ W ↔ M.denote φ ρ W ∧ M.denote ψ ρ W := Iff.rfl

@[simp] theorem denote_or {Γ : Ctx Base} (ρ : M.Valuation Γ)
    (φ ψ : Formula Const Γ) (W : M.World) :
    M.denote (.or φ ψ) ρ W ↔ M.denote φ ρ W ∨ M.denote ψ ρ W := Iff.rfl

@[simp] theorem denote_imp {Γ : Ctx Base} (ρ : M.Valuation Γ)
    (φ ψ : Formula Const Γ) (W : M.World) :
    M.denote (.imp φ ψ) ρ W ↔
      ∀ V, M.le W V → M.denote φ ρ V → M.denote ψ ρ V := Iff.rfl

@[simp] theorem denote_not {Γ : Ctx Base} (ρ : M.Valuation Γ)
    (φ : Formula Const Γ) (W : M.World) :
    M.denote (.not φ) ρ W ↔ ∀ V, M.le W V → ¬ M.denote φ ρ V := Iff.rfl

@[simp] theorem denote_eq {Γ : Ctx Base} {τ : Ty Base} (ρ : M.Valuation Γ)
    (t u : Term Const Γ τ) (W : M.World) :
    M.denote (.eq t u) ρ W ↔ M.EqvK W τ (M.denote t ρ) (M.denote u ρ) := Iff.rfl

@[simp] theorem denote_all {Γ : Ctx Base} {σ : Ty Base} (ρ : M.Valuation Γ)
    (φ : Formula Const (σ :: Γ)) (W : M.World) :
    M.denote (.all φ) ρ W ↔
      ∀ V, M.le W V → ∀ d, M.adm V σ d → M.denote φ (M.extend ρ d) V := Iff.rfl

@[simp] theorem denote_ex {Γ : Ctx Base} {σ : Ty Base} (ρ : M.Valuation Γ)
    (φ : Formula Const (σ :: Γ)) (W : M.World) :
    M.denote (.ex φ) ρ W ↔
      ∃ d, M.adm W σ d ∧ M.denote φ (M.extend ρ d) W := Iff.rfl

/-! ## Semantic substitution kit

Denotation commutes with renaming and substitution; these are the semantic
analogues of the syntactic `subst`/`rename` lemmas and carry the quantifier
and equality soundness cases. -/

theorem denote_ext {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ) :
    ∀ {ρ₁ ρ₂ : M.Valuation Γ},
      (∀ {σ} (v : Var Γ σ), ρ₁ v = ρ₂ v) →
        M.denote t ρ₁ = M.denote t ρ₂ := by
  induction t with
  | var v => intro ρ₁ ρ₂ h; exact h v
  | const c => intro ρ₁ ρ₂ _; rfl
  | app f t ihf iht => intro ρ₁ ρ₂ h; simp only [denote_app, ihf h, iht h]
  | lam t iht =>
      intro ρ₁ ρ₂ h
      funext d
      simp only [denote_lam]
      refine iht ?_
      intro σ v
      cases v with
      | vz => rfl
      | vs v => exact h v
  | top => intro ρ₁ ρ₂ _; rfl
  | bot => intro ρ₁ ρ₂ _; rfl
  | and φ ψ ihφ ihψ => intro ρ₁ ρ₂ h; simp only [denote]; rw [ihφ h, ihψ h]
  | or φ ψ ihφ ihψ => intro ρ₁ ρ₂ h; simp only [denote]; rw [ihφ h, ihψ h]
  | imp φ ψ ihφ ihψ => intro ρ₁ ρ₂ h; simp only [denote]; rw [ihφ h, ihψ h]
  | not φ ihφ => intro ρ₁ ρ₂ h; simp only [denote]; rw [ihφ h]
  | eq t u iht ihu => intro ρ₁ ρ₂ h; simp only [denote]; rw [iht h, ihu h]
  | all φ ihφ =>
      intro ρ₁ ρ₂ h
      simp only [denote]
      have hbody : ∀ d, M.denote φ (M.extend ρ₁ d) = M.denote φ (M.extend ρ₂ d) := by
        intro d
        refine ihφ ?_
        intro σ v
        cases v with
        | vz => rfl
        | vs v => exact h v
      simp only [hbody]
  | ex φ ihφ =>
      intro ρ₁ ρ₂ h
      simp only [denote]
      have hbody : ∀ d, M.denote φ (M.extend ρ₁ d) = M.denote φ (M.extend ρ₂ d) := by
        intro d
        refine ihφ ?_
        intro σ v
        cases v with
        | vz => rfl
        | vs v => exact h v
      simp only [hbody]

theorem denote_rename {Γ : Ctx Base} {τ : Ty Base}
    (t : Term Const Γ τ) :
    ∀ {Δ : Ctx Base} (r : Rename Base Γ Δ) (ρ : M.Valuation Δ),
      M.denote (rename r t) ρ = M.denote t (fun v => ρ (r v)) := by
  induction t with
  | var v => intro Δ r ρ; rfl
  | const c => intro Δ r ρ; rfl
  | app f t ihf iht =>
      intro Δ r ρ
      simp only [rename, denote_app, ihf r ρ, iht r ρ]
  | lam t iht =>
      intro Δ r ρ
      funext d
      calc M.denote (rename (Rename.lift r) t) (M.extend ρ d)
          = M.denote t (fun v => M.extend ρ d (Rename.lift r v)) :=
            iht (Rename.lift r) (M.extend ρ d)
        _ = M.denote t (M.extend (fun v => ρ (r v)) d) :=
            M.denote_ext t (by intro σ' v; cases v <;> rfl)
  | top => intro Δ r ρ; rfl
  | bot => intro Δ r ρ; rfl
  | and φ ψ ihφ ihψ =>
      intro Δ r ρ; simp only [rename, denote, ihφ r ρ, ihψ r ρ]
  | or φ ψ ihφ ihψ =>
      intro Δ r ρ; simp only [rename, denote, ihφ r ρ, ihψ r ρ]
  | imp φ ψ ihφ ihψ =>
      intro Δ r ρ; simp only [rename, denote, ihφ r ρ, ihψ r ρ]
  | not φ ihφ =>
      intro Δ r ρ; simp only [rename, denote, ihφ r ρ]
  | eq t u iht ihu =>
      intro Δ r ρ; simp only [rename, denote, iht r ρ, ihu r ρ]
  | all φ ihφ =>
      intro Δ r ρ
      have hbody : ∀ d, M.denote (rename (Rename.lift r) φ) (M.extend ρ d)
          = M.denote φ (M.extend (fun v => ρ (r v)) d) := by
        intro d
        calc M.denote (rename (Rename.lift r) φ) (M.extend ρ d)
            = M.denote φ (fun v => M.extend ρ d (Rename.lift r v)) :=
              ihφ (Rename.lift r) (M.extend ρ d)
          _ = M.denote φ (M.extend (fun v => ρ (r v)) d) :=
              M.denote_ext φ (by intro σ' v; cases v <;> rfl)
      simp only [rename, denote, hbody]
  | ex φ ihφ =>
      intro Δ r ρ
      have hbody : ∀ d, M.denote (rename (Rename.lift r) φ) (M.extend ρ d)
          = M.denote φ (M.extend (fun v => ρ (r v)) d) := by
        intro d
        calc M.denote (rename (Rename.lift r) φ) (M.extend ρ d)
            = M.denote φ (fun v => M.extend ρ d (Rename.lift r v)) :=
              ihφ (Rename.lift r) (M.extend ρ d)
          _ = M.denote φ (M.extend (fun v => ρ (r v)) d) :=
              M.denote_ext φ (by intro σ' v; cases v <;> rfl)
      simp only [rename, denote, hbody]

/-- Weakened terms ignore the newest valuation entry. -/
theorem denote_weaken {Γ : Ctx Base} {σ τ : Ty Base}
    (t : Term Const Γ τ) (ρ : M.Valuation Γ)
    (d : Ty.denoteK M.Carrier M.World σ) :
    M.denote (weaken (σ := σ) t) (M.extend ρ d) = M.denote t ρ := by
  unfold weaken
  exact (M.denote_rename t (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ))
      (M.extend ρ d)).trans
    (M.denote_ext t (by intro σ' v; rfl))

theorem denote_subst {Γ : Ctx Base} {τ : Ty Base}
    (t : Term Const Γ τ) :
    ∀ {Δ : Ctx Base} (σs : Subst Const Γ Δ) (ρ : M.Valuation Δ),
      M.denote (subst σs t) ρ = M.denote t (fun v => M.denote (σs v) ρ) := by
  induction t with
  | var v => intro Δ σs ρ; rfl
  | const c => intro Δ σs ρ; rfl
  | app f t ihf iht =>
      intro Δ σs ρ
      simp only [subst, denote_app, ihf σs ρ, iht σs ρ]
  | lam t iht =>
      intro Δ σs ρ
      funext d
      calc M.denote (subst (Subst.lift σs) t) (M.extend ρ d)
          = M.denote t (fun v => M.denote (Subst.lift σs v) (M.extend ρ d)) :=
            iht (Subst.lift σs) (M.extend ρ d)
        _ = M.denote t (M.extend (fun v => M.denote (σs v) ρ) d) := by
            refine M.denote_ext t ?_
            intro σ' v
            cases v with
            | vz => rfl
            | vs v => exact M.denote_weaken (σs v) ρ d
  | top => intro Δ σs ρ; rfl
  | bot => intro Δ σs ρ; rfl
  | and φ ψ ihφ ihψ =>
      intro Δ σs ρ; simp only [subst, denote, ihφ σs ρ, ihψ σs ρ]
  | or φ ψ ihφ ihψ =>
      intro Δ σs ρ; simp only [subst, denote, ihφ σs ρ, ihψ σs ρ]
  | imp φ ψ ihφ ihψ =>
      intro Δ σs ρ; simp only [subst, denote, ihφ σs ρ, ihψ σs ρ]
  | not φ ihφ =>
      intro Δ σs ρ; simp only [subst, denote, ihφ σs ρ]
  | eq t u iht ihu =>
      intro Δ σs ρ; simp only [subst, denote, iht σs ρ, ihu σs ρ]
  | all φ ihφ =>
      intro Δ σs ρ
      have hbody : ∀ d, M.denote (subst (Subst.lift σs) φ) (M.extend ρ d)
          = M.denote φ (M.extend (fun v => M.denote (σs v) ρ) d) := by
        intro d
        calc M.denote (subst (Subst.lift σs) φ) (M.extend ρ d)
            = M.denote φ (fun v => M.denote (Subst.lift σs v) (M.extend ρ d)) :=
              ihφ (Subst.lift σs) (M.extend ρ d)
          _ = M.denote φ (M.extend (fun v => M.denote (σs v) ρ) d) := by
              refine M.denote_ext φ ?_
              intro σ' v
              cases v with
              | vz => rfl
              | vs v => exact M.denote_weaken (σs v) ρ d
      simp only [subst, denote, hbody]
  | ex φ ihφ =>
      intro Δ σs ρ
      have hbody : ∀ d, M.denote (subst (Subst.lift σs) φ) (M.extend ρ d)
          = M.denote φ (M.extend (fun v => M.denote (σs v) ρ) d) := by
        intro d
        calc M.denote (subst (Subst.lift σs) φ) (M.extend ρ d)
            = M.denote φ (fun v => M.denote (Subst.lift σs v) (M.extend ρ d)) :=
              ihφ (Subst.lift σs) (M.extend ρ d)
          _ = M.denote φ (M.extend (fun v => M.denote (σs v) ρ) d) := by
              refine M.denote_ext φ ?_
              intro σ' v
              cases v with
              | vz => rfl
              | vs v => exact M.denote_weaken (σs v) ρ d
      simp only [subst, denote, hbody]

/-- The single substitution-denotation lemma: instantiating the top variable
denotes to extending the valuation by the denoted term. -/
theorem denote_instantiate {Γ : Ctx Base} {σ τ : Ty Base}
    (t : Term Const Γ σ) (u : Term Const (σ :: Γ) τ) (ρ : M.Valuation Γ) :
    M.denote (instantiate t u) ρ = M.denote u (M.extend ρ (M.denote t ρ)) := by
  unfold instantiate
  exact (M.denote_subst u (Subst.single t) ρ).trans
    (M.denote_ext u (by intro σ' v; cases v <;> rfl))

end KripkePreModel

/-- A Kripke-Henkin general model: a premodel closed under denotations of all
terms at admissible valuations, whose admissible functions moreover respect
world-indexed extensional equality in their arguments. -/
structure KripkeHenkinGeneral (Base : Type u) (Const : Ty Base → Type v)
    extends KripkePreModel Base Const where
  term_closed :
    ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ) (W : World)
      (ρ : toKripkePreModel.Valuation Γ),
      toKripkePreModel.ValuationAdm W ρ →
        adm W τ (toKripkePreModel.denote t ρ)
  app_congr_arg :
    ∀ {W : World} {σ τ : Ty Base}
      {f : Ty.denoteK Carrier World (σ ⇒ τ)}
      {d e : Ty.denoteK Carrier World σ},
      adm W (σ ⇒ τ) f → adm W σ d → adm W σ e →
        toKripkePreModel.EqvK W σ d e →
          toKripkePreModel.EqvK W τ (f d) (f e)

namespace KripkeHenkinGeneral

variable (M : KripkeHenkinGeneral Base Const)

abbrev Valuation (Γ : Ctx Base) := M.toKripkePreModel.Valuation Γ

abbrev ValuationAdm {Γ : Ctx Base} (W : M.World) (ρ : M.Valuation Γ) : Prop :=
  M.toKripkePreModel.ValuationAdm W ρ

abbrev extend {Γ : Ctx Base} {σ : Ty Base} (ρ : M.Valuation Γ)
    (d : Ty.denoteK M.Carrier M.World σ) : M.Valuation (σ :: Γ) :=
  M.toKripkePreModel.extend ρ d

abbrev EqvK (W : M.World) (τ : Ty Base) :=
  M.toKripkePreModel.EqvK W τ

abbrev denote {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ)
    (ρ : M.Valuation Γ) : Ty.denoteK M.Carrier M.World τ :=
  M.toKripkePreModel.denote t ρ

/-- Denotations of proposition-typed terms at admissible valuations are
Kripke-monotone. -/
theorem denote_prop_mono {Γ : Ctx Base} (φ : Formula Const Γ)
    {W : M.World} {ρ : M.Valuation Γ} (hρ : M.ValuationAdm W ρ)
    {U V : M.World} (hUV : M.le U V)
    (h : M.denote φ ρ U) : M.denote φ ρ V :=
  M.prop_adm_upset (M.term_closed φ W ρ hρ) hUV h

/-- All hypotheses in a list are denoted at a world. -/
def DenotesHyps {Γ : Ctx Base} (W : M.World) (ρ : M.Valuation Γ)
    (Δ : List (Formula Const Γ)) : Prop :=
  ∀ φ ∈ Δ, M.denote φ ρ W

theorem denotesHyps_mono {Γ : Ctx Base} {W V : M.World} {ρ : M.Valuation Γ}
    {Δ : List (Formula Const Γ)} (hρ : M.ValuationAdm W ρ)
    (hWV : M.le W V) (hΔ : M.DenotesHyps W ρ Δ) : M.DenotesHyps V ρ Δ :=
  fun φ hφ => M.denote_prop_mono φ hρ hWV (hΔ φ hφ)

theorem denotesHyps_cons {Γ : Ctx Base} {W : M.World} {ρ : M.Valuation Γ}
    {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (hφ : M.denote φ ρ W) (hΔ : M.DenotesHyps W ρ Δ) :
    M.DenotesHyps W ρ (φ :: Δ) := by
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact hφ
  · exact hΔ ψ hψ

/-- Weakened hypothesis lists are denoted at extended valuations. -/
theorem denotesHyps_weaken_extend {Γ : Ctx Base} {σ : Ty Base} {W : M.World}
    {ρ : M.Valuation Γ} {Δ : List (Formula Const Γ)}
    (hΔ : M.DenotesHyps W ρ Δ) (d : Ty.denoteK M.Carrier M.World σ) :
    M.DenotesHyps W (M.extend ρ d) (weakenHyps (Base := Base) (σ := σ) Δ) := by
  intro φ hφ
  rcases List.mem_map.mp hφ with ⟨ψ, hψ, rfl⟩
  exact (congrFun (M.toKripkePreModel.denote_weaken ψ ρ d) W).mpr (hΔ ψ hψ)

/-- **Soundness** of the EM-free extensional derivation calculus for every
Kripke-Henkin general model.  The object calculus contains no excluded-middle
schema; the metatheory is Lean's classical environment. -/
theorem sound {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (d : ExtDerivation Const Δ φ) :
    ∀ (M : KripkeHenkinGeneral Base Const) (W : M.World) (ρ : M.Valuation Γ),
      M.ValuationAdm W ρ → M.DenotesHyps W ρ Δ → M.denote φ ρ W := by
  induction d with
  | hyp hmem =>
      intro M W ρ hρ hΔ
      exact hΔ _ hmem
  | topI =>
      intro M W ρ hρ hΔ
      exact trivial
  | botE h ih =>
      intro M W ρ hρ hΔ
      exact (ih M W ρ hρ hΔ).elim
  | andI hφ hψ ihφ ihψ =>
      intro M W ρ hρ hΔ
      exact ⟨ihφ M W ρ hρ hΔ, ihψ M W ρ hρ hΔ⟩
  | andEL h ih =>
      intro M W ρ hρ hΔ
      exact (ih M W ρ hρ hΔ).1
  | andER h ih =>
      intro M W ρ hρ hΔ
      exact (ih M W ρ hρ hΔ).2
  | orIL h ih =>
      intro M W ρ hρ hΔ
      exact Or.inl (ih M W ρ hρ hΔ)
  | orIR h ih =>
      intro M W ρ hρ hΔ
      exact Or.inr (ih M W ρ hρ hΔ)
  | orE hor hφ hψ ihor ihφ ihψ =>
      intro M W ρ hρ hΔ
      rcases ihor M W ρ hρ hΔ with h | h
      · exact ihφ M W ρ hρ (M.denotesHyps_cons h hΔ)
      · exact ihψ M W ρ hρ (M.denotesHyps_cons h hΔ)
  | impI h ih =>
      intro M W ρ hρ hΔ V hWV hφV
      exact ih M V ρ (M.toKripkePreModel.valuationAdm_mono hWV hρ)
        (M.denotesHyps_cons hφV (M.denotesHyps_mono hρ hWV hΔ))
  | impE himp hφ ihimp ihφ =>
      intro M W ρ hρ hΔ
      exact ihimp M W ρ hρ hΔ W (M.le_refl W) (ihφ M W ρ hρ hΔ)
  | notI h ih =>
      intro M W ρ hρ hΔ V hWV hφV
      exact ih M V ρ (M.toKripkePreModel.valuationAdm_mono hWV hρ)
        (M.denotesHyps_cons hφV (M.denotesHyps_mono hρ hWV hΔ))
  | notE hnot hφ ihnot ihφ =>
      intro M W ρ hρ hΔ
      exact ihnot M W ρ hρ hΔ W (M.le_refl W) (ihφ M W ρ hρ hΔ)
  | allI h ih =>
      intro M W ρ hρ hΔ V hWV d hd
      exact ih M V (M.extend ρ d)
        (M.toKripkePreModel.extend_adm
          (M.toKripkePreModel.valuationAdm_mono hWV hρ) hd)
        (M.denotesHyps_weaken_extend (M.denotesHyps_mono hρ hWV hΔ) d)
  | allE t h ih =>
      rename_i σ' φ'
      intro M W ρ hρ hΔ
      have hall := ih M W ρ hρ hΔ W (M.le_refl W) (M.denote t ρ)
        (M.term_closed t W ρ hρ)
      exact (congrFun (M.toKripkePreModel.denote_instantiate t φ' ρ) W).mpr hall
  | exI t h ih =>
      rename_i σ' φ'
      intro M W ρ hρ hΔ
      refine ⟨M.denote t ρ, M.term_closed t W ρ hρ, ?_⟩
      exact (congrFun (M.toKripkePreModel.denote_instantiate t φ' ρ) W).mp
        (ih M W ρ hρ hΔ)
  | exE hex hbody ihex ihbody =>
      rename_i σ' φ' ψ'
      intro M W ρ hρ hΔ
      obtain ⟨d, hd, hφd⟩ := ihex M W ρ hρ hΔ
      have hψ := ihbody M W (M.extend ρ d)
        (M.toKripkePreModel.extend_adm hρ hd)
        (M.denotesHyps_cons hφd (M.denotesHyps_weaken_extend hΔ d))
      exact (congrFun (M.toKripkePreModel.denote_weaken ψ' ρ d) W).mp hψ
  | eqRefl t =>
      intro M W ρ hρ hΔ
      exact M.toKripkePreModel.eqvK_refl (M.term_closed t W ρ hρ)
  | eqSymm h ih =>
      intro M W ρ hρ hΔ
      exact M.toKripkePreModel.eqvK_symm (ih M W ρ hρ hΔ)
  | eqTrans htu huv ihtu ihuv =>
      intro M W ρ hρ hΔ
      exact M.toKripkePreModel.eqvK_trans (ihtu M W ρ hρ hΔ) (ihuv M W ρ hρ hΔ)
  | eqPropI hpq hqp ihpq ihqp =>
      intro M W ρ hρ hΔ V hWV
      constructor
      · exact fun hp => ihpq M W ρ hρ hΔ V hWV hp
      · exact fun hq => ihqp M W ρ hρ hΔ V hWV hq
  | eqPropEL hpq ihpq =>
      intro M W ρ hρ hΔ V hWV hp
      exact (ihpq M W ρ hρ hΔ V hWV).mp hp
  | eqPropER hpq ihpq =>
      intro M W ρ hρ hΔ V hWV hq
      exact (ihpq M W ρ hρ hΔ V hWV).mpr hq
  | eqApp t h ih =>
      intro M W ρ hρ hΔ
      exact ih M W ρ hρ hΔ W (M.le_refl W) (M.denote t ρ)
        (M.term_closed t W ρ hρ)
  | eqAppArg f h ih =>
      intro M W ρ hρ hΔ
      exact M.app_congr_arg (M.term_closed f W ρ hρ)
        (M.term_closed _ W ρ hρ) (M.term_closed _ W ρ hρ)
        (ih M W ρ hρ hΔ)
  | eqLam h ih =>
      intro M W ρ hρ hΔ V hWV d hd
      exact ih M V (M.extend ρ d)
        (M.toKripkePreModel.extend_adm
          (M.toKripkePreModel.valuationAdm_mono hWV hρ) hd)
        (M.denotesHyps_weaken_extend (M.denotesHyps_mono hρ hWV hΔ) d)
  | funExt h ih =>
      rename_i σ' τ' f g
      intro M W ρ hρ hΔ V hWV d hd
      have hpoint' : M.EqvK V τ'
          ((M.denote (weaken (Base := Base) (σ := σ') f) (M.extend ρ d)) d)
          ((M.denote (weaken (Base := Base) (σ := σ') g) (M.extend ρ d)) d) :=
        ih M W ρ hρ hΔ V hWV d hd
      have ef := congrFun (M.toKripkePreModel.denote_weaken f ρ d) d
      have eg := congrFun (M.toKripkePreModel.denote_weaken g ρ d) d
      exact ef ▸ eg ▸ hpoint'
  | beta t u =>
      intro M W ρ hρ hΔ
      show M.EqvK W _ (M.denote u (M.extend ρ (M.denote t ρ)))
        (M.denote (instantiate (Base := Base) t u) ρ)
      refine (congrArg
        (fun z => M.EqvK W _ (M.denote u (M.extend ρ (M.denote t ρ))) z)
        (M.toKripkePreModel.denote_instantiate t u ρ)).mpr ?_
      exact M.toKripkePreModel.eqvK_refl
        (M.term_closed u W (M.extend ρ (M.denote t ρ))
          (M.toKripkePreModel.extend_adm hρ (M.term_closed t W ρ hρ)))
  | eta f =>
      intro M W ρ hρ hΔ V hWV d hd
      show M.EqvK V _ ((M.denote (weaken (Base := Base) f) (M.extend ρ d)) d)
        ((M.denote f ρ) d)
      refine (congrArg (fun z => M.EqvK V _ z ((M.denote f ρ) d))
        (congrFun (M.toKripkePreModel.denote_weaken f ρ d) d)).mpr ?_
      exact M.toKripkePreModel.eqvK_refl
        (M.app_mem (M.adm_mono hWV (M.term_closed f W ρ hρ)) hd)

/-- The empty valuation for closed formulas. -/
def emptyVal : M.Valuation ([] : Ctx Base) := fun v => nomatch v

theorem emptyVal_adm (W : M.World) : M.ValuationAdm W M.emptyVal :=
  fun v => nomatch v

/-- A closed EM-free derivation from the empty theory is denoted at every
world of every Kripke-Henkin general model. -/
theorem denote_of_provable_empty {φ : ClosedFormula Const}
    (hφ : ClosedTheorySet.Provable (Const := Const) (∅ : ClosedTheorySet Const) φ)
    (W : M.World) : M.denote φ M.emptyVal W := by
  rcases hφ with ⟨Γ, hΓ, d⟩
  exact sound d M W M.emptyVal (M.emptyVal_adm W)
    (by intro ψ hψ; exact (hΓ ψ hψ).elim)

/-- A single counterworld in a Kripke-Henkin general model refutes
empty-theory EM-free derivability. -/
theorem not_provable_empty_of_countermodel {φ : ClosedFormula Const}
    (W : M.World) (hφ : ¬ M.denote φ M.emptyVal W) :
    ¬ ClosedTheorySet.Provable (Const := Const) (∅ : ClosedTheorySet Const) φ :=
  fun hProv => hφ (M.denote_of_provable_empty hProv W)

/-- A formula not yet denoted at a world but denoted at an accessible future
world refutes its excluded-middle instance at the original world. -/
theorem not_denote_excludedMiddle_of_eventual_counterexample
    {φ : ClosedFormula Const} {W : M.World}
    (hNow : ¬ M.denote φ M.emptyVal W)
    (hLater : ∃ V : M.World, M.le W V ∧ M.denote φ M.emptyVal V) :
    ¬ M.denote (.or φ (.not φ)) M.emptyVal W := by
  rintro (h | h)
  · exact hNow h
  · obtain ⟨V, hWV, hφV⟩ := hLater
    exact h V hWV hφV

/-- A growing-world counterexample refutes EM-free empty-theory derivability
of the corresponding excluded-middle instance. -/
theorem not_provable_empty_excludedMiddle_of_eventual_counterexample
    {φ : ClosedFormula Const} {W : M.World}
    (hNow : ¬ M.denote φ M.emptyVal W)
    (hLater : ∃ V : M.World, M.le W V ∧ M.denote φ M.emptyVal V) :
    ¬ ClosedTheorySet.Provable (Const := Const) (∅ : ClosedTheorySet Const)
        (.or φ (.not φ)) :=
  M.not_provable_empty_of_countermodel W
    (M.not_denote_excludedMiddle_of_eventual_counterexample hNow hLater)

end KripkeHenkinGeneral

end Mettapedia.Logic.HOL
