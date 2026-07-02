import Mettapedia.Logic.HOL.CanonicalTheory
import Mettapedia.PLN.WorldModel.WMReadout
import Provenance.Semirings.Bool
import Provenance.Semirings.Nat

/-!
# Provenance-semiring readout for HOL derivation trees

This module adds a proof-relevant mirror of the current extensional HOL
derivation calculus.  The tree erases to `ExtDerivation`; Boolean evaluation
recovers ordinary derivability through tree existence; Nat evaluation gives a
concrete counting grade for an individual derivation tree.

The WM readout below is intentionally modest: it packages the Nat semiring
carrier with the derivability support order using a theoremhood/tree-existence
indicator.  It does not claim a canonical minimal proof count.

WM-2.5 adds three aggregation views over all trees of a formula:

* why-provenance: a set/ideal of source-support ledgers;
* counting evidence: finite bags of trees, ordered by Nat length;
* proof effort: cost spectra and upper-bound sets over `evalNat`.

These are kept as separate views because they need different order structure.
-/

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Proof-relevant mirror of the live `ExtDerivation` constructor surface. -/
inductive DerivationTree (Const : Ty Base → Type v) :
    {Γ : Ctx Base} → List (Formula Const Γ) → Formula Const Γ → Type (max u v) where
  | hyp {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
      φ ∈ Δ → DerivationTree Const Δ φ
  | topI {Γ : Ctx Base} {Δ : List (Formula Const Γ)} :
      DerivationTree Const Δ .top
  | botE {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
      DerivationTree Const Δ .bot → DerivationTree Const Δ φ
  | andI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      DerivationTree Const Δ φ → DerivationTree Const Δ ψ →
        DerivationTree Const Δ (.and φ ψ)
  | andEL {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      DerivationTree Const Δ (.and φ ψ) → DerivationTree Const Δ φ
  | andER {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      DerivationTree Const Δ (.and φ ψ) → DerivationTree Const Δ ψ
  | orIL {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      DerivationTree Const Δ φ → DerivationTree Const Δ (.or φ ψ)
  | orIR {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      DerivationTree Const Δ ψ → DerivationTree Const Δ (.or φ ψ)
  | orE {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ χ : Formula Const Γ} :
      DerivationTree Const Δ (.or φ ψ) →
      DerivationTree Const (φ :: Δ) χ →
      DerivationTree Const (ψ :: Δ) χ →
      DerivationTree Const Δ χ
  | impI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      DerivationTree Const (φ :: Δ) ψ → DerivationTree Const Δ (.imp φ ψ)
  | impE {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      DerivationTree Const Δ (.imp φ ψ) →
      DerivationTree Const Δ φ →
      DerivationTree Const Δ ψ
  | notI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ : Formula Const Γ} :
      DerivationTree Const (φ :: Δ) .bot → DerivationTree Const Δ (.not φ)
  | notE {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ : Formula Const Γ} :
      DerivationTree Const Δ (.not φ) →
      DerivationTree Const Δ φ →
      DerivationTree Const Δ .bot
  | allI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)} :
      DerivationTree Const (weakenHyps (Base := Base) (σ := σ) Δ) φ →
      DerivationTree Const Δ (.all φ)
  | allE {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)}
      (t : Term Const Γ σ) :
      DerivationTree Const Δ (.all φ) →
      DerivationTree Const Δ (instantiate (Base := Base) t φ)
  | exI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)}
      (t : Term Const Γ σ) :
      DerivationTree Const Δ (instantiate (Base := Base) t φ) →
      DerivationTree Const Δ (.ex φ)
  | exE {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {ψ : Formula Const Γ} :
      DerivationTree Const Δ (.ex φ) →
      DerivationTree Const (φ :: weakenHyps (Base := Base) (σ := σ) Δ)
        (weaken (Base := Base) (σ := σ) ψ) →
      DerivationTree Const Δ ψ
  | eqRefl {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {τ : Ty Base} (t : Term Const Γ τ) :
      DerivationTree Const Δ (.eq t t)
  | eqSymm {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {τ : Ty Base} {t u : Term Const Γ τ} :
      DerivationTree Const Δ (.eq t u) →
      DerivationTree Const Δ (.eq u t)
  | eqTrans {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {τ : Ty Base} {t u v : Term Const Γ τ} :
      DerivationTree Const Δ (.eq t u) →
      DerivationTree Const Δ (.eq u v) →
      DerivationTree Const Δ (.eq t v)
  | eqPropI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {p q : Formula Const Γ} :
      DerivationTree Const Δ (.imp p q) →
      DerivationTree Const Δ (.imp q p) →
      DerivationTree Const Δ (.eq p q)
  | eqPropEL {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {p q : Formula Const Γ} :
      DerivationTree Const Δ (.eq p q) →
      DerivationTree Const Δ (.imp p q)
  | eqPropER {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {p q : Formula Const Γ} :
      DerivationTree Const Δ (.eq p q) →
      DerivationTree Const Δ (.imp q p)
  | eqApp {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} {f g : Term Const Γ (σ ⇒ τ)} (t : Term Const Γ σ) :
      DerivationTree Const Δ (.eq f g) →
      DerivationTree Const Δ (.eq (.app f t) (.app g t))
  | eqAppArg {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} (f : Term Const Γ (σ ⇒ τ)) {t u : Term Const Γ σ} :
      DerivationTree Const Δ (.eq t u) →
      DerivationTree Const Δ (.eq (.app f t) (.app f u))
  | eqLam {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} {t u : Term Const (σ :: Γ) τ} :
      DerivationTree Const (weakenHyps (Base := Base) (σ := σ) Δ) (.eq t u) →
      DerivationTree Const Δ (.eq (.lam t) (.lam u))
  | funExt {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} {f g : Term Const Γ (σ ⇒ τ)} :
      DerivationTree Const Δ
        (.all (.eq (.app (weaken (Base := Base) (σ := σ) f) (.var .vz))
                   (.app (weaken (Base := Base) (σ := σ) g) (.var .vz)))) →
      DerivationTree Const Δ (.eq f g)
  | beta {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} (t : Term Const Γ σ) (u : Term Const (σ :: Γ) τ) :
      DerivationTree Const Δ (.eq (.app (.lam u) t) (instantiate (Base := Base) t u))
  | eta {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} (f : Term Const Γ (σ ⇒ τ)) :
      DerivationTree Const Δ (.eq (.lam (.app (weaken (Base := Base) (σ := σ) f) (.var .vz))) f)

namespace DerivationTree

variable {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ ψ : Formula Const Γ}

/-- Erase a proof-relevant tree to the kernel-checked extensional derivation. -/
def erase :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} → {φ : Formula Const Γ} →
      DerivationTree Const Δ φ → ExtDerivation Const Δ φ
  | _, _, _, hyp h => ExtDerivation.hyp h
  | _, _, _, topI => ExtDerivation.topI
  | _, _, _, botE d => ExtDerivation.botE d.erase
  | _, _, _, andI dφ dψ => ExtDerivation.andI dφ.erase dψ.erase
  | _, _, _, andEL d => ExtDerivation.andEL d.erase
  | _, _, _, andER d => ExtDerivation.andER d.erase
  | _, _, _, orIL d => ExtDerivation.orIL d.erase
  | _, _, _, orIR d => ExtDerivation.orIR d.erase
  | _, _, _, orE dor dφ dψ => ExtDerivation.orE dor.erase dφ.erase dψ.erase
  | _, _, _, impI d => ExtDerivation.impI d.erase
  | _, _, _, impE dImp dφ => ExtDerivation.impE dImp.erase dφ.erase
  | _, _, _, notI d => ExtDerivation.notI d.erase
  | _, _, _, notE dNot dφ => ExtDerivation.notE dNot.erase dφ.erase
  | _, _, _, allI d => ExtDerivation.allI d.erase
  | _, _, _, allE t d => ExtDerivation.allE t d.erase
  | _, _, _, exI t d => ExtDerivation.exI t d.erase
  | _, _, _, exE dEx dψ => ExtDerivation.exE dEx.erase dψ.erase
  | _, _, _, eqRefl t => ExtDerivation.eqRefl t
  | _, _, _, eqSymm d => ExtDerivation.eqSymm d.erase
  | _, _, _, eqTrans dtu duv => ExtDerivation.eqTrans dtu.erase duv.erase
  | _, _, _, eqPropI dpq dqp => ExtDerivation.eqPropI dpq.erase dqp.erase
  | _, _, _, eqPropEL d => ExtDerivation.eqPropEL d.erase
  | _, _, _, eqPropER d => ExtDerivation.eqPropER d.erase
  | _, _, _, eqApp t d => ExtDerivation.eqApp t d.erase
  | _, _, _, eqAppArg f d => ExtDerivation.eqAppArg f d.erase
  | _, _, _, eqLam d => ExtDerivation.eqLam d.erase
  | _, _, _, funExt d => ExtDerivation.funExt d.erase
  | _, _, _, beta t u => ExtDerivation.beta t u
  | _, _, _, eta f => ExtDerivation.eta f

/-- Reconstruct a proof-relevant tree from a Prop-valued derivation, up to
`Nonempty`. -/
theorem nonempty_of_extDerivation :
    ExtDerivation Const Δ φ → Nonempty (DerivationTree Const Δ φ) := by
  intro d
  induction d with
  | hyp h => exact ⟨hyp h⟩
  | topI => exact ⟨topI⟩
  | botE _ ih =>
      rcases ih with ⟨d⟩
      exact ⟨botE d⟩
  | andI _ _ ihφ ihψ =>
      rcases ihφ with ⟨dφ⟩
      rcases ihψ with ⟨dψ⟩
      exact ⟨andI dφ dψ⟩
  | andEL _ ih =>
      rcases ih with ⟨d⟩
      exact ⟨andEL d⟩
  | andER _ ih =>
      rcases ih with ⟨d⟩
      exact ⟨andER d⟩
  | orIL _ ih =>
      rcases ih with ⟨d⟩
      exact ⟨orIL d⟩
  | orIR _ ih =>
      rcases ih with ⟨d⟩
      exact ⟨orIR d⟩
  | orE _ _ _ ihor ihφ ihψ =>
      rcases ihor with ⟨dor⟩
      rcases ihφ with ⟨dφ⟩
      rcases ihψ with ⟨dψ⟩
      exact ⟨orE dor dφ dψ⟩
  | impI _ ih =>
      rcases ih with ⟨d⟩
      exact ⟨impI d⟩
  | impE _ _ ihImp ihφ =>
      rcases ihImp with ⟨dImp⟩
      rcases ihφ with ⟨dφ⟩
      exact ⟨impE dImp dφ⟩
  | notI _ ih =>
      rcases ih with ⟨d⟩
      exact ⟨notI d⟩
  | notE _ _ ihNot ihφ =>
      rcases ihNot with ⟨dNot⟩
      rcases ihφ with ⟨dφ⟩
      exact ⟨notE dNot dφ⟩
  | allI _ ih =>
      rcases ih with ⟨d⟩
      exact ⟨allI d⟩
  | allE t _ ih =>
      rcases ih with ⟨d⟩
      exact ⟨allE t d⟩
  | exI t _ ih =>
      rcases ih with ⟨d⟩
      exact ⟨exI t d⟩
  | exE _ _ ihEx ihψ =>
      rcases ihEx with ⟨dEx⟩
      rcases ihψ with ⟨dψ⟩
      exact ⟨exE dEx dψ⟩
  | eqRefl t => exact ⟨eqRefl t⟩
  | eqSymm _ ih =>
      rcases ih with ⟨d⟩
      exact ⟨eqSymm d⟩
  | eqTrans _ _ ih₁ ih₂ =>
      rcases ih₁ with ⟨d₁⟩
      rcases ih₂ with ⟨d₂⟩
      exact ⟨eqTrans d₁ d₂⟩
  | eqPropI _ _ ih₁ ih₂ =>
      rcases ih₁ with ⟨d₁⟩
      rcases ih₂ with ⟨d₂⟩
      exact ⟨eqPropI d₁ d₂⟩
  | eqPropEL _ ih =>
      rcases ih with ⟨d⟩
      exact ⟨eqPropEL d⟩
  | eqPropER _ ih =>
      rcases ih with ⟨d⟩
      exact ⟨eqPropER d⟩
  | eqApp t _ ih =>
      rcases ih with ⟨d⟩
      exact ⟨eqApp t d⟩
  | eqAppArg f _ ih =>
      rcases ih with ⟨d⟩
      exact ⟨eqAppArg f d⟩
  | eqLam _ ih =>
      rcases ih with ⟨d⟩
      exact ⟨eqLam d⟩
  | funExt _ ih =>
      rcases ih with ⟨d⟩
      exact ⟨funExt d⟩
  | beta t u => exact ⟨beta t u⟩
  | eta f => exact ⟨eta f⟩

/-- Tree existence is equivalent to the original Prop-valued derivation. -/
theorem nonempty_iff_extDerivation :
    Nonempty (DerivationTree Const Δ φ) ↔ ExtDerivation Const Δ φ :=
  ⟨fun h => h.elim (fun d => d.erase), nonempty_of_extDerivation⟩

/-- Per-constructor algebra for grading a derivation tree.  The recursive
spine is `gradeWith`; payloads supply only the local evidence operation for
each rule node. -/
structure GradePayload (Const : Ty Base → Type v) (Q : Type w) where
  hyp :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} → {φ : Formula Const Γ} →
      φ ∈ Δ → Q
  topI : Q
  botE :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
      DerivationTree Const Δ .bot → Q → Q
  andI :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
      {φ ψ : Formula Const Γ} →
      DerivationTree Const Δ φ → DerivationTree Const Δ ψ → Q → Q → Q
  andEL :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
      {φ ψ : Formula Const Γ} →
      DerivationTree Const Δ (.and φ ψ) → Q → Q
  andER :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
      {φ ψ : Formula Const Γ} →
      DerivationTree Const Δ (.and φ ψ) → Q → Q
  orIL :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
      {φ : Formula Const Γ} →
      DerivationTree Const Δ φ → Q → Q
  orIR :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
      {ψ : Formula Const Γ} →
      DerivationTree Const Δ ψ → Q → Q
  orE :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
      {φ ψ χ : Formula Const Γ} →
      DerivationTree Const Δ (.or φ ψ) →
      DerivationTree Const (φ :: Δ) χ →
      DerivationTree Const (ψ :: Δ) χ →
      Q → Q → Q → Q
  impI :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
      {φ ψ : Formula Const Γ} →
      DerivationTree Const (φ :: Δ) ψ → Q → Q
  impE :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
      {φ ψ : Formula Const Γ} →
      DerivationTree Const Δ (.imp φ ψ) →
      DerivationTree Const Δ φ → Q → Q → Q
  notI :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
      {φ : Formula Const Γ} →
      DerivationTree Const (φ :: Δ) .bot → Q → Q
  notE :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
      {φ : Formula Const Γ} →
      DerivationTree Const Δ (.not φ) →
      DerivationTree Const Δ φ → Q → Q → Q
  allI :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
      {σ : Ty Base} → {φ : Formula Const (σ :: Γ)} →
      DerivationTree Const (weakenHyps (Base := Base) (σ := σ) Δ) φ → Q → Q
  allE :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
      {σ : Ty Base} → {φ : Formula Const (σ :: Γ)} →
      (t : Term Const Γ σ) →
      DerivationTree Const Δ (.all φ) → Q → Q
  exI :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} → {σ : Ty Base} →
      {φ : Formula Const Γ} →
      (t : Term Const Γ σ) →
      DerivationTree Const Δ φ → Q → Q
  exE :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
      {σ : Ty Base} → {φ : Formula Const (σ :: Γ)} →
      {χ : Formula Const (σ :: Γ)} →
      DerivationTree Const Δ (.ex φ) →
      DerivationTree Const (φ :: weakenHyps (Base := Base) (σ := σ) Δ) χ →
      Q → Q → Q
  eqRefl :
    {Γ : Ctx Base} → {τ : Ty Base} → Term Const Γ τ → Q
  eqSymm :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
      {τ : Ty Base} → {t u : Term Const Γ τ} →
      DerivationTree Const Δ (.eq t u) → Q → Q
  eqTrans :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
      {τ : Ty Base} → {t u v : Term Const Γ τ} →
      DerivationTree Const Δ (.eq t u) →
      DerivationTree Const Δ (.eq u v) → Q → Q → Q
  eqPropI :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
      {p q : Formula Const Γ} →
      DerivationTree Const Δ (.imp p q) →
      DerivationTree Const Δ (.imp q p) → Q → Q → Q
  eqPropEL :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
      {p q : Formula Const Γ} →
      DerivationTree Const Δ (.eq p q) → Q → Q
  eqPropER :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
      {p q : Formula Const Γ} →
      DerivationTree Const Δ (.eq p q) → Q → Q
  eqApp :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
      {σ τ : Ty Base} → {f g : Term Const Γ (σ ⇒ τ)} →
      Term Const Γ σ → DerivationTree Const Δ (.eq f g) → Q → Q
  eqAppArg :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
      {σ τ : Ty Base} → {t u : Term Const Γ σ} →
      Term Const Γ (σ ⇒ τ) →
      DerivationTree Const Δ (.eq t u) → Q → Q
  eqLam :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
      {σ τ : Ty Base} → {t u : Term Const (σ :: Γ) τ} →
      DerivationTree Const (weakenHyps (Base := Base) (σ := σ) Δ) (.eq t u) →
      Q → Q
  funExt :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
      {σ τ : Ty Base} → {f g : Term Const Γ (σ ⇒ τ)} →
      DerivationTree Const Δ
        (.all (.eq (.app (weaken (Base := Base) (σ := σ) f) (.var .vz))
                   (.app (weaken (Base := Base) (σ := σ) g) (.var .vz)))) →
      Q → Q
  beta :
    {Γ : Ctx Base} → {σ τ : Ty Base} →
      Term Const Γ σ → Term Const (σ :: Γ) τ → Q
  eta :
    {Γ : Ctx Base} → {σ τ : Ty Base} → Term Const Γ (σ ⇒ τ) → Q

/-- Generic derivation-tree grading fold. -/
@[simp] def gradeWith {Q : Type w} (payload : GradePayload Const Q) :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} → {φ : Formula Const Γ} →
      DerivationTree Const Δ φ → Q
  | _, _, _, hyp h => payload.hyp h
  | _, _, _, topI => payload.topI
  | _, _, _, botE d => payload.botE d (gradeWith payload d)
  | _, _, _, andI dφ dψ =>
      payload.andI dφ dψ (gradeWith payload dφ) (gradeWith payload dψ)
  | _, _, _, andEL d => payload.andEL d (gradeWith payload d)
  | _, _, _, andER d => payload.andER d (gradeWith payload d)
  | _, _, _, orIL d => payload.orIL d (gradeWith payload d)
  | _, _, _, orIR d => payload.orIR d (gradeWith payload d)
  | _, _, _, orE dor dφ dψ =>
      payload.orE dor dφ dψ (gradeWith payload dor)
        (gradeWith payload dφ) (gradeWith payload dψ)
  | _, _, _, impI d => payload.impI d (gradeWith payload d)
  | _, _, _, impE dImp dφ =>
      payload.impE dImp dφ (gradeWith payload dImp) (gradeWith payload dφ)
  | _, _, _, notI d => payload.notI d (gradeWith payload d)
  | _, _, _, notE dNot dφ =>
      payload.notE dNot dφ (gradeWith payload dNot) (gradeWith payload dφ)
  | _, _, _, allI d => payload.allI d (gradeWith payload d)
  | _, _, _, allE t d => payload.allE t d (gradeWith payload d)
  | _, _, _, exI t d => payload.exI t d (gradeWith payload d)
  | _, _, _, exE dEx dψ =>
      payload.exE dEx dψ (gradeWith payload dEx) (gradeWith payload dψ)
  | _, _, _, eqRefl t => payload.eqRefl t
  | _, _, _, eqSymm d => payload.eqSymm d (gradeWith payload d)
  | _, _, _, eqTrans d1 d2 =>
      payload.eqTrans d1 d2 (gradeWith payload d1) (gradeWith payload d2)
  | _, _, _, eqPropI d1 d2 =>
      payload.eqPropI d1 d2 (gradeWith payload d1) (gradeWith payload d2)
  | _, _, _, eqPropEL d => payload.eqPropEL d (gradeWith payload d)
  | _, _, _, eqPropER d => payload.eqPropER d (gradeWith payload d)
  | _, _, _, eqApp t d => payload.eqApp t d (gradeWith payload d)
  | _, _, _, eqAppArg f d => payload.eqAppArg f d (gradeWith payload d)
  | _, _, _, eqLam d => payload.eqLam d (gradeWith payload d)
  | _, _, _, funExt d => payload.funExt d (gradeWith payload d)
  | _, _, _, beta t u => payload.beta t u
  | _, _, _, eta f => payload.eta f

@[simp] theorem gradeWith_impE {Q : Type w} (payload : GradePayload Const Q)
    (dImp : DerivationTree Const Δ (.imp φ ψ))
    (dφ : DerivationTree Const Δ φ) :
    gradeWith payload (impE dImp dφ) =
      payload.impE dImp dφ (gradeWith payload dImp) (gradeWith payload dφ) := rfl

@[simp] theorem gradeWith_allE {Q : Type w} (payload : GradePayload Const Q)
    {σ : Ty Base} {θ : Formula Const (σ :: Γ)}
    (t : Term Const Γ σ) (d : DerivationTree Const Δ (.all θ)) :
    gradeWith payload (allE t d) =
      payload.allE t d (gradeWith payload d) := rfl

/-- Semiring payload that recovers the original rule-counting evaluator. -/
def evalPayload {K : Type w} [Semiring K] : GradePayload Const K where
  hyp _ := 1
  topI := 1
  botE _ x := 1 + x
  andI _ _ x y := 1 + x + y
  andEL _ x := 1 + x
  andER _ x := 1 + x
  orIL _ x := 1 + x
  orIR _ x := 1 + x
  orE _ _ _ x y z := 1 + x + y + z
  impI _ x := 1 + x
  impE _ _ x y := 1 + x + y
  notI _ x := 1 + x
  notE _ _ x y := 1 + x + y
  allI _ x := 1 + x
  allE _ _ x := 1 + x
  exI _ _ x := 1 + x
  exE _ _ x y := 1 + x + y
  eqRefl _ := 1
  eqSymm _ x := 1 + x
  eqTrans _ _ x y := 1 + x + y
  eqPropI _ _ x y := 1 + x + y
  eqPropEL _ x := 1 + x
  eqPropER _ x := 1 + x
  eqApp _ _ x := 1 + x
  eqAppArg _ _ x := 1 + x
  eqLam _ x := 1 + x
  funExt _ x := 1 + x
  beta _ _ := 1
  eta _ := 1

/-- Rule-counting semiring evaluation of a single derivation tree. -/
def eval {K : Type w} [Semiring K] (d : DerivationTree Const Δ φ) : K :=
  gradeWith (evalPayload (Const := Const) (K := K)) d

/-- Boolean evaluation of a tree in the provenance Boolean semiring. -/
def evalBool (d : DerivationTree Const Δ φ) : Bool :=
  d.eval (K := Bool)

/-- Nat evaluation of a tree in the provenance counting semiring. -/
def evalNat (d : DerivationTree Const Δ φ) : Nat :=
  d.eval (K := Nat)

@[simp] theorem evalBool_eq_true (d : DerivationTree Const Δ φ) :
    d.evalBool = true := by
  induction d <;> simp_all [evalBool, eval, gradeWith, evalPayload] <;> aesop

@[simp] theorem evalNat_topI :
    (topI (Const := Const) (Γ := Γ) (Δ := Δ)).evalNat = 1 := by
  simp [evalNat, eval, gradeWith, evalPayload]

@[simp] theorem evalNat_andI
    (dφ : DerivationTree Const Δ φ) (dψ : DerivationTree Const Δ ψ) :
    (andI dφ dψ).evalNat = 1 + dφ.evalNat + dψ.evalNat := by
  simp [evalNat, eval, gradeWith, evalPayload]

@[simp] theorem evalNat_impE
    (dImp : DerivationTree Const Δ (.imp φ ψ))
    (dφ : DerivationTree Const Δ φ) :
    (impE dImp dφ).evalNat = 1 + dImp.evalNat + dφ.evalNat := by
  simp [evalNat, eval, gradeWith, evalPayload]

@[simp] theorem evalNat_pos (d : DerivationTree Const Δ φ) :
    0 < d.evalNat := by
  induction d <;> simp [evalNat, eval, evalPayload]

/-- A concrete positive counting example: deriving `top ∧ top` uses three
rule tokens in this local tree evaluator. -/
def topAndTopTree (Δ : List (Formula Const Γ)) :
    DerivationTree Const Δ
      (.and (.top : Formula Const Γ) (.top : Formula Const Γ)) :=
  andI topI topI

@[simp] theorem evalNat_topAndTopTree
    (Δ : List (Formula Const Γ)) :
    (topAndTopTree (Const := Const) Δ).evalNat = 3 := by
  simp [topAndTopTree, evalNat, eval, gradeWith, evalPayload]

/-- A second concrete tree for `top ∧ top`, useful as a positive
multi-derivation example. -/
def topAndTopTreeAlt (Δ : List (Formula Const Γ)) :
    DerivationTree Const Δ
      (.and (.top : Formula Const Γ) (.top : Formula Const Γ)) :=
  andI (andEL (topAndTopTree (Const := Const) Δ)) topI

@[simp] theorem evalNat_topAndTopTreeAlt
    (Δ : List (Formula Const Γ)) :
    (topAndTopTreeAlt (Const := Const) Δ).evalNat = 6 := by
  simp [topAndTopTreeAlt, topAndTopTree, evalNat, eval, gradeWith, evalPayload]

theorem topAndTopTree_ne_topAndTopTreeAlt
    (Δ : List (Formula Const Γ)) :
    topAndTopTree (Const := Const) Δ ≠ topAndTopTreeAlt (Const := Const) Δ := by
  intro h
  have hcost := congrArg DerivationTree.evalNat h
  simp at hcost

/-- Tags for the leaf sources of a derivation tree.  Only hypotheses and
zero-premise axiom/rule leaves are recorded here; internal inference steps are
handled by the tree shape and the cost evaluator. -/
inductive AxiomLeaf where
  | topI
  | eqRefl
  | beta
  | eta
  deriving DecidableEq, Repr

/-- A source token may be a hypothesis formula in any object context, or one
of the zero-premise rule leaves. -/
inductive SourceToken (Const : Ty Base → Type v) : Type (max u v) where
  | hyp {Γ : Ctx Base} (φ : Formula Const Γ)
  | axiom (r : AxiomLeaf)

/-- Leaf-support ledger for a derivation tree. -/
def sourceSupport :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} → {φ : Formula Const Γ} →
      DerivationTree Const Δ φ → Set (SourceToken (Base := Base) Const)
  | _, _, _, hyp (φ := φ) _ => {SourceToken.hyp φ}
  | _, _, _, topI => {SourceToken.axiom AxiomLeaf.topI}
  | _, _, _, botE d => d.sourceSupport
  | _, _, _, andI dφ dψ => dφ.sourceSupport ∪ dψ.sourceSupport
  | _, _, _, andEL d => d.sourceSupport
  | _, _, _, andER d => d.sourceSupport
  | _, _, _, orIL d => d.sourceSupport
  | _, _, _, orIR d => d.sourceSupport
  | _, _, _, orE dor dφ dψ =>
      dor.sourceSupport ∪ dφ.sourceSupport ∪ dψ.sourceSupport
  | _, _, _, impI d => d.sourceSupport
  | _, _, _, impE dImp dφ => dImp.sourceSupport ∪ dφ.sourceSupport
  | _, _, _, notI d => d.sourceSupport
  | _, _, _, notE dNot dφ => dNot.sourceSupport ∪ dφ.sourceSupport
  | _, _, _, allI d => d.sourceSupport
  | _, _, _, allE _ d => d.sourceSupport
  | _, _, _, exI _ d => d.sourceSupport
  | _, _, _, exE dEx dψ => dEx.sourceSupport ∪ dψ.sourceSupport
  | _, _, _, eqRefl _ => {SourceToken.axiom AxiomLeaf.eqRefl}
  | _, _, _, eqSymm d => d.sourceSupport
  | _, _, _, eqTrans d₁ d₂ => d₁.sourceSupport ∪ d₂.sourceSupport
  | _, _, _, eqPropI d₁ d₂ => d₁.sourceSupport ∪ d₂.sourceSupport
  | _, _, _, eqPropEL d => d.sourceSupport
  | _, _, _, eqPropER d => d.sourceSupport
  | _, _, _, eqApp _ d => d.sourceSupport
  | _, _, _, eqAppArg _ d => d.sourceSupport
  | _, _, _, eqLam d => d.sourceSupport
  | _, _, _, funExt d => d.sourceSupport
  | _, _, _, beta _ _ => {SourceToken.axiom AxiomLeaf.beta}
  | _, _, _, eta _ => {SourceToken.axiom AxiomLeaf.eta}

/-- Set-level independence predicate over the leaf-source support readout.
The ledger-backed WM-3b bridge is proved in the BinaryEvidence readout layer,
where concrete `EvidentialLedger` items are available. -/
def SourceDisjoint (d e : DerivationTree Const Δ φ) : Prop :=
  Disjoint d.sourceSupport e.sourceSupport

/-- A finite bag of derivation trees, used for the counting/hplus-compatible
aggregation view. -/
abbrev TreeBag (Const : Ty Base → Type v)
    {Γ : Ctx Base} (Δ : List (Formula Const Γ)) (φ : Formula Const Γ) :=
  List (DerivationTree Const Δ φ)

/-- Counting grade for a finite tree bag. -/
def TreeBag.countGrade (bag : TreeBag Const Δ φ) : Nat :=
  bag.length

@[simp] theorem TreeBag.countGrade_nil :
    TreeBag.countGrade ([] : TreeBag Const Δ φ) = 0 := rfl

@[simp] theorem TreeBag.countGrade_cons
    (d : DerivationTree Const Δ φ) (bag : TreeBag Const Δ φ) :
    TreeBag.countGrade (d :: bag) = TreeBag.countGrade bag + 1 := by
  simp [TreeBag.countGrade, Nat.add_comm]

/-- Adding a tree to a finite evidence bag never decreases its Nat grade. -/
theorem TreeBag.countGrade_le_cons
    (d : DerivationTree Const Δ φ) (bag : TreeBag Const Δ φ) :
    TreeBag.countGrade bag ≤ TreeBag.countGrade (d :: bag) := by
  simp [TreeBag.countGrade]

/-- Adding a source-disjoint tree never decreases the finite counting grade.
The source-disjointness assumption is retained for the WM-3b ledger contract;
the Nat-stage monotonicity itself only needs bag extension. -/
theorem TreeBag.countGrade_le_cons_of_sourceDisjoint
    (d e : DerivationTree Const Δ φ) (bag : TreeBag Const Δ φ)
    (_h : SourceDisjoint d e) :
    TreeBag.countGrade bag ≤ TreeBag.countGrade (d :: bag) :=
  TreeBag.countGrade_le_cons d bag

/-- Two-tree positive example for `top ∧ top`. -/
def topAndTopTwoTreeBag (Δ : List (Formula Const Γ)) :
    TreeBag Const Δ (.and (.top : Formula Const Γ) (.top : Formula Const Γ)) :=
  [topAndTopTree (Const := Const) Δ, topAndTopTreeAlt (Const := Const) Δ]

@[simp] theorem countGrade_topAndTopTwoTreeBag
    (Δ : List (Formula Const Γ)) :
    TreeBag.countGrade (topAndTopTwoTreeBag (Const := Const) Δ) = 2 := rfl

theorem countGrade_single_lt_topAndTopTwoTreeBag
    (Δ : List (Formula Const Γ)) :
    TreeBag.countGrade [topAndTopTree (Const := Const) Δ] <
      TreeBag.countGrade (topAndTopTwoTreeBag (Const := Const) Δ) := by
  simp [TreeBag.countGrade, topAndTopTwoTreeBag]

/-- Aggregate object for all trees of a fixed finite theory-context and
formula. -/
structure TreeAggregate (Const : Ty Base → Type v)
    {Γ : Ctx Base} (Δ : List (Formula Const Γ)) (φ : Formula Const Γ) where
  trees : Set (DerivationTree Const Δ φ)

/-- The all-tree aggregate. -/
def allTreesAggregate (Δ : List (Formula Const Γ)) (φ : Formula Const Γ) :
    TreeAggregate Const Δ φ where
  trees := Set.univ

/-- Exact Nat costs appearing in an aggregate. -/
def TreeAggregate.costSpectrum (A : TreeAggregate Const Δ φ) : Set Nat :=
  {n | ∃ d, d ∈ A.trees ∧ d.evalNat = n}

/-- Upper bounds above the exact tree costs in an aggregate.  This is the
order-theoretic face used for min-cost reasoning without requiring the Nat
semiring itself to carry arbitrary infima. -/
def TreeAggregate.costUpperBounds (A : TreeAggregate Const Δ φ) : Set Nat :=
  {n | ∃ d, d ∈ A.trees ∧ d.evalNat ≤ n}

/-- Why-provenance ideal: all source ledgers extending the support of at least
one tree in the aggregate. -/
def TreeAggregate.sourceIdeal (A : TreeAggregate Const Δ φ) :
    Set (Set (SourceToken (Base := Base) Const)) :=
  {S | ∃ d, d ∈ A.trees ∧ d.sourceSupport ⊆ S}

theorem TreeAggregate.sourceIdeal_upward
    {A : TreeAggregate Const Δ φ}
    {S S' : Set (SourceToken (Base := Base) Const)}
    (hS : S ∈ A.sourceIdeal) (hSS' : S ⊆ S') :
    S' ∈ A.sourceIdeal := by
  rcases hS with ⟨d, hdA, hdS⟩
  exact ⟨d, hdA, Set.Subset.trans hdS hSS'⟩

/-- Lift finite-context inclusion under a freshly assumed formula. -/
theorem consContext_mono
    {Δ Δ' : List (Formula Const Γ)} {φ : Formula Const Γ}
    (hsub : ∀ {χ : Formula Const Γ}, χ ∈ Δ → χ ∈ Δ') :
    ∀ {χ : Formula Const Γ}, χ ∈ φ :: Δ → χ ∈ φ :: Δ' := by
  intro χ hχ
  rw [List.mem_cons] at hχ ⊢
  rcases hχ with hχ | hχ
  · exact Or.inl hχ
  · exact Or.inr (hsub hχ)

/-- Lift finite-context inclusion through object-context weakening. -/
theorem weakenHyps_mono
    {σ : Ty Base} {Δ Δ' : List (Formula Const Γ)}
    (hsub : ∀ {χ : Formula Const Γ}, χ ∈ Δ → χ ∈ Δ') :
    ∀ {χ : Formula Const (σ :: Γ)},
      χ ∈ weakenHyps (Base := Base) (σ := σ) Δ →
        χ ∈ weakenHyps (Base := Base) (σ := σ) Δ' := by
  intro χ hχ
  rw [weakenHyps] at hχ ⊢
  rcases List.mem_map.mp hχ with ⟨ξ, hξ, rfl⟩
  exact List.mem_map.mpr ⟨ξ, hsub hξ, rfl⟩

/-- Monotonicity of proof-relevant trees under finite-context inclusion. -/
def mono :
    {Γ : Ctx Base} →
    {Δ Δ' : List (Formula Const Γ)} →
    {φ : Formula Const Γ} →
    (∀ {χ : Formula Const Γ}, χ ∈ Δ → χ ∈ Δ') →
    DerivationTree Const Δ φ → DerivationTree Const Δ' φ
  | _, _, _, _, hsub, hyp h => hyp (hsub h)
  | _, _, _, _, _, topI => topI
  | _, _, _, _, hsub, botE d => botE (mono hsub d)
  | _, _, _, _, hsub, andI dφ dψ => andI (mono hsub dφ) (mono hsub dψ)
  | _, _, _, _, hsub, andEL d => andEL (mono hsub d)
  | _, _, _, _, hsub, andER d => andER (mono hsub d)
  | _, _, _, _, hsub, orIL d => orIL (mono hsub d)
  | _, _, _, _, hsub, orIR d => orIR (mono hsub d)
  | _, _, _, _, hsub, orE dor dφ dψ =>
      orE (mono hsub dor)
        (mono (consContext_mono hsub) dφ)
        (mono (consContext_mono hsub) dψ)
  | _, _, _, _, hsub, impI d =>
      impI (mono (consContext_mono hsub) d)
  | _, _, _, _, hsub, impE dImp dφ => impE (mono hsub dImp) (mono hsub dφ)
  | _, _, _, _, hsub, notI d =>
      notI (mono (consContext_mono hsub) d)
  | _, _, _, _, hsub, notE dNot dφ => notE (mono hsub dNot) (mono hsub dφ)
  | _, _, _, _, hsub, allI d =>
      allI (mono (weakenHyps_mono hsub) d)
  | _, _, _, _, hsub, allE t d => allE t (mono hsub d)
  | _, _, _, _, hsub, exI t d => exI t (mono hsub d)
  | _, _, _, _, hsub, exE dEx dψ =>
      exE (mono hsub dEx)
        (mono (consContext_mono (weakenHyps_mono hsub)) dψ)
  | _, _, _, _, _, eqRefl t => eqRefl t
  | _, _, _, _, hsub, eqSymm d => eqSymm (mono hsub d)
  | _, _, _, _, hsub, eqTrans d₁ d₂ => eqTrans (mono hsub d₁) (mono hsub d₂)
  | _, _, _, _, hsub, eqPropI d₁ d₂ => eqPropI (mono hsub d₁) (mono hsub d₂)
  | _, _, _, _, hsub, eqPropEL d => eqPropEL (mono hsub d)
  | _, _, _, _, hsub, eqPropER d => eqPropER (mono hsub d)
  | _, _, _, _, hsub, eqApp t d => eqApp t (mono hsub d)
  | _, _, _, _, hsub, eqAppArg f d => eqAppArg f (mono hsub d)
  | _, _, _, _, hsub, eqLam d =>
      eqLam (mono (weakenHyps_mono hsub) d)
  | _, _, _, _, hsub, funExt d => funExt (mono hsub d)
  | _, _, _, _, _, beta t u => beta t u
  | _, _, _, _, _, eta f => eta f

@[simp] theorem eval_mono
    {K : Type w} [Semiring K]
    {Δ Δ' : List (Formula Const Γ)}
    (hsub : ∀ {χ : Formula Const Γ}, χ ∈ Δ → χ ∈ Δ')
    (d : DerivationTree Const Δ φ) :
    (mono hsub d).eval (K := K) = d.eval (K := K) := by
  induction d <;> simp_all [mono, eval, gradeWith, evalPayload]
  case allI d ih =>
    have h := ih (weakenHyps_mono hsub)
    simpa [mono, eval, gradeWith, evalPayload] using
      congrArg (fun x => (1 : K) + x) h
  case exE φEx ψ dEx dψ ihEx ihψ =>
    have hEx := ihEx hsub
    have hψ := ihψ (Δ' := φEx :: weakenHyps (Base := Base) Δ')
      (by exact List.mem_cons_self) (by
      intro a ha
      exact List.mem_cons_of_mem φEx (weakenHyps_mono hsub ha))
    simp [hψ]
  case eqLam d ih =>
    have h := ih (weakenHyps_mono hsub)
    simpa [mono, eval, gradeWith, evalPayload] using
      congrArg (fun x => (1 : K) + x) h

@[simp] theorem evalNat_mono
    {Δ Δ' : List (Formula Const Γ)}
    (hsub : ∀ {χ : Formula Const Γ}, χ ∈ Δ → χ ∈ Δ')
    (d : DerivationTree Const Δ φ) :
    (mono hsub d).evalNat = d.evalNat :=
  eval_mono (K := Nat) hsub d

/-- Move a tree to the left side of an appended context. -/
def appendLeft
    {Δ₁ Δ₂ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (d : DerivationTree Const Δ₁ φ) :
    DerivationTree Const (Δ₁ ++ Δ₂) φ :=
  mono (by intro χ hχ; exact List.mem_append_left _ hχ) d

/-- Move a tree to the right side of an appended context. -/
def appendRight
    {Δ₁ Δ₂ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (d : DerivationTree Const Δ₂ φ) :
    DerivationTree Const (Δ₁ ++ Δ₂) φ :=
  mono (by intro χ hχ; exact List.mem_append_right _ hχ) d

@[simp] theorem evalNat_appendLeft
    {Δ₁ Δ₂ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (d : DerivationTree Const Δ₁ φ) :
    (appendLeft (Const := Const) (Δ₂ := Δ₂) d).evalNat = d.evalNat := by
  unfold appendLeft
  exact evalNat_mono (by intro χ hχ; exact List.mem_append_left _ hχ) d

@[simp] theorem evalNat_appendRight
    {Δ₁ Δ₂ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (d : DerivationTree Const Δ₂ φ) :
    (appendRight (Const := Const) (Δ₁ := Δ₁) d).evalNat = d.evalNat := by
  unfold appendRight
  exact evalNat_mono (by intro χ hχ; exact List.mem_append_right _ hχ) d

/-- Compose an implication tree with an antecedent tree, appending their finite
contexts. -/
def composeImp
    {ΔImp Δφ : List (Formula Const Γ)} {φ ψ : Formula Const Γ}
    (dImp : DerivationTree Const ΔImp (.imp φ ψ))
    (dφ : DerivationTree Const Δφ φ) :
    DerivationTree Const (ΔImp ++ Δφ) ψ :=
  impE (appendLeft (Const := Const) (Δ₂ := Δφ) dImp)
    (appendRight (Const := Const) (Δ₁ := ΔImp) dφ)

@[simp] theorem evalNat_composeImp
    {ΔImp Δφ : List (Formula Const Γ)} {φ ψ : Formula Const Γ}
    (dImp : DerivationTree Const ΔImp (.imp φ ψ))
    (dφ : DerivationTree Const Δφ φ) :
    (composeImp (Const := Const) dImp dφ).evalNat =
      1 + dImp.evalNat + dφ.evalNat := by
  unfold composeImp
  rw [evalNat_impE]
  simp

end DerivationTree

namespace ClosedTheory

/-- Proof-relevant derivability from a finite closed theory. -/
def TreeProvable (Δ : ClosedTheory Const) (φ : ClosedFormula Const) : Prop :=
  Nonempty (DerivationTree Const Δ φ)

/-- Boolean-evaluating tree derivability from a finite closed theory. -/
def BoolTreeProvable (Δ : ClosedTheory Const) (φ : ClosedFormula Const) : Prop :=
  ∃ d : DerivationTree Const Δ φ, d.evalBool = true

theorem treeProvable_iff_provable
    {Δ : ClosedTheory Const} {φ : ClosedFormula Const} :
    TreeProvable (Const := Const) Δ φ ↔ Provable (Const := Const) Δ φ :=
  DerivationTree.nonempty_iff_extDerivation

theorem boolTreeProvable_iff_provable
    {Δ : ClosedTheory Const} {φ : ClosedFormula Const} :
    BoolTreeProvable (Const := Const) Δ φ ↔ Provable (Const := Const) Δ φ := by
  constructor
  · rintro ⟨d, _⟩
    exact d.erase
  · intro h
    rcases DerivationTree.nonempty_of_extDerivation (Const := Const) h with ⟨d⟩
    exact ⟨d, d.evalBool_eq_true⟩

end ClosedTheory

namespace ClosedTheorySet

/-- Proof-relevant finite derivability from a closed theory set. -/
def TreeProvable (T : ClosedTheorySet Const) (φ : ClosedFormula Const) : Prop :=
  ∃ Γ : ClosedTheory Const,
    (∀ ψ, ψ ∈ Γ → ψ ∈ T) ∧ Nonempty (DerivationTree Const Γ φ)

/-- Boolean-evaluating tree derivability from a closed theory set. -/
def BoolTreeProvable (T : ClosedTheorySet Const) (φ : ClosedFormula Const) : Prop :=
  ∃ Γ : ClosedTheory Const,
    (∀ ψ, ψ ∈ Γ → ψ ∈ T) ∧
      ∃ d : DerivationTree Const Γ φ, d.evalBool = true

theorem treeProvable_iff_provable
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const} :
    TreeProvable (Const := Const) T φ ↔ Provable (Const := Const) T φ := by
  constructor
  · rintro ⟨Γ, hΓ, hTree⟩
    exact ⟨Γ, hΓ, DerivationTree.nonempty_iff_extDerivation.mp hTree⟩
  · rintro ⟨Γ, hΓ, hDer⟩
    exact ⟨Γ, hΓ, DerivationTree.nonempty_iff_extDerivation.mpr hDer⟩

theorem boolTreeProvable_iff_provable
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const} :
    BoolTreeProvable (Const := Const) T φ ↔ Provable (Const := Const) T φ := by
  constructor
  · rintro ⟨Γ, hΓ, d, _⟩
    exact ⟨Γ, hΓ, d.erase⟩
  · rintro ⟨Γ, hΓ, hDer⟩
    rcases DerivationTree.nonempty_of_extDerivation (Const := Const) hDer with ⟨d⟩
    exact ⟨Γ, hΓ, d, d.evalBool_eq_true⟩

/-- A concrete proof-relevant witness for finite derivability from a closed
theory set.  This is the all-tree aggregate's element type at theory-set level. -/
structure TreeWitness (T : ClosedTheorySet Const) (φ : ClosedFormula Const) where
  ctx : ClosedTheory Const
  ctx_mem : ∀ ψ, ψ ∈ ctx → ψ ∈ T
  tree : DerivationTree Const ctx φ

namespace TreeWitness

theorem provable {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (w : TreeWitness (Const := Const) T φ) :
    Provable (Const := Const) T φ :=
  ⟨w.ctx, w.ctx_mem, w.tree.erase⟩

end TreeWitness

/-- Exact Nat costs of all proof-relevant finite derivations of a formula. -/
def costSpectrum (T : ClosedTheorySet Const) (φ : ClosedFormula Const) : Set Nat :=
  {n | ∃ w : TreeWitness (Const := Const) T φ, w.tree.evalNat = n}

/-- Upper bounds above exact tree costs.  This is the order-theoretic face used
for min-cost reasoning; the Nat semiring itself is not asked to carry infima. -/
def costUpperBounds (T : ClosedTheorySet Const) (φ : ClosedFormula Const) : Set Nat :=
  {n | ∃ w : TreeWitness (Const := Const) T φ, w.tree.evalNat ≤ n}

/-- Why-provenance ideal over all source ledgers for trees of a formula. -/
def sourceIdeal (T : ClosedTheorySet Const) (φ : ClosedFormula Const) :
    Set (Set (DerivationTree.SourceToken (Base := Base) Const)) :=
  {S | ∃ w : TreeWitness (Const := Const) T φ, w.tree.sourceSupport ⊆ S}

theorem sourceIdeal_upward
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    {S S' : Set (DerivationTree.SourceToken (Base := Base) Const)}
    (hS : S ∈ sourceIdeal (Const := Const) T φ) (hSS' : S ⊆ S') :
    S' ∈ sourceIdeal (Const := Const) T φ := by
  rcases hS with ⟨w, hwS⟩
  exact ⟨w, Set.Subset.trans hwS hSS'⟩

theorem costSpectrum_empty_of_not_provable
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (hNot : ¬ Provable (Const := Const) T φ) :
    costSpectrum (Const := Const) T φ = ∅ := by
  ext n
  constructor
  · rintro ⟨w, _⟩
    exact False.elim (hNot w.provable)
  · intro h
    cases h

theorem sourceIdeal_empty_of_not_provable
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (hNot : ¬ Provable (Const := Const) T φ) :
    sourceIdeal (Const := Const) T φ = ∅ := by
  ext S
  constructor
  · rintro ⟨w, _⟩
    exact False.elim (hNot w.provable)
  · intro h
    cases h

theorem costUpperBounds_upward
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    {n m : Nat} (hn : n ∈ costUpperBounds (Const := Const) T φ)
    (hnm : n ≤ m) :
    m ∈ costUpperBounds (Const := Const) T φ := by
  rcases hn with ⟨w, hw⟩
  exact ⟨w, Nat.le_trans hw hnm⟩

/-- Derivable implication transports exact-cost evidence with honest additive
slack from the implication-elimination machinery. -/
theorem costSpectrum_mono_derivability
    {T : ClosedTheorySet Const} {φ ψ : ClosedFormula Const}
    (hImp : Provable (Const := Const) T (.imp φ ψ)) :
    ∀ {n}, n ∈ costSpectrum (Const := Const) T φ →
      ∃ m, m ∈ costSpectrum (Const := Const) T ψ ∧ n ≤ m := by
  rcases treeProvable_iff_provable.mpr hImp with ⟨ΓImp, hΓImp, ⟨dImp⟩⟩
  intro n hn
  rcases hn with ⟨wφ, hwφ⟩
  let wψ : TreeWitness (Const := Const) T ψ :=
    { ctx := ΓImp ++ wφ.ctx
      ctx_mem := by
        intro ξ hξ
        rcases List.mem_append.mp hξ with hξ | hξ
        · exact hΓImp ξ hξ
        · exact wφ.ctx_mem ξ hξ
      tree := DerivationTree.composeImp (Const := Const) dImp wφ.tree }
  refine ⟨wψ.tree.evalNat, ⟨wψ, rfl⟩, ?_⟩
  rw [DerivationTree.evalNat_composeImp, hwφ]
  exact Nat.le_add_left n (1 + dImp.evalNat)

/-- If `n` bounds the cost of proving `φ`, then composing with a fixed proof of
`φ → ψ` gives an explicit upper bound for proving `ψ`. -/
theorem costUpperBounds_imp_slack
    {T : ClosedTheorySet Const} {φ ψ : ClosedFormula Const}
    (hImp : TreeWitness (Const := Const) T (.imp φ ψ))
    {n : Nat} (hn : n ∈ costUpperBounds (Const := Const) T φ) :
    (1 + hImp.tree.evalNat + n) ∈ costUpperBounds (Const := Const) T ψ := by
  rcases hn with ⟨wφ, hwφ⟩
  let wψ : TreeWitness (Const := Const) T ψ :=
    { ctx := hImp.ctx ++ wφ.ctx
      ctx_mem := by
        intro ξ hξ
        rcases List.mem_append.mp hξ with hξ | hξ
        · exact hImp.ctx_mem ξ hξ
        · exact wφ.ctx_mem ξ hξ
      tree := DerivationTree.composeImp (Const := Const) hImp.tree wφ.tree }
  refine ⟨wψ, ?_⟩
  rw [DerivationTree.evalNat_composeImp]
  exact Nat.add_le_add_left hwφ (1 + hImp.tree.evalNat)

/-- Hypothesis-free witness for the shorter `top ∧ top` tree. -/
def topAndTopWitness (T : ClosedTheorySet Const) :
    TreeWitness (Const := Const) T
      (.and (.top : ClosedFormula Const) (.top : ClosedFormula Const)) where
  ctx := []
  ctx_mem := by
    intro ξ hξ
    cases hξ
  tree := DerivationTree.topAndTopTree (Const := Const) []

/-- Hypothesis-free witness for the longer `top ∧ top` tree. -/
def topAndTopWitnessAlt (T : ClosedTheorySet Const) :
    TreeWitness (Const := Const) T
      (.and (.top : ClosedFormula Const) (.top : ClosedFormula Const)) where
  ctx := []
  ctx_mem := by
    intro ξ hξ
    cases hξ
  tree := DerivationTree.topAndTopTreeAlt (Const := Const) []

theorem costSpectrum_topAndTop_contains_three (T : ClosedTheorySet Const) :
    3 ∈ costSpectrum (Const := Const) T
      (.and (.top : ClosedFormula Const) (.top : ClosedFormula Const)) :=
  ⟨topAndTopWitness (Const := Const) T, by simp [topAndTopWitness]⟩

theorem costSpectrum_topAndTop_contains_six (T : ClosedTheorySet Const) :
    6 ∈ costSpectrum (Const := Const) T
      (.and (.top : ClosedFormula Const) (.top : ClosedFormula Const)) :=
  ⟨topAndTopWitnessAlt (Const := Const) T, by simp [topAndTopWitnessAlt]⟩

end ClosedTheorySet

end Mettapedia.Logic.HOL

namespace Mettapedia.PLN.Bridges.HOL.ProvenanceSemiringReadout

open Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Nat-valued theoremhood/tree-existence indicator over a closed theory set. -/
noncomputable def natTreeExistenceGrade
    (T : ClosedTheorySet Const) (φ : ClosedFormula Const) : Nat := by
  classical
  exact if ClosedTheorySet.TreeProvable (Const := Const) T φ then 1 else 0

theorem natTreeExistenceGrade_eq_one_iff
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const} :
    natTreeExistenceGrade (Const := Const) T φ = 1 ↔
      ClosedTheorySet.Provable (Const := Const) T φ := by
  classical
  unfold natTreeExistenceGrade
  by_cases hTree : ClosedTheorySet.TreeProvable (Const := Const) T φ
  · have hProv : ClosedTheorySet.Provable (Const := Const) T φ :=
      ClosedTheorySet.treeProvable_iff_provable.mp hTree
    simp [hTree, hProv]
  · have hNotProv : ¬ ClosedTheorySet.Provable (Const := Const) T φ := by
      intro hProv
      exact hTree (ClosedTheorySet.treeProvable_iff_provable.mpr hProv)
    simp [hTree, hNotProv]

theorem natTreeExistenceGrade_eq_zero_of_not_provable
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (hNot : ¬ ClosedTheorySet.Provable (Const := Const) T φ) :
    natTreeExistenceGrade (Const := Const) T φ = 0 := by
  classical
  unfold natTreeExistenceGrade
  have hNoTree : ¬ ClosedTheorySet.TreeProvable (Const := Const) T φ := by
    intro hTree
    exact hNot (ClosedTheorySet.treeProvable_iff_provable.mp hTree)
  simp [hNoTree]

/-- Degenerate WM-2 baseline: this readout only records theoremhood/tree
existence as `0` or `1`.  The cost-spectrum readout below is the genuinely
graded WM-2.5 successor. -/
noncomputable def natTreeExistenceWMReadout (T : ClosedTheorySet Const) :
    Mettapedia.PLN.WorldModel.WMReadout
      (ClosedFormula Const) Nat
      (fun φ ψ => ClosedTheorySet.Provable (Const := Const) T (.imp φ ψ))
      (· ≤ ·) where
  mu := natTreeExistenceGrade (Const := Const) T
  monotone := by
    classical
    intro φ ψ hImp
    unfold natTreeExistenceGrade
    by_cases hφ : ClosedTheorySet.TreeProvable (Const := Const) T φ
    · have hφProv : ClosedTheorySet.Provable (Const := Const) T φ :=
        ClosedTheorySet.treeProvable_iff_provable.mp hφ
      have hψProv : ClosedTheorySet.Provable (Const := Const) T ψ :=
        ClosedTheorySet.provable_mp (Const := Const) hImp hφProv
      have hψ : ClosedTheorySet.TreeProvable (Const := Const) T ψ :=
        ClosedTheorySet.treeProvable_iff_provable.mpr hψProv
      simp [hφ, hψ]
    · simp [hφ]

/-- Cost-spectrum evidence order: every exact cost in `A` is transported to
some exact cost in `B` that is at least as large.  This is monotone for
derivable implication because implication elimination adds honest rule cost. -/
def CostSpectrumLE (A B : Set Nat) : Prop :=
  ∀ {n}, n ∈ A → ∃ m, m ∈ B ∧ n ≤ m

/-- WM-2.5 genuinely graded readout: formulas map to the set of exact Nat costs
of all proof-relevant finite derivations from `T`. -/
def natCostSpectrumWMReadout (T : ClosedTheorySet Const) :
    Mettapedia.PLN.WorldModel.WMReadout
      (ClosedFormula Const) (Set Nat)
      (fun φ ψ => ClosedTheorySet.Provable (Const := Const) T (.imp φ ψ))
      CostSpectrumLE where
  mu := ClosedTheorySet.costSpectrum (Const := Const) T
  monotone := by
    intro φ ψ hImp
    exact ClosedTheorySet.costSpectrum_mono_derivability (Const := Const) hImp

end Mettapedia.PLN.Bridges.HOL.ProvenanceSemiringReadout
