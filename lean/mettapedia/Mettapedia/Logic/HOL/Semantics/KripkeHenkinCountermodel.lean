import Mettapedia.Logic.HOL.Semantics.KripkeHenkin
import Mettapedia.Logic.HOL.Semantics.KripkeHenkinGeneral

/-!
# Excluded-middle canary signature and countermodel surface

The concrete canary signature (one propositional atom over no base types, a
two-world frame) together with the generation-free canary surfaces: the
countermodel-conditional negative canary and the positive derivable/semantic
twins.  The concrete `KripkeHenkin` countermodel instance is the open
obligation recorded in the consolidation verdict.  Split out of
`Semantics/KripkeHenkin.lean`; namespaces are unchanged.
-/

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

open Mettapedia.Logic.HOL.WithParams

namespace KripkeHenkin

/-- The base-type signature for the concrete excluded-middle canary: no
individual base types are needed. -/
abbrev EMCanaryBase : Type := PEmpty

/-- The constant signature for the concrete excluded-middle canary: one
propositional atom and no other constants. -/
inductive EMCanaryConst : Ty EMCanaryBase → Type
  | p : EMCanaryConst propTy

/-- The distinguished proposition used by the excluded-middle canary. -/
def emCanaryAtom : ClosedFormula EMCanaryConst :=
  .const EMCanaryConst.p

/-- The concrete excluded-middle formula whose underivability is the negative
canary target. -/
def emCanaryExcludedMiddle : ClosedFormula EMCanaryConst :=
  excludedMiddleConst (Base := EMCanaryBase) (Const := EMCanaryConst) EMCanaryConst.p

/-- The two information states for the concrete excluded-middle canary. -/
inductive EMCanaryWorld where
  | root
  | leaf
deriving DecidableEq

namespace EMCanaryWorld

/-- The root sees itself and the leaf; the leaf sees only itself. -/
def le : EMCanaryWorld → EMCanaryWorld → Prop
  | root, _ => True
  | leaf, leaf => True
  | leaf, root => False

theorem le_refl : ∀ W : EMCanaryWorld, le W W
  | root => trivial
  | leaf => trivial

theorem le_trans {U V W : EMCanaryWorld} (hUV : le U V) (hVW : le V W) : le U W := by
  cases U <;> cases V <;> cases W <;> trivial

end EMCanaryWorld

/-- The intended monotone atom valuation for the canary frame: `p` is absent at
the root and present at the leaf. -/
def emCanaryAtomVal (W : EMCanaryWorld) (φ : ClosedFormula EMCanaryConst) : Prop :=
  φ = emCanaryAtom ∧ W = EMCanaryWorld.leaf

theorem emCanaryAtomVal_mono
    {U V : EMCanaryWorld} {φ : ClosedFormula EMCanaryConst}
    (hUV : EMCanaryWorld.le U V) (hφ : emCanaryAtomVal U φ) :
    emCanaryAtomVal V φ := by
  rcases hφ with ⟨hAtom, hU⟩
  refine ⟨hAtom, ?_⟩
  cases U with
  | root =>
      cases hU
  | leaf =>
      cases V with
      | root =>
          cases hUV
      | leaf =>
          rfl

theorem emCanaryAtomVal_not_root :
    ¬ emCanaryAtomVal EMCanaryWorld.root emCanaryAtom := by
  intro h
  exact EMCanaryWorld.noConfusion h.2

theorem emCanaryAtomVal_later :
    ∃ V : EMCanaryWorld,
      EMCanaryWorld.le EMCanaryWorld.root V ∧ emCanaryAtomVal V emCanaryAtom :=
  ⟨EMCanaryWorld.leaf, trivial, rfl, rfl⟩

/-- Once the concrete two-world countermodel is supplied, the EM-free calculus
does not derive the canary excluded-middle instance from the empty theory. -/
theorem emCanary_not_derivable_of_countermodel
    (C : ExcludedMiddleCountermodel (Base := EMCanaryBase) (Const := EMCanaryConst)
      emCanaryAtom) :
    ¬ ClosedTheorySet.Provable (Const := EMCanaryConst) (∅ : ClosedTheorySet EMCanaryConst)
        emCanaryExcludedMiddle := by
  simpa [emCanaryAtom, emCanaryExcludedMiddle] using
    (ExcludedMiddleCountermodel.not_provable_empty_const
      (Base := EMCanaryBase) (Const := EMCanaryConst) EMCanaryConst.p C)


/-- Positive canary target: `p → p` is derivable in the same canary language. -/
theorem emCanary_positive_derivable :
    ClosedTheorySet.Provable (Const := EMCanaryConst) (∅ : ClosedTheorySet EMCanaryConst)
      (.imp emCanaryAtom emCanaryAtom) :=
  provable_empty_imp_self (Base := EMCanaryBase) (Const := EMCanaryConst) emCanaryAtom

/-- Semantic positive twin: `p → p` is valid as an empty-theory consequence in
the canary language. -/
theorem emCanary_positive_consequence :
    Consequence.{0, 0, w} (Base := EMCanaryBase) (Const := EMCanaryConst)
      (∅ : ClosedTheorySet EMCanaryConst) (.imp emCanaryAtom emCanaryAtom) :=
  consequence_empty_imp_self (Base := EMCanaryBase) (Const := EMCanaryConst) emCanaryAtom

/-! ## The concrete two-world Kripke-Henkin general countermodel

Types are interpreted over full function spaces with upset-valued
propositions; admissibility is the hereditarily-extensional logical relation
`EMCanarySemAdm`, so admissible functions respect the observational equality
`EMCanarySemEq` by construction.  The fundamental lemma then closes
`term_closed` and `app_congr_arg`, and excluded middle for the canary atom is
refuted at the root world. -/

/-- Base-type carriers for the canary: there are no base types. -/
def EMCanaryCarrier : EMCanaryBase → Type := fun b => b.elim

/-- Ambient values of the canary model. -/
abbrev EMCanaryVal (τ : Ty EMCanaryBase) : Type :=
  Ty.denoteK EMCanaryCarrier EMCanaryWorld τ

mutual

/-- Hereditarily-extensional admissibility: upsets at propositions, and at
function types closure under admissible application together with respect for
the observational equality. -/
def EMCanarySemAdm : (τ : Ty EMCanaryBase) → EMCanaryVal τ → Prop
  | .prop, S => ∀ {U V : EMCanaryWorld}, EMCanaryWorld.le U V → S U → S V
  | .base _, _ => True
  | .arr σ τ, f =>
      (∀ d, EMCanarySemAdm σ d → EMCanarySemAdm τ (f d)) ∧
      (∀ (W : EMCanaryWorld) (d e : EMCanaryVal σ),
        EMCanarySemAdm σ d → EMCanarySemAdm σ e →
          EMCanarySemEq W σ d e → EMCanarySemEq W τ (f d) (f e))

/-- World-indexed observational equality on canary values. -/
def EMCanarySemEq : EMCanaryWorld → (τ : Ty EMCanaryBase) →
    EMCanaryVal τ → EMCanaryVal τ → Prop
  | W, .prop, S, T => ∀ V, EMCanaryWorld.le W V → (S V ↔ T V)
  | _, .base _, d, e => d = e
  | W, .arr σ τ, f, g =>
      ∀ V, EMCanaryWorld.le W V → ∀ d, EMCanarySemAdm σ d →
        EMCanarySemEq V τ (f d) (g d)

end

theorem emCanarySemEq_mono {τ : Ty EMCanaryBase} {U V : EMCanaryWorld}
    {d e : EMCanaryVal τ} (hUV : EMCanaryWorld.le U V)
    (h : EMCanarySemEq U τ d e) : EMCanarySemEq V τ d e := by
  cases τ with
  | prop => exact fun V' hV' => h V' (EMCanaryWorld.le_trans hUV hV')
  | base b => exact h
  | arr σ τ => exact fun V' hV' => h V' (EMCanaryWorld.le_trans hUV hV')

theorem emCanarySemEq_refl : ∀ {τ : Ty EMCanaryBase} {W : EMCanaryWorld}
    {d : EMCanaryVal τ}, EMCanarySemAdm τ d → EMCanarySemEq W τ d d
  | .prop, _, _, _ => fun _ _ => Iff.rfl
  | .base _, _, _, _ => rfl
  | .arr _ _, _, _, hf => fun _V _hV d hd => emCanarySemEq_refl (hf.1 d hd)

theorem emCanarySemEq_symm : ∀ {τ : Ty EMCanaryBase} {W : EMCanaryWorld}
    {d e : EMCanaryVal τ},
    EMCanarySemEq W τ d e → EMCanarySemEq W τ e d
  | .prop, _, _, _, h => fun V hV => (h V hV).symm
  | .base _, _, _, _, h => h.symm
  | .arr _ _, _, _, _, h => fun V hV d hd => emCanarySemEq_symm (h V hV d hd)

theorem emCanarySemEq_trans : ∀ {τ : Ty EMCanaryBase} {W : EMCanaryWorld}
    {d e k : EMCanaryVal τ},
    EMCanarySemEq W τ d e → EMCanarySemEq W τ e k → EMCanarySemEq W τ d k
  | .prop, _, _, _, _, h₁, h₂ => fun V hV => (h₁ V hV).trans (h₂ V hV)
  | .base _, _, _, _, _, h₁, h₂ => h₁.trans h₂
  | .arr _ _, _, _, _, _, h₁, h₂ => fun V hV d hd =>
      emCanarySemEq_trans (h₁ V hV d hd) (h₂ V hV d hd)

/-- The canary premodel: two worlds, no base types, one propositional atom
true exactly at the leaf. -/
def emCanaryPreModel : KripkePreModel EMCanaryBase EMCanaryConst where
  World := EMCanaryWorld
  le := EMCanaryWorld.le
  le_refl := EMCanaryWorld.le_refl
  le_trans := EMCanaryWorld.le_trans
  Carrier := EMCanaryCarrier
  baseEq := fun _ b => b.elim
  baseEq_mono := fun {_ _ b} => b.elim
  baseEq_refl := fun _ b => b.elim
  baseEq_symm := fun {_ b} => b.elim
  baseEq_trans := fun {_ b} => b.elim
  adm := fun _ τ d => EMCanarySemAdm τ d
  adm_mono := fun _ h => h
  prop_adm_upset := fun h => h
  base_mem := fun _ _ _ => trivial
  app_mem := fun hf hd => hf.1 _ hd
  constDen := fun c =>
    match c with
    | .p => fun W => W = EMCanaryWorld.leaf
  const_mem := by
    rintro W τ ⟨⟩
    intro U V hUV hU
    cases U with
    | root => exact absurd hU (by intro h; cases h)
    | leaf =>
        cases V with
        | root => cases hUV
        | leaf => rfl

/-- The model's typed equality agrees with the observational equality. -/
theorem emCanary_eqvK_iff_semEq :
    ∀ (τ : Ty EMCanaryBase) (W : EMCanaryWorld)
      (d e : EMCanaryVal τ),
      emCanaryPreModel.EqvK W τ d e ↔ EMCanarySemEq W τ d e
  | .prop, W, S, T => Iff.rfl
  | .base b, _, d, e => b.elim
  | .arr σ τ, W, f, g => by
      constructor
      · intro h V hV d hd
        exact (emCanary_eqvK_iff_semEq τ V (f d) (g d)).mp (h V hV d hd)
      · intro h V hV d hd
        exact (emCanary_eqvK_iff_semEq τ V (f d) (g d)).mpr (h V hV d hd)

/-- Admissible environments for the canary premodel. -/
abbrev EMCanaryEnvAdm {Γ : Ctx EMCanaryBase}
    (ρ : emCanaryPreModel.Valuation Γ) : Prop :=
  ∀ {σ : Ty EMCanaryBase} (v : Var Γ σ), EMCanarySemAdm σ (ρ v)

/-- Pointwise observational equality of environments. -/
abbrev EMCanaryEnvEq {Γ : Ctx EMCanaryBase} (W : EMCanaryWorld)
    (ρ₁ ρ₂ : emCanaryPreModel.Valuation Γ) : Prop :=
  ∀ {σ : Ty EMCanaryBase} (v : Var Γ σ), EMCanarySemEq W σ (ρ₁ v) (ρ₂ v)

/-- **Fundamental lemma** for the canary premodel: denotation at admissible
environments is admissible, and observationally-equal admissible environments
give observationally-equal denotations. -/
theorem emCanary_fundamental {Γ : Ctx EMCanaryBase} {τ : Ty EMCanaryBase}
    (t : Term EMCanaryConst Γ τ) :
    (∀ (ρ : emCanaryPreModel.Valuation Γ), EMCanaryEnvAdm ρ →
      EMCanarySemAdm τ (emCanaryPreModel.denote t ρ)) ∧
    (∀ (W : EMCanaryWorld) (ρ₁ ρ₂ : emCanaryPreModel.Valuation Γ),
      EMCanaryEnvAdm ρ₁ → EMCanaryEnvAdm ρ₂ → EMCanaryEnvEq W ρ₁ ρ₂ →
        EMCanarySemEq W τ (emCanaryPreModel.denote t ρ₁)
          (emCanaryPreModel.denote t ρ₂)) := by
  induction t with
  | var v =>
      exact ⟨fun ρ hρ => hρ v, fun W ρ₁ ρ₂ _ _ hEq => hEq v⟩
  | const c =>
      cases c with
      | p =>
          refine ⟨fun ρ hρ => ?_, fun W ρ₁ ρ₂ _ _ _ => fun V hV => Iff.rfl⟩
          intro U V hUV hU
          cases U with
          | root => exact absurd hU (by intro h; cases h)
          | leaf =>
              cases V with
              | root => cases hUV
              | leaf => rfl
  | app f t ihf iht =>
      constructor
      · intro ρ hρ
        exact (ihf.1 ρ hρ).1 _ (iht.1 ρ hρ)
      · intro W ρ₁ ρ₂ h₁ h₂ hEq
        have hff := ihf.2 W ρ₁ ρ₂ h₁ h₂ hEq W (EMCanaryWorld.le_refl W)
          (emCanaryPreModel.denote t ρ₁) (iht.1 ρ₁ h₁)
        have hresp := (ihf.1 ρ₂ h₂).2 W
          (emCanaryPreModel.denote t ρ₁) (emCanaryPreModel.denote t ρ₂)
          (iht.1 ρ₁ h₁) (iht.1 ρ₂ h₂) (iht.2 W ρ₁ ρ₂ h₁ h₂ hEq)
        exact emCanarySemEq_trans hff hresp
  | lam t iht =>
      constructor
      · intro ρ hρ
        constructor
        · intro d hd
          refine iht.1 (emCanaryPreModel.extend ρ d) ?_
          intro σ' v
          cases v with
          | vz => exact hd
          | vs v => exact hρ v
        · intro W d e hd he hde
          refine iht.2 W (emCanaryPreModel.extend ρ d)
            (emCanaryPreModel.extend ρ e) ?_ ?_ ?_
          · intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact hρ v
          · intro σ' v; cases v with
            | vz => exact he
            | vs v => exact hρ v
          · intro σ' v; cases v with
            | vz => exact hde
            | vs v => exact emCanarySemEq_refl (hρ v)
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV d hd
        refine iht.2 V (emCanaryPreModel.extend ρ₁ d)
          (emCanaryPreModel.extend ρ₂ d) ?_ ?_ ?_
        · intro σ' v; cases v with
          | vz => exact hd
          | vs v => exact h₁ v
        · intro σ' v; cases v with
          | vz => exact hd
          | vs v => exact h₂ v
        · intro σ' v; cases v with
          | vz => exact emCanarySemEq_refl hd
          | vs v => exact emCanarySemEq_mono hV (hEq v)
  | top =>
      exact ⟨fun ρ hρ _ _ _ h => h, fun W ρ₁ ρ₂ _ _ _ _ _ => Iff.rfl⟩
  | bot =>
      exact ⟨fun ρ hρ _ _ _ h => h, fun W ρ₁ ρ₂ _ _ _ _ _ => Iff.rfl⟩
  | and φ ψ ihφ ihψ =>
      constructor
      · intro ρ hρ U V hUV h
        exact ⟨ihφ.1 ρ hρ hUV h.1, ihψ.1 ρ hρ hUV h.2⟩
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV
        exact and_congr (ihφ.2 W ρ₁ ρ₂ h₁ h₂ hEq V hV)
          (ihψ.2 W ρ₁ ρ₂ h₁ h₂ hEq V hV)
  | or φ ψ ihφ ihψ =>
      constructor
      · intro ρ hρ U V hUV h
        rcases h with h | h
        · exact Or.inl (ihφ.1 ρ hρ hUV h)
        · exact Or.inr (ihψ.1 ρ hρ hUV h)
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV
        exact or_congr (ihφ.2 W ρ₁ ρ₂ h₁ h₂ hEq V hV)
          (ihψ.2 W ρ₁ ρ₂ h₁ h₂ hEq V hV)
  | imp φ ψ ihφ ihψ =>
      constructor
      · intro ρ hρ U V hUV h V' hV' hφ
        exact h V' (EMCanaryWorld.le_trans hUV hV') hφ
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV
        constructor
        · intro h V' hV' hφ
          exact (ihψ.2 W ρ₁ ρ₂ h₁ h₂ hEq V'
              (EMCanaryWorld.le_trans hV hV')).mp
            (h V' hV' ((ihφ.2 W ρ₁ ρ₂ h₁ h₂ hEq V'
              (EMCanaryWorld.le_trans hV hV')).mpr hφ))
        · intro h V' hV' hφ
          exact (ihψ.2 W ρ₁ ρ₂ h₁ h₂ hEq V'
              (EMCanaryWorld.le_trans hV hV')).mpr
            (h V' hV' ((ihφ.2 W ρ₁ ρ₂ h₁ h₂ hEq V'
              (EMCanaryWorld.le_trans hV hV')).mp hφ))
  | not φ ihφ =>
      constructor
      · intro ρ hρ U V hUV h V' hV' hφ
        exact h V' (EMCanaryWorld.le_trans hUV hV') hφ
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV
        constructor
        · intro h V' hV' hφ
          exact h V' hV' ((ihφ.2 W ρ₁ ρ₂ h₁ h₂ hEq V'
            (EMCanaryWorld.le_trans hV hV')).mpr hφ)
        · intro h V' hV' hφ
          exact h V' hV' ((ihφ.2 W ρ₁ ρ₂ h₁ h₂ hEq V'
            (EMCanaryWorld.le_trans hV hV')).mp hφ)
  | eq t u iht ihu =>
      constructor
      · intro ρ hρ U V hUV h
        exact emCanaryPreModel.eqvK_mono hUV h
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV
        have ht := emCanarySemEq_mono hV (iht.2 W ρ₁ ρ₂ h₁ h₂ hEq)
        have hu := emCanarySemEq_mono hV (ihu.2 W ρ₁ ρ₂ h₁ h₂ hEq)
        constructor
        · intro h
          refine (emCanary_eqvK_iff_semEq _ _ _ _).mpr ?_
          exact emCanarySemEq_trans (emCanarySemEq_symm ht)
            (emCanarySemEq_trans ((emCanary_eqvK_iff_semEq _ _ _ _).mp h) hu)
        · intro h
          refine (emCanary_eqvK_iff_semEq _ _ _ _).mpr ?_
          exact emCanarySemEq_trans ht
            (emCanarySemEq_trans ((emCanary_eqvK_iff_semEq _ _ _ _).mp h)
              (emCanarySemEq_symm hu))
  | all φ ihφ =>
      constructor
      · intro ρ hρ U V hUV h V' hV' d hd
        exact h V' (EMCanaryWorld.le_trans hUV hV') d hd
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV
        constructor
        · intro h V' hV' d hd
          refine (ihφ.2 V' (emCanaryPreModel.extend ρ₁ d)
              (emCanaryPreModel.extend ρ₂ d) ?_ ?_ ?_ V'
              (EMCanaryWorld.le_refl V')).mp (h V' hV' d hd)
          · intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact h₁ v
          · intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact h₂ v
          · intro σ' v; cases v with
            | vz => exact emCanarySemEq_refl hd
            | vs v =>
                exact emCanarySemEq_mono (EMCanaryWorld.le_trans hV hV') (hEq v)
        · intro h V' hV' d hd
          refine (ihφ.2 V' (emCanaryPreModel.extend ρ₁ d)
              (emCanaryPreModel.extend ρ₂ d) ?_ ?_ ?_ V'
              (EMCanaryWorld.le_refl V')).mpr (h V' hV' d hd)
          · intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact h₁ v
          · intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact h₂ v
          · intro σ' v; cases v with
            | vz => exact emCanarySemEq_refl hd
            | vs v =>
                exact emCanarySemEq_mono (EMCanaryWorld.le_trans hV hV') (hEq v)
  | ex φ ihφ =>
      constructor
      · intro ρ hρ U V hUV h
        obtain ⟨d, hd, hbody⟩ := h
        exact ⟨d, hd, ihφ.1 (emCanaryPreModel.extend ρ d)
          (by intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact hρ v) hUV hbody⟩
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV
        constructor
        · rintro ⟨d, hd, hbody⟩
          refine ⟨d, hd, ?_⟩
          refine (ihφ.2 V (emCanaryPreModel.extend ρ₁ d)
              (emCanaryPreModel.extend ρ₂ d) ?_ ?_ ?_ V
              (EMCanaryWorld.le_refl V)).mp hbody
          · intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact h₁ v
          · intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact h₂ v
          · intro σ' v; cases v with
            | vz => exact emCanarySemEq_refl hd
            | vs v => exact emCanarySemEq_mono hV (hEq v)
        · rintro ⟨d, hd, hbody⟩
          refine ⟨d, hd, ?_⟩
          refine (ihφ.2 V (emCanaryPreModel.extend ρ₁ d)
              (emCanaryPreModel.extend ρ₂ d) ?_ ?_ ?_ V
              (EMCanaryWorld.le_refl V)).mpr hbody
          · intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact h₁ v
          · intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact h₂ v
          · intro σ' v; cases v with
            | vz => exact emCanarySemEq_refl hd
            | vs v => exact emCanarySemEq_mono hV (hEq v)

/-- The concrete two-world Kripke-Henkin general model for the canary. -/
def emCanaryModel : KripkeHenkinGeneral EMCanaryBase EMCanaryConst where
  toKripkePreModel := emCanaryPreModel
  term_closed := fun t _W ρ hρ => (emCanary_fundamental t).1 ρ (fun v => hρ v)
  app_congr_arg := fun hf hd he hde =>
    (emCanary_eqvK_iff_semEq _ _ _ _).mpr
      (hf.2 _ _ _ hd he ((emCanary_eqvK_iff_semEq _ _ _ _).mp hde))

/-- The canary atom is not denoted at the root world. -/
theorem emCanaryModel_root_not_atom :
    ¬ emCanaryModel.denote emCanaryAtom emCanaryModel.emptyVal
        EMCanaryWorld.root := by
  intro h
  cases h

/-- The canary atom is denoted at the leaf world. -/
theorem emCanaryModel_leaf_atom :
    emCanaryModel.denote emCanaryAtom emCanaryModel.emptyVal
      EMCanaryWorld.leaf := rfl

/-- **The negative canary, closed end-to-end**: the EM-free calculus does not
derive the canary excluded-middle instance from the empty theory. -/
theorem em_not_derivable :
    ¬ ClosedTheorySet.Provable (Const := EMCanaryConst)
        (∅ : ClosedTheorySet EMCanaryConst) emCanaryExcludedMiddle := by
  have h := emCanaryModel.not_provable_empty_excludedMiddle_of_eventual_counterexample
    (φ := emCanaryAtom) (W := EMCanaryWorld.root)
    emCanaryModel_root_not_atom
    ⟨EMCanaryWorld.leaf, trivial, emCanaryModel_leaf_atom⟩
  simpa [emCanaryExcludedMiddle, excludedMiddleConst, excludedMiddle,
    emCanaryAtom] using h

end KripkeHenkin

end Mettapedia.Logic.HOL
