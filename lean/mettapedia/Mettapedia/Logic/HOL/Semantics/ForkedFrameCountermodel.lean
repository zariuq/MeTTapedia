import Mettapedia.Logic.HOL.Semantics.KripkeHenkinGeneral

/-!
# Forked-frame countermodel for prelinearity

A concrete three-world V-frame for the EM-free calculus: the root sees two
incomparable leaves.  The propositional atom `p` is true only at the left leaf,
and `q` is true only at the right leaf.  The root therefore forces neither
`p → q` nor `q → p`, so prelinearity is not derivable from the empty theory.
-/

namespace Mettapedia.Logic.HOL

namespace KripkeHenkin

/-- No base types are needed for the forked-frame prelinearity canary. -/
abbrev ForkedFrameBase : Type := PEmpty

/-- Two propositional atoms and no other constants. -/
inductive ForkedFrameConst : Ty ForkedFrameBase → Type
  | p : ForkedFrameConst propTy
  | q : ForkedFrameConst propTy

/-- The left-only atom. -/
def forkedP : ClosedFormula ForkedFrameConst :=
  .const ForkedFrameConst.p

/-- The right-only atom. -/
def forkedQ : ClosedFormula ForkedFrameConst :=
  .const ForkedFrameConst.q

/-- The prelinearity instance refuted by the V-frame root. -/
def forkedPrelinearity : ClosedFormula ForkedFrameConst :=
  .or (.imp forkedP forkedQ) (.imp forkedQ forkedP)

/-- The excluded-middle instance for `p`, also refuted at the V-frame root. -/
def forkedExcludedMiddleP : ClosedFormula ForkedFrameConst :=
  .or forkedP (.not forkedP)

/-- The three worlds of the V-frame. -/
inductive ForkedFrameWorld where
  | root
  | left
  | right
deriving DecidableEq

namespace ForkedFrameWorld

/-- The root sees both leaves; the leaves see only themselves. -/
def le : ForkedFrameWorld → ForkedFrameWorld → Prop
  | root, _ => True
  | left, left => True
  | right, right => True
  | _, _ => False

theorem le_refl : ∀ W : ForkedFrameWorld, le W W
  | root => trivial
  | left => trivial
  | right => trivial

theorem le_trans {U V W : ForkedFrameWorld} (hUV : le U V) (hVW : le V W) :
    le U W := by
  cases U <;> cases V <;> cases W <;> trivial

end ForkedFrameWorld

/-- Base-type carriers for the forked-frame model: there are no base types. -/
def ForkedFrameCarrier : ForkedFrameBase → Type := fun b => b.elim

/-- Ambient values of the forked-frame model. -/
abbrev ForkedFrameVal (τ : Ty ForkedFrameBase) : Type :=
  Ty.denoteK ForkedFrameCarrier ForkedFrameWorld τ

mutual

/-- Hereditarily-extensional admissibility over the V-frame. -/
def ForkedFrameSemAdm : (τ : Ty ForkedFrameBase) → ForkedFrameVal τ → Prop
  | .prop, S => ∀ {U V : ForkedFrameWorld}, ForkedFrameWorld.le U V → S U → S V
  | .base _, _ => True
  | .arr σ τ, f =>
      (∀ d, ForkedFrameSemAdm σ d → ForkedFrameSemAdm τ (f d)) ∧
      (∀ (W : ForkedFrameWorld) (d e : ForkedFrameVal σ),
        ForkedFrameSemAdm σ d → ForkedFrameSemAdm σ e →
          ForkedFrameSemEq W σ d e → ForkedFrameSemEq W τ (f d) (f e))

/-- World-indexed observational equality on forked-frame values. -/
def ForkedFrameSemEq : ForkedFrameWorld → (τ : Ty ForkedFrameBase) →
    ForkedFrameVal τ → ForkedFrameVal τ → Prop
  | W, .prop, S, T => ∀ V, ForkedFrameWorld.le W V → (S V ↔ T V)
  | _, .base _, d, e => d = e
  | W, .arr σ τ, f, g =>
      ∀ V, ForkedFrameWorld.le W V → ∀ d, ForkedFrameSemAdm σ d →
        ForkedFrameSemEq V τ (f d) (g d)

end

theorem forkedFrameSemEq_mono {τ : Ty ForkedFrameBase} {U V : ForkedFrameWorld}
    {d e : ForkedFrameVal τ} (hUV : ForkedFrameWorld.le U V)
    (h : ForkedFrameSemEq U τ d e) : ForkedFrameSemEq V τ d e := by
  cases τ with
  | prop => exact fun V' hV' => h V' (ForkedFrameWorld.le_trans hUV hV')
  | base b => exact h
  | arr σ τ => exact fun V' hV' => h V' (ForkedFrameWorld.le_trans hUV hV')

theorem forkedFrameSemEq_refl : ∀ {τ : Ty ForkedFrameBase} {W : ForkedFrameWorld}
    {d : ForkedFrameVal τ}, ForkedFrameSemAdm τ d → ForkedFrameSemEq W τ d d
  | .prop, _, _, _ => fun _ _ => Iff.rfl
  | .base _, _, _, _ => rfl
  | .arr _ _, _, _, hf => fun _V _hV d hd => forkedFrameSemEq_refl (hf.1 d hd)

theorem forkedFrameSemEq_symm : ∀ {τ : Ty ForkedFrameBase} {W : ForkedFrameWorld}
    {d e : ForkedFrameVal τ},
    ForkedFrameSemEq W τ d e → ForkedFrameSemEq W τ e d
  | .prop, _, _, _, h => fun V hV => (h V hV).symm
  | .base _, _, _, _, h => h.symm
  | .arr _ _, _, _, _, h => fun V hV d hd => forkedFrameSemEq_symm (h V hV d hd)

theorem forkedFrameSemEq_trans : ∀ {τ : Ty ForkedFrameBase} {W : ForkedFrameWorld}
    {d e k : ForkedFrameVal τ},
    ForkedFrameSemEq W τ d e → ForkedFrameSemEq W τ e k →
      ForkedFrameSemEq W τ d k
  | .prop, _, _, _, _, h₁, h₂ => fun V hV => (h₁ V hV).trans (h₂ V hV)
  | .base _, _, _, _, _, h₁, h₂ => h₁.trans h₂
  | .arr _ _, _, _, _, _, h₁, h₂ => fun V hV d hd =>
      forkedFrameSemEq_trans (h₁ V hV d hd) (h₂ V hV d hd)

/-- The forked-frame premodel: `p` holds only at `left`, and `q` only at
`right`. -/
def forkedFramePreModel : KripkePreModel ForkedFrameBase ForkedFrameConst where
  World := ForkedFrameWorld
  le := ForkedFrameWorld.le
  le_refl := ForkedFrameWorld.le_refl
  le_trans := ForkedFrameWorld.le_trans
  Carrier := ForkedFrameCarrier
  baseEq := fun _ b => b.elim
  baseEq_mono := fun {_ _ b} => b.elim
  baseEq_refl := fun _ b => b.elim
  baseEq_symm := fun {_ b} => b.elim
  baseEq_trans := fun {_ b} => b.elim
  adm := fun _ τ d => ForkedFrameSemAdm τ d
  adm_mono := fun _ h => h
  prop_adm_upset := fun h => h
  base_mem := fun _ _ _ => trivial
  app_mem := fun hf hd => hf.1 _ hd
  constDen := fun c =>
    match c with
    | .p => fun W => W = ForkedFrameWorld.left
    | .q => fun W => W = ForkedFrameWorld.right
  const_mem := by
    rintro W τ (⟨⟩ | ⟨⟩)
    · intro U V hUV hU
      cases U <;> cases V <;> simp_all [ForkedFrameWorld.le]
    · intro U V hUV hU
      cases U <;> cases V <;> simp_all [ForkedFrameWorld.le]

/-- The model's typed equality agrees with the observational equality. -/
theorem forkedFrame_eqvK_iff_semEq :
    ∀ (τ : Ty ForkedFrameBase) (W : ForkedFrameWorld)
      (d e : ForkedFrameVal τ),
      forkedFramePreModel.EqvK W τ d e ↔ ForkedFrameSemEq W τ d e
  | .prop, W, S, T => Iff.rfl
  | .base b, _, d, e => b.elim
  | .arr σ τ, W, f, g => by
      constructor
      · intro h V hV d hd
        exact (forkedFrame_eqvK_iff_semEq τ V (f d) (g d)).mp (h V hV d hd)
      · intro h V hV d hd
        exact (forkedFrame_eqvK_iff_semEq τ V (f d) (g d)).mpr (h V hV d hd)

/-- Admissible environments for the forked-frame premodel. -/
abbrev ForkedFrameEnvAdm {Γ : Ctx ForkedFrameBase}
    (ρ : forkedFramePreModel.Valuation Γ) : Prop :=
  ∀ {σ : Ty ForkedFrameBase} (v : Var Γ σ), ForkedFrameSemAdm σ (ρ v)

/-- Pointwise observational equality of environments. -/
abbrev ForkedFrameEnvEq {Γ : Ctx ForkedFrameBase} (W : ForkedFrameWorld)
    (ρ₁ ρ₂ : forkedFramePreModel.Valuation Γ) : Prop :=
  ∀ {σ : Ty ForkedFrameBase} (v : Var Γ σ), ForkedFrameSemEq W σ (ρ₁ v) (ρ₂ v)

/-- Fundamental lemma for the forked-frame premodel. -/
theorem forkedFrame_fundamental {Γ : Ctx ForkedFrameBase} {τ : Ty ForkedFrameBase}
    (t : Term ForkedFrameConst Γ τ) :
    (∀ (ρ : forkedFramePreModel.Valuation Γ), ForkedFrameEnvAdm ρ →
      ForkedFrameSemAdm τ (forkedFramePreModel.denote t ρ)) ∧
    (∀ (W : ForkedFrameWorld) (ρ₁ ρ₂ : forkedFramePreModel.Valuation Γ),
      ForkedFrameEnvAdm ρ₁ → ForkedFrameEnvAdm ρ₂ → ForkedFrameEnvEq W ρ₁ ρ₂ →
        ForkedFrameSemEq W τ (forkedFramePreModel.denote t ρ₁)
          (forkedFramePreModel.denote t ρ₂)) := by
  induction t with
  | var v =>
      exact ⟨fun ρ hρ => hρ v, fun W ρ₁ ρ₂ _ _ hEq => hEq v⟩
  | const c =>
      cases c with
      | p =>
          refine ⟨fun ρ hρ => ?_, fun W ρ₁ ρ₂ _ _ _ => fun V hV => Iff.rfl⟩
          intro U V hUV hU
          cases U with
          | root => cases hU
          | left =>
              cases V with
              | root => cases hUV
              | left => rfl
              | right => cases hUV
          | right => cases hU
      | q =>
          refine ⟨fun ρ hρ => ?_, fun W ρ₁ ρ₂ _ _ _ => fun V hV => Iff.rfl⟩
          intro U V hUV hU
          cases U with
          | root => cases hU
          | left => cases hU
          | right =>
              cases V with
              | root => cases hUV
              | left => cases hUV
              | right => rfl
  | app f t ihf iht =>
      constructor
      · intro ρ hρ
        exact (ihf.1 ρ hρ).1 _ (iht.1 ρ hρ)
      · intro W ρ₁ ρ₂ h₁ h₂ hEq
        have hff := ihf.2 W ρ₁ ρ₂ h₁ h₂ hEq W (ForkedFrameWorld.le_refl W)
          (forkedFramePreModel.denote t ρ₁) (iht.1 ρ₁ h₁)
        have hresp := (ihf.1 ρ₂ h₂).2 W
          (forkedFramePreModel.denote t ρ₁) (forkedFramePreModel.denote t ρ₂)
          (iht.1 ρ₁ h₁) (iht.1 ρ₂ h₂) (iht.2 W ρ₁ ρ₂ h₁ h₂ hEq)
        exact forkedFrameSemEq_trans hff hresp
  | lam t iht =>
      constructor
      · intro ρ hρ
        constructor
        · intro d hd
          refine iht.1 (forkedFramePreModel.extend ρ d) ?_
          intro σ' v
          cases v with
          | vz => exact hd
          | vs v => exact hρ v
        · intro W d e hd he hde
          refine iht.2 W (forkedFramePreModel.extend ρ d)
            (forkedFramePreModel.extend ρ e) ?_ ?_ ?_
          · intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact hρ v
          · intro σ' v; cases v with
            | vz => exact he
            | vs v => exact hρ v
          · intro σ' v; cases v with
            | vz => exact hde
            | vs v => exact forkedFrameSemEq_refl (hρ v)
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV d hd
        refine iht.2 V (forkedFramePreModel.extend ρ₁ d)
          (forkedFramePreModel.extend ρ₂ d) ?_ ?_ ?_
        · intro σ' v; cases v with
          | vz => exact hd
          | vs v => exact h₁ v
        · intro σ' v; cases v with
          | vz => exact hd
          | vs v => exact h₂ v
        · intro σ' v; cases v with
          | vz => exact forkedFrameSemEq_refl hd
          | vs v => exact forkedFrameSemEq_mono hV (hEq v)
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
        exact h V' (ForkedFrameWorld.le_trans hUV hV') hφ
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV
        constructor
        · intro h V' hV' hφ
          exact (ihψ.2 W ρ₁ ρ₂ h₁ h₂ hEq V'
              (ForkedFrameWorld.le_trans hV hV')).mp
            (h V' hV' ((ihφ.2 W ρ₁ ρ₂ h₁ h₂ hEq V'
              (ForkedFrameWorld.le_trans hV hV')).mpr hφ))
        · intro h V' hV' hφ
          exact (ihψ.2 W ρ₁ ρ₂ h₁ h₂ hEq V'
              (ForkedFrameWorld.le_trans hV hV')).mpr
            (h V' hV' ((ihφ.2 W ρ₁ ρ₂ h₁ h₂ hEq V'
              (ForkedFrameWorld.le_trans hV hV')).mp hφ))
  | not φ ihφ =>
      constructor
      · intro ρ hρ U V hUV h V' hV' hφ
        exact h V' (ForkedFrameWorld.le_trans hUV hV') hφ
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV
        constructor
        · intro h V' hV' hφ
          exact h V' hV' ((ihφ.2 W ρ₁ ρ₂ h₁ h₂ hEq V'
            (ForkedFrameWorld.le_trans hV hV')).mpr hφ)
        · intro h V' hV' hφ
          exact h V' hV' ((ihφ.2 W ρ₁ ρ₂ h₁ h₂ hEq V'
            (ForkedFrameWorld.le_trans hV hV')).mp hφ)
  | eq t u iht ihu =>
      constructor
      · intro ρ hρ U V hUV h
        exact forkedFramePreModel.eqvK_mono hUV h
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV
        have ht := forkedFrameSemEq_mono hV (iht.2 W ρ₁ ρ₂ h₁ h₂ hEq)
        have hu := forkedFrameSemEq_mono hV (ihu.2 W ρ₁ ρ₂ h₁ h₂ hEq)
        constructor
        · intro h
          refine (forkedFrame_eqvK_iff_semEq _ _ _ _).mpr ?_
          exact forkedFrameSemEq_trans (forkedFrameSemEq_symm ht)
            (forkedFrameSemEq_trans ((forkedFrame_eqvK_iff_semEq _ _ _ _).mp h) hu)
        · intro h
          refine (forkedFrame_eqvK_iff_semEq _ _ _ _).mpr ?_
          exact forkedFrameSemEq_trans ht
            (forkedFrameSemEq_trans ((forkedFrame_eqvK_iff_semEq _ _ _ _).mp h)
              (forkedFrameSemEq_symm hu))
  | all φ ihφ =>
      constructor
      · intro ρ hρ U V hUV h V' hV' d hd
        exact h V' (ForkedFrameWorld.le_trans hUV hV') d hd
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV
        constructor
        · intro h V' hV' d hd
          refine (ihφ.2 V' (forkedFramePreModel.extend ρ₁ d)
              (forkedFramePreModel.extend ρ₂ d) ?_ ?_ ?_ V'
              (ForkedFrameWorld.le_refl V')).mp (h V' hV' d hd)
          · intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact h₁ v
          · intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact h₂ v
          · intro σ' v; cases v with
            | vz => exact forkedFrameSemEq_refl hd
            | vs v =>
                exact forkedFrameSemEq_mono (ForkedFrameWorld.le_trans hV hV') (hEq v)
        · intro h V' hV' d hd
          refine (ihφ.2 V' (forkedFramePreModel.extend ρ₁ d)
              (forkedFramePreModel.extend ρ₂ d) ?_ ?_ ?_ V'
              (ForkedFrameWorld.le_refl V')).mpr (h V' hV' d hd)
          · intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact h₁ v
          · intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact h₂ v
          · intro σ' v; cases v with
            | vz => exact forkedFrameSemEq_refl hd
            | vs v =>
                exact forkedFrameSemEq_mono (ForkedFrameWorld.le_trans hV hV') (hEq v)
  | ex φ ihφ =>
      constructor
      · intro ρ hρ U V hUV h
        obtain ⟨d, hd, hbody⟩ := h
        exact ⟨d, hd, ihφ.1 (forkedFramePreModel.extend ρ d)
          (by intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact hρ v) hUV hbody⟩
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV
        constructor
        · rintro ⟨d, hd, hbody⟩
          refine ⟨d, hd, ?_⟩
          refine (ihφ.2 V (forkedFramePreModel.extend ρ₁ d)
              (forkedFramePreModel.extend ρ₂ d) ?_ ?_ ?_ V
              (ForkedFrameWorld.le_refl V)).mp hbody
          · intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact h₁ v
          · intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact h₂ v
          · intro σ' v; cases v with
            | vz => exact forkedFrameSemEq_refl hd
            | vs v => exact forkedFrameSemEq_mono hV (hEq v)
        · rintro ⟨d, hd, hbody⟩
          refine ⟨d, hd, ?_⟩
          refine (ihφ.2 V (forkedFramePreModel.extend ρ₁ d)
              (forkedFramePreModel.extend ρ₂ d) ?_ ?_ ?_ V
              (ForkedFrameWorld.le_refl V)).mpr hbody
          · intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact h₁ v
          · intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact h₂ v
          · intro σ' v; cases v with
            | vz => exact forkedFrameSemEq_refl hd
            | vs v => exact forkedFrameSemEq_mono hV (hEq v)

/-- The concrete V-frame Kripke-Henkin general model. -/
def forkedFrameModel : KripkeHenkinGeneral ForkedFrameBase ForkedFrameConst where
  toKripkePreModel := forkedFramePreModel
  term_closed := fun t _W ρ hρ => (forkedFrame_fundamental t).1 ρ (fun v => hρ v)
  app_congr_arg := fun hf hd he hde =>
    (forkedFrame_eqvK_iff_semEq _ _ _ _).mpr
      (hf.2 _ _ _ hd he ((forkedFrame_eqvK_iff_semEq _ _ _ _).mp hde))

theorem forkedFrameModel_left_p :
    forkedFrameModel.denote forkedP forkedFrameModel.emptyVal
      ForkedFrameWorld.left := rfl

theorem forkedFrameModel_right_q :
    forkedFrameModel.denote forkedQ forkedFrameModel.emptyVal
      ForkedFrameWorld.right := rfl

theorem forkedFrameModel_root_not_p :
    ¬ forkedFrameModel.denote forkedP forkedFrameModel.emptyVal
        ForkedFrameWorld.root := by
  intro h
  cases h

theorem forkedFrameModel_root_not_p_imp_q :
    ¬ forkedFrameModel.denote (.imp forkedP forkedQ) forkedFrameModel.emptyVal
        ForkedFrameWorld.root := by
  intro h
  have hq := h ForkedFrameWorld.left trivial forkedFrameModel_left_p
  cases hq

theorem forkedFrameModel_root_not_q_imp_p :
    ¬ forkedFrameModel.denote (.imp forkedQ forkedP) forkedFrameModel.emptyVal
        ForkedFrameWorld.root := by
  intro h
  have hp := h ForkedFrameWorld.right trivial forkedFrameModel_right_q
  cases hp

theorem forkedFrameModel_root_not_prelinearity :
    ¬ forkedFrameModel.denote forkedPrelinearity forkedFrameModel.emptyVal
        ForkedFrameWorld.root := by
  intro h
  rcases h with h | h
  · exact forkedFrameModel_root_not_p_imp_q h
  · exact forkedFrameModel_root_not_q_imp_p h

/-- The forked-frame canary: EM-free HOL does not derive prelinearity. -/
theorem prelinearity_not_derivable :
    ¬ ClosedTheorySet.Provable (Const := ForkedFrameConst)
        (∅ : ClosedTheorySet ForkedFrameConst) forkedPrelinearity :=
  forkedFrameModel.not_provable_empty_of_countermodel ForkedFrameWorld.root
    forkedFrameModel_root_not_prelinearity

theorem forkedFrameModel_root_not_excludedMiddleP :
    ¬ forkedFrameModel.denote forkedExcludedMiddleP forkedFrameModel.emptyVal
        ForkedFrameWorld.root := by
  intro h
  rcases h with h | h
  · exact forkedFrameModel_root_not_p h
  · exact h ForkedFrameWorld.left trivial forkedFrameModel_left_p

/-- The same forked-frame model also gives the usual excluded-middle canary
for `p`. -/
theorem forked_excludedMiddleP_not_derivable :
    ¬ ClosedTheorySet.Provable (Const := ForkedFrameConst)
        (∅ : ClosedTheorySet ForkedFrameConst) forkedExcludedMiddleP :=
  forkedFrameModel.not_provable_empty_of_countermodel ForkedFrameWorld.root
    forkedFrameModel_root_not_excludedMiddleP

end KripkeHenkin

end Mettapedia.Logic.HOL
