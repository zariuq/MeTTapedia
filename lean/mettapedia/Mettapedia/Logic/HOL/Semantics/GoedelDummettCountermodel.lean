import Mettapedia.Logic.HOL.Semantics.GoedelDummett
import Mettapedia.Logic.HOL.Semantics.KripkeHenkinCountermodel
import Mettapedia.Logic.HOL.Semantics.ForkedFrameCountermodel
import Mettapedia.Logic.HOL.ClassicalExcludedMiddle

/-!
# Gödel-Dummett countermodel for excluded middle

The two-world canary frame is linearly ordered, so its upset algebra is the
three-element Gödel chain.  This file uses that concrete chain as a
Kripke-Henkin general model for the `WithParams` language: original `p` is true
only at the leaf, and fresh parameter constants are interpreted by canonical
admissible default values.  Linear Kripke-Henkin general models validate the
prelinearity schema, so any LC derivation is sound in this model; excluded
middle for `p` is still refuted at the root.
-/

namespace Mettapedia.Logic.HOL

namespace KripkeHenkin

open Mettapedia.Logic.HOL.WithParams
open Mettapedia.Logic.HOL.HeytingSem.GoedelDummett

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Canonical admissible defaults for interpreting fresh parameters in the
two-world canary model. -/
def emCanaryDefaultVal : (τ : Ty EMCanaryBase) → EMCanaryVal τ
  | .prop => fun _ => True
  | .base b => b.elim
  | .arr _ τ => fun _ => emCanaryDefaultVal τ

theorem emCanaryDefault_adm :
    ∀ τ : Ty EMCanaryBase, EMCanarySemAdm τ (emCanaryDefaultVal τ)
  | .prop => by
      intro _ _
      trivial
  | .base b => b.elim
  | .arr σ τ => by
      constructor
      · intro d hd
        exact emCanaryDefault_adm τ
      · intro W d e hd he hde
        exact emCanarySemEq_refl (emCanaryDefault_adm τ)

/-- The canary premodel over `WithParams`: original `p` keeps the leaf-only
valuation, while fresh parameters denote canonical admissible defaults. -/
def emCanaryWithParamsPreModel :
    KripkePreModel EMCanaryBase (WithParams EMCanaryConst) where
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
  constDen := fun {τ} c =>
    match c with
    | Sum.inl EMCanaryConst.p => fun W => W = EMCanaryWorld.leaf
    | Sum.inr _ => emCanaryDefaultVal τ
  const_mem := by
    intro W τ c
    cases c with
    | inl c =>
        cases c with
        | p =>
            intro U V hUV hU
            cases U with
            | root =>
                cases hU
            | leaf =>
                cases V with
                | root => cases hUV
                | leaf => rfl
    | inr _ =>
        exact emCanaryDefault_adm τ

/-- The `WithParams` canary model's typed equality agrees with the original
canary observational equality. -/
theorem emCanaryWithParams_eqvK_iff_semEq :
    ∀ (τ : Ty EMCanaryBase) (W : EMCanaryWorld)
      (d e : EMCanaryVal τ),
      emCanaryWithParamsPreModel.EqvK W τ d e ↔ EMCanarySemEq W τ d e
  | .prop, W, S, T => Iff.rfl
  | .base b, _, d, e => b.elim
  | .arr σ τ, W, f, g => by
      constructor
      · intro h V hV d hd
        exact (emCanaryWithParams_eqvK_iff_semEq τ V (f d) (g d)).mp
          (h V hV d hd)
      · intro h V hV d hd
        exact (emCanaryWithParams_eqvK_iff_semEq τ V (f d) (g d)).mpr
          (h V hV d hd)

abbrev EMCanaryWithParamsEnvAdm {Γ : Ctx EMCanaryBase}
    (ρ : emCanaryWithParamsPreModel.Valuation Γ) : Prop :=
  ∀ {σ : Ty EMCanaryBase} (v : Var Γ σ), EMCanarySemAdm σ (ρ v)

abbrev EMCanaryWithParamsEnvEq {Γ : Ctx EMCanaryBase} (W : EMCanaryWorld)
    (ρ₁ ρ₂ : emCanaryWithParamsPreModel.Valuation Γ) : Prop :=
  ∀ {σ : Ty EMCanaryBase} (v : Var Γ σ), EMCanarySemEq W σ (ρ₁ v) (ρ₂ v)

/-- Fundamental lemma for the `WithParams` canary premodel. -/
theorem emCanaryWithParams_fundamental {Γ : Ctx EMCanaryBase} {τ : Ty EMCanaryBase}
    (t : Term (WithParams EMCanaryConst) Γ τ) :
    (∀ (ρ : emCanaryWithParamsPreModel.Valuation Γ), EMCanaryWithParamsEnvAdm ρ →
      EMCanarySemAdm τ (emCanaryWithParamsPreModel.denote t ρ)) ∧
    (∀ (W : EMCanaryWorld) (ρ₁ ρ₂ : emCanaryWithParamsPreModel.Valuation Γ),
      EMCanaryWithParamsEnvAdm ρ₁ → EMCanaryWithParamsEnvAdm ρ₂ →
        EMCanaryWithParamsEnvEq W ρ₁ ρ₂ →
          EMCanarySemEq W τ (emCanaryWithParamsPreModel.denote t ρ₁)
            (emCanaryWithParamsPreModel.denote t ρ₂)) := by
  induction t with
  | var v =>
      exact ⟨fun ρ hρ => hρ v, fun W ρ₁ ρ₂ _ _ hEq => hEq v⟩
  | const c =>
      cases c with
      | inl c =>
          cases c with
          | p =>
              refine ⟨fun ρ hρ => ?_, fun W ρ₁ ρ₂ _ _ _ => fun V hV => Iff.rfl⟩
              intro U V hUV hU
              cases U with
              | root =>
                  cases hU
              | leaf =>
                  cases V with
                  | root => cases hUV
                  | leaf => rfl
      | inr _ =>
          refine ⟨fun ρ hρ => emCanaryDefault_adm _, fun W ρ₁ ρ₂ _ _ _ => ?_⟩
          exact emCanarySemEq_refl (emCanaryDefault_adm _)
  | app f t ihf iht =>
      constructor
      · intro ρ hρ
        exact (ihf.1 ρ hρ).1 _ (iht.1 ρ hρ)
      · intro W ρ₁ ρ₂ h₁ h₂ hEq
        have hff := ihf.2 W ρ₁ ρ₂ h₁ h₂ hEq W (EMCanaryWorld.le_refl W)
          (emCanaryWithParamsPreModel.denote t ρ₁) (iht.1 ρ₁ h₁)
        have hresp := (ihf.1 ρ₂ h₂).2 W
          (emCanaryWithParamsPreModel.denote t ρ₁)
          (emCanaryWithParamsPreModel.denote t ρ₂)
          (iht.1 ρ₁ h₁) (iht.1 ρ₂ h₂) (iht.2 W ρ₁ ρ₂ h₁ h₂ hEq)
        exact emCanarySemEq_trans hff hresp
  | lam t iht =>
      constructor
      · intro ρ hρ
        constructor
        · intro d hd
          refine iht.1 (emCanaryWithParamsPreModel.extend ρ d) ?_
          intro σ' v
          cases v with
          | vz => exact hd
          | vs v => exact hρ v
        · intro W d e hd he hde
          refine iht.2 W (emCanaryWithParamsPreModel.extend ρ d)
            (emCanaryWithParamsPreModel.extend ρ e) ?_ ?_ ?_
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
        refine iht.2 V (emCanaryWithParamsPreModel.extend ρ₁ d)
          (emCanaryWithParamsPreModel.extend ρ₂ d) ?_ ?_ ?_
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
        exact emCanaryWithParamsPreModel.eqvK_mono hUV h
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV
        have ht := emCanarySemEq_mono hV (iht.2 W ρ₁ ρ₂ h₁ h₂ hEq)
        have hu := emCanarySemEq_mono hV (ihu.2 W ρ₁ ρ₂ h₁ h₂ hEq)
        constructor
        · intro h
          refine (emCanaryWithParams_eqvK_iff_semEq _ _ _ _).mpr ?_
          exact emCanarySemEq_trans (emCanarySemEq_symm ht)
            (emCanarySemEq_trans
              ((emCanaryWithParams_eqvK_iff_semEq _ _ _ _).mp h) hu)
        · intro h
          refine (emCanaryWithParams_eqvK_iff_semEq _ _ _ _).mpr ?_
          exact emCanarySemEq_trans ht
            (emCanarySemEq_trans
              ((emCanaryWithParams_eqvK_iff_semEq _ _ _ _).mp h)
              (emCanarySemEq_symm hu))
  | all φ ihφ =>
      constructor
      · intro ρ hρ U V hUV h V' hV' d hd
        exact h V' (EMCanaryWorld.le_trans hUV hV') d hd
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV
        constructor
        · intro h V' hV' d hd
          refine (ihφ.2 V' (emCanaryWithParamsPreModel.extend ρ₁ d)
              (emCanaryWithParamsPreModel.extend ρ₂ d) ?_ ?_ ?_ V'
              (EMCanaryWorld.le_refl V')).mp (h V' hV' d hd)
          · intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact h₁ v
          · intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact h₂ v
          · intro σ' v; cases v with
            | vz => exact emCanarySemEq_refl hd
            | vs v => exact emCanarySemEq_mono (EMCanaryWorld.le_trans hV hV') (hEq v)
        · intro h V' hV' d hd
          refine (ihφ.2 V' (emCanaryWithParamsPreModel.extend ρ₁ d)
              (emCanaryWithParamsPreModel.extend ρ₂ d) ?_ ?_ ?_ V'
              (EMCanaryWorld.le_refl V')).mpr (h V' hV' d hd)
          · intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact h₁ v
          · intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact h₂ v
          · intro σ' v; cases v with
            | vz => exact emCanarySemEq_refl hd
            | vs v => exact emCanarySemEq_mono (EMCanaryWorld.le_trans hV hV') (hEq v)
  | ex φ ihφ =>
      constructor
      · intro ρ hρ U V hUV h
        obtain ⟨d, hd, hbody⟩ := h
        exact ⟨d, hd, ihφ.1 (emCanaryWithParamsPreModel.extend ρ d)
          (by intro σ' v; cases v with
            | vz => exact hd
            | vs v => exact hρ v) hUV hbody⟩
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV
        constructor
        · rintro ⟨d, hd, hbody⟩
          refine ⟨d, hd, ?_⟩
          refine (ihφ.2 V (emCanaryWithParamsPreModel.extend ρ₁ d)
              (emCanaryWithParamsPreModel.extend ρ₂ d) ?_ ?_ ?_ V
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
          refine (ihφ.2 V (emCanaryWithParamsPreModel.extend ρ₁ d)
              (emCanaryWithParamsPreModel.extend ρ₂ d) ?_ ?_ ?_ V
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

/-- The canary model over the parameter-extended language. -/
def emCanaryWithParamsModel :
    KripkeHenkinGeneral EMCanaryBase (WithParams EMCanaryConst) where
  toKripkePreModel := emCanaryWithParamsPreModel
  term_closed := fun t _W ρ hρ => (emCanaryWithParams_fundamental t).1 ρ (fun v => hρ v)
  app_congr_arg := fun hf hd he hde =>
    (emCanaryWithParams_eqvK_iff_semEq _ _ _ _).mpr
      (hf.2 _ _ _ hd he ((emCanaryWithParams_eqvK_iff_semEq _ _ _ _).mp hde))

/-- The two-world canary frame is linear; its upsets form the three-element
Gödel chain. -/
theorem emCanaryWorld_linear :
    ∀ U V : EMCanaryWorld, EMCanaryWorld.le U V ∨ EMCanaryWorld.le V U := by
  intro U V
  cases U <;> cases V <;> simp [EMCanaryWorld.le]

theorem general_denote_prelinearity_of_linear
    (M : KripkeHenkinGeneral Base Const)
    (hlin : ∀ U V : M.World, M.le U V ∨ M.le V U)
    {Γ : Ctx Base} (A B : Formula Const Γ)
    {W : M.World} {ρ : M.Valuation Γ}
    (hρ : M.ValuationAdm W ρ) :
    M.denote (.or (.imp A B) (.imp B A)) ρ W := by
  classical
  by_cases hAB : ∀ V, M.le W V → M.denote A ρ V → M.denote B ρ V
  · exact Or.inl hAB
  · right
    have hEx : ∃ V, M.le W V ∧ M.denote A ρ V ∧ ¬ M.denote B ρ V := by
      by_contra hNo
      apply hAB
      intro V hWV hAV
      by_contra hBV
      exact hNo ⟨V, hWV, hAV, hBV⟩
    obtain ⟨V, hWV, hAV, hNotBV⟩ := hEx
    intro U hWU hBU
    rcases hlin U V with hUV | hVU
    · exact False.elim
        (hNotBV (M.denote_prop_mono B
          (M.toKripkePreModel.valuationAdm_mono hWU hρ) hUV hBU))
    · exact M.denote_prop_mono A
        (M.toKripkePreModel.valuationAdm_mono hWV hρ) hVU hAV

theorem prelinShape_denote_of_linear
    (M : KripkeHenkinGeneral Base (WithParams Const))
    (hlin : ∀ U V : M.World, M.le U V ∨ M.le V U) :
    ∀ {Γ : Ctx Base} {φ : Formula (WithParams Const) Γ},
      PrelinShape (Base := Base) φ →
        ∀ {W : M.World} {ρ : M.Valuation Γ},
          M.ValuationAdm W ρ → M.denote φ ρ W := by
  intro Γ φ h
  induction h with
  | base A B =>
      intro W ρ hρ
      exact general_denote_prelinearity_of_linear M hlin A B hρ
  | all h ih =>
      intro W ρ hρ V hWV d hd
      exact ih (W := V) (ρ := M.extend ρ d)
        (M.toKripkePreModel.extend_adm
          (M.toKripkePreModel.valuationAdm_mono hWV hρ) hd)

/-- Soundness of LC derivability in linearly ordered Kripke-Henkin general
models. -/
theorem denote_of_provableLC_empty_linear
    {θ : ClosedFormula (WithParams Const)}
    (h : ProvableLC (Base := Base) (Const := Const)
      (∅ : ClosedTheorySet (WithParams Const)) θ)
    (M : KripkeHenkinGeneral Base (WithParams Const))
    (hlin : ∀ U V : M.World, M.le U V ∨ M.le V U)
    (W : M.World) (ρ : M.Valuation ([] : Ctx Base))
    (hρ : M.ValuationAdm W ρ) :
    (M.denote θ ρ) W := by
  rcases h with ⟨Γ, hΓ, d⟩
  exact KripkeHenkinGeneral.sound d M W ρ hρ
    (by
      intro ψ hψ
      rcases hΓ ψ hψ with hEmpty | hSchema
      · cases hEmpty
      · exact prelinShape_denote_of_linear M hlin hSchema hρ)

/-- The distinguished atom in the parameter-extended canary language. -/
def emCanaryAtomLC : ClosedFormula (WithParams EMCanaryConst) :=
  .const (WithParams.inj EMCanaryConst.p)

/-- Excluded middle for the distinguished atom in the LC language. -/
def emCanaryExcludedMiddleLC : ClosedFormula (WithParams EMCanaryConst) :=
  .or emCanaryAtomLC (.not emCanaryAtomLC)

theorem emCanaryWithParamsModel_root_not_atom :
    ¬ emCanaryWithParamsModel.denote emCanaryAtomLC emCanaryWithParamsModel.emptyVal
        EMCanaryWorld.root := by
  intro h
  cases h

theorem emCanaryWithParamsModel_leaf_atom :
    emCanaryWithParamsModel.denote emCanaryAtomLC emCanaryWithParamsModel.emptyVal
      EMCanaryWorld.leaf := rfl

theorem emCanaryWithParamsModel_root_not_excludedMiddleLC :
    ¬ emCanaryWithParamsModel.denote emCanaryExcludedMiddleLC
        emCanaryWithParamsModel.emptyVal EMCanaryWorld.root := by
  intro h
  rcases h with h | h
  · exact emCanaryWithParamsModel_root_not_atom h
  · exact h EMCanaryWorld.leaf trivial emCanaryWithParamsModel_leaf_atom

/-- LC does not derive excluded middle: the linear two-world model validates
prelinearity but refutes `p ∨ ¬p` at the root. -/
theorem em_not_derivable_LC :
    ¬ ProvableLC (Base := EMCanaryBase) (Const := EMCanaryConst)
        (∅ : ClosedTheorySet (WithParams EMCanaryConst)) emCanaryExcludedMiddleLC := by
  intro h
  exact emCanaryWithParamsModel_root_not_excludedMiddleLC
    (denote_of_provableLC_empty_linear h emCanaryWithParamsModel
      emCanaryWorld_linear EMCanaryWorld.root emCanaryWithParamsModel.emptyVal
      (emCanaryWithParamsModel.emptyVal_adm EMCanaryWorld.root))

/-- The left-only atom, embedded into the LC parameter language. -/
def forkedP_LC : ClosedFormula (WithParams ForkedFrameConst) :=
  .const (WithParams.inj ForkedFrameConst.p)

/-- The right-only atom, embedded into the LC parameter language. -/
def forkedQ_LC : ClosedFormula (WithParams ForkedFrameConst) :=
  .const (WithParams.inj ForkedFrameConst.q)

/-- The LC-side prelinearity instance corresponding to the forked-frame
countermodel. -/
def forkedPrelinearityLC : ClosedFormula (WithParams ForkedFrameConst) :=
  .or (.imp forkedP_LC forkedQ_LC) (.imp forkedQ_LC forkedP_LC)

/-- LC proves the injected forked-frame prelinearity instance by schema
membership. -/
theorem forked_prelinearityLC_provableLC :
    ProvableLC (Base := ForkedFrameBase) (Const := ForkedFrameConst)
      (∅ : ClosedTheorySet (WithParams ForkedFrameConst)) forkedPrelinearityLC := by
  simpa [forkedPrelinearityLC, forkedP_LC, forkedQ_LC] using
    (provableLC_prelinearity (Base := ForkedFrameBase) (Const := ForkedFrameConst)
      (∅ : ClosedTheorySet (WithParams ForkedFrameConst)) forkedP_LC forkedQ_LC)

/-- Packaged strictness of intuitionistic HOL below LC: prelinearity is not
derivable in the EM-free calculus, while its injected instance is an LC schema
theorem. -/
theorem intuitionistic_strictly_below_lc :
    (¬ ClosedTheorySet.Provable (Const := ForkedFrameConst)
        (∅ : ClosedTheorySet ForkedFrameConst) forkedPrelinearity) ∧
      ProvableLC (Base := ForkedFrameBase) (Const := ForkedFrameConst)
        (∅ : ClosedTheorySet (WithParams ForkedFrameConst)) forkedPrelinearityLC :=
  ⟨prelinearity_not_derivable, forked_prelinearityLC_provableLC⟩

/-- Classical HOL proves excluded middle by membership in the excluded-middle
schema. -/
theorem classical_provable_excludedMiddleLC :
    ClosedTheorySet.Provable (Const := WithParams EMCanaryConst)
      (EMSchema (Base := EMCanaryBase) EMCanaryConst) emCanaryExcludedMiddleLC := by
  exact ClosedTheorySet.provable_of_mem
    (emClosed_mem (Base := EMCanaryBase) (Const := EMCanaryConst) emCanaryAtomLC)

/-- Packaged strictness of LC below classical HOL: the same excluded-middle
instance is classically derivable but not LC-derivable. -/
theorem lc_strictly_below_classical :
    (¬ ProvableLC (Base := EMCanaryBase) (Const := EMCanaryConst)
        (∅ : ClosedTheorySet (WithParams EMCanaryConst)) emCanaryExcludedMiddleLC) ∧
      ClosedTheorySet.Provable (Const := WithParams EMCanaryConst)
        (EMSchema (Base := EMCanaryBase) EMCanaryConst) emCanaryExcludedMiddleLC :=
  ⟨em_not_derivable_LC, classical_provable_excludedMiddleLC⟩

end KripkeHenkin

end Mettapedia.Logic.HOL
