import Mettapedia.Logic.HOL.Derivation
import Mettapedia.Logic.HOL.Semantics.Extensionality

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

namespace Soundness

/-- Assumption satisfaction at a valuation. -/
def SatisfiesHyps (M : HenkinModel.{u, v, w} Base Const) {Γ : Ctx Base}
    (ρ : HenkinModel.Valuation M Γ) (Δ : List (Formula Const Γ)) : Prop :=
  ∀ φ, φ ∈ Δ → (HenkinModel.denote M φ ρ).down

/-- Precompose a valuation with a variable renaming. -/
def renameVal (M : HenkinModel.{u, v, w} Base Const)
    (ρr : Rename Base Γ Δ) (ν : HenkinModel.Valuation M Δ) :
    HenkinModel.Valuation M Γ :=
  fun v => ν (ρr v)

theorem renameVal_lift (M : HenkinModel.{u, v, w} Base Const)
    (ρr : Rename Base Γ Δ) (ν : HenkinModel.Valuation M Δ) (x : Ty.denote M.Carrier σ) :
    (renameVal M (Rename.lift (σ := σ) ρr) (HenkinModel.extend M ν x) :
        HenkinModel.Valuation M (σ :: Γ)) =
      (HenkinModel.extend M (renameVal M ρr ν) x :
        HenkinModel.Valuation M (σ :: Γ)) := by
  funext τ v
  cases v <;> rfl

theorem denote_rename (M : HenkinModel.{u, v, w} Base Const) :
    ∀ {Γ Δ : Ctx Base} {τ : Ty Base}
      (ρr : Rename Base Γ Δ) (t : Term Const Γ τ) (ν : HenkinModel.Valuation M Δ),
      HenkinModel.denote M (rename ρr t) ν =
        HenkinModel.denote M t (renameVal M ρr ν)
  | _, _, _, ρr, .var v, ν => rfl
  | _, _, _, ρr, .const c, ν => rfl
  | _, _, _, ρr, .app f t, ν => by
      simp [rename, HenkinModel.denote, PreModel.denote,
        denote_rename M ρr f ν, denote_rename M ρr t ν]
  | _, _, _, ρr, .lam t, ν => by
      funext x
      change
        HenkinModel.denote M (rename (Rename.lift ρr) t) (HenkinModel.extend M ν x) =
          HenkinModel.denote M t (HenkinModel.extend M (renameVal M ρr ν) x)
      rw [denote_rename M (Rename.lift ρr) t (HenkinModel.extend M ν x)]
      rw [renameVal_lift M ρr ν x]
  | _, _, _, ρr, .top, ν => rfl
  | _, _, _, ρr, .bot, ν => rfl
  | _, _, _, ρr, .and φ ψ, ν => by
      apply congrArg ULift.up
      apply propext
      simp [denote_rename M ρr φ ν, denote_rename M ρr ψ ν]
  | _, _, _, ρr, .or φ ψ, ν => by
      apply congrArg ULift.up
      apply propext
      simp [denote_rename M ρr φ ν, denote_rename M ρr ψ ν]
  | _, _, _, ρr, .imp φ ψ, ν => by
      apply congrArg ULift.up
      apply propext
      simp [denote_rename M ρr φ ν, denote_rename M ρr ψ ν]
  | _, _, _, ρr, .not φ, ν => by
      apply congrArg ULift.up
      apply propext
      simp [denote_rename M ρr φ ν]
  | _, _, _, ρr, .eq t u, ν => by
      apply congrArg ULift.up
      simp [denote_rename M ρr t ν, denote_rename M ρr u ν]
  | _, _, _, ρr, .all φ, ν => by
      apply congrArg ULift.up
      apply propext
      constructor <;> intro h x hx
      · have hbody := h x hx
        have hrename :=
          congrArg ULift.down
            (denote_rename M (Rename.lift ρr) φ (HenkinModel.extend M ν x))
        rw [renameVal_lift M ρr ν x] at hrename
        exact hrename.mp hbody
      · have hbody := h x hx
        have hrename :=
          congrArg ULift.down
            (denote_rename M (Rename.lift ρr) φ (HenkinModel.extend M ν x))
        rw [renameVal_lift M ρr ν x] at hrename
        exact hrename.mpr hbody
  | _, _, _, ρr, .ex φ, ν => by
      apply congrArg ULift.up
      apply propext
      constructor
      · rintro ⟨x, hx, hbody⟩
        refine ⟨x, hx, ?_⟩
        have hrename :=
          congrArg ULift.down
            (denote_rename M (Rename.lift ρr) φ (HenkinModel.extend M ν x))
        rw [renameVal_lift M ρr ν x] at hrename
        exact hrename.mp hbody
      · rintro ⟨x, hx, hbody⟩
        refine ⟨x, hx, ?_⟩
        have hrename :=
          congrArg ULift.down
            (denote_rename M (Rename.lift ρr) φ (HenkinModel.extend M ν x))
        rw [renameVal_lift M ρr ν x] at hrename
        exact hrename.mpr hbody

@[simp] theorem denote_weaken (M : HenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ)
    (ρ : HenkinModel.Valuation M Γ) (x : Ty.denote M.Carrier σ) :
    HenkinModel.denote M (weaken (Base := Base) (σ := σ) t) (HenkinModel.extend M ρ x) =
      HenkinModel.denote M t ρ := by
  simpa [weaken, renameVal, renameVal_lift] using
    (denote_rename M (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ)) t
      (HenkinModel.extend M ρ x))

/-- Substitute denotations of a term substitution into a valuation. -/
def substVal (M : HenkinModel.{u, v, w} Base Const)
    (σs : Subst Const Γ Δ) (ν : HenkinModel.Valuation M Δ) :
    HenkinModel.Valuation M Γ :=
  fun v => HenkinModel.denote M (σs v) ν

theorem substVal_lift (M : HenkinModel.{u, v, w} Base Const)
    (σs : Subst Const Γ Δ) (ν : HenkinModel.Valuation M Δ) (x : Ty.denote M.Carrier σ) :
    (substVal M (Subst.lift (Base := Base) (σ := σ) σs) (HenkinModel.extend M ν x) :
        HenkinModel.Valuation M (σ :: Γ)) =
      (HenkinModel.extend M (substVal M σs ν) x :
        HenkinModel.Valuation M (σ :: Γ)) := by
  funext τ v
  cases v with
  | vz =>
      rfl
  | vs v =>
      have h := denote_weaken (M := M) (t := σs v) (ρ := ν) (x := x)
      simpa [substVal, Subst.lift, weaken] using h

theorem denote_subst (M : HenkinModel.{u, v, w} Base Const) :
    ∀ {Γ Δ : Ctx Base} {τ : Ty Base}
      (σs : Subst Const Γ Δ) (t : Term Const Γ τ) (ν : HenkinModel.Valuation M Δ),
      HenkinModel.denote M (subst σs t) ν =
        HenkinModel.denote M t (substVal M σs ν)
  | _, _, _, σs, .var v, ν => rfl
  | _, _, _, σs, .const c, ν => rfl
  | _, _, _, σs, .app f t, ν => by
      simp [subst, HenkinModel.denote, PreModel.denote,
        denote_subst M σs f ν, denote_subst M σs t ν]
  | _, _, _, σs, .lam t, ν => by
      funext x
      change
        HenkinModel.denote M (subst (Subst.lift (Base := Base) (σ := _) σs) t)
            (HenkinModel.extend M ν x) =
          HenkinModel.denote M t (HenkinModel.extend M (substVal M σs ν) x)
      rw [denote_subst M (Subst.lift (Base := Base) (σ := _) σs) t (HenkinModel.extend M ν x)]
      rw [substVal_lift M σs ν x]
  | _, _, _, σs, .top, ν => rfl
  | _, _, _, σs, .bot, ν => rfl
  | _, _, _, σs, .and φ ψ, ν => by
      apply congrArg ULift.up
      apply propext
      simp [denote_subst M σs φ ν, denote_subst M σs ψ ν]
  | _, _, _, σs, .or φ ψ, ν => by
      apply congrArg ULift.up
      apply propext
      simp [denote_subst M σs φ ν, denote_subst M σs ψ ν]
  | _, _, _, σs, .imp φ ψ, ν => by
      apply congrArg ULift.up
      apply propext
      simp [denote_subst M σs φ ν, denote_subst M σs ψ ν]
  | _, _, _, σs, .not φ, ν => by
      apply congrArg ULift.up
      apply propext
      simp [denote_subst M σs φ ν]
  | _, _, _, σs, .eq t u, ν => by
      apply congrArg ULift.up
      simp [denote_subst M σs t ν, denote_subst M σs u ν]
  | _, _, _, σs, .all φ, ν => by
      apply congrArg ULift.up
      apply propext
      constructor <;> intro h x hx
      · have hbody := h x hx
        have hsubst :=
          congrArg ULift.down
            (denote_subst M (Subst.lift (Base := Base) (σ := _) σs) φ
              (HenkinModel.extend M ν x))
        rw [substVal_lift M σs ν x] at hsubst
        exact hsubst.mp hbody
      · have hbody := h x hx
        have hsubst :=
          congrArg ULift.down
            (denote_subst M (Subst.lift (Base := Base) (σ := _) σs) φ
              (HenkinModel.extend M ν x))
        rw [substVal_lift M σs ν x] at hsubst
        exact hsubst.mpr hbody
  | _, _, _, σs, .ex φ, ν => by
      apply congrArg ULift.up
      apply propext
      constructor
      · rintro ⟨x, hx, hbody⟩
        refine ⟨x, hx, ?_⟩
        have hsubst :=
          congrArg ULift.down
            (denote_subst M (Subst.lift (Base := Base) (σ := _) σs) φ
              (HenkinModel.extend M ν x))
        rw [substVal_lift M σs ν x] at hsubst
        exact hsubst.mp hbody
      · rintro ⟨x, hx, hbody⟩
        refine ⟨x, hx, ?_⟩
        have hsubst :=
          congrArg ULift.down
            (denote_subst M (Subst.lift (Base := Base) (σ := _) σs) φ
              (HenkinModel.extend M ν x))
        rw [substVal_lift M σs ν x] at hsubst
        exact hsubst.mpr hbody

@[simp] theorem denote_instantiate_term (M : HenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} {σ τ : Ty Base} (t : Term Const Γ σ) (u : Term Const (σ :: Γ) τ)
    (ρ : HenkinModel.Valuation M Γ) :
    HenkinModel.denote M (instantiate (Base := Base) t u) ρ =
      HenkinModel.denote M u
        (HenkinModel.extend M ρ (HenkinModel.denote M t ρ)) := by
  have hsubst := denote_subst M (Subst.single t) u ρ
  have hsingle :
      (substVal M (Subst.single t) ρ : HenkinModel.Valuation M (σ :: Γ)) =
        (HenkinModel.extend M ρ (HenkinModel.denote M t ρ) :
          HenkinModel.Valuation M (σ :: Γ)) := by
    funext τ v
    cases v with
    | vz => rfl
    | vs v => rfl
  rw [hsingle] at hsubst
  exact hsubst

theorem denote_instantiate (M : HenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} {σ : Ty Base} (t : Term Const Γ σ) (φ : Formula Const (σ :: Γ))
    (ρ : HenkinModel.Valuation M Γ) :
    (HenkinModel.denote M (instantiate (Base := Base) t φ) ρ).down ↔
      (HenkinModel.denote M φ (HenkinModel.extend M ρ (HenkinModel.denote M t ρ))).down := by
  have hsubst := congrArg ULift.down (denote_instantiate_term M t φ ρ)
  exact Iff.of_eq hsubst

theorem satisfies_weakenHyps (M : HenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {ρ : HenkinModel.Valuation M Γ} (hΔ : SatisfiesHyps M ρ Δ)
    (x : Ty.denote M.Carrier σ) :
    SatisfiesHyps M (HenkinModel.extend M ρ x) (weakenHyps (Base := Base) (σ := σ) Δ) := by
  intro φ hφ
  rcases List.mem_map.mp hφ with ⟨ψ, hψ, rfl⟩
  have hψε := hΔ ψ hψ
  simpa using (congrArg ULift.down (denote_weaken M ψ ρ x)).mpr hψε

theorem derivation_sound
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (d : Derivation Const Δ φ) :
    ∀ {M : HenkinModel.{u, v, w} Base Const} {ρ : HenkinModel.Valuation M Γ},
      HenkinModel.ValuationAdmissible M ρ →
      SatisfiesHyps M ρ Δ →
      (HenkinModel.denote M φ ρ).down := by
  induction d with
  | hyp hmem =>
      intro M ρ hρ hΔ
      exact hΔ _ hmem
  | topI =>
      intro M ρ hρ hΔ
      simp
  | botE h ih =>
      intro M ρ hρ hΔ
      exact False.elim (ih hρ hΔ)
  | andI hφ hψ ihφ ihψ =>
      intro M ρ hρ hΔ
      exact ⟨ihφ hρ hΔ, ihψ hρ hΔ⟩
  | andEL h ih =>
      intro M ρ hρ hΔ
      exact (ih hρ hΔ).1
  | andER h ih =>
      intro M ρ hρ hΔ
      exact (ih hρ hΔ).2
  | orIL h ih =>
      intro M ρ hρ hΔ
      exact Or.inl (ih hρ hΔ)
  | orIR h ih =>
      intro M ρ hρ hΔ
      exact Or.inr (ih hρ hΔ)
  | orE hor hφ hψ ihor ihφ ihψ =>
      intro M ρ hρ hΔ
      rcases ihor hρ hΔ with h | h
      · exact ihφ hρ (by
          intro χ hχ
          rw [List.mem_cons] at hχ
          rcases hχ with rfl | hχ
          · simpa using h
          · exact hΔ _ hχ)
      · exact ihψ hρ (by
          intro χ hχ
          rw [List.mem_cons] at hχ
          rcases hχ with rfl | hχ
          · simpa using h
          · exact hΔ _ hχ)
  | impI h ih =>
      intro M ρ hρ hΔ hφ
      exact ih hρ (by
        intro χ hχ
        rw [List.mem_cons] at hχ
        rcases hχ with rfl | hχ
        · simpa using hφ
        · exact hΔ _ hχ)
  | impE himp hφ ihimp ihφ =>
      intro M ρ hρ hΔ
      exact (ihimp hρ hΔ) (ihφ hρ hΔ)
  | notI h ih =>
      intro M ρ hρ hΔ hφ
      exact ih hρ (by
        intro χ hχ
        rw [List.mem_cons] at hχ
        rcases hχ with rfl | hχ
        · simpa using hφ
        · exact hΔ _ hχ)
  | notE hnot hφ ihnot ihφ =>
      intro M ρ hρ hΔ
      exact (ihnot hρ hΔ) (ihφ hρ hΔ)
  | allI h ih =>
      intro M ρ hρ hΔ x hx
      exact ih (HenkinModel.extend_admissible M hρ hx)
        (satisfies_weakenHyps M hΔ x)
  | allE t h ih =>
      intro M ρ hρ hΔ
      have hall := ih hρ hΔ
      have ht : M.adm _ (HenkinModel.denote M t ρ) :=
        HenkinModel.denote_admissible M hρ t
      exact (denote_instantiate M t _ ρ).mpr (hall _ ht)
  | exI t h ih =>
      intro M ρ hρ hΔ
      refine ⟨HenkinModel.denote M t ρ, HenkinModel.denote_admissible M hρ t, ?_⟩
      exact (denote_instantiate M t _ ρ).mp (ih hρ hΔ)
  | exE hex hbody ihex ihbody =>
      intro M ρ hρ hΔ
      rcases ihex hρ hΔ with ⟨x, hx, hφ⟩
      have hbody' :=
        ihbody (HenkinModel.extend_admissible M hρ hx) (by
          intro χ hχ
          rw [List.mem_cons] at hχ
          rcases hχ with rfl | hχ
          · exact hφ
          · exact satisfies_weakenHyps M hΔ x _ hχ)
      simpa using hbody'
  | eqRefl t =>
      intro M ρ hρ hΔ
      simpa using HenkinModel.eqv_refl M (HenkinModel.denote_admissible M hρ t)
  | eqSymm h ih =>
      intro M ρ hρ hΔ
      exact HenkinModel.eqv_symm M (ih hρ hΔ)
  | eqTrans htu huv ihtu ihuv =>
      intro M ρ hρ hΔ
      exact HenkinModel.eqv_trans M (ihtu hρ hΔ) (ihuv hρ hΔ)
  | eqApp t h ih =>
      intro M ρ hρ hΔ
      exact HenkinModel.eqv_arr_apply M (ih hρ hΔ)
        (HenkinModel.denote_admissible M hρ t)
  | eqLam h ih =>
      intro M ρ hρ hΔ x hx
      exact ih (HenkinModel.extend_admissible M hρ hx)
        (satisfies_weakenHyps M hΔ x)
  | funExt h ih =>
      intro M ρ hρ hΔ x hx
      have hpoint := ih hρ hΔ x hx
      simpa [HenkinModel.denote, PreModel.denote] using hpoint
  | beta t u =>
      intro M ρ hρ hΔ
      simpa [HenkinModel.denote, PreModel.denote] using
        HenkinModel.eqv_refl M
          (HenkinModel.denote_admissible M hρ (instantiate (Base := Base) t u))
  | eta f =>
      intro M ρ hρ hΔ x hx
      simpa [HenkinModel.denote, PreModel.denote] using
        (HenkinModel.eqv_refl M
          (M.app_mem (HenkinModel.denote_admissible M hρ f) hx))

/-- Closed HOL theorems are valid in every Henkin model. -/
theorem theorem_sound {φ : ClosedFormula Const}
    (d : Derivation.Theorem Const φ) (M : HenkinModel.{u, v, w} Base Const) :
    HenkinModel.models M φ := by
  exact derivation_sound d (M := M) (ρ := fun v => nomatch v) (by intro τ v; nomatch v) (by
    intro ψ hψ
    nomatch hψ)

end Soundness

end Mettapedia.Logic.HOL
