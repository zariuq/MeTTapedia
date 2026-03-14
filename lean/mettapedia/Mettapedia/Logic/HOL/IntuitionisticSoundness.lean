import Mettapedia.Logic.HOL.DerivationExtensionality
import Mettapedia.Logic.HOL.Semantics.HeytingHenkin

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

namespace IntuitionisticSoundness

abbrev denoteFormula (M : HeytingHenkinModel.{u, v, w} Base Const) {Γ : Ctx Base}
    (φ : Formula Const Γ) (ρ : HeytingHenkinModel.Valuation M Γ) : M.Ω :=
  show M.Ω from HeytingHenkinModel.denote M φ ρ

/-- Precompose a valuation with a variable renaming. -/
def renameVal (M : HeytingHenkinModel.{u, v, w} Base Const)
    (ρr : Rename Base Γ Δ) (ν : HeytingHenkinModel.Valuation M Δ) :
    HeytingHenkinModel.Valuation M Γ :=
  fun v => ν (ρr v)

theorem renameVal_lift (M : HeytingHenkinModel.{u, v, w} Base Const)
    (ρr : Rename Base Γ Δ) (ν : HeytingHenkinModel.Valuation M Δ)
    (x : Ty.denoteHeyting M.Carrier M.Ω σ) :
    (renameVal M (Rename.lift (σ := σ) ρr) (HeytingHenkinModel.extend M ν x) :
        HeytingHenkinModel.Valuation M (σ :: Γ)) =
      (HeytingHenkinModel.extend M (renameVal M ρr ν) x :
        HeytingHenkinModel.Valuation M (σ :: Γ)) := by
  funext τ v
  cases v <;> rfl

theorem denote_rename (M : HeytingHenkinModel.{u, v, w} Base Const) :
    ∀ {Γ Δ : Ctx Base} {τ : Ty Base}
      (ρr : Rename Base Γ Δ) (t : Term Const Γ τ)
      (ν : HeytingHenkinModel.Valuation M Δ),
      HeytingHenkinModel.denote M (rename ρr t) ν =
        HeytingHenkinModel.denote M t (renameVal M ρr ν)
  | _, _, _, ρr, .var v, ν => rfl
  | _, _, _, ρr, .const c, ν => rfl
  | _, _, _, ρr, .app f t, ν => by
      simp [rename, HeytingHenkinModel.denote, HeytingPreModel.denote,
        denote_rename M ρr f ν, denote_rename M ρr t ν]
  | _, _, _, ρr, .lam t, ν => by
      funext x
      change
        HeytingHenkinModel.denote M (rename (Rename.lift (σ := _) ρr) t)
            (HeytingHenkinModel.extend M ν x) =
          HeytingHenkinModel.denote M t
            (HeytingHenkinModel.extend M (renameVal M ρr ν) x)
      simpa [renameVal_lift] using
        (denote_rename M (Rename.lift (σ := _) ρr) t (HeytingHenkinModel.extend M ν x))
  | _, _, _, ρr, .top, ν => rfl
  | _, _, _, ρr, .bot, ν => rfl
  | _, _, _, ρr, .and φ ψ, ν => by
      simp [rename, HeytingHenkinModel.denote, HeytingPreModel.denote,
        denote_rename M ρr φ ν, denote_rename M ρr ψ ν]
  | _, _, _, ρr, .or φ ψ, ν => by
      simp [rename, HeytingHenkinModel.denote, HeytingPreModel.denote,
        denote_rename M ρr φ ν, denote_rename M ρr ψ ν]
  | _, _, _, ρr, .imp φ ψ, ν => by
      simp [rename, HeytingHenkinModel.denote, HeytingPreModel.denote,
        denote_rename M ρr φ ν, denote_rename M ρr ψ ν]
  | _, _, _, ρr, .not φ, ν => by
      simp [rename, HeytingHenkinModel.denote, HeytingPreModel.denote,
        denote_rename M ρr φ ν]
  | _, _, _, ρr, .eq t u, ν => by
      simp [rename, HeytingHenkinModel.denote, HeytingPreModel.denote,
        denote_rename M ρr t ν, denote_rename M ρr u ν]
  | _, _, _, ρr, .all φ, ν => by
      apply congrArg (HeytingPreModel.allAdmissible M.toHeytingPreModel)
      funext x
      simpa [renameVal_lift] using
        (denote_rename M (Rename.lift (σ := _) ρr) φ
          (HeytingHenkinModel.extend M ν x.1))
  | _, _, _, ρr, .ex φ, ν => by
      apply congrArg (HeytingPreModel.anyAdmissible M.toHeytingPreModel)
      funext x
      simpa [renameVal_lift] using
        (denote_rename M (Rename.lift (σ := _) ρr) φ
          (HeytingHenkinModel.extend M ν x.1))

@[simp] theorem denote_weaken (M : HeytingHenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ)
    (ρ : HeytingHenkinModel.Valuation M Γ) (x : Ty.denoteHeyting M.Carrier M.Ω σ) :
    HeytingHenkinModel.denote M (weaken (Base := Base) (σ := σ) t)
        (HeytingHenkinModel.extend M ρ x) =
      HeytingHenkinModel.denote M t ρ := by
  simpa [weaken, renameVal, renameVal_lift] using
    (denote_rename M (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ)) t
      (HeytingHenkinModel.extend M ρ x))

/-- Substitute denotations of a term substitution into a valuation. -/
def substVal (M : HeytingHenkinModel.{u, v, w} Base Const)
    (σs : Subst Const Γ Δ) (ν : HeytingHenkinModel.Valuation M Δ) :
    HeytingHenkinModel.Valuation M Γ :=
  fun v => HeytingHenkinModel.denote M (σs v) ν

theorem substVal_lift (M : HeytingHenkinModel.{u, v, w} Base Const)
    (σs : Subst Const Γ Δ) (ν : HeytingHenkinModel.Valuation M Δ)
    (x : Ty.denoteHeyting M.Carrier M.Ω σ) :
    (substVal M (Subst.lift (Base := Base) (σ := σ) σs)
        (HeytingHenkinModel.extend M ν x) :
        HeytingHenkinModel.Valuation M (σ :: Γ)) =
      (HeytingHenkinModel.extend M (substVal M σs ν) x :
        HeytingHenkinModel.Valuation M (σ :: Γ)) := by
  funext τ v
  cases v with
  | vz =>
      rfl
  | vs v =>
      have h := denote_weaken (M := M) (t := σs v) (ρ := ν) (x := x)
      simpa [substVal, Subst.lift, weaken] using h

theorem denote_subst (M : HeytingHenkinModel.{u, v, w} Base Const) :
    ∀ {Γ Δ : Ctx Base} {τ : Ty Base}
      (σs : Subst Const Γ Δ) (t : Term Const Γ τ)
      (ν : HeytingHenkinModel.Valuation M Δ),
      HeytingHenkinModel.denote M (subst σs t) ν =
        HeytingHenkinModel.denote M t (substVal M σs ν)
  | _, _, _, σs, .var v, ν => rfl
  | _, _, _, σs, .const c, ν => rfl
  | _, _, _, σs, .app f t, ν => by
      simp [subst, HeytingHenkinModel.denote, HeytingPreModel.denote,
        denote_subst M σs f ν, denote_subst M σs t ν]
  | _, _, _, σs, .lam t, ν => by
      funext x
      change
        HeytingHenkinModel.denote M (subst (Subst.lift (Base := Base) (σ := _) σs) t)
            (HeytingHenkinModel.extend M ν x) =
          HeytingHenkinModel.denote M t
            (HeytingHenkinModel.extend M (substVal M σs ν) x)
      simpa [substVal_lift] using
        (denote_subst M (Subst.lift (Base := Base) (σ := _) σs) t
          (HeytingHenkinModel.extend M ν x))
  | _, _, _, σs, .top, ν => rfl
  | _, _, _, σs, .bot, ν => rfl
  | _, _, _, σs, .and φ ψ, ν => by
      simp [subst, HeytingHenkinModel.denote, HeytingPreModel.denote,
        denote_subst M σs φ ν, denote_subst M σs ψ ν]
  | _, _, _, σs, .or φ ψ, ν => by
      simp [subst, HeytingHenkinModel.denote, HeytingPreModel.denote,
        denote_subst M σs φ ν, denote_subst M σs ψ ν]
  | _, _, _, σs, .imp φ ψ, ν => by
      simp [subst, HeytingHenkinModel.denote, HeytingPreModel.denote,
        denote_subst M σs φ ν, denote_subst M σs ψ ν]
  | _, _, _, σs, .not φ, ν => by
      simp [subst, HeytingHenkinModel.denote, HeytingPreModel.denote,
        denote_subst M σs φ ν]
  | _, _, _, σs, .eq t u, ν => by
      simp [subst, HeytingHenkinModel.denote, HeytingPreModel.denote,
        denote_subst M σs t ν, denote_subst M σs u ν]
  | _, _, _, σs, .all φ, ν => by
      apply congrArg (HeytingPreModel.allAdmissible M.toHeytingPreModel)
      funext x
      simpa [substVal_lift] using
        (denote_subst M (Subst.lift (Base := Base) (σ := _) σs) φ
          (HeytingHenkinModel.extend M ν x.1))
  | _, _, _, σs, .ex φ, ν => by
      apply congrArg (HeytingPreModel.anyAdmissible M.toHeytingPreModel)
      funext x
      simpa [substVal_lift] using
        (denote_subst M (Subst.lift (Base := Base) (σ := _) σs) φ
          (HeytingHenkinModel.extend M ν x.1))

@[simp] theorem denote_instantiate_term (M : HeytingHenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} {σ τ : Ty Base} (t : Term Const Γ σ)
    (u : Term Const (σ :: Γ) τ) (ρ : HeytingHenkinModel.Valuation M Γ) :
    HeytingHenkinModel.denote M (instantiate (Base := Base) t u) ρ =
      HeytingHenkinModel.denote M u
        (HeytingHenkinModel.extend M ρ (HeytingHenkinModel.denote M t ρ)) := by
  have hsubst := denote_subst M (Subst.single t) u ρ
  have hsingle :
      (substVal M (Subst.single t) ρ : HeytingHenkinModel.Valuation M (σ :: Γ)) =
        (HeytingHenkinModel.extend M ρ (HeytingHenkinModel.denote M t ρ) :
          HeytingHenkinModel.Valuation M (σ :: Γ)) := by
    funext τ v
    cases v with
    | vz => rfl
    | vs v => rfl
  rw [hsingle] at hsubst
  exact hsubst

@[simp] theorem denote_instantiate_formula (M : HeytingHenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} {σ : Ty Base} (t : Term Const Γ σ)
    (φ : Formula Const (σ :: Γ)) (ρ : HeytingHenkinModel.Valuation M Γ) :
    denoteFormula M (instantiate (Base := Base) t φ) ρ =
      denoteFormula M φ
        (HeytingHenkinModel.extend M ρ (HeytingHenkinModel.denote M t ρ)) := by
  exact denote_instantiate_term (M := M) (t := t) (u := φ) (ρ := ρ)

@[simp] theorem contextDenote_weakenHyps
    (M : HeytingHenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} (Δ : List (Formula Const Γ))
    (ρ : HeytingHenkinModel.Valuation M Γ)
    (x : Ty.denoteHeyting M.Carrier M.Ω σ) :
    HeytingHenkinModel.contextDenote M
        (weakenHyps (Base := Base) (σ := σ) Δ)
        (HeytingHenkinModel.extend M ρ x) =
      HeytingHenkinModel.contextDenote M Δ ρ := by
  induction Δ with
  | nil =>
      rfl
  | cons φ Δ ih =>
      have hφw :
          denoteFormula M (weaken (Base := Base) (σ := σ) φ)
              (HeytingHenkinModel.extend M ρ x) =
            denoteFormula M φ ρ := by
        exact denote_weaken (M := M) (t := φ) (ρ := ρ) (x := x)
      calc
        HeytingHenkinModel.contextDenote M
            (weakenHyps (Base := Base) (σ := σ) (φ :: Δ))
            (HeytingHenkinModel.extend M ρ x) =
          denoteFormula M (weaken (Base := Base) (σ := σ) φ)
              (HeytingHenkinModel.extend M ρ x) ⊓
            HeytingHenkinModel.contextDenote M
              (weakenHyps (Base := Base) (σ := σ) Δ)
              (HeytingHenkinModel.extend M ρ x) := by
            simp [weakenHyps]
        _ =
          denoteFormula M φ ρ ⊓
            HeytingHenkinModel.contextDenote M
              (weakenHyps (Base := Base) (σ := σ) Δ)
              (HeytingHenkinModel.extend M ρ x) := by
            rw [hφw]
        _ = denoteFormula M φ ρ ⊓ HeytingHenkinModel.contextDenote M Δ ρ := by
            rw [ih]
        _ = HeytingHenkinModel.contextDenote M (φ :: Δ) ρ := by
            simp [HeytingHenkinModel.contextDenote, HeytingPreModel.contextDenote]

theorem derivation_sound
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (d : ExtDerivation Const Δ φ) :
    ∀ {M : HeytingHenkinModel.{u, v, w} Base Const}
      {ρ : HeytingHenkinModel.Valuation M Γ},
      HeytingHenkinModel.ValuationAdmissible M ρ →
      HeytingHenkinModel.contextDenote M Δ ρ ≤ denoteFormula M φ ρ := by
  induction d with
  | hyp hmem =>
      intro M ρ hρ
      exact HeytingHenkinModel.contextDenote_le_of_mem M ρ hmem
  | topI =>
      intro M ρ hρ
      exact le_top
  | botE h ih =>
      intro M ρ hρ
      exact le_trans (ih hρ) bot_le
  | andI hφ hψ ihφ ihψ =>
      intro M ρ hρ
      exact le_inf (ihφ hρ) (ihψ hρ)
  | andEL h ih =>
      intro M ρ hρ
      exact le_trans (ih hρ) inf_le_left
  | andER h ih =>
      intro M ρ hρ
      exact le_trans (ih hρ) inf_le_right
  | orIL h ih =>
      intro M ρ hρ
      exact le_trans (ih hρ) le_sup_left
  | orIR h ih =>
      intro M ρ hρ
      exact le_trans (ih hρ) le_sup_right
  | orE hor hφ hψ ihor ihφ ihψ =>
      rename_i Γ0 Δ0 φ0 ψ0 χ0
      intro M ρ hρ
      have hOr : HeytingHenkinModel.contextDenote M Δ0 ρ ≤ denoteFormula M (.or φ0 ψ0) ρ :=
        ihor hρ
      have hφCase :
          HeytingHenkinModel.contextDenote M Δ0 ρ ⊓ denoteFormula M φ0 ρ ≤ denoteFormula M χ0 ρ := by
        simpa [HeytingHenkinModel.contextDenote, HeytingPreModel.contextDenote,
          denoteFormula, inf_assoc, inf_left_comm, inf_comm] using (ihφ hρ)
      have hψCase :
          HeytingHenkinModel.contextDenote M Δ0 ρ ⊓ denoteFormula M ψ0 ρ ≤ denoteFormula M χ0 ρ := by
        simpa [HeytingHenkinModel.contextDenote, HeytingPreModel.contextDenote,
          denoteFormula, inf_assoc, inf_left_comm, inf_comm] using (ihψ hρ)
      calc
        HeytingHenkinModel.contextDenote M Δ0 ρ
            = HeytingHenkinModel.contextDenote M Δ0 ρ ⊓ denoteFormula M (.or φ0 ψ0) ρ := by
              symm
              exact inf_eq_left.mpr hOr
        _ = (HeytingHenkinModel.contextDenote M Δ0 ρ ⊓ denoteFormula M φ0 ρ) ⊔
              (HeytingHenkinModel.contextDenote M Δ0 ρ ⊓ denoteFormula M ψ0 ρ) := by
              rw [show denoteFormula M (.or φ0 ψ0) ρ = denoteFormula M φ0 ρ ⊔ denoteFormula M ψ0 ρ by
                    rfl]
              simpa using (inf_sup_left (HeytingHenkinModel.contextDenote M Δ0 ρ)
                (denoteFormula M φ0 ρ) (denoteFormula M ψ0 ρ) :
                HeytingHenkinModel.contextDenote M Δ0 ρ ⊓
                  (denoteFormula M φ0 ρ ⊔ denoteFormula M ψ0 ρ) =
                (HeytingHenkinModel.contextDenote M Δ0 ρ ⊓ denoteFormula M φ0 ρ) ⊔
                  (HeytingHenkinModel.contextDenote M Δ0 ρ ⊓ denoteFormula M ψ0 ρ))
        _ ≤ denoteFormula M χ0 ρ := sup_le hφCase hψCase
  | impI h ih =>
      rename_i Γ0 Δ0 φ0 ψ0
      intro M ρ hρ
      exact (le_himp_iff).2 <| by
        simpa [HeytingHenkinModel.contextDenote, HeytingPreModel.contextDenote,
          denoteFormula, inf_assoc, inf_left_comm, inf_comm] using (ih hρ)
  | impE himp hφ ihimp ihφ =>
      rename_i Γ0 Δ0 φ0 ψ0
      intro M ρ hρ
      have hImp := (le_himp_iff).1 (ihimp hρ)
      have hφv := ihφ hρ
      calc
        HeytingHenkinModel.contextDenote M Δ0 ρ
            = HeytingHenkinModel.contextDenote M Δ0 ρ ⊓ denoteFormula M φ0 ρ := by
              symm
              exact inf_eq_left.mpr hφv
        _ ≤ denoteFormula M ψ0 ρ := hImp
  | notI h ih =>
      rename_i Γ0 Δ0 φ0
      intro M ρ hρ
      have hraw := ih hρ
      change HeytingHenkinModel.contextDenote M (φ0 :: Δ0) ρ ≤ (⊥ : M.Ω) at hraw
      have hbot :
          HeytingHenkinModel.contextDenote M Δ0 ρ ⊓ denoteFormula M φ0 ρ ≤ (⊥ : M.Ω) := by
        simpa [HeytingHenkinModel.contextDenote, HeytingPreModel.contextDenote,
          denoteFormula, inf_assoc, inf_left_comm, inf_comm] using hraw
      exact (le_himp_iff).2 hbot
  | notE hnot hφ ihnot ihφ =>
      rename_i Γ0 Δ0 φ0
      intro M ρ hρ
      have hNot := (le_himp_iff).1 (ihnot hρ)
      have hφv := ihφ hρ
      calc
        HeytingHenkinModel.contextDenote M Δ0 ρ
            = HeytingHenkinModel.contextDenote M Δ0 ρ ⊓ denoteFormula M φ0 ρ := by
              symm
              exact inf_eq_left.mpr hφv
        _ ≤ (⊥ : M.Ω) := hNot
  | allI h ih =>
      rename_i Γ0 Δ0 σ0 φ0
      intro M ρ hρ
      refine HeytingPreModel.le_allAdmissible M.toHeytingPreModel ?_
      intro x
      have hbody := ih (HeytingHenkinModel.extend_admissible M hρ x.2)
      simpa [contextDenote_weakenHyps, denoteFormula] using hbody
  | allE t h ih =>
      rename_i Γ0 Δ0 σ0 φ0
      intro M ρ hρ
      have hall := ih hρ
      have ht : M.adm σ0 (HeytingHenkinModel.denote M t ρ) :=
        HeytingHenkinModel.denote_admissible M hρ t
      calc
        HeytingHenkinModel.contextDenote M Δ0 ρ
            ≤ HeytingPreModel.allAdmissible M.toHeytingPreModel
                (fun x => denoteFormula M φ0 (HeytingHenkinModel.extend M ρ x.1)) := hall
        _ ≤ denoteFormula M φ0
              (HeytingHenkinModel.extend M ρ (HeytingHenkinModel.denote M t ρ)) :=
          HeytingPreModel.allAdmissible_le M.toHeytingPreModel
            ⟨HeytingHenkinModel.denote M t ρ, ht⟩
        _ = denoteFormula M (instantiate (Base := Base) t φ0) ρ := by
          symm
          exact denote_instantiate_formula M t φ0 ρ
  | exI t h ih =>
      rename_i Γ0 Δ0 σ0 φ0
      intro M ρ hρ
      have ht : M.adm σ0 (HeytingHenkinModel.denote M t ρ) :=
        HeytingHenkinModel.denote_admissible M hρ t
      let p : {x : Ty.denoteHeyting M.Carrier M.Ω σ0 // M.adm σ0 x} → M.Ω :=
        fun x => denoteFormula M φ0 (HeytingHenkinModel.extend M ρ x.1)
      calc
        HeytingHenkinModel.contextDenote M Δ0 ρ
            ≤ denoteFormula M (instantiate (Base := Base) t φ0) ρ := ih hρ
        _ = denoteFormula M φ0
              (HeytingHenkinModel.extend M ρ (HeytingHenkinModel.denote M t ρ)) := by
          exact denote_instantiate_formula M t φ0 ρ
        _ = p ⟨HeytingHenkinModel.denote M t ρ, ht⟩ := by
          rfl
        _ ≤ HeytingPreModel.anyAdmissible M.toHeytingPreModel p :=
          HeytingPreModel.le_anyAdmissible M.toHeytingPreModel
            ⟨HeytingHenkinModel.denote M t ρ, ht⟩
  | exE hex hbody ihex ihbody =>
      rename_i Γ0 Δ0 σ0 φ0 ψ0
      intro M ρ hρ
      have hEx := ihex hρ
      let c : M.Ω := HeytingHenkinModel.contextDenote M Δ0 ρ
      let p : {x : Ty.denoteHeyting M.Carrier M.Ω σ0 // M.adm σ0 x} → M.Ω :=
        fun x => denoteFormula M φ0 (HeytingHenkinModel.extend M ρ x.1)
      have hbodyEach :
          ∀ x : {x : Ty.denoteHeyting M.Carrier M.Ω σ0 // M.adm σ0 x},
            c ⊓ p x ≤
              denoteFormula M ψ0 ρ := by
        intro x
        have hbodyx := ihbody (HeytingHenkinModel.extend_admissible M hρ x.2)
        simpa [contextDenote_weakenHyps, denoteFormula, inf_assoc, inf_left_comm, inf_comm,
          denote_weaken] using hbodyx
      have hdist :
          c ⊓ HeytingPreModel.anyAdmissible M.toHeytingPreModel p =
            HeytingPreModel.anyAdmissible M.toHeytingPreModel (fun x => c ⊓ p x) := by
        rw [HeytingPreModel.anyAdmissible, inf_sSup_eq, HeytingPreModel.anyAdmissible]
        apply le_antisymm
        · refine iSup₂_le ?_
          intro b hb
          rcases hb with ⟨x, rfl⟩
          exact HeytingPreModel.le_anyAdmissible M.toHeytingPreModel
            (p := fun x => c ⊓ p x) x
        · refine HeytingPreModel.anyAdmissible_le M.toHeytingPreModel ?_
          intro x
          exact le_iSup_of_le (p x) <| le_iSup_of_le ⟨x, rfl⟩ le_rfl
      calc
        c = c ⊓ HeytingPreModel.anyAdmissible M.toHeytingPreModel p := by
              symm
              exact inf_eq_left.mpr hEx
        _ = HeytingPreModel.anyAdmissible M.toHeytingPreModel (fun x => c ⊓ p x) := hdist
        _ ≤ denoteFormula M ψ0 ρ := by
          refine HeytingPreModel.anyAdmissible_le M.toHeytingPreModel ?_
          intro x
          exact hbodyEach x
  | eqRefl t =>
      rename_i Γ0 Δ0 τ0
      intro M ρ hρ
      have htop : HeytingHenkinModel.contextDenote M Δ0 ρ ≤ (⊤ : M.Ω) := le_top
      calc
        HeytingHenkinModel.contextDenote M Δ0 ρ ≤ (⊤ : M.Ω) := htop
        _ = denoteFormula M (.eq t t) ρ := by
          symm
          simpa [denoteFormula] using
            (HeytingHenkinModel.eqv_refl M (HeytingHenkinModel.denote_admissible M hρ t))
  | eqSymm h ih =>
      rename_i Γ0 Δ0 τ0 t0 u0
      intro M ρ hρ
      exact le_trans (ih hρ) (HeytingHenkinModel.eqv_symm M)
  | eqTrans htu huv ihtu ihuv =>
      rename_i Γ0 Δ0 τ0 t0 u0 v0
      intro M ρ hρ
      calc
        HeytingHenkinModel.contextDenote M Δ0 ρ
            = HeytingHenkinModel.contextDenote M Δ0 ρ ⊓
                HeytingHenkinModel.contextDenote M Δ0 ρ := by
              symm
              exact inf_idem _
        _ ≤ denoteFormula M (.eq t0 u0) ρ ⊓ denoteFormula M (.eq u0 v0) ρ := by
              exact inf_le_inf (ihtu hρ) (ihuv hρ)
        _ ≤ denoteFormula M (.eq t0 v0) ρ := HeytingHenkinModel.eqv_trans M
  | eqPropI hpq hqp ihpq ihqp =>
      rename_i Γ0 Δ0 p0 q0
      intro M ρ hρ
      exact le_inf (ihpq hρ) (ihqp hρ)
  | eqPropEL hpq ihpq =>
      rename_i Γ0 Δ0 p0 q0
      intro M ρ hρ
      exact le_trans (ihpq hρ) inf_le_left
  | eqPropER hpq ihpq =>
      rename_i Γ0 Δ0 p0 q0
      intro M ρ hρ
      exact le_trans (ihpq hρ) inf_le_right
  | eqApp t h ih =>
      rename_i Γ0 Δ0 σ0 τ0 f0 g0
      intro M ρ hρ
      have ht : M.adm σ0 (HeytingHenkinModel.denote M t ρ) :=
        HeytingHenkinModel.denote_admissible M hρ t
      have happ :
          denoteFormula M (.eq f0 g0) ρ ≤
            denoteFormula M (.eq (.app f0 t) (.app g0 t)) ρ :=
        HeytingPreModel.allAdmissible_le M.toHeytingPreModel
          ⟨HeytingHenkinModel.denote M t ρ, ht⟩
      exact le_trans (ih hρ) happ
  | eqAppArg f h ih =>
      rename_i Γ0 Δ0 σ0 τ0 t0 u0
      intro M ρ hρ
      have hf : M.adm (σ0 ⇒ τ0) (HeytingHenkinModel.denote M f ρ) :=
        HeytingHenkinModel.denote_admissible M hρ f
      have ht : M.adm σ0 (HeytingHenkinModel.denote M t0 ρ) :=
        HeytingHenkinModel.denote_admissible M hρ t0
      have hu : M.adm σ0 (HeytingHenkinModel.denote M u0 ρ) :=
        HeytingHenkinModel.denote_admissible M hρ u0
      exact le_trans (ih hρ) (M.app_respects_eq hf ht hu)
  | eqLam h ih =>
      rename_i Γ0 Δ0 σ0 τ0 t0 u0
      intro M ρ hρ
      refine HeytingPreModel.le_allAdmissible M.toHeytingPreModel ?_
      intro x
      have hbody := ih (HeytingHenkinModel.extend_admissible M hρ x.2)
      simpa [contextDenote_weakenHyps, denoteFormula] using hbody
  | funExt h ih =>
      rename_i Γ0 Δ0 σ0 τ0 f0 g0
      intro M ρ hρ
      simpa [denoteFormula, HeytingHenkinModel.denote, HeytingPreModel.denote, denote_weaken]
        using (ih hρ)
  | beta t u =>
      rename_i Γ0 Δ0 σ0 τ0
      intro M ρ hρ
      have htop : HeytingHenkinModel.contextDenote M Δ0 ρ ≤ (⊤ : M.Ω) := le_top
      calc
        HeytingHenkinModel.contextDenote M Δ0 ρ ≤ (⊤ : M.Ω) := htop
        _ = denoteFormula M (.eq (.app (.lam u) t) (instantiate (Base := Base) t u)) ρ := by
          symm
          simpa [denoteFormula, HeytingHenkinModel.denote, HeytingPreModel.denote,
            denote_instantiate_term] using
            (HeytingHenkinModel.eqv_refl M
              (HeytingHenkinModel.denote_admissible M hρ (instantiate (Base := Base) t u)))
  | eta f =>
      rename_i Γ0 Δ0 σ0 τ0
      intro M ρ hρ
      refine HeytingPreModel.le_allAdmissible M.toHeytingPreModel ?_
      intro x
      have htop : HeytingHenkinModel.contextDenote M Δ0 ρ ≤ (⊤ : M.Ω) := le_top
      let y : Ty.denoteHeyting M.Carrier M.Ω τ0 :=
        (HeytingHenkinModel.denote M f ρ) x.1
      have hy : M.adm τ0 y :=
        M.app_mem (HeytingHenkinModel.denote_admissible M hρ f) x.2
      have hEqTop : (⊤ : M.Ω) = HeytingHenkinModel.Eqv M τ0 y y := by
        symm
        simpa [y] using (HeytingHenkinModel.eqv_refl M hy)
      calc
        HeytingHenkinModel.contextDenote M Δ0 ρ ≤ (⊤ : M.Ω) := htop
        _ = HeytingHenkinModel.Eqv M τ0
              (HeytingHenkinModel.denote M (.app (weaken (Base := Base) (σ := σ0) f) (.var .vz))
                (HeytingHenkinModel.extend M ρ x.1))
              ((HeytingHenkinModel.denote M f ρ) x.1) := by
          simpa [HeytingHenkinModel.denote, HeytingPreModel.denote, denote_weaken, y] using hEqTop

theorem theorem_sound {φ : ClosedFormula Const}
    (d : ExtDerivation.Theorem Const φ)
    (M : HeytingHenkinModel.{u, v, w} Base Const) :
    HeytingHenkinModel.models M φ := by
  have hs : (⊤ : M.Ω) ≤ denoteFormula M φ (fun v => nomatch v) := by
    simpa [HeytingHenkinModel.contextDenote, HeytingPreModel.contextDenote, denoteFormula] using
      (derivation_sound d (M := M) (ρ := fun v => nomatch v) (by intro τ v; nomatch v))
  exact le_antisymm le_top hs

end IntuitionisticSoundness

end Mettapedia.Logic.HOL
