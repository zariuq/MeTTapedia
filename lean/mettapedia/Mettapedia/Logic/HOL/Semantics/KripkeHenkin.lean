import Mettapedia.Logic.HOL.Syntax.Closed
import Mettapedia.Logic.HOL.IntuitionisticWorld
import Mettapedia.Logic.HOL.WorldEquality

/-!
# Substitutional Kripke-Henkin semantics

This file defines the EM-free Kripke-Henkin semantic interface used by the
intuitionistic completeness route.  It is intentionally independent of canonical
theories: a model supplies worlds, a preorder, monotone atomic and equality
valuation, syntactic equality congruence/extensionality laws, and a forcing
relation satisfying the substitutional Kripke clauses.
-/

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

open Mettapedia.Logic.HOL.WithParams

/-- A substitutional Kripke-Henkin structure for closed HOL formulas.  The class
does not mention theories; canonical worlds are only one later instance of this
interface. -/
structure KripkeHenkin (Base : Type u) (Const : Ty Base → Type v) where
  World : Type w
  le : World → World → Prop
  le_refl : ∀ W, le W W
  le_trans : ∀ {U V W}, le U V → le V W → le U W
  atom : World → ClosedFormula Const → Prop
  atom_mono :
    ∀ {U V : World} {φ : ClosedFormula Const}, le U V → atom U φ → atom V φ
  eqVal : {τ : Ty Base} → World → ClosedTerm Const τ → ClosedTerm Const τ → Prop
  eq_mono :
    ∀ {τ : Ty Base} {U V : World} {s t : ClosedTerm Const τ},
      le U V → eqVal U s t → eqVal V s t
  eq_refl : ∀ {τ : Ty Base} (W : World) (t : ClosedTerm Const τ), eqVal W t t
  eq_symm :
    ∀ {τ : Ty Base} {W : World} {s t : ClosedTerm Const τ},
      eqVal W s t → eqVal W t s
  eq_trans :
    ∀ {τ : Ty Base} {W : World} {r s t : ClosedTerm Const τ},
      eqVal W r s → eqVal W s t → eqVal W r t
  eq_app_congr :
    ∀ {σ τ : Ty Base} {W : World}
      {f g : ClosedTerm Const (σ ⇒ τ)} {s t : ClosedTerm Const σ},
      eqVal W f g → eqVal W s t → eqVal W (.app f s) (.app g t)
  eq_funext :
    ∀ {σ τ : Ty Base} {W : World} {f g : ClosedTerm Const (σ ⇒ τ)},
      (∀ t : ClosedTerm Const σ, eqVal W (.app f t) (.app g t)) →
        eqVal W f g
  eq_beta :
    ∀ {σ τ : Ty Base} {W : World}
      (t : ClosedTerm Const σ) (u : Term Const [σ] τ),
      eqVal W (.app (.lam u) t) (instantiate (Base := Base) t u)
  eq_eta :
    ∀ {σ τ : Ty Base} {W : World} (f : ClosedTerm Const (σ ⇒ τ)),
      eqVal W
        (.lam (.app (weaken (Base := Base) (Const := Const) (σ := σ) f) (.var .vz)))
        f
  forces : World → ClosedFormula Const → Prop
  forces_mono :
    ∀ {U V : World} {φ : ClosedFormula Const}, le U V → forces U φ → forces V φ
  forces_atom_const :
    ∀ {W : World} (c : Const propTy),
      forces W (.const c : ClosedFormula Const) ↔
        atom W (.const c : ClosedFormula Const)
  forces_atom_app :
    ∀ {W : World} {σ : Ty Base}
      (f : ClosedTerm Const (σ ⇒ propTy)) (t : ClosedTerm Const σ),
      forces W (.app f t : ClosedFormula Const) ↔
        atom W (.app f t : ClosedFormula Const)
  forces_top :
    ∀ {W : World}, forces W (.top : ClosedFormula Const)
  forces_bot :
    ∀ {W : World}, ¬ forces W (.bot : ClosedFormula Const)
  forces_and :
    ∀ {W : World} {φ ψ : ClosedFormula Const},
      forces W (.and φ ψ) ↔ forces W φ ∧ forces W ψ
  forces_or :
    ∀ {W : World} {φ ψ : ClosedFormula Const},
      forces W (.or φ ψ) ↔ forces W φ ∨ forces W ψ
  forces_imp :
    ∀ {W : World} {φ ψ : ClosedFormula Const},
      forces W (.imp φ ψ) ↔
        ∀ V, le W V → forces V φ → forces V ψ
  forces_not :
    ∀ {W : World} {φ : ClosedFormula Const},
      forces W (.not φ) ↔ ∀ V, le W V → ¬ forces V φ
  forces_eq :
    ∀ {W : World} {τ : Ty Base} {s t : ClosedTerm Const τ},
      forces W (.eq s t : ClosedFormula Const) ↔ eqVal W s t
  eq_prop_intro :
    ∀ {W : World} {p q : ClosedFormula Const},
      forces W (.imp p q) → forces W (.imp q p) → eqVal W p q
  eq_prop_elim_left :
    ∀ {W : World} {p q : ClosedFormula Const},
      eqVal W p q → forces W (.imp p q)
  eq_prop_elim_right :
    ∀ {W : World} {p q : ClosedFormula Const},
      eqVal W p q → forces W (.imp q p)
  forces_all :
    ∀ {W : World} {σ : Ty Base} {φ : Formula Const [σ]},
      forces W (.all φ : ClosedFormula Const) ↔
        ∀ V, le W V → ∀ t : ClosedTerm Const σ,
          forces V (instantiate (Base := Base) t φ)
  forces_ex :
    ∀ {W : World} {σ : Ty Base} {φ : Formula Const [σ]},
      forces W (.ex φ : ClosedFormula Const) ↔
        ∃ t : ClosedTerm Const σ, ∀ V, le W V →
          forces V (instantiate (Base := Base) t φ)

namespace KripkeHenkin

/-- Forcing is monotone along the Kripke preorder. -/
theorem forcing_mono (M : KripkeHenkin.{u, v, w} Base Const)
    {W V : M.World} {φ : ClosedFormula Const}
    (hWV : M.le W V) (hφ : M.forces W φ) :
    M.forces V φ :=
  M.forces_mono hWV hφ

/-- A syntactic closed-term environment for a HOL context. -/
abbrev ClosedEnv (Const : Ty Base → Type v) (Γ : Ctx Base) :=
  Subst Const Γ []

namespace ClosedEnv

/-- The unique closed environment for the empty context. -/
def empty : ClosedEnv (Base := Base) Const [] :=
  fun {_τ} v => by cases v

/-- Closed terms ignore the chosen environment for the empty context. -/
@[simp] theorem subst_empty (ρ : ClosedEnv (Base := Base) Const [])
    (t : ClosedTerm Const τ) :
    subst (Base := Base) (Const := Const) ρ t = t := by
  calc
    subst (Base := Base) (Const := Const) ρ t =
        subst (Base := Base) (Const := Const)
          (Subst.id (Base := Base) (Const := Const) (Γ := [])) t := by
          apply subst_ext
          intro τ v
          cases v
    _ = t := subst_id (Base := Base) (Const := Const) t

/-- Extend a closed environment with a closed term for the newest variable. -/
def extend (ρ : ClosedEnv (Base := Base) Const Γ) (t : ClosedTerm Const σ) :
    ClosedEnv (Base := Base) Const (σ :: Γ)
  | _, .vz => t
  | _, .vs v => ρ v

@[simp] theorem extend_vz (ρ : ClosedEnv (Base := Base) Const Γ) (t : ClosedTerm Const σ) :
    extend (Base := Base) (Const := Const) ρ t (.vz : Var (σ :: Γ) σ) = t := rfl

@[simp] theorem extend_vs (ρ : ClosedEnv (Base := Base) Const Γ)
    (t : ClosedTerm Const σ) (v : Var Γ τ) :
    extend (Base := Base) (Const := Const) ρ t (.vs v : Var (σ :: Γ) τ) = ρ v := rfl

@[simp] theorem subst_weaken_extend
    (ρ : ClosedEnv (Base := Base) Const Γ) (t : ClosedTerm Const σ)
    (φ : Formula Const Γ) :
    subst (extend (Base := Base) (Const := Const) ρ t)
        (weaken (Base := Base) (Const := Const) (σ := σ) φ) =
      subst ρ φ := by
  unfold weaken
  calc
    subst (extend (Base := Base) (Const := Const) ρ t)
        (rename (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ)) φ) =
      subst
        (fun {τ} v =>
          extend (Base := Base) (Const := Const) ρ t
            (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ) v)) φ := by
        simpa using
          (subst_rename (Base := Base) (Const := Const)
            (σs := extend (Base := Base) (Const := Const) ρ t)
            (ρ := Rename.weaken (Base := Base) (Γ := Γ) (σ := σ))
            (t := φ))
    _ = subst ρ φ := by
      apply subst_ext
      intro τ v
      rfl

@[simp] theorem subst_instantiate
    (ρ : ClosedEnv (Base := Base) Const Γ) (t : Term Const Γ σ)
    (u : Term Const (σ :: Γ) τ) :
    subst ρ (instantiate (Base := Base) t u) =
      subst (extend (Base := Base) (Const := Const) ρ (subst ρ t)) u := by
  unfold instantiate
  calc
    subst ρ (subst (Subst.single (Base := Base) (Const := Const) t) u) =
      subst
        (Subst.comp ρ (Subst.single (Base := Base) (Const := Const) t)) u := by
        exact subst_comp (Base := Base) (Const := Const)
          (τs := ρ) (σs := Subst.single (Base := Base) (Const := Const) t) (t := u)
    _ = subst (extend (Base := Base) (Const := Const) ρ (subst ρ t)) u := by
      apply subst_ext
      intro τ v
      cases v <;> rfl

@[simp] theorem instantiate_subst_lift_extend
    (ρ : ClosedEnv (Base := Base) Const Γ) (t : ClosedTerm Const σ)
    (u : Term Const (σ :: Γ) τ) :
    instantiate (Base := Base) t
        (subst (Subst.lift (Base := Base) (Const := Const) (σ := σ) ρ) u) =
      subst (extend (Base := Base) (Const := Const) ρ t) u := by
  unfold instantiate
  calc
    subst (Subst.single (Base := Base) (Const := Const) t)
        (subst (Subst.lift (Base := Base) (Const := Const) (σ := σ) ρ) u) =
      subst
        (Subst.comp (Subst.single (Base := Base) (Const := Const) t)
          (Subst.lift (Base := Base) (Const := Const) (σ := σ) ρ)) u := by
        exact subst_comp (Base := Base) (Const := Const)
          (τs := Subst.single (Base := Base) (Const := Const) t)
          (σs := Subst.lift (Base := Base) (Const := Const) (σ := σ) ρ)
          (t := u)
    _ = subst (extend (Base := Base) (Const := Const) ρ t) u := by
      apply subst_ext
      intro τ v
      cases v with
      | vz =>
          rfl
      | vs v =>
          exact instantiate_weaken (Base := Base) (Const := Const) (σ := σ)
            (t := t) (u := ρ v)

@[simp] theorem subst_extend_empty
    (t : ClosedTerm Const σ) (u : Term Const [σ] τ) :
    subst (extend (Base := Base) (Const := Const)
        (empty (Base := Base) (Const := Const)) t) u =
      instantiate (Base := Base) t u := by
  unfold instantiate
  apply subst_ext
  intro τ v
  cases v with
  | vz => rfl
  | vs v => cases v

@[simp] theorem subst_instantiate_lift
    (ρ : ClosedEnv (Base := Base) Const Γ) (t : Term Const Γ σ)
    (u : Term Const (σ :: Γ) τ) :
    subst ρ (instantiate (Base := Base) t u) =
      instantiate (Base := Base) (subst ρ t)
        (subst (Subst.lift (Base := Base) (Const := Const) (σ := σ) ρ) u) := by
  rw [subst_instantiate, instantiate_subst_lift_extend]

end ClosedEnv

/-- Force an open formula by first closing it with a closed-term environment. -/
def ForcesAt (M : KripkeHenkin.{u, v, w} Base Const)
    {Γ : Ctx Base} (W : M.World) (ρ : ClosedEnv (Base := Base) Const Γ)
    (φ : Formula Const Γ) : Prop :=
  M.forces W (subst ρ φ)

/-- A list of open hypotheses is forced under a closed-term environment. -/
def ForcesHyps (M : KripkeHenkin.{u, v, w} Base Const)
    {Γ : Ctx Base} (W : M.World) (ρ : ClosedEnv (Base := Base) Const Γ)
    (Δ : List (Formula Const Γ)) : Prop :=
  ∀ φ, φ ∈ Δ → ForcesAt M W ρ φ

theorem forcesAt_mono (M : KripkeHenkin.{u, v, w} Base Const)
    {Γ : Ctx Base} {W V : M.World} {ρ : ClosedEnv (Base := Base) Const Γ}
    {φ : Formula Const Γ} (hWV : M.le W V)
    (hφ : ForcesAt M W ρ φ) :
    ForcesAt M V ρ φ :=
  M.forces_mono hWV hφ

theorem forcesHyps_mono (M : KripkeHenkin.{u, v, w} Base Const)
    {Γ : Ctx Base} {W V : M.World} {ρ : ClosedEnv (Base := Base) Const Γ}
    {Δ : List (Formula Const Γ)} (hWV : M.le W V)
    (hΔ : ForcesHyps M W ρ Δ) :
    ForcesHyps M V ρ Δ := by
  intro φ hφ
  exact forcesAt_mono M hWV (hΔ φ hφ)

theorem forcesHyps_cons (M : KripkeHenkin.{u, v, w} Base Const)
    {Γ : Ctx Base} {W : M.World} {ρ : ClosedEnv (Base := Base) Const Γ}
    {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (hφ : ForcesAt M W ρ φ) (hΔ : ForcesHyps M W ρ Δ) :
    ForcesHyps M W ρ (φ :: Δ) := by
  intro ψ hψ
  rw [List.mem_cons] at hψ
  rcases hψ with rfl | hψ
  · exact hφ
  · exact hΔ ψ hψ

theorem forcesHyps_tail (M : KripkeHenkin.{u, v, w} Base Const)
    {Γ : Ctx Base} {W : M.World} {ρ : ClosedEnv (Base := Base) Const Γ}
    {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (hΔ : ForcesHyps M W ρ (φ :: Δ)) :
    ForcesHyps M W ρ Δ := by
  intro ψ hψ
  exact hΔ ψ (List.mem_cons.mpr (.inr hψ))

theorem forcesHyps_weaken_extend (M : KripkeHenkin.{u, v, w} Base Const)
    {Γ : Ctx Base} {W : M.World} {ρ : ClosedEnv (Base := Base) Const Γ}
    {Δ : List (Formula Const Γ)} (hΔ : ForcesHyps M W ρ Δ)
    (t : ClosedTerm Const σ) :
    ForcesHyps M W (ClosedEnv.extend (Base := Base) (Const := Const) ρ t)
      (weakenHyps (Base := Base) (Const := Const) (σ := σ) Δ) := by
  intro φ hφ
  rcases List.mem_map.mp hφ with ⟨ψ, hψ, rfl⟩
  simpa [ForcesAt] using hΔ ψ hψ

/-- Soundness of the EM-free extensional derivation calculus for every
substitutional Kripke-Henkin structure.  The metatheory is Lean's classical
environment when downstream construction uses choice; the object calculus here
contains no excluded-middle schema. -/
theorem extDerivation_sound
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (d : ExtDerivation Const Δ φ) :
    ∀ {M : KripkeHenkin.{u, v, w} Base Const} {W : M.World}
      {ρ : ClosedEnv (Base := Base) Const Γ},
      ForcesHyps M W ρ Δ → ForcesAt M W ρ φ := by
  induction d with
  | hyp hmem =>
      intro M W ρ hΔ
      exact hΔ _ hmem
  | topI =>
      intro M W ρ hΔ
      simpa [ForcesAt, subst] using (M.forces_top (W := W))
  | botE h ih =>
      intro M W ρ hΔ
      have hbot : M.forces W (.bot : ClosedFormula Const) := by
        simpa [ForcesAt, subst] using ih (M := M) (W := W) (ρ := ρ) hΔ
      exact False.elim (M.forces_bot hbot)
  | andI hφ hψ ihφ ihψ =>
      intro M W ρ hΔ
      have hφ' := ihφ (M := M) (W := W) (ρ := ρ) hΔ
      have hψ' := ihψ (M := M) (W := W) (ρ := ρ) hΔ
      simpa [ForcesAt, subst] using
        (M.forces_and (W := W) (φ := subst ρ _) (ψ := subst ρ _)).mpr
          ⟨hφ', hψ'⟩
  | andEL h ih =>
      intro M W ρ hΔ
      have hand := ih (M := M) (W := W) (ρ := ρ) hΔ
      exact (M.forces_and.mp (by simpa [ForcesAt, subst] using hand)).1
  | andER h ih =>
      intro M W ρ hΔ
      have hand := ih (M := M) (W := W) (ρ := ρ) hΔ
      exact (M.forces_and.mp (by simpa [ForcesAt, subst] using hand)).2
  | orIL h ih =>
      intro M W ρ hΔ
      have hφ := ih (M := M) (W := W) (ρ := ρ) hΔ
      simpa [ForcesAt, subst] using
        (M.forces_or (W := W) (φ := subst ρ _) (ψ := subst ρ _)).mpr (.inl hφ)
  | orIR h ih =>
      intro M W ρ hΔ
      have hψ := ih (M := M) (W := W) (ρ := ρ) hΔ
      simpa [ForcesAt, subst] using
        (M.forces_or (W := W) (φ := subst ρ _) (ψ := subst ρ _)).mpr (.inr hψ)
  | orE hor hφ hψ ihor ihφ ihψ =>
      intro M W ρ hΔ
      have hor' := ihor (M := M) (W := W) (ρ := ρ) hΔ
      rcases M.forces_or.mp (by simpa [ForcesAt, subst] using hor') with hleft | hright
      · exact ihφ (M := M) (W := W) (ρ := ρ)
          (forcesHyps_cons M (by simpa [ForcesAt] using hleft) hΔ)
      · exact ihψ (M := M) (W := W) (ρ := ρ)
          (forcesHyps_cons M (by simpa [ForcesAt] using hright) hΔ)
  | impI h ih =>
      intro M W ρ hΔ
      apply (M.forces_imp (W := W) (φ := subst ρ _) (ψ := subst ρ _)).mpr
      intro V hWV hφ
      exact ih (M := M) (W := V) (ρ := ρ)
        (forcesHyps_cons M (by simpa [ForcesAt] using hφ)
          (forcesHyps_mono M hWV hΔ))
  | impE himp hφ ihimp ihφ =>
      intro M W ρ hΔ
      have himp' := ihimp (M := M) (W := W) (ρ := ρ) hΔ
      have hφ' := ihφ (M := M) (W := W) (ρ := ρ) hΔ
      exact M.forces_imp.mp (by simpa [ForcesAt, subst] using himp') W (M.le_refl W) hφ'
  | notI h ih =>
      intro M W ρ hΔ
      apply (M.forces_not (W := W) (φ := subst ρ _)).mpr
      intro V hWV hφ
      have hbot := ih (M := M) (W := V) (ρ := ρ)
        (forcesHyps_cons M (by simpa [ForcesAt] using hφ)
          (forcesHyps_mono M hWV hΔ))
      exact M.forces_bot (by simpa [ForcesAt, subst] using hbot)
  | notE hnot hφ ihnot ihφ =>
      intro M W ρ hΔ
      have hnot' := ihnot (M := M) (W := W) (ρ := ρ) hΔ
      have hφ' := ihφ (M := M) (W := W) (ρ := ρ) hΔ
      exact False.elim
        (M.forces_not.mp (by simpa [ForcesAt, subst] using hnot') W (M.le_refl W) hφ')
  | allI h ih =>
      intro M W ρ hΔ
      apply (M.forces_all (W := W) (φ := subst (Subst.lift ρ) _)).mpr
      intro V hWV t
      have hbody := ih (M := M) (W := V)
        (ρ := ClosedEnv.extend (Base := Base) (Const := Const) ρ t)
        (forcesHyps_weaken_extend M (forcesHyps_mono M hWV hΔ) t)
      simpa [ForcesAt, subst, ClosedEnv.instantiate_subst_lift_extend] using hbody
  | allE t h ih =>
      intro M W ρ hΔ
      have hall := ih (M := M) (W := W) (ρ := ρ) hΔ
      have hinst :=
        M.forces_all.mp (by simpa [ForcesAt, subst] using hall)
          W (M.le_refl W) (subst ρ t)
      simpa [ForcesAt, ClosedEnv.subst_instantiate,
        ClosedEnv.instantiate_subst_lift_extend] using hinst
  | exI t h ih =>
      intro M W ρ hΔ
      apply (M.forces_ex (W := W) (φ := subst (Subst.lift ρ) _)).mpr
      refine ⟨subst ρ t, ?_⟩
      intro V hWV
      have hbodyW := ih (M := M) (W := W) (ρ := ρ) hΔ
      have hbodyV := forcesAt_mono M hWV hbodyW
      simpa [ForcesAt, ClosedEnv.subst_instantiate,
        ClosedEnv.instantiate_subst_lift_extend] using hbodyV
  | exE hex hbody ihex ihbody =>
      intro M W ρ hΔ
      have hex' := ihex (M := M) (W := W) (ρ := ρ) hΔ
      rcases M.forces_ex.mp (by simpa [ForcesAt, subst] using hex') with ⟨t, ht⟩
      have hψ := ihbody (M := M) (W := W)
        (ρ := ClosedEnv.extend (Base := Base) (Const := Const) ρ t)
        (forcesHyps_cons M
          (by
            simpa [ForcesAt, ClosedEnv.instantiate_subst_lift_extend, Subst.lift]
              using ht W (M.le_refl W))
          (forcesHyps_weaken_extend M hΔ t))
      simpa [ForcesAt] using hψ
  | eqRefl t =>
      intro M W ρ hΔ
      simpa [ForcesAt, subst] using
        (M.forces_eq (W := W) (s := subst ρ t) (t := subst ρ t)).mpr
          (M.eq_refl W (subst ρ t))
  | eqSymm h ih =>
      intro M W ρ hΔ
      have heq := ih (M := M) (W := W) (ρ := ρ) hΔ
      exact (M.forces_eq).mpr (M.eq_symm ((M.forces_eq).mp (by simpa [ForcesAt, subst] using heq)))
  | eqTrans htu huv ihtu ihuv =>
      intro M W ρ hΔ
      have htu' := ihtu (M := M) (W := W) (ρ := ρ) hΔ
      have huv' := ihuv (M := M) (W := W) (ρ := ρ) hΔ
      exact (M.forces_eq).mpr
        (M.eq_trans ((M.forces_eq).mp (by simpa [ForcesAt, subst] using htu'))
          ((M.forces_eq).mp (by simpa [ForcesAt, subst] using huv')))
  | eqPropI hpq hqp ihpq ihqp =>
      intro M W ρ hΔ
      have hpq' := ihpq (M := M) (W := W) (ρ := ρ) hΔ
      have hqp' := ihqp (M := M) (W := W) (ρ := ρ) hΔ
      exact (M.forces_eq).mpr
        (M.eq_prop_intro (by simpa [ForcesAt, subst] using hpq')
          (by simpa [ForcesAt, subst] using hqp'))
  | eqPropEL hpq ihpq =>
      intro M W ρ hΔ
      have hpq' := ihpq (M := M) (W := W) (ρ := ρ) hΔ
      exact M.eq_prop_elim_left ((M.forces_eq).mp (by simpa [ForcesAt, subst] using hpq'))
  | eqPropER hpq ihpq =>
      intro M W ρ hΔ
      have hpq' := ihpq (M := M) (W := W) (ρ := ρ) hΔ
      exact M.eq_prop_elim_right ((M.forces_eq).mp (by simpa [ForcesAt, subst] using hpq'))
  | eqApp t h ih =>
      intro M W ρ hΔ
      have hf := ih (M := M) (W := W) (ρ := ρ) hΔ
      exact (M.forces_eq).mpr
        (M.eq_app_congr ((M.forces_eq).mp (by simpa [ForcesAt, subst] using hf))
          (M.eq_refl W (subst ρ t)))
  | eqAppArg f h ih =>
      intro M W ρ hΔ
      have ht := ih (M := M) (W := W) (ρ := ρ) hΔ
      exact (M.forces_eq).mpr
        (M.eq_app_congr (M.eq_refl W (subst ρ f))
          ((M.forces_eq).mp (by simpa [ForcesAt, subst] using ht)))
  | eqLam h ih =>
      intro M W ρ hΔ
      apply (M.forces_eq).mpr
      apply M.eq_funext
      intro t
      have hbody := ih (M := M) (W := W)
        (ρ := ClosedEnv.extend (Base := Base) (Const := Const) ρ t)
        (forcesHyps_weaken_extend M hΔ t)
      have hbodyEq :=
        (M.forces_eq).mp (by simpa [ForcesAt, subst] using hbody)
      exact M.eq_trans
        (M.eq_beta (W := W) t (subst (Subst.lift ρ) _))
        (M.eq_trans
          (by
            convert hbodyEq using 1
            · exact (ClosedEnv.instantiate_subst_lift_extend
                (Base := Base) (Const := Const) (ρ := ρ) (t := t) (u := _))
            · exact (ClosedEnv.instantiate_subst_lift_extend
                (Base := Base) (Const := Const) (ρ := ρ) (t := t) (u := _)))
          (M.eq_symm (M.eq_beta (W := W) t (subst (Subst.lift ρ) _))))
  | funExt h ih =>
      intro M W ρ hΔ
      apply (M.forces_eq).mpr
      apply M.eq_funext
      intro t
      have hall := ih (M := M) (W := W) (ρ := ρ) hΔ
      have hpoint :=
        M.forces_all.mp (by simpa [ForcesAt, subst] using hall)
          W (M.le_refl W) t
      exact (M.forces_eq).mp
        (by
          convert hpoint using 1
          simp [instantiate, subst, Subst.single, Subst.lift]
          constructor
          · exact (instantiate_weaken (Base := Base) (Const := Const)
              (t := t) (u := subst ρ _)).symm
          · exact (instantiate_weaken (Base := Base) (Const := Const)
              (t := t) (u := subst ρ _)).symm)
  | beta t u =>
      intro M W ρ hΔ
      exact (M.forces_eq).mpr
        (by
          convert (M.eq_beta (W := W) (subst ρ t) (subst (Subst.lift ρ) u)) using 1
          · simp [subst]
          · exact ClosedEnv.subst_instantiate_lift
              (Base := Base) (Const := Const) (ρ := ρ) (t := t) (u := u))
  | eta f =>
      intro M W ρ hΔ
      exact (M.forces_eq).mpr
        (by
          simpa [ForcesAt, subst, ClosedEnv.subst_weaken_extend, Subst.lift] using
            (M.eq_eta (W := W) (subst ρ f)))

/-- A closed formula is valid in a substitutional Kripke-Henkin structure when
all worlds force it. -/
def ValidIn (M : KripkeHenkin.{u, v, w} Base Const) (φ : ClosedFormula Const) : Prop :=
  ∀ W, M.forces W φ

/-- Semantic consequence over a class of substitutional Kripke-Henkin
structures. -/
def Consequence (T : ClosedTheorySet Const) (φ : ClosedFormula Const) : Prop :=
  ∀ (M : KripkeHenkin.{u, v, w} Base Const) (W : M.World),
    (∀ {ψ : ClosedFormula Const}, ψ ∈ T → M.forces W ψ) →
      M.forces W φ

/-- EM-free closed derivability is sound for semantic consequence over every
substitutional Kripke-Henkin structure. -/
theorem consequence_of_provable
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (hφ : ClosedTheorySet.Provable (Const := Const) T φ) :
    Consequence.{u, v, w} (Base := Base) (Const := Const) T φ := by
  rcases hφ with ⟨Γ, hΓ, d⟩
  intro M W hT
  let ρ : ClosedEnv (Base := Base) Const [] :=
    ClosedEnv.empty (Base := Base) (Const := Const)
  have hClosed : subst (Base := Base) (Const := Const) ρ φ = φ :=
    ClosedEnv.subst_empty (Base := Base) (Const := Const) ρ φ
  simpa [ForcesAt, hClosed] using
    (extDerivation_sound (Base := Base) (Const := Const) d
      (M := M) (W := W) (ρ := ρ)
      (by
        intro ψ hψ
        have hψClosed : subst (Base := Base) (Const := Const) ρ ψ = ψ :=
          ClosedEnv.subst_empty (Base := Base) (Const := Const) ρ ψ
        simpa [ForcesAt, hψClosed] using hT (hΓ ψ hψ)))

/-- A closed EM-free derivation from the empty theory is forced at every world
of every substitutional Kripke-Henkin structure. -/
theorem forces_of_provable_empty
    {φ : ClosedFormula Const}
    (hφ : ClosedTheorySet.Provable (Const := Const) (∅ : ClosedTheorySet Const) φ)
    (M : KripkeHenkin.{u, v, w} Base Const) (W : M.World) :
    M.forces W φ := by
  rcases hφ with ⟨Γ, hΓ, d⟩
  let ρ : ClosedEnv (Base := Base) Const [] := fun {_τ} v => by cases v
  have hClosed :
      subst (Base := Base) (Const := Const) ρ φ = φ := by
    calc
      subst (Base := Base) (Const := Const) ρ φ =
          subst (Base := Base) (Const := Const)
            (Subst.id (Base := Base) (Const := Const) (Γ := [])) φ := by
            apply subst_ext
            intro τ v
            cases v
      _ = φ := subst_id (Base := Base) (Const := Const) φ
  simpa [ForcesAt, hClosed] using
    (extDerivation_sound (Base := Base) (Const := Const) d
      (M := M) (W := W) (ρ := ρ)
      (by
        intro ψ hψ
        exact False.elim (hΓ ψ hψ)))

/-- A single Kripke-Henkin counterworld refutes empty-theory EM-free
derivability. -/
theorem not_provable_empty_of_countermodel
    {φ : ClosedFormula Const}
    (M : KripkeHenkin.{u, v, w} Base Const) (W : M.World)
    (hφ : ¬ M.forces W φ) :
    ¬ ClosedTheorySet.Provable (Const := Const) (∅ : ClosedTheorySet Const) φ := by
  intro hProv
  exact hφ (forces_of_provable_empty (Base := Base) (Const := Const) hProv M W)

/-- The closed excluded-middle instance for a formula.  This is a semantic
canary for the EM-free calculus: valid structures must not force this merely by
definition. -/
def excludedMiddle (φ : ClosedFormula Const) : ClosedFormula Const :=
  .or φ (.not φ)

/-- The excluded-middle instance for a propositional constant. -/
def excludedMiddleConst (c : Const propTy) : ClosedFormula Const :=
  excludedMiddle (Base := Base) (.const c : ClosedFormula Const)

/-- Data for the excluded-middle canary: a root world where `φ` is not yet
forced and an accessible future world where `φ` is forced.  A concrete
two-world instance of this structure is the remaining negative canary model. -/
structure ExcludedMiddleCountermodel (φ : ClosedFormula Const) where
  M : KripkeHenkin.{u, v, w} Base Const
  root : M.World
  not_now : ¬ M.forces root φ
  later : ∃ V : M.World, M.le root V ∧ M.forces V φ

/-- If a formula is not forced at a world but becomes forced at an accessible
future world, excluded middle for that formula is not forced at the original
world. -/
theorem not_forces_excludedMiddle_of_eventual_counterexample
    (M : KripkeHenkin.{u, v, w} Base Const) {W : M.World}
    {φ : ClosedFormula Const}
    (hNow : ¬ M.forces W φ)
    (hLater : ∃ V : M.World, M.le W V ∧ M.forces V φ) :
    ¬ M.forces W (excludedMiddle (Base := Base) (Const := Const) φ) := by
  intro hEM
  rcases (M.forces_or).mp hEM with hφ | hnφ
  · exact hNow hφ
  · obtain ⟨V, hWV, hφV⟩ := hLater
    exact (M.forces_not.mp hnφ V hWV) hφV

/-- A growing-world counterexample refutes validity of the corresponding
excluded-middle instance in that structure. -/
theorem not_validIn_excludedMiddle_of_eventual_counterexample
    (M : KripkeHenkin.{u, v, w} Base Const) {W : M.World}
    {φ : ClosedFormula Const}
    (hNow : ¬ M.forces W φ)
    (hLater : ∃ V : M.World, M.le W V ∧ M.forces V φ) :
    ¬ ValidIn (Base := Base) (Const := Const) M
        (excludedMiddle (Base := Base) (Const := Const) φ) := by
  intro hValid
  exact not_forces_excludedMiddle_of_eventual_counterexample
    (Base := Base) (Const := Const) M hNow hLater (hValid W)

/-- A growing-world counterexample refutes semantic consequence from the empty
theory for the corresponding excluded-middle instance. -/
theorem not_consequence_empty_excludedMiddle_of_eventual_counterexample
    (M : KripkeHenkin.{u, v, w} Base Const) {W : M.World}
    {φ : ClosedFormula Const}
    (hNow : ¬ M.forces W φ)
    (hLater : ∃ V : M.World, M.le W V ∧ M.forces V φ) :
    ¬ Consequence.{u, v, w} (Base := Base) (Const := Const)
        (∅ : ClosedTheorySet Const)
        (excludedMiddle (Base := Base) (Const := Const) φ) := by
  intro hSem
  exact not_forces_excludedMiddle_of_eventual_counterexample
    (Base := Base) (Const := Const) M hNow hLater
    (hSem M W (by intro ψ hψ; cases hψ))

/-- A growing-world counterexample is already enough to refute EM-free
empty-theory derivability of that excluded-middle instance. -/
theorem not_provable_empty_excludedMiddle_of_eventual_counterexample
    (M : KripkeHenkin.{u, v, w} Base Const) {W : M.World}
    {φ : ClosedFormula Const}
    (hNow : ¬ M.forces W φ)
    (hLater : ∃ V : M.World, M.le W V ∧ M.forces V φ) :
    ¬ ClosedTheorySet.Provable (Const := Const) (∅ : ClosedTheorySet Const)
        (excludedMiddle (Base := Base) (Const := Const) φ) := by
  exact not_provable_empty_of_countermodel
    (Base := Base) (Const := Const) M W
    (not_forces_excludedMiddle_of_eventual_counterexample
      (Base := Base) (Const := Const) M hNow hLater)

/-- Countermodel-package form of excluded-middle underivability. -/
theorem ExcludedMiddleCountermodel.not_provable_empty
    {φ : ClosedFormula Const} (C : ExcludedMiddleCountermodel.{u, v, w} (Base := Base) φ) :
    ¬ ClosedTheorySet.Provable (Const := Const) (∅ : ClosedTheorySet Const)
        (excludedMiddle (Base := Base) (Const := Const) φ) :=
  not_provable_empty_excludedMiddle_of_eventual_counterexample
    (Base := Base) (Const := Const) C.M C.not_now C.later

/-- Countermodel-package form specialized to a propositional constant. -/
theorem ExcludedMiddleCountermodel.not_provable_empty_const
    (c : Const propTy)
    (C : ExcludedMiddleCountermodel.{u, v, w} (Base := Base)
      (.const c : ClosedFormula Const)) :
    ¬ ClosedTheorySet.Provable (Const := Const) (∅ : ClosedTheorySet Const)
        (excludedMiddleConst (Base := Base) (Const := Const) c) := by
  simpa [excludedMiddleConst] using
    (ExcludedMiddleCountermodel.not_provable_empty
      (Base := Base) (Const := Const) C)

/-- Positive canary: every substitutional Kripke-Henkin structure forces
`φ → φ` at every world. -/
theorem validIn_imp_self
    (M : KripkeHenkin.{u, v, w} Base Const) (φ : ClosedFormula Const) :
    ValidIn (Base := Base) (Const := Const) M (.imp φ φ) := by
  intro W
  exact (M.forces_imp).mpr (by
    intro V _hWV hφ
    exact hφ)

/-- Semantic consequence from the empty theory for the positive `φ → φ`
canary. -/
theorem consequence_empty_imp_self (φ : ClosedFormula Const) :
    Consequence.{u, v, w} (Base := Base) (Const := Const)
      (∅ : ClosedTheorySet Const) (.imp φ φ) := by
  intro M W _hT
  exact validIn_imp_self (Base := Base) (Const := Const) M φ W

/-- Positive derivability twin for the semantic `φ → φ` canary. -/
theorem provable_empty_imp_self (φ : ClosedFormula Const) :
    ClosedTheorySet.Provable (Const := Const) (∅ : ClosedTheorySet Const) (.imp φ φ) := by
  refine ⟨[], ?_, ExtDerivation.theorem_imp_refl φ⟩
  intro ψ hψ
  cases hψ


end KripkeHenkin

end Mettapedia.Logic.HOL
