import Mettapedia.Logic.HOL.Syntax.Closed
import Mettapedia.Logic.HOL.Derivation
import Mettapedia.Logic.HOL.DerivationExtensionality
import Mettapedia.Logic.HOL.LindenbaumSet
import Mettapedia.Logic.HOL.Semantics.KripkeHenkin

/-!
# Heyting-valued substitutional models

Algebraic (Heyting-valued) semantics for the EM-free extensional calculus, in
the Rasiowa–Sikorski style: a model assigns to every closed formula a value in
a Heyting-ordered structure, compositionally on the propositional connectives,
with the quantifier values pinned by substitutional bounds (upper/lower bound
over all closed-term instances, and exactness: the quantifier value is the
best such bound).  Equality is constrained by inequational forms of the
extensionality rules.

This class avoids the impredicative truth-lemma obstruction (DeMarco–Lipton
2005): no interpretation is defined by recursion on formulas — instances
supply the whole valuation, and the Lindenbaum term model supplies it
syntactically, with quantifier exactness furnished by the fresh-parameter
generalization lemma.
-/

namespace Mettapedia.Logic.HOL
namespace HeytingSem

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-- A Heyting-valued substitutional model of the EM-free calculus. -/
structure HeytingGeneralModel (Base : Type u) (Const : Ty Base → Type v) where
  Ω : Type w
  le : Ω → Ω → Prop
  le_refl : ∀ a, le a a
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  top : Ω
  bot : Ω
  inf : Ω → Ω → Ω
  sup : Ω → Ω → Ω
  himp : Ω → Ω → Ω
  le_top : ∀ a, le a top
  bot_le : ∀ a, le bot a
  inf_le_left : ∀ a b, le (inf a b) a
  inf_le_right : ∀ a b, le (inf a b) b
  le_inf : ∀ {a b c}, le a b → le a c → le a (inf b c)
  le_sup_left : ∀ a b, le a (sup a b)
  le_sup_right : ∀ a b, le b (sup a b)
  sup_le : ∀ {a b c}, le a c → le b c → le (sup a b) c
  himp_adjoint_mp : ∀ {a b c}, le a (himp b c) → le (inf a b) c
  himp_adjoint_intro : ∀ {a b c}, le (inf a b) c → le a (himp b c)
  inf_sup_distrib :
    ∀ a b c, le (inf a (sup b c)) (sup (inf a b) (inf a c))
  val : ClosedFormula Const → Ω
  val_top : val (.top : ClosedFormula Const) = top
  val_bot : val (.bot : ClosedFormula Const) = bot
  val_and : ∀ φ ψ : ClosedFormula Const, val (.and φ ψ) = inf (val φ) (val ψ)
  val_or : ∀ φ ψ : ClosedFormula Const, val (.or φ ψ) = sup (val φ) (val ψ)
  val_imp : ∀ φ ψ : ClosedFormula Const, val (.imp φ ψ) = himp (val φ) (val ψ)
  val_not_le : ∀ φ : ClosedFormula Const, le (val (.not φ)) (himp (val φ) bot)
  le_val_not : ∀ φ : ClosedFormula Const, le (himp (val φ) bot) (val (.not φ))
  val_all_le :
    ∀ {σ : Ty Base} (φ : Formula Const [σ]) (t : ClosedTerm Const σ),
      le (val (.all φ)) (val (instantiate (Base := Base) t φ))
  le_val_all :
    ∀ {σ : Ty Base} (φ : Formula Const [σ]) (ω : Ω),
      (∀ t : ClosedTerm Const σ, le ω (val (instantiate (Base := Base) t φ))) →
        le ω (val (.all φ))
  val_ex_le :
    ∀ {σ : Ty Base} (φ : Formula Const [σ]) (ω : Ω),
      (∀ t : ClosedTerm Const σ, le (val (instantiate (Base := Base) t φ)) ω) →
        le (val (.ex φ)) ω
  le_val_ex :
    ∀ {σ : Ty Base} (φ : Formula Const [σ]) (t : ClosedTerm Const σ),
      le (val (instantiate (Base := Base) t φ)) (val (.ex φ))
  val_eq_refl :
    ∀ {τ : Ty Base} (t : ClosedTerm Const τ), le top (val (.eq t t))
  val_eq_symm :
    ∀ {τ : Ty Base} (t u : ClosedTerm Const τ),
      le (val (.eq t u)) (val (.eq u t))
  val_eq_trans :
    ∀ {τ : Ty Base} (t u v : ClosedTerm Const τ),
      le (inf (val (.eq t u)) (val (.eq u v))) (val (.eq t v))
  val_eq_app :
    ∀ {σ τ : Ty Base} (f g : ClosedTerm Const (σ ⇒ τ)) (t : ClosedTerm Const σ),
      le (val (.eq f g)) (val (.eq (.app f t) (.app g t)))
  val_eq_appArg :
    ∀ {σ τ : Ty Base} (f : ClosedTerm Const (σ ⇒ τ)) (t u : ClosedTerm Const σ),
      le (val (.eq t u)) (val (.eq (.app f t) (.app f u)))
  val_eq_propI :
    ∀ (p q : ClosedFormula Const),
      le (inf (val (.imp p q)) (val (.imp q p))) (val (.eq p q))
  val_eq_propEL :
    ∀ (p q : ClosedFormula Const),
      le (val (.eq p q)) (val (.imp p q))
  val_eq_propER :
    ∀ (p q : ClosedFormula Const),
      le (val (.eq p q)) (val (.imp q p))
  val_eq_lam :
    ∀ {σ τ : Ty Base} (t u : Term Const [σ] τ) (ω : Ω),
      (∀ w : ClosedTerm Const σ,
        le ω (val (.eq (instantiate (Base := Base) w t)
          (instantiate (Base := Base) w u)))) →
        le ω (val (.eq (.lam t) (.lam u)))
  val_funExt :
    ∀ {σ τ : Ty Base} (f g : ClosedTerm Const (σ ⇒ τ)),
      le (val (.all (.eq (.app (weaken (Base := Base) (σ := σ) f) (.var .vz))
                         (.app (weaken (Base := Base) (σ := σ) g) (.var .vz)))))
        (val (.eq f g))
  val_beta :
    ∀ {σ τ : Ty Base} (t : ClosedTerm Const σ) (u : Term Const [σ] τ),
      le top (val (.eq (.app (.lam u) t) (instantiate (Base := Base) t u)))
  val_eta :
    ∀ {σ τ : Ty Base} (f : ClosedTerm Const (σ ⇒ τ)),
      le top (val (.eq (.lam (.app (weaken (Base := Base) (σ := σ) f) (.var .vz))) f))

namespace HeytingGeneralModel

variable (M : HeytingGeneralModel.{u, v, w} Base Const)

/-- The value of a list of closed hypotheses: iterated meet. -/
def hypVal : List (ClosedFormula Const) → M.Ω
  | [] => M.top
  | φ :: Δ => M.inf (M.val φ) (hypVal Δ)

theorem hypVal_le_of_mem {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} (h : φ ∈ Δ) :
    M.le (M.hypVal Δ) (M.val φ) := by
  induction Δ with
  | nil => cases h
  | cons ψ Δ ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact M.inf_le_left _ _
      · exact M.le_trans (M.inf_le_right _ _) (ih h)

theorem hypVal_mono {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    M.le (M.hypVal (φ :: Δ)) (M.hypVal Δ) :=
  M.inf_le_right _ _

theorem le_hypVal_cons {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} {ω : M.Ω}
    (hφ : M.le ω (M.val φ)) (hΔ : M.le ω (M.hypVal Δ)) :
    M.le ω (M.hypVal (φ :: Δ)) :=
  M.le_inf hφ hΔ

theorem inf_comm_le (a b : M.Ω) : M.le (M.inf a b) (M.inf b a) :=
  M.le_inf (M.inf_le_right _ _) (M.inf_le_left _ _)

theorem le_of_top_le {a b : M.Ω} (h : M.le M.top b) : M.le a b :=
  M.le_trans (M.le_top a) h

/-- Mapped weakened hypotheses collapse under an extended closing
substitution. -/
theorem map_weakenHyps_extend {Γ : Ctx Base} {σ : Ty Base}
    {Δ : List (Formula Const Γ)} (ρ : Subst Const Γ [])
    (t : ClosedTerm Const σ) :
    (weakenHyps (Base := Base) (σ := σ) Δ).map
        (subst (KripkeHenkin.ClosedEnv.extend (Base := Base) (Const := Const) ρ t)) =
      Δ.map (subst ρ) := by
  unfold weakenHyps
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro ψ _
  exact KripkeHenkin.ClosedEnv.subst_weaken_extend
    (Base := Base) (Const := Const) ρ t ψ

end HeytingGeneralModel

open HeytingGeneralModel in
/-- **Algebraic soundness**: every EM-free derivation is valid in every
Heyting-valued substitutional model, under every closing substitution. -/
theorem sound {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (d : ExtDerivation Const Δ φ) :
    ∀ (M : HeytingGeneralModel.{u, v, w} Base Const) (ρ : Subst Const Γ []),
      M.le (M.hypVal (Δ.map (subst ρ))) (M.val (subst ρ φ)) := by
  induction d with
  | hyp hmem =>
      intro M ρ
      exact M.hypVal_le_of_mem (List.mem_map_of_mem hmem)
  | topI =>
      intro M ρ
      rw [show subst ρ (.top : Formula Const _) = .top from rfl, M.val_top]
      exact M.le_top _
  | botE h ih =>
      intro M ρ
      have hb := ih M ρ
      rw [show subst ρ (.bot : Formula Const _) = .bot from rfl, M.val_bot] at hb
      exact M.le_trans hb (M.bot_le _)
  | andI hφ hψ ihφ ihψ =>
      intro M ρ
      rw [show subst ρ (.and _ _) = .and (subst ρ _) (subst ρ _) from rfl, M.val_and]
      exact M.le_inf (ihφ M ρ) (ihψ M ρ)
  | andEL h ih =>
      intro M ρ
      have hand := ih M ρ
      rw [show subst ρ (.and _ _) = .and (subst ρ _) (subst ρ _) from rfl, M.val_and] at hand
      exact M.le_trans hand (M.inf_le_left _ _)
  | andER h ih =>
      intro M ρ
      have hand := ih M ρ
      rw [show subst ρ (.and _ _) = .and (subst ρ _) (subst ρ _) from rfl, M.val_and] at hand
      exact M.le_trans hand (M.inf_le_right _ _)
  | orIL h ih =>
      intro M ρ
      rw [show subst ρ (.or _ _) = .or (subst ρ _) (subst ρ _) from rfl, M.val_or]
      exact M.le_trans (ih M ρ) (M.le_sup_left _ _)
  | orIR h ih =>
      intro M ρ
      rw [show subst ρ (.or _ _) = .or (subst ρ _) (subst ρ _) from rfl, M.val_or]
      exact M.le_trans (ih M ρ) (M.le_sup_right _ _)
  | orE hor hφ hψ ihor ihφ ihψ =>
      intro M ρ
      have hor' := ihor M ρ
      rw [show subst ρ (.or _ _) = .or (subst ρ _) (subst ρ _) from rfl, M.val_or] at hor'
      refine M.le_trans (M.le_inf (M.le_refl _) hor')
        (M.le_trans (M.inf_sup_distrib _ _ _) (M.sup_le ?_ ?_))
      · exact M.le_trans (M.inf_comm_le _ _) (ihφ M ρ)
      · exact M.le_trans (M.inf_comm_le _ _) (ihψ M ρ)
  | impI h ih =>
      intro M ρ
      rw [show subst ρ (.imp _ _) = .imp (subst ρ _) (subst ρ _) from rfl, M.val_imp]
      refine M.himp_adjoint_intro ?_
      exact M.le_trans (M.inf_comm_le _ _) (ih M ρ)
  | impE himp hφ ihimp ihφ =>
      intro M ρ
      have h1 := ihimp M ρ
      rw [show subst ρ (.imp _ _) = .imp (subst ρ _) (subst ρ _) from rfl, M.val_imp] at h1
      exact M.le_trans (M.le_inf (M.le_refl _) (ihφ M ρ)) (M.himp_adjoint_mp h1)
  | notI h ih =>
      intro M ρ
      rw [show subst ρ (.not _) = .not (subst ρ _) from rfl]
      refine M.le_trans (M.himp_adjoint_intro ?_) (M.le_val_not _)
      have hb := ih M ρ
      rw [show subst ρ (.bot : Formula Const _) = .bot from rfl, M.val_bot] at hb
      exact M.le_trans (M.inf_comm_le _ _) hb
  | notE hnot hφ ihnot ihφ =>
      intro M ρ
      have h1 := ihnot M ρ
      rw [show subst ρ (.not _) = .not (subst ρ _) from rfl] at h1
      have h1' := M.le_trans h1 (M.val_not_le _)
      rw [show subst ρ (.bot : Formula Const _) = .bot from rfl, M.val_bot]
      exact M.le_trans (M.le_inf (M.le_refl _) (ihφ M ρ)) (M.himp_adjoint_mp h1')
  | allI h ih =>
      intro M ρ
      rw [show subst ρ (.all _) = .all (subst (Subst.lift ρ) _) from rfl]
      refine M.le_val_all _ _ (fun t => ?_)
      have hbody := ih M (KripkeHenkin.ClosedEnv.extend (Base := Base) (Const := Const) ρ t)
      rw [map_weakenHyps_extend ρ t] at hbody
      rw [KripkeHenkin.ClosedEnv.instantiate_subst_lift_extend
        (Base := Base) (Const := Const) (ρ := ρ) (t := t)]
      exact hbody
  | allE t h ih =>
      intro M ρ
      have hall := ih M ρ
      rw [show subst ρ (.all _) = .all (subst (Subst.lift ρ) _) from rfl] at hall
      have hinst := M.le_trans hall (M.val_all_le (subst (Subst.lift ρ) _) (subst ρ t))
      rw [KripkeHenkin.ClosedEnv.subst_instantiate_lift
        (Base := Base) (Const := Const) (ρ := ρ) (t := t)]
      exact hinst
  | exI t h ih =>
      intro M ρ
      rw [show subst ρ (.ex _) = .ex (subst (Subst.lift ρ) _) from rfl]
      have hinst := ih M ρ
      rw [KripkeHenkin.ClosedEnv.subst_instantiate_lift
        (Base := Base) (Const := Const) (ρ := ρ) (t := t)] at hinst
      exact M.le_trans hinst (M.le_val_ex (subst (Subst.lift ρ) _) (subst ρ t))
  | exE hex hbody ihex ihbody =>
      rename_i Γ' Δ' σ' φ' ψ'
      intro M ρ
      have hex' := ihex M ρ
      rw [show subst ρ (.ex φ') = .ex (subst (Subst.lift ρ) φ') from rfl] at hex'
      have hbound : M.le (M.val (.ex (subst (Subst.lift ρ) φ')))
          (M.himp (M.hypVal (List.map (subst ρ) Δ')) (M.val (subst ρ ψ'))) := by
        refine M.val_ex_le _ _ (fun t => ?_)
        refine M.himp_adjoint_intro ?_
        have hb := ihbody M (KripkeHenkin.ClosedEnv.extend (Base := Base) (Const := Const) ρ t)
        simp only [List.map_cons] at hb
        rw [map_weakenHyps_extend ρ t] at hb
        rw [KripkeHenkin.ClosedEnv.subst_weaken_extend
          (Base := Base) (Const := Const) ρ t] at hb
        rw [KripkeHenkin.ClosedEnv.instantiate_subst_lift_extend
          (Base := Base) (Const := Const) (ρ := ρ) (t := t)]
        have hb' : M.le
            (M.inf
              (M.val (subst (KripkeHenkin.ClosedEnv.extend
                (Base := Base) (Const := Const) ρ t) φ'))
              (M.hypVal (List.map (subst ρ) Δ')))
            (M.val (subst ρ ψ')) := hb
        exact hb'
      have hex'' := M.le_trans hex' hbound
      exact M.le_trans (M.le_inf hex'' (M.le_refl _)) (M.himp_adjoint_mp (M.le_refl _))
  | eqRefl t =>
      intro M ρ
      exact M.le_of_top_le (M.val_eq_refl (subst ρ t))
  | eqSymm h ih =>
      intro M ρ
      exact M.le_trans (ih M ρ) (M.val_eq_symm _ _)
  | eqTrans htu huv ihtu ihuv =>
      intro M ρ
      exact M.le_trans (M.le_inf (ihtu M ρ) (ihuv M ρ)) (M.val_eq_trans _ _ _)
  | eqPropI hpq hqp ihpq ihqp =>
      intro M ρ
      exact M.le_trans (M.le_inf (ihpq M ρ) (ihqp M ρ)) (M.val_eq_propI _ _)
  | eqPropEL hpq ihpq =>
      intro M ρ
      exact M.le_trans (ihpq M ρ) (M.val_eq_propEL _ _)
  | eqPropER hpq ihpq =>
      intro M ρ
      exact M.le_trans (ihpq M ρ) (M.val_eq_propER _ _)
  | eqApp t h ih =>
      intro M ρ
      exact M.le_trans (ih M ρ) (M.val_eq_app _ _ (subst ρ t))
  | eqAppArg f h ih =>
      intro M ρ
      exact M.le_trans (ih M ρ) (M.val_eq_appArg (subst ρ f) _ _)
  | eqLam h ih =>
      intro M ρ
      refine M.val_eq_lam _ _ _ (fun w => ?_)
      have hb := ih M (KripkeHenkin.ClosedEnv.extend (Base := Base) (Const := Const) ρ w)
      rw [map_weakenHyps_extend ρ w] at hb
      rw [KripkeHenkin.ClosedEnv.instantiate_subst_lift_extend
          (Base := Base) (Const := Const) (ρ := ρ) (t := w),
        KripkeHenkin.ClosedEnv.instantiate_subst_lift_extend
          (Base := Base) (Const := Const) (ρ := ρ) (t := w)]
      exact hb
  | funExt h ih =>
      rename_i Γ' Δ' σ' τ' f g
      intro M ρ
      have hall := ih M ρ
      have hshape :
          subst ρ (.all (.eq (.app (weaken (Base := Base) (σ := σ') f) (.var .vz))
                             (.app (weaken (Base := Base) (σ := σ') g) (.var .vz)))
              : Formula Const Γ')
            = .all (.eq
                (.app (weaken (Base := Base) (σ := σ') (subst ρ f)) (.var .vz))
                (.app (weaken (Base := Base) (σ := σ') (subst ρ g)) (.var .vz))) := by
        simp [subst, subst_weaken, Subst.lift]
      rw [hshape] at hall
      exact M.le_trans hall (M.val_funExt _ _)
  | beta t u =>
      intro M ρ
      have hb := M.val_beta (subst ρ t) (subst (Subst.lift ρ) u)
      rw [show subst ρ (.eq (.app (.lam u) t) (instantiate (Base := Base) t u))
            = .eq (.app (.lam (subst (Subst.lift ρ) u)) (subst ρ t))
                  (subst ρ (instantiate (Base := Base) t u)) from rfl,
        KripkeHenkin.ClosedEnv.subst_instantiate_lift
          (Base := Base) (Const := Const) (ρ := ρ) (t := t)]
      exact M.le_of_top_le hb
  | eta f =>
      rename_i Γ' Δ' σ' τ'
      intro M ρ
      have he := M.val_eta (subst ρ f)
      have hshape :
          subst ρ (.eq (.lam (.app (weaken (Base := Base) (σ := σ') f) (.var .vz))) f
              : Formula Const Γ')
            = .eq (.lam (.app (weaken (Base := Base) (σ := σ') (subst ρ f)) (.var .vz)))
                (subst ρ f) := by
        simp [subst, subst_weaken, Subst.lift]
      rw [hshape]
      exact M.le_of_top_le he

/-! ## The Lindenbaum model over a parameter-free theory

Values are closed formulas themselves; the preorder is derivability over the
theory with the source formula as an extra hypothesis.  All valuation
equations hold by `rfl`; the lattice/adjunction laws are the deduction
theorem and small natural-deduction compositions; quantifier exactness is the
fresh-parameter generalization. -/

namespace Lindenbaum

open ClosedTheorySet
open Mettapedia.Logic.HOL.WithParams

variable {T : ClosedTheorySet (WithParams Const)}

theorem provable_mono {T T' : ClosedTheorySet (WithParams Const)}
    (hTT : T ⊆ T') {φ : ClosedFormula (WithParams Const)}
    (h : Provable (Const := WithParams Const) T φ) :
    Provable (Const := WithParams Const) T' φ := by
  rcases h with ⟨Γ, hΓ, d⟩
  exact ⟨Γ, fun ψ hψ => hTT (hΓ ψ hψ), d⟩

theorem provable_of_der1 {a b : ClosedFormula (WithParams Const)}
    (d : ExtDerivation (WithParams Const) [a] b) :
    Provable (Const := WithParams Const) (insert a T) b :=
  ⟨[a], fun ψ hψ => by
    rcases List.mem_singleton.mp hψ with rfl
    exact Set.mem_insert _ _, d⟩

theorem provable_and_intro {a b : ClosedFormula (WithParams Const)}
    (h₁ : Provable (Const := WithParams Const) T a)
    (h₂ : Provable (Const := WithParams Const) T b) :
    Provable (Const := WithParams Const) T (.and a b) := by
  rcases h₁ with ⟨Γ₁, hΓ₁, d₁⟩
  rcases h₂ with ⟨Γ₂, hΓ₂, d₂⟩
  refine ⟨Γ₁ ++ Γ₂, ?_, ?_⟩
  · intro ψ hψ
    rcases List.mem_append.mp hψ with h | h
    · exact hΓ₁ ψ h
    · exact hΓ₂ ψ h
  · exact ExtDerivation.andI
      (ExtDerivation.mono (by intro ξ hξ; exact List.mem_append_left _ hξ) d₁)
      (ExtDerivation.mono (by intro ξ hξ; exact List.mem_append_right _ hξ) d₂)

theorem provable_or_inl {a b : ClosedFormula (WithParams Const)}
    (h : Provable (Const := WithParams Const) T a) :
    Provable (Const := WithParams Const) T (.or a b) := by
  rcases h with ⟨Γ, hΓ, d⟩; exact ⟨Γ, hΓ, ExtDerivation.orIL d⟩

theorem provable_or_inr {a b : ClosedFormula (WithParams Const)}
    (h : Provable (Const := WithParams Const) T b) :
    Provable (Const := WithParams Const) T (.or a b) := by
  rcases h with ⟨Γ, hΓ, d⟩; exact ⟨Γ, hΓ, ExtDerivation.orIR d⟩

theorem provable_cut {a X : ClosedFormula (WithParams Const)}
    (h₁ : Provable (Const := WithParams Const) (insert a T) X)
    (h₂ : Provable (Const := WithParams Const) T a) :
    Provable (Const := WithParams Const) T X :=
  provable_mp (provable_imp_of_insert (Const := WithParams Const) h₁) h₂

theorem provable_eqApp {σ τ : Ty Base}
    {f g : ClosedTerm (WithParams Const) (σ ⇒ τ)}
    (t : ClosedTerm (WithParams Const) σ)
    (h : Provable (Const := WithParams Const) T (.eq f g)) :
    Provable (Const := WithParams Const) T (.eq (.app f t) (.app g t)) := by
  rcases h with ⟨Γ, hΓ, d⟩; exact ⟨Γ, hΓ, ExtDerivation.eqApp t d⟩

theorem provable_eqAppArg {σ τ : Ty Base}
    (f : ClosedTerm (WithParams Const) (σ ⇒ τ))
    {t u : ClosedTerm (WithParams Const) σ}
    (h : Provable (Const := WithParams Const) T (.eq t u)) :
    Provable (Const := WithParams Const) T (.eq (.app f t) (.app f u)) := by
  rcases h with ⟨Γ, hΓ, d⟩; exact ⟨Γ, hΓ, ExtDerivation.eqAppArg f d⟩

theorem provable_funExt {σ τ : Ty Base}
    {f g : ClosedTerm (WithParams Const) (σ ⇒ τ)}
    (h : Provable (Const := WithParams Const) T
      (.all (.eq (.app (weaken (Base := Base) (σ := σ) f) (.var .vz))
                 (.app (weaken (Base := Base) (σ := σ) g) (.var .vz))))) :
    Provable (Const := WithParams Const) T (.eq f g) := by
  rcases h with ⟨Γ, hΓ, d⟩; exact ⟨Γ, hΓ, ExtDerivation.funExt d⟩

/-- Fresh-parameter universal introduction over the theory `insert ω T`, for
parameter-free `T`. -/
theorem all_intro_of_instances
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    {σ' : Ty Base} {φb : Formula (WithParams Const) [σ']}
    {ω : ClosedFormula (WithParams Const)}
    (h : ∀ t : ClosedTerm (WithParams Const) σ',
      Provable (Const := WithParams Const) (insert ω T)
        (instantiate (Base := Base) t φb)) :
    Provable (Const := WithParams Const) (insert ω T) (.all φb) := by
  classical
  set k := max (maxParam ω) (maxParam φb) with hk
  refine provable_all_intro_fresh (param σ' k) ?_ ?_ (h (.const (param σ' k)))
  · intro ψ hψ
    rcases Set.mem_insert_iff.mp hψ with rfl | hψ
    · exact noConstOccurrence_param_of_ge k ψ (le_max_left _ _)
    · exact hT0 ψ hψ σ' k
  · exact noConstOccurrence_param_of_ge k φb (le_max_right _ _)

/-- The Lindenbaum Heyting-valued model of a theory equipped with a
fresh-parameter universal-introduction capability (parameter-free theories and
schema-extensions of them both qualify). -/
noncomputable def lindenbaumModelOfAllIntro (T : ClosedTheorySet (WithParams Const))
    (hAll : ∀ {σ' : Ty Base} {φb : Formula (WithParams Const) [σ']}
      {ω : ClosedFormula (WithParams Const)},
      (∀ t : ClosedTerm (WithParams Const) σ',
        Provable (Const := WithParams Const) (insert ω T)
          (instantiate (Base := Base) t φb)) →
      Provable (Const := WithParams Const) (insert ω T) (.all φb)) :
    HeytingGeneralModel Base (WithParams Const) where
  Ω := ClosedFormula (WithParams Const)
  le a b := Provable (Const := WithParams Const) (insert a T) b
  le_refl a := provable_of_mem (Set.mem_insert _ _)
  le_trans := fun {a b c} h₁ h₂ =>
    provable_mp
      (provable_mono (Set.subset_insert _ _)
        (provable_imp_of_insert (Const := WithParams Const) h₂)) h₁
  top := .top
  bot := .bot
  inf := .and
  sup := .or
  himp := .imp
  le_top a := by
    refine provable_of_der1 ?_
    exact ExtDerivation.topI
  bot_le a := by
    refine provable_of_der1 ?_
    exact ExtDerivation.botE (ExtDerivation.hyp (List.Mem.head _))
  inf_le_left a b := provable_of_der1
    (ExtDerivation.andEL (ψ := b) (ExtDerivation.hyp (List.Mem.head _)))
  inf_le_right a b := provable_of_der1
    (ExtDerivation.andER (φ := a) (ExtDerivation.hyp (List.Mem.head _)))
  le_inf := fun h₁ h₂ => provable_and_intro h₁ h₂
  le_sup_left a b := provable_of_der1
    (ExtDerivation.orIL (ExtDerivation.hyp (List.Mem.head _)))
  le_sup_right a b := provable_of_der1
    (ExtDerivation.orIR (ExtDerivation.hyp (List.Mem.head _)))
  sup_le := fun {a b c} h₁ h₂ =>
    provable_or_elim (Const := WithParams Const)
      (provable_of_mem (Set.mem_insert _ _))
      (provable_mono (Set.insert_subset_insert (Set.subset_insert _ _)) h₁)
      (provable_mono (Set.insert_subset_insert (Set.subset_insert _ _)) h₂)
  himp_adjoint_mp := fun {a b c} h =>
    provable_mp
      (provable_mp
        (provable_mono (Set.subset_insert _ _)
          (provable_imp_of_insert (Const := WithParams Const) h))
        (provable_of_der1 (ExtDerivation.andEL (ψ := b) (ExtDerivation.hyp (List.Mem.head _)))))
      (provable_of_der1 (ExtDerivation.andER (φ := a) (ExtDerivation.hyp (List.Mem.head _))))
  himp_adjoint_intro := fun {a b c} h => by
    refine provable_imp_of_insert (Const := WithParams Const) ?_
    refine provable_cut
      (provable_mono (Set.insert_subset_insert
        (Set.Subset.trans (Set.subset_insert _ _) (Set.subset_insert _ _))) h) ?_
    exact provable_and_intro
      (provable_of_mem (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
      (provable_of_mem (Set.mem_insert _ _))
  inf_sup_distrib := fun a b c => by
    refine provable_or_elim (Const := WithParams Const) (φ := b) (ψ := c)
      (provable_of_der1 (ExtDerivation.andER (φ := a) (ExtDerivation.hyp (List.Mem.head _)))) ?_ ?_
    · refine provable_or_inl (provable_and_intro ?_ ?_)
      · exact provable_mono (Set.subset_insert _ _)
          (provable_of_der1 (ExtDerivation.andEL (ψ := .or b c) (ExtDerivation.hyp (List.Mem.head _))))
      · exact provable_of_mem (Set.mem_insert _ _)
    · refine provable_or_inr (provable_and_intro ?_ ?_)
      · exact provable_mono (Set.subset_insert _ _)
          (provable_of_der1 (ExtDerivation.andEL (ψ := .or b c) (ExtDerivation.hyp (List.Mem.head _))))
      · exact provable_of_mem (Set.mem_insert _ _)
  val := id
  val_top := rfl
  val_bot := rfl
  val_and := fun _ _ => rfl
  val_or := fun _ _ => rfl
  val_imp := fun _ _ => rfl
  val_not_le := fun φ => provable_of_der1
    (ExtDerivation.impI (ExtDerivation.notE
      (ExtDerivation.hyp (List.Mem.tail _ (List.Mem.head _)))
      (ExtDerivation.hyp (List.Mem.head _))))
  le_val_not := fun φ => provable_of_der1
    (ExtDerivation.notI (ExtDerivation.impE
      (ExtDerivation.hyp (List.Mem.tail _ (List.Mem.head _)))
      (ExtDerivation.hyp (List.Mem.head _))))
  val_all_le := fun φb t => provable_of_der1
    (ExtDerivation.allE (φ := φb) t (ExtDerivation.hyp (List.Mem.head _)))
  le_val_all := fun φb ω h => hAll h
  val_ex_le := fun {σ'} φb ω h => by
    refine provable_of_ex_and_all_imp (Const := WithParams Const)
      (provable_of_mem (Set.mem_insert _ _)) ?_
    have hAll : Provable (Const := WithParams Const)
        (insert (.ex φb : ClosedFormula (WithParams Const)) T)
        (.all (.imp φb (weaken (Base := Base) ω))) := by
      refine hAll (fun t => ?_)
      have hinst :
          instantiate (Base := Base) t (.imp φb (weaken (Base := Base) ω))
            = .imp (instantiate (Base := Base) t φb) ω := by
        show (.imp (instantiate (Base := Base) t φb)
            (instantiate (Base := Base) t (weaken (Base := Base) ω))
          : ClosedFormula (WithParams Const)) = _
        rw [instantiate_weaken]
      rw [hinst]
      refine provable_imp_of_insert (Const := WithParams Const) ?_
      refine provable_mono ?_ (h t)
      exact Set.insert_subset_insert (Set.subset_insert _ _)
    exact hAll
  le_val_ex := fun φb t => provable_of_der1
    (ExtDerivation.exI (φ := φb) t (ExtDerivation.hyp (List.Mem.head _)))
  val_eq_refl := fun t => ⟨[], by simp, ExtDerivation.eqRefl t⟩
  val_eq_symm := fun t u => provable_of_der1
    (ExtDerivation.eqSymm (ExtDerivation.hyp (List.Mem.head _)))
  val_eq_trans := fun t u v => provable_of_der1
    (ExtDerivation.eqTrans
      (ExtDerivation.andEL (ψ := .eq u v) (ExtDerivation.hyp (List.Mem.head _)))
      (ExtDerivation.andER (φ := .eq t u) (ExtDerivation.hyp (List.Mem.head _))))
  val_eq_app := fun f g t => provable_of_der1
    (ExtDerivation.eqApp t (ExtDerivation.hyp (List.Mem.head _)))
  val_eq_appArg := fun f t u => provable_of_der1
    (ExtDerivation.eqAppArg f (ExtDerivation.hyp (List.Mem.head _)))
  val_eq_propI := fun p q => provable_of_der1
    (ExtDerivation.eqPropI
      (ExtDerivation.andEL (ψ := .imp q p) (ExtDerivation.hyp (List.Mem.head _)))
      (ExtDerivation.andER (φ := .imp p q) (ExtDerivation.hyp (List.Mem.head _))))
  val_eq_propEL := fun p q => provable_of_der1
    (ExtDerivation.eqPropEL (ExtDerivation.hyp (List.Mem.head _)))
  val_eq_propER := fun p q => provable_of_der1
    (ExtDerivation.eqPropER (ExtDerivation.hyp (List.Mem.head _)))
  val_eq_lam := fun {σ' τ'} t u ω h => by
    refine provable_funExt ?_
    refine hAll (fun w => ?_)
    have hshape :
        instantiate (Base := Base) w
            (.eq (.app (weaken (Base := Base) (σ := σ') (.lam t)) (.var .vz))
                 (.app (weaken (Base := Base) (σ := σ') (.lam u)) (.var .vz))
              : Formula (WithParams Const) [σ'])
          = .eq (.app (.lam t) w) (.app (.lam u) w) := by
      show (.eq (.app (instantiate (Base := Base) w
              (weaken (Base := Base) (σ := σ') (.lam t)))
            (instantiate (Base := Base) w (.var .vz)))
          (.app (instantiate (Base := Base) w
              (weaken (Base := Base) (σ := σ') (.lam u)))
            (instantiate (Base := Base) w (.var .vz)))
        : ClosedFormula (WithParams Const)) = _
      simp only [instantiate_weaken, instantiate_var_vz]
    rw [hshape]
    have hb1 : Provable (Const := WithParams Const) (insert ω T)
        (.eq (.app (.lam t) w) (instantiate (Base := Base) w t)) :=
      ⟨[], by simp, ExtDerivation.beta w t⟩
    have hb2 : Provable (Const := WithParams Const) (insert ω T)
        (.eq (.app (.lam u) w) (instantiate (Base := Base) w u)) :=
      ⟨[], by simp, ExtDerivation.beta w u⟩
    have hb2' : Provable (Const := WithParams Const) (insert ω T)
        (.eq (instantiate (Base := Base) w u) (.app (.lam u) w)) := by
      rcases hb2 with ⟨Γ, hΓ, d⟩
      exact ⟨Γ, hΓ, ExtDerivation.eqSymm d⟩
    have hmid := h w
    rcases hb1 with ⟨Γ₁, hΓ₁, d₁⟩
    rcases hmid with ⟨Γ₂, hΓ₂, d₂⟩
    rcases hb2' with ⟨Γ₃, hΓ₃, d₃⟩
    refine ⟨Γ₁ ++ Γ₂ ++ Γ₃, ?_, ?_⟩
    · intro ψ hψ
      rcases List.mem_append.mp hψ with h12 | h3
      · rcases List.mem_append.mp h12 with h1 | h2
        · exact hΓ₁ ψ h1
        · exact hΓ₂ ψ h2
      · exact hΓ₃ ψ h3
    · refine ExtDerivation.eqTrans
        (ExtDerivation.mono (by intro ξ hξ; exact List.mem_append_left _ (List.mem_append_left _ hξ)) d₁)
        (ExtDerivation.eqTrans
          (ExtDerivation.mono (by intro ξ hξ; exact List.mem_append_left _ (List.mem_append_right _ hξ)) d₂)
          (ExtDerivation.mono (by intro ξ hξ; exact List.mem_append_right _ hξ) d₃))
  val_funExt := fun f g => provable_funExt
    (provable_of_mem (Set.mem_insert _ _))
  val_beta := fun t u => ⟨[], by simp, ExtDerivation.beta t u⟩
  val_eta := fun f => ⟨[], by simp, ExtDerivation.eta f⟩

/-- The Lindenbaum Heyting-valued model of a parameter-free theory. -/
noncomputable def lindenbaumModel (T : ClosedTheorySet (WithParams Const))
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ) :
    HeytingGeneralModel Base (WithParams Const) :=
  lindenbaumModelOfAllIntro (Base := Base) T
    (fun {_σ' _φb _ω} h => all_intro_of_instances hT0 h)

end Lindenbaum

open Mettapedia.Logic.HOL.WithParams

/-! ## Completeness for Heyting-valued substitutional models -/

/-- The empty closing substitution. -/
def emptySubst : Subst Const [] [] := fun v => nomatch v

/-- Semantic consequence over all Heyting-valued substitutional models. -/
def HeytingConsequence (T : ClosedTheorySet Const) (θ : ClosedFormula Const) : Prop :=
  ∀ M : HeytingGeneralModel.{u, v, max u v} Base Const,
    (∀ ψ ∈ T, M.le M.top (M.val ψ)) → M.le M.top (M.val θ)

/-- Soundness packaging: derivable closed formulas are semantic consequences. -/
theorem heytingConsequence_of_provable {T : ClosedTheorySet Const}
    {θ : ClosedFormula Const}
    (h : ClosedTheorySet.Provable (Const := Const) T θ) :
    HeytingConsequence (Base := Base) T θ := by
  intro M hT
  rcases h with ⟨Γ, hΓ, d⟩
  have hclosed : ∀ ψ : ClosedFormula Const,
      subst (emptySubst (Base := Base) (Const := Const)) ψ = ψ := fun ψ =>
    KripkeHenkin.ClosedEnv.subst_empty (Base := Base) (Const := Const) _ ψ
  have hhyps : ∀ (Γ' : List (ClosedFormula Const)), (∀ ψ ∈ Γ', ψ ∈ T) →
      M.le M.top (M.hypVal (Γ'.map (subst (emptySubst (Base := Base) (Const := Const))))) := by
    intro Γ'
    induction Γ' with
    | nil => intro _; exact M.le_refl _
    | cons ψ Γ' ih =>
        intro hmem
        refine M.le_inf ?_ (ih (fun ξ hξ => hmem ξ (List.mem_cons_of_mem _ hξ)))
        rw [hclosed ψ]
        exact hT ψ (hmem ψ List.mem_cons_self)
  have hs := sound d M (emptySubst (Base := Base) (Const := Const))
  have hcomb := M.le_trans (hhyps Γ hΓ) hs
  rw [← hclosed θ]
  exact hcomb

/-- **Completeness** for parameter-free theories: a semantic consequence over
all Heyting-valued substitutional models is derivable. -/
theorem provable_of_heytingConsequence_param_free
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (hSem : HeytingConsequence (Base := Base) T θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ := by
  classical
  have hLin := hSem (Lindenbaum.lindenbaumModel (Base := Base) T hT0)
    (fun ψ hψ => Lindenbaum.provable_mono (Set.subset_insert _ _)
      (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hψ))
  exact Lindenbaum.provable_cut hLin
    (ClosedTheorySet.provable_top (Const := WithParams Const) T)

/-- **The textbook iff**: for parameter-free theories over the parameter
language, EM-free derivability coincides with semantic consequence over all
Heyting-valued substitutional models. -/
theorem provable_iff_heytingConsequence_param_free
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      HeytingConsequence (Base := Base) T θ :=
  ⟨heytingConsequence_of_provable (Base := Base),
    provable_of_heytingConsequence_param_free (Base := Base) hT0⟩

/-- **The canonical countermodel interface**: the Lindenbaum model itself
refutes every non-theorem — the one model class carries completeness through
its canonical member.  (The canonical KRIPKE model cannot inhabit the
`KripkeHenkinGeneral` class: its `term_closed` obligation fails at low worlds
for formulas mentioning future parameters — see the consolidation record.
The Heyting-valued class is the correct single umbrella.) -/
theorem lindenbaumModel_refutes_nontheorem
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (h : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T θ) :
    ¬ (Lindenbaum.lindenbaumModel (Base := Base) T hT0).le
        (Lindenbaum.lindenbaumModel (Base := Base) T hT0).top
        ((Lindenbaum.lindenbaumModel (Base := Base) T hT0).val θ) := by
  intro hle
  exact h (Lindenbaum.provable_cut hle
    (ClosedTheorySet.provable_top (Const := WithParams Const) T))

/-! ## Kripke models as Heyting-valued models

Every substitutional Kripke-Henkin model induces a Heyting-valued
substitutional model on the upsets of its frame, with forcing as valuation.
This places the Kripke semantics (including the canonical interfaces and the
excluded-middle countermodel world) under the algebraic completeness umbrella;
the WorldModel/neighborhood instantiation is the named follow-on bridge. -/

open Mettapedia.Logic.HOL.KripkeHenkin in
/-- The upset Heyting-valued model of a substitutional Kripke-Henkin model. -/
noncomputable def ofKripkeHenkin (K : KripkeHenkin.{u, v, w} Base Const) :
    HeytingGeneralModel Base Const where
  Ω := {S : K.World → Prop // ∀ {U V : K.World}, K.le U V → S U → S V}
  le S T := ∀ W, S.1 W → T.1 W
  le_refl S := fun _ h => h
  le_trans h₁ h₂ := fun W h => h₂ W (h₁ W h)
  top := ⟨fun _ => True, fun _ _ => trivial⟩
  bot := ⟨fun _ => False, fun _ h => h⟩
  inf S T := ⟨fun W => S.1 W ∧ T.1 W,
    fun hUV h => ⟨S.2 hUV h.1, T.2 hUV h.2⟩⟩
  sup S T := ⟨fun W => S.1 W ∨ T.1 W,
    fun hUV h => h.elim (fun h => Or.inl (S.2 hUV h)) (fun h => Or.inr (T.2 hUV h))⟩
  himp S T := ⟨fun W => ∀ V, K.le W V → S.1 V → T.1 V,
    fun hUV h V hV hs => h V (K.le_trans hUV hV) hs⟩
  le_top _ := fun _ _ => trivial
  bot_le _ := fun _ h => h.elim
  inf_le_left _ _ := fun _ h => h.1
  inf_le_right _ _ := fun _ h => h.2
  le_inf h₁ h₂ := fun W h => ⟨h₁ W h, h₂ W h⟩
  le_sup_left _ _ := fun _ h => Or.inl h
  le_sup_right _ _ := fun _ h => Or.inr h
  sup_le h₁ h₂ := fun W h => h.elim (h₁ W) (h₂ W)
  himp_adjoint_mp h := fun W hab =>
    h W hab.1 W (K.le_refl W) hab.2
  himp_adjoint_intro {a b c} h := fun W ha V hV hb =>
    h V ⟨a.2 hV ha, hb⟩
  inf_sup_distrib a b c := fun W h =>
    h.2.elim (fun hb => Or.inl ⟨h.1, hb⟩) (fun hc => Or.inr ⟨h.1, hc⟩)
  val φ := ⟨fun W => K.forces W φ, fun hUV h => K.forces_mono hUV h⟩
  val_top := Subtype.ext (funext fun W =>
    propext ⟨fun _ => trivial, fun _ => K.forces_top⟩)
  val_bot := Subtype.ext (funext fun W =>
    propext ⟨fun h => K.forces_bot h, False.elim⟩)
  val_and φ ψ := Subtype.ext (funext fun W => propext K.forces_and)
  val_or φ ψ := Subtype.ext (funext fun W => propext K.forces_or)
  val_imp φ ψ := Subtype.ext (funext fun W => propext K.forces_imp)
  val_not_le φ := fun W h => K.forces_not.mp h
  le_val_not φ := fun W h => K.forces_not.mpr h
  val_all_le φb t := fun W h =>
    K.forces_all.mp h W (K.le_refl W) t
  le_val_all φb ω h := fun W hω =>
    K.forces_all.mpr (fun V hV t => h t V (ω.2 hV hω))
  val_ex_le φb ω h := fun W hex => by
    obtain ⟨t, ht⟩ := K.forces_ex.mp hex
    exact h t W (ht W (K.le_refl W))
  le_val_ex φb t := fun W h =>
    K.forces_ex.mpr ⟨t, fun V hV => K.forces_mono hV h⟩
  val_eq_refl t := fun W _ => K.forces_eq.mpr (K.eq_refl W t)
  val_eq_symm t u := fun W h => K.forces_eq.mpr (K.eq_symm (K.forces_eq.mp h))
  val_eq_trans t u v := fun W h => K.forces_eq.mpr
    (K.eq_trans (K.forces_eq.mp h.1) (K.forces_eq.mp h.2))
  val_eq_app f g t := fun W h => K.forces_eq.mpr
    (K.eq_app_congr (K.forces_eq.mp h) (K.eq_refl W t))
  val_eq_appArg f t u := fun W h => K.forces_eq.mpr
    (K.eq_app_congr (K.eq_refl W f) (K.forces_eq.mp h))
  val_eq_propI p q := fun W h => K.forces_eq.mpr
    (K.eq_prop_intro h.1 h.2)
  val_eq_propEL p q := fun W h => K.eq_prop_elim_left (K.forces_eq.mp h)
  val_eq_propER p q := fun W h => K.eq_prop_elim_right (K.forces_eq.mp h)
  val_eq_lam t u ω h := fun W hω => by
    refine K.forces_eq.mpr (K.eq_funext (fun w => ?_))
    have hmid := K.forces_eq.mp (h w W hω)
    exact K.eq_trans (K.eq_beta (W := W) w t)
      (K.eq_trans hmid (K.eq_symm (K.eq_beta (W := W) w u)))
  val_funExt f g := fun W h => by
    refine K.forces_eq.mpr (K.eq_funext (fun w => ?_))
    have hpoint := K.forces_all.mp h W (K.le_refl W) w
    have hshape :
        instantiate (Base := Base) w
            (.eq (.app (weaken (Base := Base) f) (.var .vz))
                 (.app (weaken (Base := Base) g) (.var .vz))
              : Formula Const _)
          = .eq (.app f w) (.app g w) := by
      show (.eq (.app (instantiate (Base := Base) w (weaken (Base := Base) f))
            (instantiate (Base := Base) w (.var .vz)))
          (.app (instantiate (Base := Base) w (weaken (Base := Base) g))
            (instantiate (Base := Base) w (.var .vz)))
        : ClosedFormula Const) = _
      simp only [instantiate_weaken, instantiate_var_vz]
    rw [hshape] at hpoint
    exact K.forces_eq.mp hpoint
  val_beta t u := fun W _ => K.forces_eq.mpr (K.eq_beta (W := W) t u)
  val_eta f := fun W _ => K.forces_eq.mpr (K.eq_eta (W := W) f)

end HeytingSem
end Mettapedia.Logic.HOL
