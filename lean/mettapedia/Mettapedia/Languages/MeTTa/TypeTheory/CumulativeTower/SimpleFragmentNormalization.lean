import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SimpleFragmentConversion
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.TowerConversionSkeleton
import Mettapedia.Languages.MeTTa.Pure.Intrinsic.RegularNormalization

/-!
# Strong normalization of the intrinsic simple fragment

The existing regular Pure normalization theorem applies through a
type-preserving interpretation of simple types as constant dependent types.
Every intrinsic beta step becomes one Pure reduction, so accessibility pulls
back without any assumption that raw erasure is injective.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace SimpleFragmentNormalization

open FourFaceBetaExperiment FourFaceBetaExperiment.IntrinsicSTT
open Mettapedia.Languages.MeTTa.Pure.Intrinsic
open PresentationBoundary

variable {Γ Δ : List Ty} {A B : Ty} {n m : Nat}

def toPure (t : Term Γ A) : Syntax.PureTm Γ.length :=
  Presentation.TowerConversionSkeleton.erase (TowerDTT.eraseTerm t)

def toPureType (n : Nat) (A : Ty) : Syntax.PureTm n :=
  Presentation.TowerConversionSkeleton.erase (TowerDTT.eraseTypeAt n A)

@[simp] theorem toPureType_rename (ρ : Renaming.Ren n m) (A : Ty) :
    Renaming.rename ρ (toPureType n A) = toPureType m A := by
  unfold toPureType
  rw [← Presentation.TowerConversionSkeleton.erase_rename, TowerDTT.eraseTypeAt_rename]

@[simp] theorem toPureType_subst (σ : Substitution.Sub n m) (A : Ty) :
    Substitution.subst σ (toPureType n A) = toPureType m A := by
  induction A generalizing n m with
  | atom => rfl
  | arr A B ihA ihB =>
      change Syntax.PureTm.pi (Substitution.subst σ (toPureType n A))
        (Substitution.subst (Substitution.liftSub σ) (toPureType (n + 1) B)) = _
      rw [ihA, ihB]
      rfl

theorem toPureType_formed (Γ : Context.Ctx n) (A : Ty) :
    RegularHasType Γ (toPureType n A) .u1 := by
  induction A generalizing n with
  | atom => exact .u0_type Γ
  | arr A B ihA ihB => exact .pi_form (ihA Γ) (ihB (.snoc Γ (toPureType n A)))

def toPureContext : (Γ : List Ty) → Context.Ctx Γ.length
  | [] => .nil
  | A :: Γ => .snoc (toPureContext Γ) (toPureType Γ.length A)

theorem toPureContext_regular (Γ : List Ty) : RegularCtx (toPureContext Γ) := by
  induction Γ with
  | nil => exact .nil
  | cons A Γ ih => exact .snoc ih (toPureType_formed _ A)

theorem toPureContext_lookup (v : Var Γ A) :
    Context.lookup (toPureContext Γ) (TowerDTT.eraseVar v) = toPureType Γ.length A := by
  induction v with
  | zero => exact toPureType_rename _ _
  | succ v ih =>
      change Renaming.rename Renaming.wk
        (Context.lookup (toPureContext _) (TowerDTT.eraseVar v)) = _
      rw [ih, toPureType_rename]
      rfl

theorem toPure_hasType (t : Term Γ A) :
    RegularHasType (toPureContext Γ) (toPure t) (toPureType Γ.length A) := by
  induction t with
  | var v =>
      rw [← toPureContext_lookup v]
      exact .var _
  | @lam A Γ B body ih =>
      exact .lam_intro (toPureType_formed _ A) (toPureType_formed _ B) ih
  | @app Γ A B f a ihf iha =>
      have h := RegularHasType.app_elim (toPureType_formed (toPureContext Γ) A)
        ihf iha (toPureType_formed (.snoc (toPureContext Γ) (toPureType Γ.length A)) B)
      change RegularHasType _ _
        (Substitution.subst (Substitution.subst0 (toPure a)) (toPureType (Γ.length + 1) B)) at h
      rw [toPureType_subst] at h
      exact h

theorem toPure_instantiateNewest (body : Term (A :: Γ) B) (a : Term Γ A) :
    toPure (body.instantiateNewest a) = Substitution.inst0 (toPure a) (toPure body) := by
  unfold toPure
  rw [SimpleFragmentSubstitutionTranslation.eraseTerm_instantiateNewest,
    Presentation.TowerConversionSkeleton.erase_inst0]

theorem betaStep_toPure {left right : Term Γ A} (h : BetaStep left right) :
    Reduction.Red (toPure left) (toPure right) := by
  induction h with
  | beta body a =>
      rw [toPure_instantiateNewest]
      exact .betaPi _ _
  | lam _ ih => exact .congLam ih
  | appLeft _ ih => exact .congAppFun ih
  | appRight _ ih => exact .congAppArg ih

theorem accessible_of_toPure (t : Term Γ A) (h : ReductionAccessible (toPure t)) :
    Acc (fun reduct source => BetaStep source reduct) t := by
  generalize equal : toPure t = p at h
  induction h generalizing t with
  | intro p _ ih =>
      apply Acc.intro
      intro u step
      apply ih (toPure u) _ u rfl
      rw [← equal]
      exact betaStep_toPure step

/-- Every intrinsically typed term is strongly beta normalizing. -/
theorem strong_normalization (t : Term Γ A) :
    Acc (fun reduct source => BetaStep source reduct) t :=
  accessible_of_toPure t
    (RegularJudgment.subject_accessible ⟨toPureContext_regular Γ, toPure_hasType t⟩)

/-- One outermost-leftmost beta step, retaining intrinsic typing. -/
def reduceOnce? : {Γ : List Ty} → {A : Ty} → (t : Term Γ A) →
    Option {u : Term Γ A // BetaStep t u}
  | _, _, .var _ => none
  | _, _, .lam body =>
      match reduceOnce? body with
      | none => none
      | some next => some ⟨.lam next.1, .lam next.2⟩
  | _, _, .app (.lam body) a => some ⟨body.instantiateNewest a, .beta body a⟩
  | _, _, .app f a =>
      match reduceOnce? f with
      | some next => some ⟨.app next.1 a, .appLeft next.2⟩
      | none =>
          match reduceOnce? a with
          | none => none
          | some next => some ⟨.app f next.1, .appRight next.2⟩

theorem reduceOnce_isSome_of_step {t u : Term Γ A} (h : BetaStep t u) :
    (reduceOnce? t).isSome = true := by
  induction h with
  | beta body a => simp [reduceOnce?]
  | lam _ ih =>
      obtain ⟨next, selected⟩ := Option.isSome_iff_exists.mp ih
      simp [reduceOnce?, selected]
  | @appLeft Γ A B f f' a _ ih =>
      obtain ⟨next, selected⟩ := Option.isSome_iff_exists.mp ih
      cases f <;> simp_all [reduceOnce?]
  | @appRight Γ A B f a a' _ ih =>
      obtain ⟨next, selected⟩ := Option.isSome_iff_exists.mp ih
      cases f with
      | var v => simp [reduceOnce?, selected]
      | lam body => simp [reduceOnce?]
      | app g b =>
          cases picked : reduceOnce? (g.app b) <;> simp [reduceOnce?, picked, selected]

theorem reduceOnce_eq_none_iff (t : Term Γ A) :
    reduceOnce? t = none ↔ ∀ u, ¬ BetaStep t u := by
  constructor
  · intro empty u step
    have someStep := reduceOnce_isSome_of_step step
    simp [empty] at someStep
  · intro normal
    cases selected : reduceOnce? t with
    | none => rfl
    | some next => exact False.elim (normal next.1 next.2)

/-- A normal form with a finite reduction path and irreducibility. -/
structure Result (t : Term Γ A) where
  normalForm : Term Γ A
  reduces : Relation.ReflTransGen BetaStep t normalForm
  irreducible : ∀ u, ¬ BetaStep normalForm u

def normalizeAccessible (t : Term Γ A)
    (accessible : Acc (fun reduct source => BetaStep source reduct) t) : Result t := by
  induction accessible with
  | intro t _ ih =>
      cases selected : reduceOnce? t with
      | none => exact ⟨t, .refl, (reduceOnce_eq_none_iff t).1 selected⟩
      | some next =>
          let result := ih next.1 next.2
          exact ⟨result.normalForm, .head next.2 result.reduces, result.irreducible⟩

/-- Total beta normalization; termination evidence is erased at runtime. -/
def normalize (t : Term Γ A) : Result t := normalizeAccessible t (strong_normalization t)

theorem steps_convert {left right : Term Γ A}
    (h : Relation.ReflTransGen BetaStep left right) : BetaConv left right := by
  induction h with
  | refl => exact .refl _
  | tail _ step ih => exact .trans _ _ _ ih (.rel _ _ step)

theorem normalize_convert (t : Term Γ A) : BetaConv t (normalize t).normalForm :=
  steps_convert (normalize t).reduces

theorem steps_eq_of_irreducible {t u : Term Γ A} (normal : ∀ u, ¬ BetaStep t u)
    (steps : Relation.ReflTransGen BetaStep t u) : u = t := by
  induction steps with
  | refl => rfl
  | tail _ step ih =>
      subst ih
      exact False.elim (normal _ step)

theorem normalize_of_irreducible (t : Term Γ A) (normal : ∀ u, ¬ BetaStep t u) :
    (normalize t).normalForm = t := steps_eq_of_irreducible normal (normalize t).reduces

theorem normalize_idempotent (t : Term Γ A) :
    (normalize (normalize t).normalForm).normalForm = (normalize t).normalForm :=
  normalize_of_irreducible _ (normalize t).irreducible

#print axioms toPure_hasType
#print axioms strong_normalization
#print axioms normalize
#print axioms normalize_convert

end SimpleFragmentNormalization
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
