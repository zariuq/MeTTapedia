import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.Conversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeConversionSkeleton
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.Normalization

/-!
# Strong normalization of the intrinsic simple fragment

The existing regular two-sort normalization theorem applies through a
type-preserving interpretation of simple types as constant dependent types.
Every intrinsic beta step becomes one two-sort reduction, so accessibility pulls
back without any assumption that raw erasure is injective.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.Normalization

open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId
open Regular

variable {Γ Δ : List Ty} {A B : Ty} {n m : Nat}

def toTwoSort (t : Term Γ A) : Syntax.ScopedTerm Γ.length :=
  Presentation.TowerConversionSkeleton.erase (TowerDTT.eraseTerm t)

def toTwoSortType (n : Nat) (A : Ty) : Syntax.ScopedTerm n :=
  Presentation.TowerConversionSkeleton.erase (TowerDTT.eraseTypeAt n A)

@[simp] theorem toTwoSortType_rename (ρ : Renaming.Ren n m) (A : Ty) :
    Renaming.rename ρ (toTwoSortType n A) = toTwoSortType m A := by
  unfold toTwoSortType
  rw [← Presentation.TowerConversionSkeleton.erase_rename, TowerDTT.eraseTypeAt_rename]

@[simp] theorem toTwoSortType_subst (σ : Substitution.Sub n m) (A : Ty) :
    Substitution.subst σ (toTwoSortType n A) = toTwoSortType m A := by
  induction A generalizing n m with
  | atom => rfl
  | arr A B ihA ihB =>
      change Syntax.ScopedTerm.pi (Substitution.subst σ (toTwoSortType n A))
        (Substitution.subst (Substitution.liftSub σ) (toTwoSortType (n + 1) B)) = _
      rw [ihA, ihB]
      rfl

theorem toTwoSortType_formed (Γ : Context.Ctx n) (A : Ty) :
    RegularHasType Γ (toTwoSortType n A) .u1 := by
  induction A generalizing n with
  | atom => exact .u0_type Γ
  | arr A B ihA ihB => exact .pi_form (ihA Γ) (ihB (.snoc Γ (toTwoSortType n A)))

def toTwoSortContext : (Γ : List Ty) → Context.Ctx Γ.length
  | [] => .nil
  | A :: Γ => .snoc (toTwoSortContext Γ) (toTwoSortType Γ.length A)

theorem toTwoSortContext_regular (Γ : List Ty) : RegularCtx (toTwoSortContext Γ) := by
  induction Γ with
  | nil => exact .nil
  | cons A Γ ih => exact .snoc ih (toTwoSortType_formed _ A)

theorem toTwoSortContext_lookup (v : Var Γ A) :
    Context.lookup (toTwoSortContext Γ) (TowerDTT.eraseVar v) = toTwoSortType Γ.length A := by
  induction v with
  | zero => exact toTwoSortType_rename _ _
  | succ v ih =>
      change Renaming.rename Renaming.wk
        (Context.lookup (toTwoSortContext _) (TowerDTT.eraseVar v)) = _
      rw [ih, toTwoSortType_rename]
      rfl

theorem toTwoSort_hasType (t : Term Γ A) :
    RegularHasType (toTwoSortContext Γ) (toTwoSort t) (toTwoSortType Γ.length A) := by
  induction t with
  | var v =>
      rw [← toTwoSortContext_lookup v]
      exact .var _
  | @lam A Γ B body ih =>
      exact .lam_intro (toTwoSortType_formed _ A) (toTwoSortType_formed _ B) ih
  | @app Γ A B f a ihf iha =>
      have h := RegularHasType.app_elim (toTwoSortType_formed (toTwoSortContext Γ) A)
        ihf iha (toTwoSortType_formed (.snoc (toTwoSortContext Γ) (toTwoSortType Γ.length A)) B)
      change RegularHasType _ _
        (Substitution.subst (Substitution.subst0 (toTwoSort a)) (toTwoSortType (Γ.length + 1) B)) at h
      rw [toTwoSortType_subst] at h
      exact h

theorem toTwoSort_instantiateNewest (body : Term (A :: Γ) B) (a : Term Γ A) :
    toTwoSort (body.instantiateNewest a) = Substitution.inst0 (toTwoSort a) (toTwoSort body) := by
  unfold toTwoSort
  rw [Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.SubstitutionTranslation.eraseTerm_instantiateNewest,
    Presentation.TowerConversionSkeleton.erase_inst0]

theorem betaStep_toTwoSort {left right : Term Γ A} (h : BetaStep left right) :
    Reduction.Red (toTwoSort left) (toTwoSort right) := by
  induction h with
  | beta body a =>
      rw [toTwoSort_instantiateNewest]
      exact .betaPi _ _
  | lam _ ih => exact .congLam ih
  | appLeft _ ih => exact .congAppFun ih
  | appRight _ ih => exact .congAppArg ih

theorem accessible_of_toTwoSort (t : Term Γ A) (h : ReductionAccessible (toTwoSort t)) :
    Acc (fun reduct source => BetaStep source reduct) t := by
  generalize equal : toTwoSort t = p at h
  induction h generalizing t with
  | intro p _ ih =>
      apply Acc.intro
      intro u step
      apply ih (toTwoSort u) _ u rfl
      rw [← equal]
      exact betaStep_toTwoSort step

/-- Every intrinsically typed term is strongly beta normalizing. -/
theorem strong_normalization (t : Term Γ A) :
    Acc (fun reduct source => BetaStep source reduct) t :=
  accessible_of_toTwoSort t
    (RegularJudgment.subject_accessible ⟨toTwoSortContext_regular Γ, toTwoSort_hasType t⟩)

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

/-- A second typed syntax instantiates the shared relation-level algorithm. -/
def reductionSelector (Γ : List Ty) (A : Ty) :
    Mettapedia.Logic.Relation.CompleteStepSelector (@BetaStep Γ A) where
  step := reduceOnce?
  none_iff_normal := reduceOnce_eq_none_iff

def normalizeAccessible (t : Term Γ A)
    (accessible : Acc (fun reduct source => BetaStep source reduct) t) :
    Mettapedia.Logic.Relation.NormalizationResult BetaStep t :=
  (reductionSelector Γ A).normalize t accessible

/-- Total beta normalization; termination evidence is erased at runtime. -/
def normalize (t : Term Γ A) : Mettapedia.Logic.Relation.NormalizationResult BetaStep t :=
  normalizeAccessible t (strong_normalization t)

theorem steps_convert {left right : Term Γ A}
    (h : Relation.ReflTransGen BetaStep left right) : BetaConv left right := by
  induction h with
  | refl => exact .refl _
  | tail _ step ih => exact .trans _ _ _ ih (.rel _ _ step)

theorem normalize_convert (t : Term Γ A) : BetaConv t (normalize t).normalForm :=
  steps_convert (normalize t).reduces

theorem steps_eq_of_irreducible {t u : Term Γ A} (normal : ∀ u, ¬ BetaStep t u)
    (steps : Relation.ReflTransGen BetaStep t u) : u = t :=
  Mettapedia.Logic.Relation.IsNormal.reflTransGen_eq normal steps

theorem normalize_of_irreducible (t : Term Γ A) (normal : ∀ u, ¬ BetaStep t u) :
    (normalize t).normalForm = t := steps_eq_of_irreducible normal (normalize t).reduces

theorem normalize_idempotent (t : Term Γ A) :
    (normalize (normalize t).normalForm).normalForm = (normalize t).normalForm :=
  normalize_of_irreducible _ (normalize t).irreducible

#print axioms toTwoSort_hasType
#print axioms strong_normalization
#print axioms normalize
#print axioms normalize_convert

end Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.Normalization
