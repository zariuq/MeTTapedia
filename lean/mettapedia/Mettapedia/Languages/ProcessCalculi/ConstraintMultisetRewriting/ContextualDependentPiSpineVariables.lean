import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPiSpineReindex
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentTypedInversion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruning

/-!
# Variable maps through complete dependent Pi spines

An injective variable map lifts through every supplied binder. Its computed
renaming agrees with the actual typed spine map and preserves declarations
exactly when the original map does. The outer-context inclusion is also
computed, and the spine map's action on outer variables is proved for every
typed substitution, including substitutions by compound terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPiSpine

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentTypedInversion

variable {Head : Type} {rules : Rules Head}

namespace Spine

def mapRen : {Γ : Context rules} → {type : TypeOver Γ} → (spine : Spine type) →
    {Δ : Context rules} → (base : Δ ⟶ Γ) → Ren Γ.arity Δ.arity →
      Ren spine.target.arity (spine.reindex base).target.arity
  | _, _, .stop _, _, _, rho => rho
  | _, _, .bind shape rest, _, base, rho => rest.mapRen (rawLift base shape.domain) (liftRen rho)

theorem mapRen_substitution {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ {Δ : Context rules} (base : Δ ⟶ Γ) (rho : Ren Γ.arity Δ.arity), base.substitution = renSub rho →
      (spine.map base).substitution = renSub (spine.mapRen base rho) := by
  induction spine with
  | stop type => intro Δ base rho asVariables; exact asVariables
  | bind shape rest ih =>
      intro Δ base rho asVariables
      apply ih (rawLift base shape.domain) (liftRen rho)
      change liftSub base.substitution = renSub (liftRen rho)
      rw [asVariables, liftSub_renSub]

theorem mapRen_injective {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ {Δ : Context rules} (base : Δ ⟶ Γ) (rho : Ren Γ.arity Δ.arity), Function.Injective rho →
      Function.Injective (spine.mapRen base rho) := by
  induction spine with
  | stop type => intro Δ base rho injective; exact injective
  | bind shape rest ih =>
      intro Δ base rho injective
      exact ih (rawLift base shape.domain) (liftRen rho) (ContextualDependentPruning.liftRen_injective injective)

theorem mapRen_compatible {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ {Δ : Context rules} (base : Δ ⟶ Γ) (rho : Ren Γ.arity Δ.arity), base.substitution = renSub rho →
      CtxRen Γ.raw Δ.raw rho → CtxRen spine.target.raw (spine.reindex base).target.raw (spine.mapRen base rho) := by
  induction spine with
  | stop type => intro Δ base rho asVariables compatible; exact compatible
  | @bind context shape rest ih =>
      intro Δ base rho asVariables compatible
      have liftedVariables : (rawLift base shape.domain).substitution = renSub (liftRen rho) := by
        change liftSub base.substitution = renSub (liftRen rho)
        rw [asVariables, liftSub_renSub]
      apply ih (rawLift base shape.domain) (liftRen rho) liftedVariables
      change CtxRen (.snoc context.raw shape.domain.code) (.snoc Δ.raw (subst base.substitution shape.domain.code)) (liftRen rho)
      rw [asVariables, subst_renSub]
      exact compatible.snoc shape.domain.code

def mapInclusion {Γ Δ : Context rules} {type : TypeOver Γ} (spine : Spine type) (inclusion : Inclusion Γ Δ) :
    Inclusion spine.target (spine.reindex inclusion.hom).target where
  forward := spine.mapRen inclusion.hom inclusion.forward
  injective := spine.mapRen_injective inclusion.hom inclusion.forward inclusion.injective
  typed := by
    have typed := (spine.map inclusion.hom).typed
    rw [spine.mapRen_substitution inclusion.hom inclusion.forward rfl] at typed
    exact typed

theorem mapInclusion_hom {Γ Δ : Context rules} {type : TypeOver Γ} (spine : Spine type) (inclusion : Inclusion Γ Δ) :
    (spine.mapInclusion inclusion).hom = spine.map inclusion.hom :=
  Hom.ext (spine.mapRen_substitution inclusion.hom inclusion.forward rfl).symm

theorem mapInclusion_compatible {Γ Δ : Context rules} {type : TypeOver Γ} (spine : Spine type) (inclusion : Inclusion Γ Δ)
    (compatible : CtxRen Γ.raw Δ.raw inclusion.forward) :
    CtxRen spine.target.raw (spine.reindex inclusion.hom).target.raw (spine.mapInclusion inclusion).forward :=
  spine.mapRen_compatible inclusion.hom inclusion.forward rfl compatible

def outerRen : {Γ : Context rules} → {type : TypeOver Γ} → (spine : Spine type) → Ren Γ.arity spine.target.arity
  | _, _, .stop _ => idRen
  | _, _, .bind _ rest => fun index => rest.outerRen index.succ

theorem projection_substitution {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    spine.projection.substitution = renSub spine.outerRen := by
  induction spine with
  | stop type => rfl
  | bind shape rest ih =>
      funext index
      change rest.projection.substitution index.succ = .var (rest.outerRen index.succ)
      rw [ih]
      rfl

theorem outerRen_injective {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) : Function.Injective spine.outerRen := by
  induction spine with
  | stop type => exact Function.injective_id
  | bind shape rest ih => exact ih.comp (Fin.succ_injective _)

theorem outerRen_compatible {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    CtxRen Γ.raw spine.target.raw spine.outerRen := by
  induction spine with
  | stop type => exact CtxRen.id _
  | @bind context shape rest ih =>
      change CtxRen context.raw rest.target.raw (fun index => rest.outerRen index.succ)
      exact CtxRen.comp (CtxRen.wk _ shape.domain.code) ih

def outerInclusion {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) : Inclusion Γ spine.target where
  forward := spine.outerRen
  injective := spine.outerRen_injective
  typed := by
    have typed := spine.projection.typed
    rw [spine.projection_substitution] at typed
    exact typed

theorem map_outer {Γ Δ : Context rules} {type : TypeOver Γ} (spine : Spine type) (base : Δ ⟶ Γ) (index : Fin Γ.arity) :
    (spine.map base).substitution (spine.outerRen index) =
      Presentation.rename (spine.reindex base).outerRen (base.substitution index) := by
  have square := congrArg (fun map => map.substitution index) (spine.map_projection base)
  change subst (spine.map base).substitution (spine.projection.substitution index) =
    subst (spine.reindex base).projection.substitution (base.substitution index) at square
  rw [spine.projection_substitution, (spine.reindex base).projection_substitution] at square
  simpa only [renSub, subst, subst_renSub] using square

theorem map_outer_term {Γ Δ : Context rules} {type : TypeOver Γ} (spine : Spine type) (base : Δ ⟶ Γ) (term : Tm Head Γ.arity) :
    subst (spine.map base).substitution (Presentation.rename spine.outerRen term) =
      Presentation.rename (spine.reindex base).outerRen (subst base.substitution term) := by
  rw [subst_rename, rename_subst]
  apply subst_ext
  exact spine.map_outer base

end Spine
end ContextualDependentPiSpine
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
