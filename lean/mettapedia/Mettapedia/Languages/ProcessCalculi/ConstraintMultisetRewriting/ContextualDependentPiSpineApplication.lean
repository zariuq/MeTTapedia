import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPiSpineReindex

/-!
# Applying a dependent Pi spine to a typed argument map

The function may live in the ambient context. Each successive argument is
read from the same typed telescope map, and application retains the exact
dependent result type. For a reindexed source function this agrees with
opening and then substituting; applying an abstraction recovers the supplied
body by typed beta equality.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual

variable {Head : Type} {rules : Rules Head}

namespace ContextualDependentPiShape.Shape

variable {Γ : Context rules} (shape : ContextualDependentPiShape.Shape Γ)

def applyAt {Δ : Context rules} (arguments : Δ ⟶ extend Γ shape.domain)
    (function : Term Δ (shape.whole.reindex (arguments ≫ projectionHom Γ shape.domain))) :
    Term Δ (shape.codomain.reindex arguments) :=
  (shape.apply (arguments ≫ projectionHom Γ shape.domain) function (pulledNewest arguments)).cast
    (congrArg (fun map => shape.codomain.reindex map) (pair_eta arguments))

theorem applyAt_reindexed {Δ : Context rules} (arguments : Δ ⟶ extend Γ shape.domain) (function : Term Γ shape.whole) :
    shape.applyAt arguments (function.reindex (arguments ≫ projectionHom Γ shape.domain)) = (shape.fresh function).reindex arguments := by
  apply Term.ext
  rw [applyAt, Term.cast_code]
  change Tm.app (subst (subComp arguments.substitution projection) function.code) (pulledNewest arguments).code =
    subst arguments.substitution (.app (Presentation.rename wk function.code) (.var 0))
  rw [pulledNewest_code, ← subst_subComp, subst_projection]
  rfl

theorem apply_congruent {Δ : Context rules} (base : Δ ⟶ Γ)
    (first second : Term Δ (shape.whole.reindex base)) (argument : Term Δ (shape.domain.reindex base))
    (same : Equal rules Δ.raw first.code second.code (shape.whole.reindex base).code) :
    Equal rules Δ.raw (shape.apply base first argument).code (shape.apply base second argument).code
      (shape.codomain.reindex (pair base argument)).code := by
  change Equal rules Δ.raw first.code second.code (subst base.substitution shape.whole.code) at same
  rw [shape.code] at same
  have applied := Derivable.appCong same (.refl argument.typed)
  change Equal rules Δ.raw (.app first.code argument.code) (.app second.code argument.code)
    (inst0 argument.code (subst (liftSub base.substitution) shape.codomain.code)) at applied
  rw [ContextualDependentSigma.inst0_lift] at applied
  exact applied

theorem applyAt_congruent {Δ : Context rules} (arguments : Δ ⟶ extend Γ shape.domain)
    (first second : Term Δ (shape.whole.reindex (arguments ≫ projectionHom Γ shape.domain)))
    (same : Equal rules Δ.raw first.code second.code (shape.whole.reindex (arguments ≫ projectionHom Γ shape.domain)).code) :
    Equal rules Δ.raw (shape.applyAt arguments first).code (shape.applyAt arguments second).code (shape.codomain.reindex arguments).code := by
  have applied := shape.apply_congruent (arguments ≫ projectionHom Γ shape.domain) first second (pulledNewest arguments) same
  change Equal rules Δ.raw (.app first.code (pulledNewest arguments).code) (.app second.code (pulledNewest arguments).code)
    (shape.codomain.reindex (pair (arguments ≫ projectionHom Γ shape.domain) (pulledNewest arguments))).code at applied
  rw [pair_eta] at applied
  simpa only [applyAt, Term.cast_code, apply] using applied

end ContextualDependentPiShape.Shape

namespace ContextualDependentPiSpine.Spine

def apply : {Γ : Context rules} → {type : TypeOver Γ} → (spine : Spine type) →
    {Δ : Context rules} → (arguments : Δ ⟶ spine.target) →
      Term Δ (type.reindex (arguments ≫ spine.projection)) → Term Δ (spine.result.reindex arguments)
  | _, type, .stop _, _, arguments, function =>
      function.cast (congrArg (fun base => type.reindex base) (Category.comp_id arguments))
  | Γ, _, .bind shape rest, _, arguments, function =>
      rest.apply arguments (shape.applyAt (arguments ≫ rest.projection)
        (function.cast (congrArg (fun base => shape.whole.reindex base)
          (Category.assoc arguments rest.projection (projectionHom Γ shape.domain)).symm)))

set_option backward.isDefEq.respectTransparency false in
theorem apply_reindexed {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ {Δ : Context rules} (arguments : Δ ⟶ spine.target) (function : Term Γ type),
      spine.apply arguments (function.reindex (arguments ≫ spine.projection)) =
        (spine.openFunction function).reindex arguments := by
  induction spine with
  | stop type =>
      intro Δ arguments function
      apply Term.ext
      rw [apply, Term.cast_code]
      change subst (arguments ≫ 𝟙 _).substitution function.code = subst arguments.substitution function.code
      rw [Category.comp_id]
  | bind shape rest ih =>
      intro Δ arguments function
      have reassociated :
          (function.reindex (arguments ≫ (rest.projection ≫ projectionHom _ shape.domain))).cast
            (congrArg (fun base => shape.whole.reindex base)
              (Category.assoc arguments rest.projection (projectionHom _ shape.domain)).symm) =
          function.reindex ((arguments ≫ rest.projection) ≫ projectionHom _ shape.domain) := by
        apply Term.ext
        rw [Term.cast_code]
        exact congrArg (fun map => subst map.substitution function.code)
          (Category.assoc arguments rest.projection (projectionHom _ shape.domain)).symm
      simp only [apply, openFunction, projection]
      rw [reassociated, shape.applyAt_reindexed]
      exact ih arguments (shape.fresh function)

set_option backward.isDefEq.respectTransparency false in
theorem apply_congruent {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ {Δ : Context rules} (arguments : Δ ⟶ spine.target)
      (first second : Term Δ (type.reindex (arguments ≫ spine.projection))),
      Equal rules Δ.raw first.code second.code (type.reindex (arguments ≫ spine.projection)).code →
        Equal rules Δ.raw (spine.apply arguments first).code (spine.apply arguments second).code (spine.result.reindex arguments).code := by
  induction spine with
  | stop type =>
      intro Δ arguments first second same
      simp only [apply, Term.cast_code]
      exact Eq.mp (congrArg (fun code => Equal rules Δ.raw first.code second.code code)
        (congrArg (fun base => (type.reindex base).code) (Category.comp_id arguments))) same
  | bind shape rest ih =>
      intro Δ arguments first second same
      let types := congrArg (fun base => shape.whole.reindex base)
        (Category.assoc arguments rest.projection (projectionHom _ shape.domain)).symm
      have converted : Equal rules Δ.raw (first.cast types).code (second.cast types).code
          (shape.whole.reindex ((arguments ≫ rest.projection) ≫ projectionHom _ shape.domain)).code := by
        rw [Term.cast_code, Term.cast_code]
        exact (congrArg TypeOver.code types) ▸ same
      exact ih arguments _ _ (shape.applyAt_congruent (arguments ≫ rest.projection) _ _ converted)

theorem apply_beta {Γ Δ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    (body : Term spine.target spine.result) (arguments : Δ ⟶ spine.target) :
    Equal rules Δ.raw (spine.apply arguments ((spine.abstractBody body).reindex (arguments ≫ spine.projection))).code
      (body.reindex arguments).code (spine.result.reindex arguments).code := by
  rw [spine.apply_reindexed]
  exact spine.applyUnder_beta body arguments

end ContextualDependentPiSpine.Spine
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
