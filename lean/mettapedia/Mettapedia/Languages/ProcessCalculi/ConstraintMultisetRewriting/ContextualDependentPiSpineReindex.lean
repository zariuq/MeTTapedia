import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPiSpine

/-!
# Reindexing complete dependent Pi spines

Each successive domain and codomain is reindexed through the actual typed
lift. The resulting context map commutes with the projection to the outer
context. Opening and abstraction commute with every outer substitution,
including the dependent annotation of the final result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPiSpine

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax

variable {Head : Type} {rules : Rules Head}

namespace Spine

def reindex : {Γ : Context rules} → {type : TypeOver Γ} → (spine : Spine type) →
    {Δ : Context rules} → (base : Δ ⟶ Γ) → Spine (type.reindex base)
  | _, type, .stop _, _, base => .stop (type.reindex base)
  | _, _, .bind shape rest, _, base => .bind (shape.reindex base) (rest.reindex (rawLift base shape.domain))

def map : {Γ : Context rules} → {type : TypeOver Γ} → (spine : Spine type) →
    {Δ : Context rules} → (base : Δ ⟶ Γ) → (spine.reindex base).target ⟶ spine.target
  | _, _, .stop _, _, base => base
  | _, _, .bind shape rest, _, base => rest.map (rawLift base shape.domain)

theorem length_reindex {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ {Δ : Context rules} (base : Δ ⟶ Γ), (spine.reindex base).length = spine.length := by
  induction spine with
  | stop type => intros; rfl
  | bind shape rest ih => intro Δ base; exact congrArg Nat.succ (ih (rawLift base shape.domain))

theorem result_reindex {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ {Δ : Context rules} (base : Δ ⟶ Γ), spine.result.reindex (spine.map base) = (spine.reindex base).result := by
  induction spine with
  | stop type => intros; rfl
  | bind shape rest ih => intro Δ base; exact ih (rawLift base shape.domain)

theorem map_projection {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ {Δ : Context rules} (base : Δ ⟶ Γ),
      spine.map base ≫ spine.projection = (spine.reindex base).projection ≫ base := by
  induction spine with
  | stop type => intro Δ base; exact (Category.comp_id base).trans (Category.id_comp base).symm
  | bind shape rest ih =>
      intro Δ base
      change rest.map (rawLift base shape.domain) ≫ (rest.projection ≫ projectionHom _ shape.domain) =
        ((rest.reindex (rawLift base shape.domain)).projection ≫ projectionHom Δ (shape.domain.reindex base)) ≫ base
      rw [← Category.assoc, ih, Category.assoc, ContextualDependentUpdate.lift_projection, ← Category.assoc]

theorem openFunction_reindex_code {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ {Δ : Context rules} (base : Δ ⟶ Γ) (function : Term Γ type),
      ((spine.openFunction function).reindex (spine.map base)).code =
        ((spine.reindex base).openFunction (function.reindex base)).code := by
  induction spine with
  | stop type => intros; rfl
  | bind shape rest ih =>
      intro Δ base function
      have crossed := ih (rawLift base shape.domain) (shape.fresh function)
      rw [shape.fresh_reindex] at crossed
      exact crossed

theorem openFunction_reindex {Γ Δ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    (base : Δ ⟶ Γ) (function : Term Γ type) :
    ((spine.openFunction function).reindex (spine.map base)).cast (spine.result_reindex base) =
      (spine.reindex base).openFunction (function.reindex base) :=
  Term.ext ((Term.cast_code _ _).trans (spine.openFunction_reindex_code base function))

theorem abstractBody_reindex_code {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ {Δ : Context rules} (base : Δ ⟶ Γ) (body : Term spine.target spine.result),
      ((spine.abstractBody body).reindex base).code =
        ((spine.reindex base).abstractBody ((body.reindex (spine.map base)).cast (spine.result_reindex base))).code := by
  induction spine with
  | stop type => intro Δ base body; exact (Term.cast_code _ _).symm
  | bind shape rest ih =>
      intro Δ base body
      exact congrArg Tm.lam (ih (rawLift base shape.domain) body)

theorem abstractBody_reindex {Γ Δ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    (base : Δ ⟶ Γ) (body : Term spine.target spine.result) :
    (spine.abstractBody body).reindex base =
      (spine.reindex base).abstractBody ((body.reindex (spine.map base)).cast (spine.result_reindex base)) :=
  Term.ext (spine.abstractBody_reindex_code base body)

end Spine
end ContextualDependentPiSpine
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
