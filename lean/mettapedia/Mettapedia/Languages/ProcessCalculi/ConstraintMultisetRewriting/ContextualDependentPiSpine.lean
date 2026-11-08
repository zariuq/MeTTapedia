import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPiShape

/-!
# Finite typed dependent Pi spines

Each binder carries its actual formed Pi annotation. Opening applies the
function to successive fresh rigid variables; abstraction closes the same
typed telescope. Their beta and eta laws hold for every finite spine and
retain dependent result types and universe metadata.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPiSpine

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentPiShape

variable {Head : Type} {rules : Rules Head}

inductive Spine : {Γ : Context rules} → TypeOver Γ → Type
  | stop {Γ : Context rules} (type : TypeOver Γ) : Spine type
  | bind {Γ : Context rules} (shape : Shape Γ) (rest : Spine shape.codomain) : Spine shape.whole

namespace Spine

def target : {Γ : Context rules} → {type : TypeOver Γ} → Spine type → Context rules
  | Γ, _, .stop _ => Γ
  | _, _, .bind _ rest => rest.target

def result : {Γ : Context rules} → {type : TypeOver Γ} → (spine : Spine type) → TypeOver spine.target
  | _, _, .stop type => type
  | _, _, .bind _ rest => rest.result

def length : {Γ : Context rules} → {type : TypeOver Γ} → Spine type → Nat
  | _, _, .stop _ => 0
  | _, _, .bind _ rest => rest.length + 1

def projection : {Γ : Context rules} → {type : TypeOver Γ} → (spine : Spine type) → spine.target ⟶ Γ
  | Γ, _, .stop _ => 𝟙 Γ
  | Γ, _, .bind shape rest => rest.projection ≫ projectionHom Γ shape.domain

def openFunction : {Γ : Context rules} → {type : TypeOver Γ} → (spine : Spine type) →
    Term Γ type → Term spine.target spine.result
  | _, _, .stop _, function => function
  | _, _, .bind shape rest, function => rest.openFunction (shape.fresh function)

def abstractBody : {Γ : Context rules} → {type : TypeOver Γ} → (spine : Spine type) →
    Term spine.target spine.result → Term Γ type
  | _, _, .stop _, body => body
  | _, _, .bind shape rest, body => shape.abstract (rest.abstractBody body)

theorem target_arity {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    spine.target.arity = Γ.arity + spine.length := by
  induction spine with
  | stop type => rfl
  | bind shape rest ih =>
      simp only [target, length, extend] at ih ⊢
      omega

theorem openFunction_congruent {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ (first second : Term Γ type), Equal rules Γ.raw first.code second.code type.code →
      Equal rules spine.target.raw (spine.openFunction first).code (spine.openFunction second).code spine.result.code := by
  induction spine with
  | stop type => intro first second same; exact same
  | bind shape rest ih =>
      intro first second same
      exact ih (shape.fresh first) (shape.fresh second) (shape.fresh_congruent first second same)

theorem abstractBody_congruent {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ (first second : Term spine.target spine.result), Equal rules spine.target.raw first.code second.code spine.result.code →
      Equal rules Γ.raw (spine.abstractBody first).code (spine.abstractBody second).code type.code := by
  induction spine with
  | stop type => intro first second same; exact same
  | bind shape rest ih =>
      intro first second same
      exact shape.abstract_congruent _ _ (ih first second same)

theorem beta {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ (body : Term spine.target spine.result),
      Equal rules spine.target.raw (spine.openFunction (spine.abstractBody body)).code body.code spine.result.code := by
  induction spine with
  | stop type => intro body; exact .refl body.typed
  | bind shape rest ih =>
      intro body
      exact (rest.openFunction_congruent _ _ (shape.fresh_beta (rest.abstractBody body))).trans (ih body)

theorem eta {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ (function : Term Γ type), Equal rules Γ.raw (spine.abstractBody (spine.openFunction function)).code function.code type.code := by
  induction spine with
  | stop type => intro function; exact .refl function.typed
  | bind shape rest ih =>
      intro function
      exact (shape.abstract_congruent _ _ (ih (shape.fresh function))).trans (shape.eta function)

theorem openFunction_equal_iff {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) (first second : Term Γ type) :
    Equal rules Γ.raw first.code second.code type.code ↔
      Equal rules spine.target.raw (spine.openFunction first).code (spine.openFunction second).code spine.result.code := by
  constructor
  · exact spine.openFunction_congruent first second
  · intro same
    exact (spine.eta first).symm.trans ((spine.abstractBody_congruent _ _ same).trans (spine.eta second))

theorem abstractBody_equal_iff {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    (first second : Term spine.target spine.result) :
    Equal rules Γ.raw (spine.abstractBody first).code (spine.abstractBody second).code type.code ↔
      Equal rules spine.target.raw first.code second.code spine.result.code := by
  constructor
  · intro same
    exact (spine.beta first).symm.trans ((spine.openFunction_congruent _ _ same).trans (spine.beta second))
  · exact spine.abstractBody_congruent first second

def applyUnder {Γ Δ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    (function : Term Γ type) (arguments : Δ ⟶ spine.target) : Term Δ (spine.result.reindex arguments) :=
  (spine.openFunction function).reindex arguments

theorem applyUnder_beta {Γ Δ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    (body : Term spine.target spine.result) (arguments : Δ ⟶ spine.target) :
    Equal rules Δ.raw (spine.applyUnder (spine.abstractBody body) arguments).code
      (body.reindex arguments).code (spine.result.reindex arguments).code :=
  (spine.beta body).substitute arguments.typed

end Spine
end ContextualDependentPiSpine
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
