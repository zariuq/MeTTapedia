import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPiSpineReindex

/-!
# Typed Pi spines and the existing rigid-scope interpretation

The same dependent telescope becomes a nested Scoped constraint. At every
outer substitution, opening a homogeneous function equation preserves and
reflects its meaning. Abstracting an equation at the final result type also
preserves and reflects its scoped meaning, using the original whole annotation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPiSpine

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentScope ContextualDependentEta

variable {Head : Type} {rules : Rules Head}

namespace Spine

def toScoped : {Γ : Context rules} → {type : TypeOver Γ} → (spine : Spine type) → Active spine.target → Scoped Γ
  | _, _, .stop _, body => .active body
  | _, _, .bind shape rest, body => .bind shape.domain (rest.toScoped body)

theorem toScoped_holds_iff {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ (body : Active spine.target) {Δ : Context rules} (solution : Δ ⟶ Γ),
      (spine.toScoped body).Holds solution ↔ body.Holds (spine.map solution) := by
  induction spine with
  | stop type => intros; rfl
  | bind shape rest ih => intro body Δ solution; exact ih body (rawLift solution shape.domain)

def openedConstraint {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) (first second : Term Γ type) : Scoped Γ :=
  spine.toScoped ⟨spine.result, spine.openFunction first, spine.openFunction second⟩

theorem openedConstraint_holds_iff {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ {Δ : Context rules} (solution : Δ ⟶ Γ) (first second : Term Γ type),
      (spine.openedConstraint first second).Holds solution ↔
        Equal rules Δ.raw (first.reindex solution).code (second.reindex solution).code (type.reindex solution).code := by
  induction spine with
  | stop type => intros; rfl
  | bind shape rest ih =>
      intro Δ solution first second
      have inner := ih (rawLift solution shape.domain) (shape.fresh first) (shape.fresh second)
      have outer := (shape.reindex solution).fresh_equal_iff (first.reindex solution) (second.reindex solution)
      rw [← shape.fresh_reindex solution first, ← shape.fresh_reindex solution second] at outer
      exact inner.trans outer.symm

def closeBody {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    (first second : Term spine.target spine.result) : Active Γ :=
  ⟨type, spine.abstractBody first, spine.abstractBody second⟩

theorem closeBody_holds_iff {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ {Δ : Context rules} (solution : Δ ⟶ Γ) (first second : Term spine.target spine.result),
      (spine.closeBody first second).Holds solution ↔
        (spine.toScoped ⟨spine.result, first, second⟩).Holds solution := by
  induction spine with
  | stop type => intros; rfl
  | bind shape rest ih =>
      intro Δ solution first second
      have outer := (shape.reindex solution).abstract_equal_iff
        ((rest.abstractBody first).reindex (rawLift solution shape.domain))
        ((rest.abstractBody second).reindex (rawLift solution shape.domain))
      rw [← shape.abstract_reindex solution (rest.abstractBody first),
        ← shape.abstract_reindex solution (rest.abstractBody second)] at outer
      exact outer.trans (ih (rawLift solution shape.domain) first second)

variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L)

theorem opened_models_iff {Γ Δ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    (first second : Term Γ type) (solution : Δ ⟶ Γ) :
    (frames levels).Models solution [((⟨type, first⟩ : TotalTerm Γ), (⟨type, second⟩ : TotalTerm Γ))] ↔
      (spine.openedConstraint first second).Holds solution :=
  (Active.holds_iff_models levels (⟨type, first, second⟩ : Active Γ) solution).symm.trans
    (spine.openedConstraint_holds_iff solution first second).symm

theorem closed_models_iff {Γ Δ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    (first second : Term spine.target spine.result) (solution : Δ ⟶ Γ) :
    (frames levels).Models solution [(spine.closeBody first second).equation] ↔
      (spine.toScoped ⟨spine.result, first, second⟩).Holds solution :=
  (Active.holds_iff_models levels (spine.closeBody first second) solution).symm.trans
    (spine.closeBody_holds_iff solution first second)

theorem fixed_point_solutions_iff {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    (first second : Term Γ type) (point : Context rules) :
    (∃ solution : point ⟶ Γ,
      (frames levels).Models solution [((⟨type, first⟩ : TotalTerm Γ), (⟨type, second⟩ : TotalTerm Γ))]) ↔
      ∃ solution : point ⟶ Γ, (spine.openedConstraint first second).Holds solution :=
  exists_congr fun solution => spine.opened_models_iff levels first second solution

end Spine
end ContextualDependentPiSpine
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
