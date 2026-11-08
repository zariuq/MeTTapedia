import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUpdateLifting
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableChecking

/-!+# Active equations under rigid local binders

An outer solution acts under a local binder by the existing typed lift: the
new variable is fixed, and only the outer metavariables are instantiated.
Closing an active homogeneous equation with lambdas preserves its solutions
at each outer substitution. Nested binders retain this interpretation.
Heterogeneous equations remain in the ordinary residual store until their
endpoint types can be compared.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentScope

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.DependentTypes TypedContextual.QuotientComprehensionSyntax
open ContextualDependentEta

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L)

theorem fresh_equal_iff {Γ : Context rules} {domain : TypeOver Γ}
    {codomain : TypeOver (extend Γ domain)}
    (first second : Term Γ (rawPi levels domain codomain)) :
    Equal rules Γ.raw first.code second.code (rawPi levels domain codomain).code ↔
      Equal rules (extend Γ domain).raw (Products.rawFreshApp levels first).code
        (Products.rawFreshApp levels second).code codomain.code := by
  constructor
  · intro same
    exact ((QTerm.mk_eq_iff levels _ _).mp (Products.rawFreshApp_congruent levels first second same)).2
  · intro same
    have lambdas := Products.rawLam_congruent levels
      (Products.rawFreshApp levels first) (Products.rawFreshApp levels second) same
    have equal := (Products.rawEta levels first).symm.trans (lambdas.trans (Products.rawEta levels second))
    exact ((QTerm.mk_eq_iff levels _ _).mp equal).2

theorem fresh_application_reindex {Γ Δ : Context rules} (solution : Δ ⟶ Γ)
    {domain : TypeOver Γ} {codomain : TypeOver (extend Γ domain)}
    (function : Term Γ (rawPi levels domain codomain)) :
    (Products.rawFreshApp levels function).reindex (rawLift solution domain) =
      Products.rawFreshApp levels ((function.reindex solution).cast
        (rawPi_reindex levels solution domain codomain)) := by
  apply Term.ext
  change Tm.app (subst (liftSub solution.substitution) (rename wk function.code)) (.var 0) =
    Tm.app (rename wk (subst solution.substitution function.code)) (.var 0)
  rw [subst_liftSub_wk]

theorem lambda_equal_iff {Γ : Context rules} {domain : TypeOver Γ}
    {codomain : TypeOver (extend Γ domain)}
    (first second : Term (extend Γ domain) codomain) :
    Equal rules Γ.raw (Products.rawLam levels first).code (Products.rawLam levels second).code
        (rawPi levels domain codomain).code ↔
      Equal rules (extend Γ domain).raw first.code second.code codomain.code := by
  constructor
  · intro same
    have applied := Products.rawFreshApp_congruent levels
      (Products.rawLam levels first) (Products.rawLam levels second) same
    have equal := (Products.rawFreshBeta levels first).symm.trans
      (applied.trans (Products.rawFreshBeta levels second))
    exact ((QTerm.mk_eq_iff levels _ _).mp equal).2
  · intro same
    exact ((QTerm.mk_eq_iff levels _ _).mp (Products.rawLam_congruent levels first second same)).2

/-- Both endpoints of an active equation have a common formed annotation. -/
structure Active (Γ : Context rules) where
  type : TypeOver Γ
  left : Term Γ type
  right : Term Γ type

namespace Active

def equation {Γ : Context rules} (active : Active Γ) : Equation (TotalTerm Γ) :=
  (⟨active.type, active.left⟩, ⟨active.type, active.right⟩)

def Holds {Γ Δ : Context rules} (active : Active Γ) (solution : Δ ⟶ Γ) : Prop :=
  Equal rules Δ.raw (subst solution.substitution active.left.code)
    (subst solution.substitution active.right.code) (subst solution.substitution active.type.code)

theorem holds_iff_models {Γ Δ : Context rules} (active : Active Γ) (solution : Δ ⟶ Γ) :
    active.Holds solution ↔ (frames levels).Models solution [active.equation] := by
  constructor
  · intro solved entry member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨(active.type.reindex solution).isType.refl, solved⟩
  · intro solved
    exact (solved active.equation (List.mem_singleton_self _)).2

noncomputable def abstract {Γ : Context rules} (domain : TypeOver Γ)
    (active : Active (extend Γ domain)) : Active Γ :=
  ⟨rawPi levels domain active.type, Products.rawLam levels active.left,
    Products.rawLam levels active.right⟩

theorem abstract_holds_iff {Γ Δ : Context rules} (domain : TypeOver Γ)
    (active : Active (extend Γ domain)) (solution : Δ ⟶ Γ) :
    (active.abstract levels domain).Holds solution ↔ active.Holds (rawLift solution domain) := by
  exact lambda_equal_iff levels
    (active.left.reindex (rawLift solution domain)) (active.right.reindex (rawLift solution domain))

/-- The computational form takes the result of the existing universe-join
operation. Its data contain no choice of a semantic representative. -/
def abstractAt {Γ : Context rules} (domain : TypeOver Γ)
    (active : Active (extend Γ domain)) (result : Head)
    (joined : rules.join domain.level active.type.level result) : Active Γ := by
  let annotation : TypeOver Γ :=
    ⟨.pi domain.code active.type.code, result, (levels.join_level joined).1,
      .piForm domain.formed domain.universeWitness active.type.formed active.type.universeWitness joined⟩
  exact ⟨annotation,
    ⟨.lam active.left.code, .lamIntro annotation.formed annotation.universeWitness active.left.typed⟩,
    ⟨.lam active.right.code, .lamIntro annotation.formed annotation.universeWitness active.right.typed⟩⟩

theorem abstractAt_holds_iff {Γ Δ : Context rules} (domain : TypeOver Γ)
    (active : Active (extend Γ domain)) (result : Head)
    (joined : rules.join domain.level active.type.level result) (solution : Δ ⟶ Γ) :
    (active.abstractAt levels domain result joined).Holds solution ↔
      active.Holds (rawLift solution domain) :=
  lambda_equal_iff levels
    (active.left.reindex (rawLift solution domain)) (active.right.reindex (rawLift solution domain))

end Active

/-- Local binders are scoped separately from the outer solvable telescope. -/
inductive Scoped : Context rules → Type
  | active {Γ : Context rules} (equation : Active Γ) : Scoped Γ
  | bind {Γ : Context rules} (domain : TypeOver Γ) (body : Scoped (extend Γ domain)) : Scoped Γ

namespace Scoped

def Holds {Γ Δ : Context rules} : Scoped Γ → (Δ ⟶ Γ) → Prop
  | .active equation, solution => equation.Holds solution
  | .bind domain body, solution => body.Holds (rawLift solution domain)

noncomputable def close {Γ : Context rules} : Scoped Γ → Active Γ
  | .active equation => equation
  | .bind domain body => (body.close).abstract levels domain

/-- Failure to choose a formation universe leaves the scoped problem
available to its caller; it is not a refutation of the equation. -/
def closeWith (choices : ExecutableChecking.HeadChoices rules) {Γ : Context rules} :
    Scoped Γ → Option (Active Γ)
  | .active equation => some equation
  | .bind domain body => do
      let active ← body.closeWith choices
      let result ← choices.join domain.level active.type.level
      return active.abstractAt levels domain result.val result.property

theorem closeWith_holds_iff (choices : ExecutableChecking.HeadChoices rules)
    {Γ : Context rules} (constraint : Scoped Γ) :
    ∀ {closed : Active Γ}, constraint.closeWith levels choices = some closed →
      ∀ {Δ : Context rules} (solution : Δ ⟶ Γ), closed.Holds solution ↔ constraint.Holds solution := by
  induction constraint with
  | active equation =>
    intro closed computed Δ solution
    have same : equation = closed := Option.some.inj computed
    subst closed
    rfl
  | bind domain body ih =>
    intro closed computed Δ solution
    cases inner : body.closeWith levels choices with
    | none => simp [closeWith, inner] at computed
    | some active =>
      cases joinResult : choices.join domain.level active.type.level with
      | none => simp [closeWith, inner, joinResult] at computed
      | some result =>
        have same : active.abstractAt levels domain result.val result.property = closed := by
          simpa [closeWith, inner, joinResult] using computed
        subst closed
        exact (Active.abstractAt_holds_iff levels domain active result.val result.property solution).trans
          (ih inner (rawLift solution domain))

theorem closeWith_exists (choices : ExecutableChecking.HeadChoices rules)
    (total : ∀ first second, rules.isUniverse first → rules.isUniverse second →
      ∃ result, choices.join first second = some result)
    {Γ : Context rules} (constraint : Scoped Γ) :
    ∃ closed, constraint.closeWith levels choices = some closed := by
  induction constraint with
  | active equation => exact ⟨equation, rfl⟩
  | bind domain body ih =>
    obtain ⟨active, inner⟩ := ih
    obtain ⟨result, joined⟩ := total domain.level active.type.level
      domain.universeWitness active.type.universeWitness
    exact ⟨active.abstractAt levels domain result.val result.property, by simp [closeWith, inner, joined]⟩

theorem close_holds_iff {Γ : Context rules} (constraint : Scoped Γ) :
    ∀ {Δ : Context rules} (solution : Δ ⟶ Γ),
      (constraint.close levels).Holds solution ↔ constraint.Holds solution := by
  induction constraint with
  | active equation => intro Δ solution; rfl
  | bind domain body ih =>
    intro Δ solution
    exact (Active.abstract_holds_iff levels domain (body.close levels) solution).trans
      (ih (rawLift solution domain))

theorem close_models_iff {Γ Δ : Context rules} (constraint : Scoped Γ) (solution : Δ ⟶ Γ) :
    (frames levels).Models solution [(constraint.close levels).equation] ↔ constraint.Holds solution :=
  (Active.holds_iff_models levels _ _).symm.trans (close_holds_iff levels constraint solution)

/-- The interpretation keeps the target of the solution fixed. Taking an
empty target therefore preserves closed solutions as well as symbolic ones. -/
theorem solutions_iff {Γ : Context rules} (constraint : Scoped Γ) (point : Context rules) :
    (∃ solution : point ⟶ Γ, (frames levels).Models solution [(constraint.close levels).equation]) ↔
      ∃ solution : point ⟶ Γ, constraint.Holds solution :=
  exists_congr fun solution => close_models_iff levels constraint solution

include levels in
theorem holds_comp {Γ Δ Θ : Context rules} (constraint : Scoped Γ)
    (solution : Δ ⟶ Γ) (refinement : Θ ⟶ Δ) (solved : constraint.Holds solution) :
    constraint.Holds (refinement ≫ solution) :=
  (close_models_iff levels constraint _).mp
    (Frames.models_comp (X := frames levels)
      ((close_models_iff levels constraint solution).mpr solved) refinement)

theorem holds_iff_of_same {Γ Δ : Context rules} (constraint : Scoped Γ)
    (first second : Δ ⟶ Γ)
    (same : ∀ term : TotalTerm Γ, (frames levels).E (term.reindex first) (term.reindex second)) :
    constraint.Holds first ↔ constraint.Holds second :=
  (close_models_iff levels constraint first).symm.trans
    ((Elimination.models_pointwise levels same [(constraint.close levels).equation]).trans
      (close_models_iff levels constraint second))

end Scoped

noncomputable def openFunction {Γ : Context rules} {domain : TypeOver Γ}
    {codomain : TypeOver (extend Γ domain)}
    (first second : Term Γ (rawPi levels domain codomain)) : Scoped Γ :=
  .bind domain (.active ⟨codomain, Products.rawFreshApp levels first, Products.rawFreshApp levels second⟩)

theorem openFunction_holds_iff {Γ Δ : Context rules} {domain : TypeOver Γ}
    {codomain : TypeOver (extend Γ domain)}
    (first second : Term Γ (rawPi levels domain codomain)) (solution : Δ ⟶ Γ) :
    (openFunction levels first second).Holds solution ↔
      Equal rules Δ.raw (subst solution.substitution first.code)
        (subst solution.substitution second.code)
        (subst solution.substitution (rawPi levels domain codomain).code) := by
  have same := (fresh_equal_iff levels
    ((first.reindex solution).cast (rawPi_reindex levels solution domain codomain))
    ((second.reindex solution).cast (rawPi_reindex levels solution domain codomain))).symm
  rw [← fresh_application_reindex levels solution first,
    ← fresh_application_reindex levels solution second] at same
  exact same

end ContextualDependentScope
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
