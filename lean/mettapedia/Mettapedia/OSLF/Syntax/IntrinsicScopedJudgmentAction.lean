import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalJudgmentCategory
import Mathlib.CategoryTheory.Types.Basic

/-!
# Substitution actions on judgment-indexed evidence

Evidence indexed by contextual judgments carries a substitution action when
each environment moves evidence at a judgment to evidence at the substituted
judgment, with the identity and composition laws. The action is independent
of any rule presentation: rule models over global or rule-local telescopes
carry the same action on their evidence, and every statement here serves
both.

Along the arrows of the fixed-sort judgment category the action is a functor
to types.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedJudgmentAction

open CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalJudgmentCategory

universe u v

variable {S : Signature}

/-- A contextual substitution action on judgment-indexed evidence: an
environment moves evidence at a judgment to evidence at the substituted
judgment. -/
abbrev ActionOn (A : BindingCloneAlgebra.Algebra.{u} S) (carrier : Judgment A → Type v) :
    Type (max u v) :=
  ∀ (j : Judgment A), carrier j →
    ∀ {Δ : Ctx S} (σ : Environment S A.substitution.Carrier j.1 Δ)
      (target : Judgment A), substJudgment j σ = target → carrier target

/-- The identity environment fixes all evidence. -/
abbrev ActionOn.IdentityLaw {A : BindingCloneAlgebra.Algebra.{u} S}
    {carrier : Judgment A → Type v} (act : ActionOn A carrier) : Prop :=
  ∀ (j : Judgment A) (value : carrier j)
    (h : substJudgment j (fun _ v => A.substitution.injectVar v) = j),
    act j value (fun _ v => A.substitution.injectVar v) j h = value

/-- Acting twice is acting along the composite environment. -/
abbrev ActionOn.CompLaw {A : BindingCloneAlgebra.Algebra.{u} S}
    {carrier : Judgment A → Type v} (act : ActionOn A carrier) : Prop :=
  ∀ (j : Judgment A) (value : carrier j) {Δ Θ : Ctx S}
    (σ : Environment S A.substitution.Carrier j.1 Δ)
    (τ : Environment S A.substitution.Carrier Δ Θ) (target : Judgment A)
    (hSecond : substJudgment (substJudgment j σ) τ = target)
    (hDirect : substJudgment j
      (fun t v => A.substitution.substitute τ (σ t v)) = target),
    act (substJudgment j σ) (act j value σ (substJudgment j σ) rfl) τ target
        hSecond =
      act j value (fun t v => A.substitution.substitute τ (σ t v)) target
        hDirect

/-- Judgment-indexed evidence with a lawful contextual substitution action. -/
structure JudgmentAction (A : BindingCloneAlgebra.Algebra.{u} S) where
  carrier : Judgment A → Type v
  act : ActionOn A carrier
  act_identity : ActionOn.IdentityLaw act
  act_comp : ActionOn.CompLaw act

namespace JudgmentAction

section Transport

variable {A : BindingCloneAlgebra.Algebra.{u} S}

/-- Transporting indices and proof witnesses does not change an action. -/
theorem act_heq (action : JudgmentAction.{u, v} A)
    {j₁ j₂ : Judgment A} (sameJudgment : j₁ = j₂)
    {value₁ : action.carrier j₁} {value₂ : action.carrier j₂}
    (sameValue : HEq value₁ value₂) {Δ : Ctx S}
    {σ₁ : Environment S A.substitution.Carrier j₁.1 Δ}
    {σ₂ : Environment S A.substitution.Carrier j₂.1 Δ} (sameEnv : HEq σ₁ σ₂)
    {target₁ target₂ : Judgment A} (sameTarget : target₁ = target₂)
    (h₁ : substJudgment j₁ σ₁ = target₁) (h₂ : substJudgment j₂ σ₂ = target₂) :
    HEq (action.act j₁ value₁ σ₁ target₁ h₁)
      (action.act j₂ value₂ σ₂ target₂ h₂) := by
  subst sameJudgment
  cases sameValue
  cases sameEnv
  subst sameTarget
  rfl

end Transport

section Arrows

variable {A : BindingCloneAlgebra.Algebra.{0} S}

/-- The action along an arrow of the fixed-sort judgment category. -/
def actArrow (action : JudgmentAction.{0, v} A) {sort : S.Srt}
    {first second : State A sort} (f : first ⟶ second)
    (value : action.carrier (first.asJudgment A)) :
    action.carrier (second.asJudgment A) :=
  action.act (first.asJudgment A) value f.environment (second.asJudgment A)
    (Map.as_substitution A f)

theorem actArrow_id (action : JudgmentAction.{0, v} A) {sort : S.Srt}
    (state : State A sort) (value : action.carrier (state.asJudgment A)) :
    action.actArrow (𝟙 state) value = value :=
  action.act_identity (state.asJudgment A) value _

/-- Acting along a composite arrow is acting along each arrow in turn. -/
theorem actArrow_comp (action : JudgmentAction.{0, v} A) {sort : S.Srt}
    {first middle last : State A sort}
    (one : first ⟶ middle) (two : middle ⟶ last)
    (value : action.carrier (first.asJudgment A)) :
    action.actArrow (one ≫ two) value =
      action.actArrow two (action.actArrow one value) := by
  let j₀ := first.asJudgment A
  let j₁ := middle.asJudgment A
  let j₂ := last.asJudgment A
  let σ := one.environment
  let τ := two.environment
  let τ₀ := castEnv (Map.as_substitution A one) τ
  let ρ := fun s v => A.substitution.substitute τ₀ (σ s v)
  have h₁ : substJudgment j₀ σ = j₁ := Map.as_substitution A one
  have h₂ : substJudgment j₁ τ = j₂ := Map.as_substitution A two
  have hSecond : substJudgment (substJudgment j₀ σ) τ₀ = j₂ :=
    (substJudgment_castEnv h₁ τ).trans h₂
  have hDirect : substJudgment j₀ ρ = j₂ :=
    (substJudgment_comp j₀ σ τ₀).symm.trans hSecond
  have compEnvEq : ρ = (one ≫ two).environment := by
    funext s v
    exact congrArg (fun env => A.substitution.substitute env (σ s v))
      (eq_of_heq (castEnv_heq h₁ τ))
  have directToComposite : HEq
      (action.act j₀ value ρ j₂ hDirect)
      (action.actArrow (one ≫ two) value) :=
    action.act_heq rfl HEq.rfl (heq_of_eq compEnvEq) rfl hDirect
      (Map.as_substitution A (one ≫ two))
  have twiceToArrows : HEq
      (action.act (substJudgment j₀ σ)
        (action.act j₀ value σ (substJudgment j₀ σ) rfl) τ₀ j₂ hSecond)
      (action.actArrow two (action.actArrow one value)) :=
    action.act_heq h₁
      (action.act_heq rfl HEq.rfl HEq.rfl h₁ rfl h₁)
      (castEnv_heq h₁ τ) rfl hSecond h₂
  exact eq_of_heq (directToComposite.symm.trans
    ((heq_of_eq (action.act_comp j₀ value σ τ₀ j₂ hSecond hDirect).symm).trans
      twiceToArrows))

/-- On each sort the action is a functor on the judgment category. -/
def functor (action : JudgmentAction.{0, 0} A) (sort : S.Srt) :
    State A sort ⥤ Type where
  obj state := action.carrier (state.asJudgment A)
  map f := TypeCat.ofHom (action.actArrow f)
  map_id state := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    exact action.actArrow_id state value
  map_comp one two := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    exact action.actArrow_comp one two value

end Arrows

section Pullback

universe uSource uTarget w

open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (mapJudgment)

variable {A : BindingCloneAlgebra.Algebra.{uSource} S}
variable {B : BindingCloneAlgebra.Algebra.{uTarget} S}

/-- Read an action along a binding-clone map: evidence at a judgment is
evidence at its image, and an environment acts through its image. -/
def pullback (h : FreeBindingClone.Hom A B) (action : JudgmentAction.{uTarget, w} B) :
    JudgmentAction.{uSource, w} A where
  carrier j := action.carrier (mapJudgment h j)
  act j value _ σ target same :=
    action.act (mapJudgment h j) value (fun t v => h.raw.map (σ t v)) (mapJudgment h target)
      ((mapJudgment_substJudgment h j σ).symm.trans (congrArg (mapJudgment h) same))
  act_identity j value _ := by
    have environment : (fun _ v => h.raw.map (A.substitution.injectVar v) :
        Environment S B.substitution.Carrier (mapJudgment h j).1 (mapJudgment h j).1) =
        fun _ v => B.substitution.injectVar v :=
      funext fun _ => funext fun v => h.raw.map_variable v
    exact eq_of_heq ((action.act_heq rfl HEq.rfl (heq_of_eq environment) rfl _
      (substJudgment_identity _)).trans
      (heq_of_eq (action.act_identity _ value (substJudgment_identity _))))
  act_comp j value _ _ σ τ target second direct := by
    have middle : mapJudgment h (substJudgment j σ) =
        substJudgment (mapJudgment h j) (fun t v => h.raw.map (σ t v)) :=
      mapJudgment_substJudgment h j σ
    have environment : (fun t v => h.raw.map (A.substitution.substitute τ (σ t v)) :
        Environment S B.substitution.Carrier (mapJudgment h j).1 _) =
        fun t v => B.substitution.substitute (fun r w => h.raw.map (τ r w))
          (h.raw.map (σ t v)) :=
      funext fun t => funext fun v => h.map_substitute τ (σ t v)
    have second' : substJudgment
        (substJudgment (mapJudgment h j) (fun t v => h.raw.map (σ t v)))
        (fun t v => h.raw.map (τ t v)) = mapJudgment h target := by
      refine (substJudgment_castEnv middle _).symm.trans ?_
      refine Eq.trans ?_ ((mapJudgment_substJudgment h (substJudgment j σ) τ).symm.trans
        (congrArg (mapJudgment h) second))
      exact congrArg (substJudgment (mapJudgment h (substJudgment j σ)))
        (eq_of_heq (castEnv_heq middle _))
    have direct' : substJudgment (mapJudgment h j)
        (fun t v => B.substitution.substitute (fun r w => h.raw.map (τ r w))
          (h.raw.map (σ t v))) = mapJudgment h target :=
      (congrArg (substJudgment (mapJudgment h j)) environment).symm.trans
        ((mapJudgment_substJudgment h j _).symm.trans (congrArg (mapJudgment h) direct))
    have inner := action.act_heq (value₁ := value) (value₂ := value) rfl HEq.rfl
      (σ₁ := fun t v => h.raw.map (σ t v)) (σ₂ := fun t v => h.raw.map (σ t v)) HEq.rfl
      middle middle.symm rfl
    refine eq_of_heq ((action.act_heq middle inner HEq.rfl rfl _ second').trans
      ((heq_of_eq (action.act_comp (mapJudgment h j) value _ _ _ second' direct')).trans ?_))
    exact action.act_heq rfl HEq.rfl (heq_of_eq environment).symm rfl direct' _

end Pullback

end JudgmentAction

end Mettapedia.OSLF.Binding.IntrinsicScopedJudgmentAction
