import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalCarrierTransport

/-!
# Typed projections of transported operational evidence

These projections keep the replacement carrier explicit when using a
transported stage model in a categorical realization.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedJudgmentAction (ActionOn)

universe u w w'
variable {S : Signature} {R : List (LocalRule S)}
variable {A : BindingCloneAlgebra.Algebra.{u} S}
variable (X : SubstitutionModel.{u, w} R A)
variable {carrier : Judgment A → Type w'} (e : ∀ j, X.carrier j ≃ carrier j)

/-- The transported action, with its replacement carrier explicit. -/
def SubstitutionModel.carrierAct : ActionOn A carrier := (X.transportCarrier e).act

/-- The transported rule algebra, with its replacement carrier explicit. -/
def SubstitutionModel.carrierRules : (IntrinsicScopedLocalPolynomial.rules R A).Algebra (fun _ j => carrier j) :=
  (X.transportCarrier e).rules

/-- Contextual substitution passes under the transported rule actions. -/
theorem SubstitutionModel.carrierRulesLaw : RulesLaw R A (X.carrierAct e) (X.carrierRules e) :=
  (X.transportCarrier e).act_rules

/-- A map into a pulled-back operational model acts on every rule at its image occurrence. -/
theorem rulesAlong_of_isHom {B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B) (Y : SubstitutionModel.{u, w'} R B)
    (image : ∀ j, X.carrier j → Y.carrier (AuthoredPositionedRulePolynomial.mapJudgment h j))
    (law : SubstitutionModel.IsHom R A X (Y.pullback h) image) :
    RulesAlong h X Y.rules image := by
  intro j shape children
  exact (law.rules j ⟨shape, children⟩).trans
    (pullback_rulesMap_act_map h Y.rules image shape children)

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel
