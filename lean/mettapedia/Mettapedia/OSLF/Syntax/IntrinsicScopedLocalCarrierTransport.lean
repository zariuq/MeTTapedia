import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalLawTransfer

/-!
# Transport of operational evidence through fiber equivalences

An equivalence of evidence carriers transports substitution and authored rule
actions together. The rule occurrence, binder-local judgments and ordered
premise positions are unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedJudgmentAction (ActionOn)

universe u w w'

variable {S : Signature} {R : List (LocalRule S)}
variable {A : BindingCloneAlgebra.Algebra.{u} S}
variable (X : SubstitutionModel.{u, w} R A)
variable {carrier : Judgment A → Type w'} (e : ∀ j, X.carrier j ≃ carrier j)

set_option backward.isDefEq.respectTransparency false in
/-- A change of evidence representation preserves the operational laws. -/
def SubstitutionModel.transportCarrier : SubstitutionModel.{u, w'} R A where
  carrier := carrier
  act j value _ σ target same := e target (X.act j ((e j).symm value) σ target same)
  act_identity j value same := by
    exact (congrArg (e j) (X.act_identity j ((e j).symm value) same)).trans
      ((e j).apply_symm_apply value)
  act_comp j value _ _ σ τ target second direct := by
    simp only [Equiv.symm_apply_apply]
    exact congrArg (e target) (X.act_comp j ((e j).symm value) σ τ target second direct)
  rules :=
    { act := fun _ j layer => e j (X.rules.act () j
        ⟨layer.1, fun position => (e _).symm (layer.2 position)⟩) }
  act_rules := by
    intro j shape children Δ σ target same
    dsimp only [IntrinsicScopedLocalPolynomial.rules]
    simp only [Equiv.symm_apply_apply]
    have law := congrArg (e target)
      (X.act_rules shape (fun position => (e _).symm (children position)) σ target same)
    refine law.trans (congrArg (e target) (congrArg (X.rules.act () target) ?_))
    refine congrArg (Sigma.mk _) ?_
    funext position
    rfl

/-- The forward evidence equivalence preserves both operational actions. -/
def SubstitutionModel.transportCarrierHom :
    SubstitutionModel.Hom R A X (X.transportCarrier e) where
  evidence :=
    { toFun := fun _ j => e j
      commutes := by
        intro base j layer
        cases base
        obtain ⟨shape, children⟩ := layer
        simp only [IndexedPolynomial.Extension.map, SubstitutionModel.transportCarrier,
          Equiv.symm_apply_apply] }
  preserves := by
    intro j value Δ σ target same
    simp only [SubstitutionModel.transportCarrier, Equiv.symm_apply_apply]

/-- The inverse evidence equivalence also preserves both actions. -/
def SubstitutionModel.transportCarrierInvHom :
    SubstitutionModel.Hom R A (X.transportCarrier e) X where
  evidence :=
    { toFun := fun _ j => (e j).symm
      commutes := by
        intro base j layer
        cases base
        obtain ⟨shape, children⟩ := layer
        simp only [IndexedPolynomial.Extension.map, SubstitutionModel.transportCarrier,
          Equiv.symm_apply_apply] }
  preserves := by
    intro j value Δ σ target same
    simp only [SubstitutionModel.transportCarrier, Equiv.symm_apply_apply]

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel
