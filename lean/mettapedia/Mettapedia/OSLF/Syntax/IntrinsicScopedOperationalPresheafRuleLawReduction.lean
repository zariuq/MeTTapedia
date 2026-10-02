import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalLawTransfer

/-!
# Checking the full local rule law on actual occurrences

Judgment and conclusion proof transports do not add a semantic obligation.
The full substitution law follows from firing each actual occurrence and its
substituted occurrence, retaining every authored ordered bound child.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafRuleLawReduction

open BindingSubstitutionAlgebra
open IntrinsicScopedLocalPolynomial
open IntrinsicScopedLocalSubstitutionModel
open IntrinsicScopedJudgmentAction (ActionOn)
open AuthoredPositionedRulePolynomial (Judgment)
open IntrinsicScopedConditionalSubstitution (substJudgment)

universe u w
variable {S : Signature} {A : BindingCloneAlgebra.Algebra.{u} S}
variable (R : List (LocalRule S)) {carrier : Judgment A → Type w}
variable (act : ActionOn A carrier)
variable (algebra : (rules R A).Algebra (fun _ j => carrier j))

/-- Actual occurrence-level substitution laws imply the fully indexed rule law. -/
theorem rulesLaw_of_occurrences
    (law : ∀ (occurrence : Instance R A)
      (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
        carrier (childJudgment R A occurrence position)) {Δ : Ctx S}
      (σ : Environment S A.substitution.Carrier occurrence.ambient Δ),
      HEq (act (conclusionJudgment R A occurrence)
        (algebra.act () _ ⟨⟨occurrence, rfl⟩, children⟩) σ
        (substJudgment (conclusionJudgment R A occurrence) σ) rfl)
        (algebra.act () (conclusionJudgment R A (Instance.subst R occurrence σ))
          ⟨⟨Instance.subst R occurrence σ, rfl⟩,
            fun position => act _ (children position)
              (A.substitution.liftEnvironment σ ((R.get occurrence.index).2.premises.get position).binders)
              (childJudgment R A (Instance.subst R occurrence σ) position)
              (childJudgment_subst R occurrence σ position).symm⟩)) : RulesLaw R A act algebra := by
  intro judgment shape children Δ σ target same
  obtain ⟨occurrence, conclusion⟩ := shape
  subst conclusion
  have movedAct := actionOn_heq act
    (value₁ := algebra.act () _ ⟨⟨occurrence, rfl⟩, children⟩)
    rfl HEq.rfl HEq.rfl same rfl same
  have movedRule := rulesAct_heq R algebra
    ((conclusionJudgment_subst R occurrence σ).trans same) rfl
    rfl ((conclusionJudgment_subst R occurrence σ).trans same)
    (fun position => act _ (children position)
      (A.substitution.liftEnvironment σ ((R.get occurrence.index).2.premises.get position).binders)
      (childJudgment R A (Instance.subst R occurrence σ) position)
      (childJudgment_subst R occurrence σ position).symm)
    (fun position => act _ (children position)
      (A.substitution.liftEnvironment σ ((R.get occurrence.index).2.premises.get position).binders)
      (childJudgment R A (Instance.subst R occurrence σ) position)
      (childJudgment_subst R occurrence σ position).symm)
    (by intro position otherPosition samePosition; cases samePosition; rfl)
  exact eq_of_heq (movedAct.symm.trans ((law occurrence children σ).trans movedRule))

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafRuleLawReduction
