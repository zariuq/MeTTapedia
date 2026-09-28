import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalEventOrbit
import Mettapedia.OSLF.Syntax.MonoidEquationRung
import Mettapedia.OSLF.Syntax.IndexedRuleFiniteContextSemantics

/-!
# A rule-algebra map that fails to preserve event substitution

With no authored rules, a pointwise event map can preserve every rule
constructor and still fail to commute with substituting ordinary variables.
This control distinguishes a classifier of rule algebras from a classifier
of substitution-operational models.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitutionGapControl

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.MonoidEquationRung

private abbrev A : BindingCloneAlgebra.Algebra MonoidEquationRung.sig :=
  BindingCloneAlgebra.terms MonoidEquationRung.sig

private abbrev R : List (Rule MonoidEquationRung.sig MonoidEquationRung.metas) := []

/-- Extra Boolean firing witnesses carry the constant substitution action. -/
noncomputable def boolModel : SubstitutionModel R A where
  evidence := {
    carrier := fun _ _ => Bool
    rules := {
      act := by
        intro base judgment layer
        exact Fin.elim0 layer.1.1.index } }
  act := by
    intro judgment value Δ σ target h
    exact value
  act_rules := by
    intro judgment shape children Δ σ target h
    exact Fin.elim0 shape.1.index
  act_identity := by
    intro judgment value h
    rfl
  act_comp := by
    intro judgment value Δ Θ σ τ target second direct
    rfl

/-- Flip evidence only at a closed judgment. With no rule constructors,
this is a valid map of the underlying indexed rule algebra. -/
noncomputable def closeFlip :
    Mettapedia.TypeTheory.IndexedPolynomial.Algebra.Hom
      boolModel.evidence.rules boolModel.evidence.rules where
  toFun := fun _ judgment value =>
    if judgment.1 = [] then !value else value
  commutes := by
    intro base judgment layer
    exact Fin.elim0 layer.1.1.index

/-- The deficient fixed-fiber classifier does regard this map as a natural
transformation, since its arrows inspect only rule trees and exact leaves. -/
noncomputable def closeFlip_fiber_natural :=
  IndexedRuleFiniteContexts.algebraSemanticsHom (rules R A) closeFlip

private def openJudgment : Judgment A :=
  ⟨[Srt.element], Srt.element,
    Term.var (Var.zero : Var [Srt.element] Srt.element),
    Term.var (Var.zero : Var [Srt.element] Srt.element)⟩

private def closedJudgment : Judgment A :=
  ⟨[], Srt.element, unitT, unitT⟩

private def closeEnvironment :
    BindingSubstitutionAlgebra.Environment MonoidEquationRung.sig
      A.substitution.Carrier [Srt.element] []
  | _, .zero => unitT
  | _, .succ old => nomatch old

private theorem closes_judgment :
    substJudgment openJudgment closeEnvironment = closedJudgment := by
  rfl

/-- The underlying rule-algebra map is not a substitution-model map:
closing the open event and flipping it gives a different Boolean witness
from flipping first and then closing it. -/
theorem closeFlip_fails_substitution :
    closeFlip.toFun () closedJudgment
      (boolModel.act openJudgment false closeEnvironment closedJudgment
        closes_judgment) ≠
    boolModel.act openJudgment
      (closeFlip.toFun () openJudgment false)
      closeEnvironment closedJudgment closes_judgment := by
  change true ≠ false
  decide

/-- There is no substitution-operational endomorphism whose evidence
component is this otherwise valid rule-algebra map. -/
theorem closeFlip_not_operational :
    ¬ ∃ h : SubstitutionModel.Hom R boolModel boolModel,
      h.evidence = closeFlip := by
  rintro ⟨h, same⟩
  have preserved := h.preserves openJudgment false closeEnvironment
    closedJudgment closes_judgment
  rw [same] at preserved
  exact closeFlip_fails_substitution preserved

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitutionGapControl
