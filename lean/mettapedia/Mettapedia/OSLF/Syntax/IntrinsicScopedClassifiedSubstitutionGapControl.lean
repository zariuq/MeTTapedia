import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalSubstitutionGapControl
import Mettapedia.OSLF.Syntax.IntrinsicScopedAuthoredClassifiedInstance

/-!
# The substitution-forgetting map remains outside operational classification

The original counterexample's Boolean evidence and original substitution
action give an actual rule-local operational model and its genuine
cocontinuous classification. Its close-only flip is still a valid map of
the underlying rule algebra, but is not an operational model map.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedClassifiedSubstitutionGapControl

open _root_.CategoryTheory
open MonoidEquationRung (sig metas Srt unitT)
open IntrinsicScopedConditionalSubstitutionGapControl (boolModel closeFlip)
open IntrinsicScopedLocalSubstitutionModel (SubstitutionModel)
open AuthoredPositionedRulePolynomial (Judgment)
open IntrinsicScopedConditionalSubstitution (substJudgment)

abbrev algebra := BindingCloneAlgebra.terms sig
abbrev rules : List (IntrinsicScopedLocalPolynomial.LocalRule sig) := []
abbrev equations : List (EqAxiom sig metas) := []

/-- The same original evidence/action, with the actual empty rule-local list. -/
def localModel : SubstitutionModel rules algebra where
  toAction := boolModel.toAction
  rules := { act := fun _ _ layer => Fin.elim0 layer.1.1.index }
  act_rules := by
    intro j shape children Δ σ target h
    exact Fin.elim0 shape.1.index

/-- This control satisfies its actual empty contextual equation presentation. -/
theorem satisfies : BindingEquationInterpretation.Satisfies algebra equations := by
  intro index
  exact Fin.elim0 index

/-- A genuine independently constructed categorical model of the same counterexample. -/
def categoricalModel :=
  IntrinsicScopedOperationalPresheafCategoricalModel.categoricalModel rules localModel equations satisfies

/-- It is an actual object of the common cocontinuous classification. -/
def interpretation :=
  (IntrinsicScopedLocalActedCategoricalModels.CocontinuousInterpretation.classificationEquivalence.{0}
    (R := rules) (equations := equations)
    (D := IntrinsicScopedOperationalPresheafPrograms.target algebra)).functor.obj categoricalModel

/-- The original deficient map really preserves the actual local rule algebra. -/
def localCloseFlip : Mettapedia.TypeTheory.IndexedPolynomial.Algebra.Hom
    localModel.rules localModel.rules where
  toFun := closeFlip.toFun
  commutes := fun _ _ layer => Fin.elim0 layer.1.1.index

/-- Closing the original open variable to the unit exhibits the same failure. -/
theorem flip_fails_substitution :
    localCloseFlip.toFun ()
      (⟨[], Srt.element, unitT, unitT⟩ : Judgment algebra)
      (localModel.act
        ⟨[Srt.element], Srt.element, .var .zero, .var .zero⟩ false
        (fun _ v => match v with
          | .zero => unitT
          | .succ old => nomatch old)
        ⟨[], Srt.element, unitT, unitT⟩ rfl) ≠
    localModel.act
      ⟨[Srt.element], Srt.element, .var .zero, .var .zero⟩
      (localCloseFlip.toFun ()
        ⟨[Srt.element], Srt.element, .var .zero, .var .zero⟩ false)
      (fun _ v => match v with
        | .zero => unitT
        | .succ old => nomatch old)
      ⟨[], Srt.element, unitT, unitT⟩ rfl :=
  IntrinsicScopedConditionalSubstitutionGapControl.closeFlip_fails_substitution

/-- Preserving rule algebra alone does not admit this map into the operational model category. -/
theorem flip_not_operational :
    ¬ ∃ map : SubstitutionModel.Hom rules algebra localModel localModel,
      map.evidence = localCloseFlip := by
  rintro ⟨map, same⟩
  have preserved := map.preserves
    (⟨[Srt.element], Srt.element, .var .zero, .var .zero⟩ : Judgment algebra) false
    (fun _ v => match v with
      | .zero => unitT
      | .succ old => nomatch old)
    (⟨[], Srt.element, unitT, unitT⟩ : Judgment algebra) rfl
  rw [same] at preserved
  exact flip_fails_substitution preserved

/-- The identity is a genuine positive operational map, including substitution. -/
def identityOperational : SubstitutionModel.Hom rules algebra localModel localModel :=
  SubstitutionModel.Hom.id rules algebra localModel

end Mettapedia.OSLF.Binding.IntrinsicScopedClassifiedSubstitutionGapControl
