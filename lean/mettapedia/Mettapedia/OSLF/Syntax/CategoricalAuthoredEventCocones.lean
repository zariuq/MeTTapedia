import Mettapedia.OSLF.Syntax.CategoricalAuthoredProgramRestriction
import Mettapedia.OSLF.Syntax.CartesianModelLexEventInterpretations

/-!
# Event objects over classified program carriers

The common program object is a cocone over authored sorts. Adding an event
object with source and target maps is a second comma construction over its
pair object. Existing binding-equation equivalences transport this actual
event arrow and all its maps. Rule actions remain independent structure.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalAuthoredEventCocones

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open Mettapedia.OSLF.Binding.CategoricalAuthoredProgramCocones
open Mettapedia.OSLF.Binding.CategoricalEquationProgramCocones
open Mettapedia.OSLF.Binding.CategoricalAuthoredOperationalModels
open Mettapedia.OSLF.Binding.CategoricalBindingQuotientEquivalence
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u v
variable {S : Signature} {schema : List (MetaArity S)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable (equations : EquationPresentation S schema)

/-- Pair the common program object of a direct authored model. -/
noncomputable def directPairs :
    SatisfyingProgramModel (D := D) equations ⥤ D where
  obj X := X.base.carrier.program ⊗ X.base.carrier.program
  map f := f.program ⊗ₘ f.program
  map_id X := by
    change (𝟙 X.base.carrier.program) ⊗ₘ (𝟙 X.base.carrier.program) = 𝟙 _
    simp
  map_comp f g := by
    change (f.program ≫ g.program) ⊗ₘ (f.program ≫ g.program) =
      (f.program ⊗ₘ f.program) ≫ (g.program ⊗ₘ g.program)
    exact (tensorHom_comp_tensorHom _ _ _ _).symm

/-- Pair the program object of a structured equation interpretation. -/
noncomputable def respectingPairs :
    RespectingProgramCocones (D := D) equations ⥤ D where
  obj X := X.right ⊗ X.right
  map f := f.right ⊗ₘ f.right
  map_id X := by simp
  map_comp f g := by simp [tensorHom_comp_tensorHom]

/-- Pair the program object over equation-class contexts. -/
noncomputable def quotientPairs :
    QuotientProgramCocones (D := D) equations ⥤ D where
  obj X := X.right ⊗ X.right
  map f := f.right ⊗ₘ f.right
  map_id X := by simp
  map_comp f g := by simp [tensorHom_comp_tensorHom]

/-- The base classifier transports the actual program-pair object, not
merely a proposition saying that an endpoint pair exists. -/
theorem directPairs_classified :
    (satisfyingProgramEquivalence (D := D) equations).functor ⋙
      respectingPairs (D := D) equations =
    directPairs (D := D) equations :=
  rfl

theorem quotientPairs_restricted :
    (quotientProgramCoconeEquivalence (D := D) equations).functor ⋙
      respectingPairs (D := D) equations =
    quotientPairs (D := D) equations :=
  rfl

/-- Direct authored equation models with a retained individual event
object and an arrow to pairs of program states. -/
abbrev DirectEventCocones :=
  Comma (𝟭 D) (directPairs (D := D) equations)

abbrev RespectingEventCocones :=
  Comma (𝟭 D) (respectingPairs (D := D) equations)

abbrev QuotientEventCocones :=
  Comma (𝟭 D) (quotientPairs (D := D) equations)

/-- The classifier extends to the individual event object and endpoint
arrow. Ordinary maps preserve events forward and need not cover target
firings. -/
noncomputable def satisfyingEventCoconeEquivalence :
    DirectEventCocones (D := D) equations ≌
      RespectingEventCocones (D := D) equations :=
  Mettapedia.OSLF.CartesianContextModels.liftEventInterpretationEquivalence
    (satisfyingProgramEquivalence (D := D) equations)
    (respectingPairs (D := D) equations)

noncomputable def quotientEventCoconeEquivalence :
    QuotientEventCocones (D := D) equations ≌
      RespectingEventCocones (D := D) equations :=
  Mettapedia.OSLF.CartesianContextModels.liftEventInterpretationEquivalence
    (quotientProgramCoconeEquivalence (D := D) equations)
    (respectingPairs (D := D) equations)

/-- Relative classification of authored equations, the program carrier,
and a proof-relevant event graph through the actual quotient context
category. It does not yet classify the authored conditional-rule actions. -/
noncomputable def satisfyingQuotientEventEquivalence :
    DirectEventCocones (D := D) equations ≌
      QuotientEventCocones (D := D) equations :=
  (satisfyingEventCoconeEquivalence (D := D) equations).trans
    (quotientEventCoconeEquivalence (D := D) equations).symm

/-- Every authored operational interpretation restricts to the event
equipped model just classified, using its actual global endpoint map. -/
def forgetRuleActions
    [MonoidalClosed D] [HasPullbacks D]
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S schema)) :
    PresentedModel (D := D) equations rules ⥤
      DirectEventCocones (D := D) equations where
  obj X := {
    left := X.event
    right := ⟨X.base, X.satisfies⟩
    hom := X.endpoints }
  map f := {
    left := f.event
    right := f.base
    w := f.endpoints_comm }
  map_id := by
    intro X
    apply CommaMorphism.ext <;> rfl
  map_comp := by
    intro X Y Z f g
    apply CommaMorphism.ext <;> rfl

/-- The classified event graph of an actual authored conditional-rule model.
The remaining classifying obligation is to extend and uniquely interpret its
scoped firing actions over this event-equipped quotient base. -/
noncomputable def classifiedEventRestriction
    [MonoidalClosed D] [HasPullbacks D]
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S schema)) :
    PresentedModel (D := D) equations rules ⥤
      QuotientEventCocones (D := D) equations :=
  forgetRuleActions (D := D) equations rules ⋙
    (satisfyingQuotientEventEquivalence (D := D) equations).functor

/-- With no authored operational rules, there is no additional action or
premise transport: the event-equipped model itself is the whole model. -/
def noRuleModelOfEvent
    [MonoidalClosed D] [HasPullbacks D] :
    DirectEventCocones (D := D) equations ⥤
      PresentedModel (D := D) equations [] where
  obj X := {
    base := X.right.base
    satisfies := X.right.satisfies
    event := X.left
    endpoints := X.hom
    action index := Fin.elim0 index }
  map f := {
    base := f.right
    event := f.left
    endpoints_comm := f.w
    premiseMap index := Fin.elim0 index
    conclusion_comm index := Fin.elim0 index
    action_comm index := Fin.elim0 index }
  map_id := by
    intro X
    apply PresentedModel.Hom.ext_of_pointwise
    · rfl
    · rfl
    · intro index
      exact Fin.elim0 index
  map_comp := by
    intro X Y Z f g
    apply PresentedModel.Hom.ext_of_pointwise
    · rfl
    · rfl
    · intro index
      exact Fin.elim0 index

instance forgetRuleActions_noRules_faithful
    [MonoidalClosed D] [HasPullbacks D] :
    (forgetRuleActions (D := D) equations []).Faithful where
  map_injective := by
    intro X Y f g same
    apply PresentedModel.Hom.ext_of_pointwise
    · exact congrArg CommaMorphism.right same
    · exact congrArg CommaMorphism.left same
    · intro index
      exact Fin.elim0 index

instance forgetRuleActions_noRules_full
    [MonoidalClosed D] [HasPullbacks D] :
    (forgetRuleActions (D := D) equations []).Full where
  map_surjective := by
    intro X Y f
    let lifted : PresentedModel.Hom X Y := {
      base := f.right
      event := f.left
      endpoints_comm := f.w
      premiseMap index := Fin.elim0 index
      conclusion_comm index := Fin.elim0 index
      action_comm index := Fin.elim0 index }
    refine ⟨lifted, ?_⟩
    apply CommaMorphism.ext <;> rfl

instance forgetRuleActions_noRules_essSurj
    [MonoidalClosed D] [HasPullbacks D] :
    (forgetRuleActions (D := D) equations []).EssSurj where
  mem_essImage X := by
    let source := (noRuleModelOfEvent (D := D) equations).obj X
    have same : (forgetRuleActions (D := D) equations []).obj source = X := by
      cases X
      rfl
    exact ⟨source, ⟨eqToIso same⟩⟩

noncomputable instance forgetRuleActions_noRules_isEquivalence
    [MonoidalClosed D] [HasPullbacks D] :
    (forgetRuleActions (D := D) equations []).IsEquivalence where

/-- The zero-rule presentation is already classified by the event cocone.
This boundary isolates the remaining conditional-rule-algebra theorem. -/
noncomputable def noRuleEventEquivalence
    [MonoidalClosed D] [HasPullbacks D] :
    PresentedModel (D := D) equations [] ≌
      QuotientEventCocones (D := D) equations :=
  (forgetRuleActions (D := D) equations []).asEquivalence |>.trans
    (satisfyingQuotientEventEquivalence (D := D) equations)

end Mettapedia.OSLF.Binding.CategoricalAuthoredEventCocones
