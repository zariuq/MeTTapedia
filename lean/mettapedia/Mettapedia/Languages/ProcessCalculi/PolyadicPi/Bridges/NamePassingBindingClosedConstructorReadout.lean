import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedConstructorExpressions
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingPrimitiveOperations

/-!
# Whole source-constructor readings through the generated interpreter

Each independent constructor expression has a complete native reading for
arbitrary source binding-operation data. The one-name comparison uses the
actual right unitor and complete function evaluation. Supplying continuation
operations afterwards therefore earns all five CPS constructor comparisons;
the function domains are not reduced to selected syntactic bodies.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedConstructorReadout

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax GeneratedCategory Interpretation
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus


universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable [MonoidalClosed C] [HasFiniteLimits C]
variable (primitives : ClosedPresentation.Operations NamePassingBindingClosedConstructorExpressions.binding C)

theorem bodies_read : primitives.assignment.evaluateObject NamePassingBindingClosedConstructorExpressions.bodies.{v}.code =
    some (NamePassingBindingPrimitiveOperations.bodies primitives) :=
  primitives.assignment.evaluate_exponential (primitives.sort_read .nm) (primitives.sort_read .tm)

theorem plain_read (sort : NamePassing.Presentation.Srt) :
    primitives.assignment.evaluateArrow (NamePassingBindingClosedConstructorExpressions.plain.{v} sort).code =
      some ⟨primitives.sort sort, (𝟙_ C ⟶[C] primitives.sort sort), NamePassingBindingPrimitiveOperations.plain primitives sort⟩ :=
  raw_curry_read primitives.assignment _ _ primitives.assignment.evaluate_terminal_object
    (primitives.sort_read sort) (primitives.sort_read sort)
    (primitives.assignment.evaluate_second primitives.assignment.evaluate_terminal_object
      (primitives.sort_read sort))

omit [HasFiniteLimits C] in
private theorem full_bound_arrow (A X : C) :
    MonoidalClosed.curry
      (lift (fst (A ⊗ 𝟙_ C) (A ⟶[C] X) ≫ fst A (𝟙_ C))
        (snd (A ⊗ 𝟙_ C) (A ⟶[C] X)) ≫ (ihom.ev A).app X) =
      (MonoidalClosed.pre (ρ_ A).hom).app X := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_curry]
  calc
    _ = (ρ_ A).hom ▷ (A ⟶[C] X) ≫ (ihom.ev A).app X := by
      congr 1
      apply hom_ext <;> simp only [lift_fst, lift_snd, whiskerRight_fst,
        whiskerRight_snd, rightUnitor_hom]
    _ = _ := (MonoidalClosed.uncurry_pre (ρ_ A).hom X).symm

theorem bound_read : primitives.assignment.evaluateArrow NamePassingBindingClosedConstructorExpressions.bound.{v}.code =
    some ⟨NamePassingBindingPrimitiveOperations.bodies primitives, primitives.power [.nm] .tm, NamePassingBindingPrimitiveOperations.bound primitives⟩ := by
  have padded := primitives.assignment.evaluate_product (primitives.sort_read .nm)
    primitives.assignment.evaluate_terminal_object
  have first := primitives.assignment.evaluate_compose _ _
    (primitives.assignment.evaluate_first padded (bodies_read primitives))
    (primitives.assignment.evaluate_first (primitives.sort_read .nm)
      primitives.assignment.evaluate_terminal_object)
  have body := raw_apply_read primitives.assignment
    (RawHom.second (product NamePassingBindingClosedConstructorExpressions.names
      (terminal NamePassingBindingClosedConstructorExpressions.signature))
      NamePassingBindingClosedConstructorExpressions.bodies)
    (RawHom.compose (RawHom.first (product NamePassingBindingClosedConstructorExpressions.names
      (terminal NamePassingBindingClosedConstructorExpressions.signature))
      NamePassingBindingClosedConstructorExpressions.bodies)
      (RawHom.first NamePassingBindingClosedConstructorExpressions.names
        (terminal NamePassingBindingClosedConstructorExpressions.signature))) _ _
    (primitives.sort_read .nm) (primitives.sort_read .tm)
    (primitives.assignment.evaluate_second padded (bodies_read primitives)) first
  have complete := raw_curry_read primitives.assignment _ _ padded
    (bodies_read primitives) (primitives.sort_read .tm) body
  exact complete.trans (congrArg (fun arrow => some
    (⟨NamePassingBindingPrimitiveOperations.bodies primitives, primitives.power [.nm] .tm, arrow⟩ : ArrowValue C))
      (full_bound_arrow (primitives.sort .nm) (primitives.sort .tm)))

theorem reference_read : primitives.assignment.evaluateArrow NamePassingBindingClosedConstructorExpressions.reference.{v}.code =
    some ⟨NamePassingBindingPrimitiveOperations.names primitives, NamePassingBindingPrimitiveOperations.terms primitives, NamePassingBindingPrimitiveOperations.reference primitives⟩ :=
  primitives.assignment.evaluate_compose _ _
    (primitives.assignment.evaluate_pair _ _ (plain_read primitives .nm)
      (primitives.assignment.evaluate_terminal_arrow (primitives.sort_read .nm))) rfl

theorem abstraction_read : primitives.assignment.evaluateArrow NamePassingBindingClosedConstructorExpressions.abstraction.{v}.code =
    some ⟨NamePassingBindingPrimitiveOperations.bodies primitives, NamePassingBindingPrimitiveOperations.terms primitives, NamePassingBindingPrimitiveOperations.abstraction primitives⟩ :=
  primitives.assignment.evaluate_compose _ _
    (primitives.assignment.evaluate_pair _ _ (bound_read primitives)
      (primitives.assignment.evaluate_terminal_arrow (bodies_read primitives))) rfl

theorem application_read : primitives.assignment.evaluateArrow NamePassingBindingClosedConstructorExpressions.application.{v}.code =
    some ⟨NamePassingBindingPrimitiveOperations.terms primitives ⊗ NamePassingBindingPrimitiveOperations.names primitives,
      NamePassingBindingPrimitiveOperations.terms primitives, NamePassingBindingPrimitiveOperations.application primitives⟩ := by
  have domain := primitives.assignment.evaluate_product (primitives.sort_read .tm) (primitives.sort_read .nm)
  exact primitives.assignment.evaluate_compose _ _
    (primitives.assignment.evaluate_pair _ _
      (primitives.assignment.evaluate_compose _ _
        (primitives.assignment.evaluate_first (primitives.sort_read .tm) (primitives.sort_read .nm))
        (plain_read primitives .tm))
      (primitives.assignment.evaluate_pair _ _
        (primitives.assignment.evaluate_compose _ _
          (primitives.assignment.evaluate_second (primitives.sort_read .tm) (primitives.sort_read .nm))
          (plain_read primitives .nm))
        (primitives.assignment.evaluate_terminal_arrow domain))) rfl

theorem definition_read : primitives.assignment.evaluateArrow NamePassingBindingClosedConstructorExpressions.definition.{v}.code =
    some ⟨NamePassingBindingPrimitiveOperations.terms primitives ⊗ NamePassingBindingPrimitiveOperations.bodies primitives,
      NamePassingBindingPrimitiveOperations.terms primitives, NamePassingBindingPrimitiveOperations.definition primitives⟩ := by
  have domain := primitives.assignment.evaluate_product (primitives.sort_read .tm) (bodies_read primitives)
  exact primitives.assignment.evaluate_compose _ _
    (primitives.assignment.evaluate_pair _ _
      (primitives.assignment.evaluate_compose _ _
        (primitives.assignment.evaluate_first (primitives.sort_read .tm) (bodies_read primitives))
        (plain_read primitives .tm))
      (primitives.assignment.evaluate_pair _ _
        (primitives.assignment.evaluate_compose _ _
          (primitives.assignment.evaluate_second (primitives.sort_read .tm) (bodies_read primitives))
          (bound_read primitives))
        (primitives.assignment.evaluate_terminal_arrow domain))) rfl

theorem carrier_read : primitives.assignment.evaluateArrow NamePassingBindingClosedConstructorExpressions.carrier.{v}.code =
    some ⟨NamePassingBindingPrimitiveOperations.names primitives ⊗
      (NamePassingBindingPrimitiveOperations.terms primitives ⊗ NamePassingBindingPrimitiveOperations.terms primitives),
      NamePassingBindingPrimitiveOperations.terms primitives, NamePassingBindingPrimitiveOperations.carrier primitives⟩ := by
  have pair := primitives.assignment.evaluate_product (primitives.sort_read .tm) (primitives.sort_read .tm)
  have domain := primitives.assignment.evaluate_product (primitives.sort_read .nm) pair
  have second := primitives.assignment.evaluate_second (primitives.sort_read .nm) pair
  have operatorRead : primitives.assignment.evaluateArrow
      (ClosedPresentation.operator.{v} NamePassing.Presentation.signature .carrier).code =
        some (primitives.primitiveValue ⟨.tm, .carrier⟩) := rfl
  have complete := primitives.assignment.evaluate_compose _ _
    (primitives.assignment.evaluate_pair _ _
      (primitives.assignment.evaluate_compose _ _
        (primitives.assignment.evaluate_first (primitives.sort_read .nm) pair)
        (plain_read primitives .nm))
      (primitives.assignment.evaluate_pair _ _
        (primitives.assignment.evaluate_compose _ _
          (primitives.assignment.evaluate_compose _ _ second
            (primitives.assignment.evaluate_first (primitives.sort_read .tm) (primitives.sort_read .tm)))
          (plain_read primitives .tm))
        (primitives.assignment.evaluate_pair _ _
          (primitives.assignment.evaluate_compose _ _
            (primitives.assignment.evaluate_compose _ _ second
              (primitives.assignment.evaluate_second (primitives.sort_read .tm) (primitives.sort_read .tm)))
            (plain_read primitives .tm))
          (primitives.assignment.evaluate_terminal_arrow domain)))) operatorRead
  dsimp only [NamePassingBindingClosedConstructorExpressions.carrier,
    NamePassingBindingClosedConstructorExpressions.names, NamePassingBindingClosedConstructorExpressions.terms,
    RawHom.compose, RawHom.pair, RawHom.first, RawHom.second, RawHom.toTerminal,
    product, ClosedPresentation.sortObject]
  simpa only [NamePassingBindingPrimitiveOperations.carrier, NamePassingBindingPrimitiveOperations.names,
    NamePassingBindingPrimitiveOperations.terms, ClosedPresentation.Operations.primitiveValue,
    Category.assoc] using complete

def domain : NamePassing.Presentation.Operator .tm → C
  | .reference => NamePassingBindingPrimitiveOperations.names primitives
  | .abstraction => NamePassingBindingPrimitiveOperations.bodies primitives
  | .application => NamePassingBindingPrimitiveOperations.terms primitives ⊗ NamePassingBindingPrimitiveOperations.names primitives
  | .definition => NamePassingBindingPrimitiveOperations.terms primitives ⊗ NamePassingBindingPrimitiveOperations.bodies primitives
  | .carrier => NamePassingBindingPrimitiveOperations.names primitives ⊗ (NamePassingBindingPrimitiveOperations.terms primitives ⊗ NamePassingBindingPrimitiveOperations.terms primitives)

def arrow : (operator : NamePassing.Presentation.Operator .tm) →
    domain primitives operator ⟶ NamePassingBindingPrimitiveOperations.terms primitives
  | .reference => NamePassingBindingPrimitiveOperations.reference primitives
  | .abstraction => NamePassingBindingPrimitiveOperations.abstraction primitives
  | .application => NamePassingBindingPrimitiveOperations.application primitives
  | .definition => NamePassingBindingPrimitiveOperations.definition primitives
  | .carrier => NamePassingBindingPrimitiveOperations.carrier primitives

theorem expression_read (operator : NamePassing.Presentation.Operator .tm) :
    primitives.assignment.evaluateArrow (NamePassingBindingClosedConstructorExpressions.expression.{v} operator).code =
      some ⟨domain primitives operator, NamePassingBindingPrimitiveOperations.terms primitives, arrow primitives operator⟩ := by
  cases operator with
  | reference => exact reference_read primitives
  | abstraction => exact abstraction_read primitives
  | application => exact application_read primitives
  | definition => exact definition_read primitives
  | carrier => exact carrier_read primitives

theorem complete_readout (operator : NamePassing.Presentation.Operator .tm) :
    (⟨primitives.interpretation.functor.obj (NamePassingBindingClosedConstructorExpressions.domain.{v} operator),
      primitives.interpretation.functor.obj NamePassingBindingClosedConstructorExpressions.terms,
      primitives.interpretation.functor.map (classOf (NamePassingBindingClosedConstructorExpressions.expression operator))⟩ : ArrowValue C) =
      ⟨domain primitives operator, NamePassingBindingPrimitiveOperations.terms primitives, arrow primitives operator⟩ :=
  Option.some.inj ((functor_complete_readout primitives.assignment primitives.realization
    (NamePassingBindingClosedConstructorExpressions.expression operator)).symm.trans (expression_read primitives operator))

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedConstructorReadout
