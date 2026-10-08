import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierRealization
import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretationReadout
import Mettapedia.CategoryTheory.HigherOrderInternalPredicateQuantifier

/-!
# Classifier-built meanings for quantifiers on genuinely generated arrows

Each route is interpreted by the independent old evaluator. Its actual
target arrow is then used to quantify the generic classified predicate.
The resulting complete function arrow satisfies the finite diagrams and
therefore realizes the authored extension. Supplied predicate readouts of
the actual generated quotient image retain their entire parameter.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.NativeMeaning

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open RelativeClosedSyntax GeneratedCategory
open HigherOrderInternalPredicateObject

universe k w z p
variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable (original : Signature (C := C) (symbols := symbols))
variable (language : PredicateSyntax original)
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (meanings : RelativeClosedSyntax.Interpretation.Assignment C symbols D)
variable (old : RelativeClosedSyntax.Interpretation.Realization original meanings)
variable (doctrine : PredicateDoctrine.HigherOrder.{w,z,p} D)

def meaning : Interpretation.Meaning original meanings old (operations doctrine) where
  universal route := HigherOrderInternalPredicateQuantifier.forallOperation doctrine
    (Interpretation.routeValue original meanings old route)
  existential route := HigherOrderInternalPredicateQuantifier.existsOperation doctrine
    (Interpretation.routeValue original meanings old route)

theorem admitted : Interpretation.Admission original meanings old (operations doctrine)
    (meaning original meanings old doctrine) where
  universalMonotonicity route := HigherOrderInternalPredicateQuantifier.forall_monotonicity doctrine
    (Interpretation.routeValue original meanings old route)
  universalUnit route := (HigherOrderInternalPredicateQuantifier.forallQualification doctrine
    (Interpretation.routeValue original meanings old route)).unit
  universalCounit route := (HigherOrderInternalPredicateQuantifier.forallQualification doctrine
    (Interpretation.routeValue original meanings old route)).counit
  existentialMonotonicity route := HigherOrderInternalPredicateQuantifier.exists_monotonicity doctrine
    (Interpretation.routeValue original meanings old route)
  existentialUnit route := (HigherOrderInternalPredicateQuantifier.existsQualification doctrine
    (Interpretation.routeValue original meanings old route)).unit
  existentialCounit route := (HigherOrderInternalPredicateQuantifier.existsQualification doctrine
    (Interpretation.routeValue original meanings old route)).counit

variable (propositionRead : RawInterpretation.ObjectReads meanings language.proposition (operations doctrine).proposition)
variable (conjunctionRead : RawInterpretation.Reads meanings language.conjunction (operations doctrine).conjunction)

include propositionRead conjunctionRead

theorem realized : RelativeClosedSyntax.Interpretation.Realization (signature original language)
    (Interpretation.finalAssignment original meanings old (operations doctrine) (meaning original meanings old doctrine)) :=
  Interpretation.realized original language meanings old (operations doctrine) (meaning original meanings old doctrine)
    propositionRead conjunctionRead (admitted original meanings old doctrine)

def diagram : Object (signature original language) ⥤ D :=
  Interpretation.diagram original language meanings old (operations doctrine) (meaning original meanings old doctrine)
    propositionRead conjunctionRead (admitted original meanings old doctrine)

omit propositionRead conjunctionRead in
theorem named_read (kind : Kind) (route : Route original) :
    RawInterpretation.Reads
      (Interpretation.finalAssignment original meanings old (operations doctrine) (meaning original meanings old doctrine))
      (named original language kind route)
      (Interpretation.operator original meanings old (operations doctrine) (meaning original meanings old doctrine) kind route) :=
  (EquationExtension.evaluate_arrow_original (arrowSignature original language) (declaration original language)
    (Interpretation.assignment original meanings old (operations doctrine) (meaning original meanings old doctrine))
    (quantifier original language kind route).code).trans
      (Interpretation.operator_read original language meanings old (operations doctrine) (meaning original meanings old doctrine) kind route)

theorem quotient_image (kind : Kind) (route : Route original) :
    (⟨(diagram original language meanings old doctrine propositionRead conjunctionRead).obj
        ((equationInclusion original language).object
          ((argumentSyntax original language).power (mappedRoute original language route).source)),
      (diagram original language meanings old doctrine propositionRead conjunctionRead).obj
        ((equationInclusion original language).object
          ((argumentSyntax original language).power (mappedRoute original language route).target)),
      (diagram original language meanings old doctrine propositionRead conjunctionRead).map
        (classOf (named original language kind route))⟩ : RelativeClosedSyntax.Interpretation.ArrowValue D) =
      Interpretation.added original meanings old (operations doctrine) (meaning original meanings old doctrine) ⟨kind, route⟩ := by
  have complete := RelativeClosedSyntax.Interpretation.functor_complete_readout
    (Interpretation.finalAssignment original meanings old (operations doctrine) (meaning original meanings old doctrine))
    (realized original language meanings old doctrine propositionRead conjunctionRead)
    (named original language kind route)
  exact Option.some.inj (complete.symm.trans (named_read original language meanings old doctrine kind route))

omit propositionRead conjunctionRead in
def operationValue (kind : Kind) (supplied : RelativeClosedSyntax.Interpretation.ArrowValue D) :
    RelativeClosedSyntax.Interpretation.ArrowValue D :=
  ⟨InternalPredicateFunctionObject.power (operations doctrine) supplied.source,
    InternalPredicateFunctionObject.power (operations doctrine) supplied.target,
    match kind with
    | .universal => HigherOrderInternalPredicateQuantifier.forallOperation doctrine supplied.arrow
    | .existential => HigherOrderInternalPredicateQuantifier.existsOperation doctrine supplied.arrow⟩

/-- A successful independently supplied old route reading determines the full
generated quantifier image, including both endpoint objects. -/
theorem quotient_image_at (kind : Kind) (route : Route original) {source target : D}
    (arrow : source ⟶ target) (reading : RawInterpretation.Reads meanings route.arrow arrow) :
    (⟨(diagram original language meanings old doctrine propositionRead conjunctionRead).obj
        ((equationInclusion original language).object
          ((argumentSyntax original language).power (mappedRoute original language route).source)),
      (diagram original language meanings old doctrine propositionRead conjunctionRead).obj
        ((equationInclusion original language).object
          ((argumentSyntax original language).power (mappedRoute original language route).target)),
      (diagram original language meanings old doctrine propositionRead conjunctionRead).map
        (classOf (named original language kind route))⟩ : RelativeClosedSyntax.Interpretation.ArrowValue D) =
      operationValue doctrine kind ⟨source, target, arrow⟩ := by
  have originalImage := Option.some.inj
    ((RelativeClosedSyntax.Interpretation.rawArrowValue_readout meanings old route.arrow).symm.trans reading)
  have complete := congrArg (operationValue doctrine kind) originalImage
  exact (quotient_image original language meanings old doctrine propositionRead conjunctionRead kind route).trans complete

def imageForRead (kind : Kind) (route : Route original) {source target : D}
    (arrow : source ⟶ target) (reading : RawInterpretation.Reads meanings route.arrow arrow) :
    InternalPredicateFunctionObject.power (operations doctrine) source ⟶
      InternalPredicateFunctionObject.power (operations doctrine) target :=
  eqToHom (congrArg RelativeClosedSyntax.Interpretation.ArrowValue.source
    (quotient_image_at original language meanings old doctrine propositionRead conjunctionRead kind route arrow reading)).symm ≫
      (diagram original language meanings old doctrine propositionRead conjunctionRead).map
        (classOf (named original language kind route)) ≫
      eqToHom (congrArg RelativeClosedSyntax.Interpretation.ArrowValue.target
        (quotient_image_at original language meanings old doctrine propositionRead conjunctionRead kind route arrow reading))

omit [Category C] [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
  propositionRead conjunctionRead in
private theorem retype_complete {X Y X' Y' : D}
    (source : X = X') (target : Y = Y') (first : X ⟶ Y) (second : X' ⟶ Y')
    (same : HEq first second) : eqToHom source.symm ≫ first ≫ eqToHom target = second := by
  cases source
  cases target
  cases same
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem imageForRead_complete (kind : Kind) (route : Route original) {source target : D}
    (arrow : source ⟶ target) (reading : RawInterpretation.Reads meanings route.arrow arrow) :
    imageForRead original language meanings old doctrine propositionRead conjunctionRead kind route arrow reading =
      (operationValue doctrine kind ⟨source, target, arrow⟩).arrow :=
  retype_complete
    (congrArg RelativeClosedSyntax.Interpretation.ArrowValue.source
      (quotient_image_at original language meanings old doctrine propositionRead conjunctionRead kind route arrow reading))
    (congrArg RelativeClosedSyntax.Interpretation.ArrowValue.target
      (quotient_image_at original language meanings old doctrine propositionRead conjunctionRead kind route arrow reading))
    ((diagram original language meanings old doctrine propositionRead conjunctionRead).map
      (classOf (named original language kind route)))
    (operationValue doctrine kind ⟨source, target, arrow⟩).arrow
    (RelativeClosedSyntax.Interpretation.ArrowValue.arrows_heq
      (quotient_image_at original language meanings old doctrine propositionRead conjunctionRead kind route arrow reading))

omit propositionRead conjunctionRead in
theorem universal_supplied (route : Route original) {parameter : D}
    (predicate : parameter ⟶ Interpretation.power original meanings old (operations doctrine) route.source) :
    family doctrine (predicate ≫ (meaning original meanings old doctrine).universal route) =
      doctrine.forallAlong (Interpretation.routeValue original meanings old route ▷ parameter) (family doctrine predicate) :=
  HigherOrderInternalPredicateQuantifier.forall_supplied doctrine
    (Interpretation.routeValue original meanings old route) predicate

omit propositionRead conjunctionRead in
theorem existential_supplied (route : Route original) {parameter : D}
    (predicate : parameter ⟶ Interpretation.power original meanings old (operations doctrine) route.source) :
    family doctrine (predicate ≫ (meaning original meanings old doctrine).existential route) =
      doctrine.existsAlong (Interpretation.routeValue original meanings old route ▷ parameter) (family doctrine predicate) :=
  HigherOrderInternalPredicateQuantifier.exists_supplied doctrine
    (Interpretation.routeValue original meanings old route) predicate

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.NativeMeaning
