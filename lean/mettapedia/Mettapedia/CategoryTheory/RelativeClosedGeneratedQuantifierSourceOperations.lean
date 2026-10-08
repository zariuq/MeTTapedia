import Mettapedia.CategoryTheory.RelativeClosedGeneratedPredicateSourceOperations
import Mettapedia.CategoryTheory.RelativeClosedSyntaxSignatureMapComposition

/-!
# Authored generated-arrow diagrams earn source quantifier adjunctions

The actual source quotient supplies each quantifier arrow. Its independent
finite diagrams, transported through the ordered-function comparison,
earn the universal and existential local qualifications. Those finite
qualifications then give the Galois connections in every parameter
context with the retained conjunctive laws. Raw source objects remain
their authored presentations throughout.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.SourceOperations

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open RelativeClosedSyntax GeneratedCategory

universe k
variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable (original : Signature (C := C) (symbols := symbols))
variable (language : PredicateSyntax original)
variable (truth : RawHom (terminal original) language.proposition)

def stageInclusion := (arrowInclusion original language).compose (equationInclusion original language)
def stageTruth : RawHom (terminal (signature original language)) (retainedSyntax original language).proposition :=
  (equationInclusion original language).rawArrow ((arrowInclusion original language).rawArrow truth)
def stageRoute (route : Route original) :=
  (mappedRoute original language route).translate (equationInclusion original language)

abbrev stageOperations := operations (retainedSyntax original language) (stageTruth original language truth)
abbrev stageFunctions (value : Object (signature original language)) :=
  functions (retainedSyntax original language) (stageTruth original language truth) value

theorem stage_laws (laws : (operations language truth).Laws) :
    (stageOperations original language truth).Laws :=
  translated_laws (argumentSyntax original language) ((arrowInclusion original language).rawArrow truth)
    (equationInclusion original language)
    (translated_laws language truth (arrowInclusion original language) laws)

def universalQualification (route : Route original) :
    InternalPredicateQuantifier.Universal (stageOperations original language truth)
      (classOf (stageRoute original language route).arrow) where
  operation := classOf (named original language .universal route)
  monotonicity := monotonicity_comparison (retainedSyntax original language) (stageTruth original language truth) _ (by
    have complete := declared_law original language ⟨.universalMonotonicity, route⟩
    change classOf ((retainedSyntax original language).powerMeet (stageRoute original language route).target
        (((retainedSyntax original language).larger (stageRoute original language route).source).compose
          (named original language .universal route))
        (((retainedSyntax original language).smaller (stageRoute original language route).source).compose
          (named original language .universal route))) =
      classOf (((retainedSyntax original language).smaller (stageRoute original language route).source).compose
        (named original language .universal route)) at complete
    exact (powerMeet_read (retainedSyntax original language) (stageTruth original language truth)
      (stageRoute original language route).target _ _).symm.trans complete)
  unit := by
    have complete := declared_law original language ⟨.universalUnit, route⟩
    change classOf ((retainedSyntax original language).powerMeet (stageRoute original language route).target
        (((retainedSyntax original language).precomposition (stageRoute original language route)).compose
          (named original language .universal route))
        (RawHom.identity ((retainedSyntax original language).power (stageRoute original language route).target))) =
      classOf (RawHom.identity ((retainedSyntax original language).power (stageRoute original language route).target)) at complete
    have read := (powerMeet_read (retainedSyntax original language) (stageTruth original language truth)
      (stageRoute original language route).target _ _).symm.trans complete
    change (stageFunctions original language truth (stageRoute original language route).target).meet
      (classOf ((retainedSyntax original language).precomposition (stageRoute original language route)) ≫
        classOf (named original language .universal route)) (𝟙 _) = 𝟙 _ at read
    rw [precomposition_read] at read
    exact read
  counit := by
    have complete := declared_law original language ⟨.universalCounit, route⟩
    change classOf ((retainedSyntax original language).powerMeet (stageRoute original language route).source
        (RawHom.identity ((retainedSyntax original language).power (stageRoute original language route).source))
        ((named original language .universal route).compose
          ((retainedSyntax original language).precomposition (stageRoute original language route)))) =
      classOf ((named original language .universal route).compose
        ((retainedSyntax original language).precomposition (stageRoute original language route))) at complete
    have read := (powerMeet_read (retainedSyntax original language) (stageTruth original language truth)
      (stageRoute original language route).source _ _).symm.trans complete
    change (stageFunctions original language truth (stageRoute original language route).source).meet (𝟙 _)
      (classOf (named original language .universal route) ≫
        classOf ((retainedSyntax original language).precomposition (stageRoute original language route))) =
      classOf (named original language .universal route) ≫
        classOf ((retainedSyntax original language).precomposition (stageRoute original language route)) at read
    rw [precomposition_read] at read
    exact read

def existentialQualification (route : Route original) :
    InternalPredicateExistential.Existential (stageOperations original language truth)
      (classOf (stageRoute original language route).arrow) where
  operation := classOf (named original language .existential route)
  monotonicity := monotonicity_comparison (retainedSyntax original language) (stageTruth original language truth) _ (by
    have complete := declared_law original language ⟨.existentialMonotonicity, route⟩
    change classOf ((retainedSyntax original language).powerMeet (stageRoute original language route).target
        (((retainedSyntax original language).larger (stageRoute original language route).source).compose
          (named original language .existential route))
        (((retainedSyntax original language).smaller (stageRoute original language route).source).compose
          (named original language .existential route))) =
      classOf (((retainedSyntax original language).smaller (stageRoute original language route).source).compose
        (named original language .existential route)) at complete
    exact (powerMeet_read (retainedSyntax original language) (stageTruth original language truth)
      (stageRoute original language route).target _ _).symm.trans complete)
  unit := by
    have complete := declared_law original language ⟨.existentialUnit, route⟩
    change classOf ((retainedSyntax original language).powerMeet (stageRoute original language route).source
        ((named original language .existential route).compose
          ((retainedSyntax original language).precomposition (stageRoute original language route)))
        (RawHom.identity ((retainedSyntax original language).power (stageRoute original language route).source))) =
      classOf (RawHom.identity ((retainedSyntax original language).power (stageRoute original language route).source)) at complete
    have read := (powerMeet_read (retainedSyntax original language) (stageTruth original language truth)
      (stageRoute original language route).source _ _).symm.trans complete
    change (stageFunctions original language truth (stageRoute original language route).source).meet
      (classOf (named original language .existential route) ≫
        classOf ((retainedSyntax original language).precomposition (stageRoute original language route))) (𝟙 _) = 𝟙 _ at read
    rw [precomposition_read] at read
    exact read
  counit := by
    have complete := declared_law original language ⟨.existentialCounit, route⟩
    change classOf ((retainedSyntax original language).powerMeet (stageRoute original language route).target
        (RawHom.identity ((retainedSyntax original language).power (stageRoute original language route).target))
        (((retainedSyntax original language).precomposition (stageRoute original language route)).compose
          (named original language .existential route))) =
      classOf (((retainedSyntax original language).precomposition (stageRoute original language route)).compose
        (named original language .existential route)) at complete
    have read := (powerMeet_read (retainedSyntax original language) (stageTruth original language truth)
      (stageRoute original language route).target _ _).symm.trans complete
    change (stageFunctions original language truth (stageRoute original language route).target).meet (𝟙 _)
      (classOf ((retainedSyntax original language).precomposition (stageRoute original language route)) ≫
        classOf (named original language .existential route)) =
      classOf ((retainedSyntax original language).precomposition (stageRoute original language route)) ≫
        classOf (named original language .existential route) at read
    rw [precomposition_read] at read
    exact read

theorem universal_galois (laws : (stageOperations original language truth).Laws)
    (route : Route original) (context : Object (signature original language)) :
    letI : SemilatticeInf (context ⟶ InternalPredicateFunctionObject.power
      (stageOperations original language truth) (stageRoute original language route).target) :=
      (stageFunctions original language truth (stageRoute original language route).target).semilattice
      (InternalPredicateFunctionObject.function_laws (stageOperations original language truth) laws _) context
    letI : SemilatticeInf (context ⟶ InternalPredicateFunctionObject.power
      (stageOperations original language truth) (stageRoute original language route).source) :=
      (stageFunctions original language truth (stageRoute original language route).source).semilattice
      (InternalPredicateFunctionObject.function_laws (stageOperations original language truth) laws _) context
    GaloisConnection
      (fun predicate : context ⟶ InternalPredicateFunctionObject.power
          (stageOperations original language truth) (stageRoute original language route).target =>
        predicate ≫ InternalPredicateQuantifier.precomposition
        (stageOperations original language truth) (classOf (stageRoute original language route).arrow))
      (fun predicate : context ⟶ InternalPredicateFunctionObject.power
          (stageOperations original language truth) (stageRoute original language route).source =>
        predicate ≫ classOf (named original language .universal route)) :=
  InternalPredicateQuantifier.Universal.adjunction (stageOperations original language truth) laws
    (classOf (stageRoute original language route).arrow)
    (universalQualification original language truth route) context

theorem existential_galois (laws : (stageOperations original language truth).Laws)
    (route : Route original) (context : Object (signature original language)) :
    letI : SemilatticeInf (context ⟶ InternalPredicateFunctionObject.power
      (stageOperations original language truth) (stageRoute original language route).source) :=
      (stageFunctions original language truth (stageRoute original language route).source).semilattice
      (InternalPredicateFunctionObject.function_laws (stageOperations original language truth) laws _) context
    letI : SemilatticeInf (context ⟶ InternalPredicateFunctionObject.power
      (stageOperations original language truth) (stageRoute original language route).target) :=
      (stageFunctions original language truth (stageRoute original language route).target).semilattice
      (InternalPredicateFunctionObject.function_laws (stageOperations original language truth) laws _) context
    GaloisConnection
      (fun predicate : context ⟶ InternalPredicateFunctionObject.power
          (stageOperations original language truth) (stageRoute original language route).source =>
        predicate ≫ classOf (named original language .existential route))
      (fun predicate : context ⟶ InternalPredicateFunctionObject.power
          (stageOperations original language truth) (stageRoute original language route).target =>
        predicate ≫ InternalPredicateQuantifier.precomposition
        (stageOperations original language truth) (classOf (stageRoute original language route).arrow)) :=
  InternalPredicateExistential.Existential.adjunction (stageOperations original language truth) laws
    (classOf (stageRoute original language route).arrow)
    (existentialQualification original language truth route) context

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.SourceOperations
