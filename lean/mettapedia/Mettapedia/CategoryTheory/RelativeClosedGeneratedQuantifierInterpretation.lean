import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierPresentation
import Mettapedia.CategoryTheory.RelativeClosedGeneratedPredicateReadout
import Mettapedia.CategoryTheory.RelativeClosedSyntaxArrowInterpretation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxEquationInterpretation
import Mettapedia.CategoryTheory.InternalPredicateExistential

/-!
# Independent quantifier meanings at all supplied generated routes

The old raw object and arrow values come from the independent structural
evaluator and its earned declaration realization. Each new universal or
existential is a separately supplied complete function-object arrow.
Admission contains only its three finite diagrams. Successful readings of
the retained proposition and conjunction earn the new headers and all
function scopes, without an assumed whole-expression interpretation law.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Interpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open RelativeClosedSyntax GeneratedCategory

universe k w z
variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable (original : Signature (C := C) (symbols := symbols))
variable (language : PredicateSyntax original)
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (meanings : RelativeClosedSyntax.Interpretation.Assignment C symbols D)
variable (old : RelativeClosedSyntax.Interpretation.Realization original meanings)
variable (operations : InternalConjunctiveObject.Operations D)

abbrev value (raw : Object original) :=
  RelativeClosedSyntax.Interpretation.objectValue meanings old raw

abbrev routeValue (route : Route original) :=
  RelativeClosedSyntax.Interpretation.rawArrowValue meanings old route.arrow

abbrev power (raw : Object original) :=
  InternalPredicateFunctionObject.power operations (value original meanings old raw)

abbrev functions (raw : Object original) :=
  InternalPredicateFunctionObject.operations operations (value original meanings old raw)

structure Meaning where
  universal (route : Route original) :
    power original meanings old operations route.source ⟶ power original meanings old operations route.target
  existential (route : Route original) :
    power original meanings old operations route.source ⟶ power original meanings old operations route.target

variable (meaning : Meaning original meanings old operations)

def operator (kind : Kind) (route : Route original) :
    power original meanings old operations route.source ⟶ power original meanings old operations route.target :=
  match kind with
  | .universal => meaning.universal route
  | .existential => meaning.existential route

/-- Three actual finite diagrams for each independently supplied operation. -/
structure Admission : Prop where
  universalMonotonicity (route : Route original) :
    InternalPredicateQuantifier.Monotonicity operations (meaning.universal route)
  universalUnit (route : Route original) :
    (functions original meanings old operations route.target).meet
      (InternalPredicateQuantifier.precomposition operations (routeValue original meanings old route) ≫ meaning.universal route)
      (𝟙 (power original meanings old operations route.target)) = 𝟙 _
  universalCounit (route : Route original) :
    (functions original meanings old operations route.source).meet (𝟙 (power original meanings old operations route.source))
      (meaning.universal route ≫ InternalPredicateQuantifier.precomposition operations (routeValue original meanings old route)) =
    meaning.universal route ≫ InternalPredicateQuantifier.precomposition operations (routeValue original meanings old route)
  existentialMonotonicity (route : Route original) :
    InternalPredicateQuantifier.Monotonicity operations (meaning.existential route)
  existentialUnit (route : Route original) :
    (functions original meanings old operations route.source).meet
      (meaning.existential route ≫ InternalPredicateQuantifier.precomposition operations (routeValue original meanings old route))
      (𝟙 (power original meanings old operations route.source)) = 𝟙 _
  existentialCounit (route : Route original) :
    (functions original meanings old operations route.target).meet (𝟙 (power original meanings old operations route.target))
      (InternalPredicateQuantifier.precomposition operations (routeValue original meanings old route) ≫ meaning.existential route) =
    InternalPredicateQuantifier.precomposition operations (routeValue original meanings old route) ≫ meaning.existential route

def added (origin : Operation original) : RelativeClosedSyntax.Interpretation.ArrowValue D :=
  ⟨power original meanings old operations origin.route.source,
    power original meanings old operations origin.route.target,
    operator original meanings old operations meaning origin.kind origin.route⟩

def assignment : RelativeClosedSyntax.Interpretation.Assignment C
    (ArrowExtension.extendedSymbols symbols (Operation original)) D :=
  ArrowExtension.extendAssignment meanings (added original meanings old operations meaning)

theorem object_original (raw : Object original) :
    RawInterpretation.ObjectReads (assignment original meanings old operations meaning)
      ((arrowInclusion original language).object raw) (value original meanings old raw) :=
  (ArrowExtension.evaluate_object_original original (arrowDeclaration original language)
    meanings (added original meanings old operations meaning) raw.code).trans
      (RelativeClosedSyntax.Interpretation.objectValue_readout meanings old raw)

theorem arrow_original (route : Route original) :
    RawInterpretation.Reads (assignment original meanings old operations meaning)
      (mappedRoute original language route).arrow (routeValue original meanings old route) :=
  (ArrowExtension.evaluate_arrow_original original (arrowDeclaration original language)
    meanings (added original meanings old operations meaning) route.arrow.code).trans
      (RelativeClosedSyntax.Interpretation.rawArrowValue_readout meanings old route.arrow)

variable (propositionRead : RawInterpretation.ObjectReads meanings language.proposition operations.proposition)
variable (conjunctionRead : RawInterpretation.Reads meanings language.conjunction operations.conjunction)

include propositionRead in
theorem added_headers : ArrowExtension.AddedAdmission original (arrowDeclaration original language)
    meanings (added original meanings old operations meaning) where
  source origin := Readout.power_read language meanings operations propositionRead
    (RelativeClosedSyntax.Interpretation.objectValue_readout meanings old origin.route.source)
  target origin := Readout.power_read language meanings operations propositionRead
    (RelativeClosedSyntax.Interpretation.objectValue_readout meanings old origin.route.target)

include propositionRead in
theorem headers_realized : RelativeClosedSyntax.Interpretation.Realization (arrowSignature original language)
    (assignment original meanings old operations meaning) :=
  ArrowExtension.extended_realization original (arrowDeclaration original language)
    meanings (added original meanings old operations meaning) old
      (added_headers original language meanings old operations meaning propositionRead)

include propositionRead in
theorem proposition_read : RawInterpretation.ObjectReads (assignment original meanings old operations meaning)
    (argumentSyntax original language).proposition operations.proposition :=
  (ArrowExtension.evaluate_object_original original (arrowDeclaration original language)
    meanings (added original meanings old operations meaning) language.proposition.code).trans propositionRead

include conjunctionRead in
theorem conjunction_read : RawInterpretation.Reads (assignment original meanings old operations meaning)
    (argumentSyntax original language).conjunction operations.conjunction :=
  (ArrowExtension.evaluate_arrow_original original (arrowDeclaration original language)
    meanings (added original meanings old operations meaning) language.conjunction.code).trans conjunctionRead

include propositionRead in
theorem power_read (raw : Object original) :
    RawInterpretation.ObjectReads (assignment original meanings old operations meaning)
      ((argumentSyntax original language).power ((arrowInclusion original language).object raw))
      (power original meanings old operations raw) :=
  Readout.power_read (argumentSyntax original language) (assignment original meanings old operations meaning) operations
    (proposition_read original language meanings old operations meaning propositionRead)
    (object_original original language meanings old operations meaning raw)

theorem operator_read (kind : Kind) (route : Route original) :
    RawInterpretation.Reads (assignment original meanings old operations meaning)
      (quantifier original language kind route) (operator original meanings old operations meaning kind route) := rfl

include propositionRead in
theorem precomposition_read (route : Route original) :
    RawInterpretation.Reads (assignment original meanings old operations meaning)
      ((argumentSyntax original language).precomposition (mappedRoute original language route))
      (InternalPredicateQuantifier.precomposition operations (routeValue original meanings old route)) :=
  Readout.precomposition_read (argumentSyntax original language) (assignment original meanings old operations meaning) operations
    (proposition_read original language meanings old operations meaning propositionRead)
    (mappedRoute original language route)
    (object_original original language meanings old operations meaning route.source)
    (object_original original language meanings old operations meaning route.target)
    (arrow_original original language meanings old operations meaning route)

include propositionRead conjunctionRead in
theorem smaller_read (raw : Object original) :
    RawInterpretation.Reads (assignment original meanings old operations meaning)
      ((argumentSyntax original language).smaller ((arrowInclusion original language).object raw))
      (InternalPredicateQuantifier.firstInput operations (value original meanings old raw)) :=
  Readout.smaller_read (argumentSyntax original language) (assignment original meanings old operations meaning) operations
    (proposition_read original language meanings old operations meaning propositionRead)
    (conjunction_read original language meanings old operations meaning conjunctionRead)
    (object_original original language meanings old operations meaning raw)

include propositionRead conjunctionRead in
theorem larger_read (raw : Object original) :
    RawInterpretation.Reads (assignment original meanings old operations meaning)
      ((argumentSyntax original language).larger ((arrowInclusion original language).object raw))
      (InternalPredicateQuantifier.secondInput operations (value original meanings old raw)) :=
  Readout.larger_read (argumentSyntax original language) (assignment original meanings old operations meaning) operations
    (proposition_read original language meanings old operations meaning propositionRead)
    (conjunction_read original language meanings old operations meaning conjunctionRead)
    (object_original original language meanings old operations meaning raw)

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Interpretation
