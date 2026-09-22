import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNaturalDeductionNativeTranslation
import Mettapedia.Logic.HOL.Embedding.ZFSetUniformListTraceTermInterpretation

/-!
# Trace meaning of represented native HOL terms

The existing HOL representation emits ordinary cumulative-tower variables,
declarations, applications, and lambdas.  This file gives those exact output
terms an independent interpretation in the uniform-list model whose function
spaces are Aczel traces.  The interpretation is indexed by the source HOL
context and type; it does not introduce an untyped carrier or an opaque source
term constructor.

Every successful source representation is related to its trace denotation.
Thus constants passed to universal elimination cross the same semantic
boundary as variables and lambda terms, while erasure remains literally the
output of the pre-existing native representation.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLUniformListTraceRepresentation

open Presentation Mettapedia.Logic
open HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniformListTraceTypeInterpretation
open ZFSetUniformListTraceTermInterpretation

universe u

abbrev SourceContext := HOL.Ctx BaseSort
abbrev Valuation (a : ZFSet.{u}) (gamma : SourceContext) :=
  ZFSetUniformListTraceTermInterpretation.Valuation a gamma

noncomputable def implicationValue (a : ZFSet.{u}) :
    Value a (.arr .prop (.arr .prop .prop)) :=
  lam (fun p => lam (fun q => ZFSetHOLTypeInterpretation.truth
    (ZFSetHOLTypeInterpretation.holds p → ZFSetHOLTypeInterpretation.holds q)))

noncomputable def universalValue (a : ZFSet.{u}) (type : HOL.Ty BaseSort) :
    Value a (.arr (.arr type .prop) .prop) :=
  lam (fun predicate => ZFSetHOLTypeInterpretation.truth
    (∀ x, ZFSetHOLTypeInterpretation.holds (app predicate x)))

noncomputable def equalityValue (a : ZFSet.{u}) (type : HOL.Ty BaseSort) :
    Value a (.arr type (.arr type .prop)) :=
  lam (fun left => lam (fun right => ZFSetHOLTypeInterpretation.truth (left = right)))

/-- A compositional semantic judgment on the actual cumulative-tower term
emitted by the original representation.  Its semantic value is defined with
trace application and abstraction, independently of native typing. -/
inductive Denotes (a : ZFSet.{u}) :
    {gamma : SourceContext} → {type : HOL.Ty BaseSort} →
      Tower.Tm gamma.length → (Valuation a gamma → Value a type) → Prop where
  | index {gamma : SourceContext} {type : HOL.Ty BaseSort}
      (index : HOL.Var gamma type) :
      Denotes a (.var (FormationSensitiveHOLInterface.variableIndex index))
        (fun valuation => valuation index)
  | constant {gamma : SourceContext} {type : HOL.Ty BaseSort}
      (symbol : Symbol type) :
      Denotes a (.const (FormationSensitiveHOLUniformList.symbolName symbol))
        (fun _ => ZFSetUniformListTraceTypeInterpretation.constant a symbol)
  | implication {gamma : SourceContext} :
      Denotes a (gamma := gamma) (.const `HOLUniformList.implication)
        (fun _ => implicationValue a)
  | universal {gamma : SourceContext} (type : HOL.Ty BaseSort) :
      Denotes a (gamma := gamma)
        (.app (.const `HOLUniformList.universal)
          (FormationSensitiveHOLInterface.typeAt
            FormationSensitiveHOLUniformList.types gamma.length type))
        (fun _ => universalValue a type)
  | equality {gamma : SourceContext} (type : HOL.Ty BaseSort) :
      Denotes a (gamma := gamma)
        (.app (.const `HOLUniformList.equality)
          (FormationSensitiveHOLInterface.typeAt
            FormationSensitiveHOLUniformList.types gamma.length type))
        (fun _ => equalityValue a type)
  | application {gamma : SourceContext} {domain codomain : HOL.Ty BaseSort}
      {function argument : Tower.Tm gamma.length}
      {functionValue : Valuation a gamma → Value a (.arr domain codomain)}
      {argumentValue : Valuation a gamma → Value a domain} :
      Denotes a function functionValue → Denotes a argument argumentValue →
        Denotes a (.app function argument)
          (fun valuation => app (functionValue valuation) (argumentValue valuation))
  | abstraction {gamma : SourceContext} {domain codomain : HOL.Ty BaseSort}
      {body : Tower.Tm (gamma.length + 1)}
      {bodyValue : Valuation a (domain :: gamma) → Value a codomain} :
      Denotes a (gamma := domain :: gamma) body bodyValue →
        Denotes a (.lam body)
          (fun valuation => lam (fun argument => bodyValue (extend valuation argument)))

theorem implicationValue_apply {a : ZFSet.{u}}
    (p q : Value a (.prop : HOL.Ty BaseSort)) :
    app (app (implicationValue a) p) q =
      ZFSetHOLTypeInterpretation.truth
        (ZFSetHOLTypeInterpretation.holds p → ZFSetHOLTypeInterpretation.holds q) := by
  simp [implicationValue]

theorem universalValue_apply {a : ZFSet.{u}} {type : HOL.Ty BaseSort}
    (predicate : Value a (.arr type .prop)) :
    app (universalValue a type) predicate =
      ZFSetHOLTypeInterpretation.truth
        (∀ x, ZFSetHOLTypeInterpretation.holds (app predicate x)) := by
  simp [universalValue]

theorem equalityValue_apply {a : ZFSet.{u}} {type : HOL.Ty BaseSort}
    (left right : Value a type) :
    app (app (equalityValue a type) left) right =
      ZFSetHOLTypeInterpretation.truth (left = right) := by
  simp [equalityValue]

private theorem application_result {n : Nat}
    {function argument : Option (Tower.Tm n)} {result : Tower.Tm n} :
    (do let f ← function; let x ← argument; pure (.app f x)) = some result ↔
      ∃ f x, function = some f ∧ argument = some x ∧ result = .app f x := by
  cases function <;> cases argument <;> simp [eq_comm]

/-- Representation and trace interpretation commute for every supported HOL
term, including the constant-bearing arguments used by universal elimination.
The native output is the existing representation result, not a recreated code
tree chosen after seeing the semantics. -/
theorem representation_square {a : ZFSet.{u}} {gamma : SourceContext}
    {type : HOL.Ty BaseSort} (term : HOL.Term Symbol gamma type)
    {code : Tower.Tm gamma.length}
    (represented : HOLNaturalDeductionNativeTranslation.represent term = some code) :
    Denotes a code (fun valuation => interpret term valuation) := by
  induction term with
  | var index =>
      cases Option.some.inj represented
      exact .index index
  | @const type gamma symbol =>
      cases Option.some.inj represented
      exact .constant (gamma := gamma) symbol
  | app function argument functionInduction argumentInduction =>
      obtain ⟨functionCode, argumentCode, functionRepresented, argumentRepresented, rfl⟩ :=
        application_result.mp represented
      exact .application (functionInduction functionRepresented)
        (argumentInduction argumentRepresented)
  | lam body inductionHypothesis =>
      obtain ⟨bodyCode, bodyRepresented, rfl⟩ := Option.map_eq_some_iff.mp represented
      exact .abstraction (inductionHypothesis bodyRepresented)
  | imp p q pInduction qInduction =>
      obtain ⟨function, qCode, functionRepresented, qRepresented, rfl⟩ :=
        application_result.mp represented
      obtain ⟨head, pCode, headRepresented, pRepresented, rfl⟩ :=
        application_result.mp functionRepresented
      cases Option.some.inj headRepresented
      have raw := Denotes.application (domain := .prop) (codomain := .prop)
        (Denotes.application (domain := .prop) (codomain := .arr .prop .prop)
          (Denotes.implication (a := a)) (pInduction pRepresented))
        (qInduction qRepresented)
      simpa only [FormationSensitiveHOLUniformList.signature, liftClosed,
        Presentation.rename, interpret, implicationValue_apply] using raw
  | @all domain gamma body inductionHypothesis =>
      obtain ⟨head, argument, headRepresented, argumentRepresented, rfl⟩ :=
        application_result.mp represented
      cases Option.some.inj headRepresented
      obtain ⟨bodyCode, bodyRepresented, rfl⟩ := Option.map_eq_some_iff.mp argumentRepresented
      have raw := Denotes.application (domain := .arr domain .prop) (codomain := .prop)
        (Denotes.universal (a := a) (gamma := gamma) domain)
        (Denotes.abstraction (inductionHypothesis bodyRepresented))
      simpa only [FormationSensitiveHOLUniformList.signature,
        FormationSensitiveHOLUniformList.universal, liftClosed, Presentation.rename,
        FormationSensitiveHOLInterface.typeAt_rename, interpret,
        universalValue_apply, app_lam] using raw
  | @eq gamma type left right leftInduction rightInduction =>
      obtain ⟨function, rightCode, functionRepresented, rightRepresented, rfl⟩ :=
        application_result.mp represented
      obtain ⟨head, leftCode, headRepresented, leftRepresented, rfl⟩ :=
        application_result.mp functionRepresented
      cases Option.some.inj headRepresented
      have raw := Denotes.application (domain := type) (codomain := .prop)
        (Denotes.application (domain := type) (codomain := .arr type .prop)
          (Denotes.equality (a := a) (gamma := gamma) type)
          (leftInduction leftRepresented))
        (rightInduction rightRepresented)
      simpa only [FormationSensitiveHOLUniformList.signature,
        FormationSensitiveHOLUniformList.equality, liftClosed, Presentation.rename,
        FormationSensitiveHOLInterface.typeAt_rename, interpret,
        equalityValue_apply] using raw
  | top | bot | and | or | not | ex =>
      cases represented

theorem represented_map_denotes {a : ZFSet.{u}}
    {gamma : SourceContext} (f : HOL.Term Symbol gamma mapping)
    (xs : HOL.Term Symbol gamma sequence) {code : Tower.Tm gamma.length}
    (represented : HOLNaturalDeductionNativeTranslation.represent
      (HOL.Term.app (HOL.Term.app (.const Symbol.map) f) xs) = some code) :
    Denotes a code (fun valuation => interpret
      (HOL.Term.app (HOL.Term.app (.const Symbol.map) f) xs) valuation) :=
  representation_square _ represented

#print axioms implicationValue_apply
#print axioms universalValue_apply
#print axioms equalityValue_apply
#print axioms representation_square
#print axioms represented_map_denotes

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLUniformListTraceRepresentation
