import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceDisplayedTerms
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLLeibnizInterface
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizRepresentation

/-!
# Literal trace meaning of the native Leibniz equality operator

The alternative native equality operator is the representation of the source
Leibniz formula.  In the full trace model its value is literally the existing
primitive equality value: a predicate separating one endpoint from the other
proves the reverse implication, while actual equality transports every
predicate.

The equality of trace values lifts into arbitrary mixed dependent contexts.
Thus the native operator and its applications can be used compositionally
without identifying native identity proofs or adding an equality equation to
the calculus.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceLeibnizDisplayed

open Presentation Mettapedia.Logic HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniformListTraceTypeInterpretation
open ZFSetUniformListTraceTermInterpretation
open NativeTraceLambdaSemantics

universe u

/-- Full predicate quantification makes source Leibniz equality and primitive
equality the same trace-encoded function, not merely equivalent relations. -/
theorem sourceEquality_trace_value (a : ZFSet.{u}) (type : HOL.Ty BaseSort) :
    ZFSetUniformListTraceTermInterpretation.interpret
        (FormationSensitiveHOLLeibnizInterface.sourceEquality type)
        (emptyValuation : Valuation a []) =
      NativeHOLUniformListTraceRepresentation.equalityValue a type := by
  unfold FormationSensitiveHOLLeibnizInterface.sourceEquality
    HOLLeibnizProofComparison.Source.leibniz
    NativeHOLUniformListTraceRepresentation.equalityValue
  simp only [ZFSetUniformListTraceTermInterpretation.interpret,
    ZFSetUniformListTraceTermInterpretation.extend,
    HOL.weaken, HOL.rename, HOL.Rename.weaken,
    ZFSetHOLTypeInterpretation.holds_truth]
  apply congrArg ZFSetUniformListTraceTypeInterpretation.lam
  funext left
  apply congrArg ZFSetUniformListTraceTypeInterpretation.lam
  funext right
  apply congrArg ZFSetHOLTypeInterpretation.truth
  apply propext
  constructor
  · intro transported
    let predicate : Value a (.arr type .prop) :=
      ZFSetUniformListTraceTypeInterpretation.lam
        (fun candidate => ZFSetHOLTypeInterpretation.truth (candidate = left))
    have selected := transported predicate
    have reflexive : ZFSetHOLTypeInterpretation.holds
        (ZFSetUniformListTraceTypeInterpretation.app predicate left) := by
      simp [predicate]
    have result := selected reflexive
    have right_eq_left : right = left := by
      have result' : ZFSetHOLTypeInterpretation.holds
          (ZFSetHOLTypeInterpretation.truth (right = left)) := by
        simpa [predicate] using result
      exact (@ZFSetHOLTypeInterpretation.holds_truth.{u} (right = left)).mp result'
    exact right_eq_left.symm
  · rintro rfl
    exact fun _ assumption => assumption

/-- The fixed original representation emits the existing native equality
operator on this constant-free source term. -/
theorem sourceEquality_represented (type : HOL.Ty BaseSort) :
    HOLNaturalDeductionNativeTranslation.represent
        (FormationSensitiveHOLLeibnizInterface.sourceEquality type) =
      some (FormationSensitiveHOLLeibnizInterface.equality type) := rfl

/-- The closed native Leibniz operator has primitive equality meaning in every
mixed semantic context. -/
theorem equality_denotes (a : ZFSet.{u}) {n : Nat} (context : Context.{u} n)
    (type : HOL.Ty BaseSort) :
    NativeHOLTraceDisplayedTerms.Denotes a context
      (type := .arr type (.arr type .prop))
      (liftClosed (FormationSensitiveHOLLeibnizInterface.equality type))
      (fun _ => NativeHOLUniformListTraceRepresentation.equalityValue a type) := by
  have sourceMeaning :=
    NativeHOLUniformListTraceRepresentation.representation_square (a := a)
      (FormationSensitiveHOLLeibnizInterface.sourceEquality type)
      (sourceEquality_represented type)
  have displayed := NativeHOLTraceDisplayedTerms.display_source_denotation sourceMeaning
    context (renSub Fin.elim0)
    (fun _ => ZFSetUniformListTraceTermInterpretation.emptyValuation)
    (fun index => nomatch index)
  apply NativeHOLTraceDisplayedTerms.Denotes.change_value
    (by simpa only [subst_renSub, liftClosed] using displayed)
  funext environment
  exact sourceEquality_trace_value a type

/-- Applying the actual native operator computes to literal equality of the
independently denoted operands. -/
theorem application_denotes {a : ZFSet.{u}} {n : Nat} {context : Context.{u} n}
    {type : HOL.Ty BaseSort} {x y : Tower.Tm n}
    {left right : context.Environment → Value a type}
    (hx : NativeHOLTraceDisplayedTerms.Denotes a context x left)
    (hy : NativeHOLTraceDisplayedTerms.Denotes a context y right) :
    NativeHOLTraceDisplayedTerms.Denotes a context (type := .prop)
      (.app (.app (liftClosed (FormationSensitiveHOLLeibnizInterface.equality type)) x) y)
      (fun environment => ZFSetHOLTypeInterpretation.truth
        (left environment = right environment)) := by
  have applied := NativeHOLTraceDisplayedTerms.Denotes.application
    (NativeHOLTraceDisplayedTerms.Denotes.application
      (equality_denotes a context type) hx) hy
  apply NativeHOLTraceDisplayedTerms.Denotes.change_value applied
  funext environment
  exact NativeHOLUniformListTraceRepresentation.equalityValue_apply
    (left environment) (right environment)

/-- Renaming the closed Leibniz equality formula into an arbitrary source
context does not change its trace value. -/
theorem equalityAt_trace_value {a : ZFSet.{u}} {gamma : HOL.Ctx BaseSort}
    (type : HOL.Ty BaseSort) (valuation : Valuation a gamma) :
    interpret (HOLLeibnizRepresentationSemantics.equalityAt gamma type) valuation =
      NativeHOLUniformListTraceRepresentation.equalityValue a type := by
  unfold HOLLeibnizRepresentationSemantics.equalityAt
  rw [ZFSetUniformListTraceTermInterpretation.interpret_rename]
  change interpret (FormationSensitiveHOLLeibnizInterface.sourceEquality type)
    (fun {_} index => nomatch index) = _
  exact sourceEquality_trace_value a type

/-- Expanding primitive equality into Leibniz equality preserves the literal
trace value at every simple type.  Full-domain extensional equality is pulled
back through the injective trace decoder. -/
theorem expansion_trace_value {a : ZFSet.{u}} {gamma : HOL.Ctx BaseSort}
    {type : HOL.Ty BaseSort} (term : HOL.Term Symbol gamma type)
    (valuation : Valuation a gamma) :
    interpret (HOLLeibnizRepresentationSemantics.expand term) valuation =
      interpret term valuation := by
  induction term with
  | var | const | top | bot => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [HOLLeibnizRepresentationSemantics.expand, interpret,
        functionInduction valuation, argumentInduction valuation]
  | lam body inductionHypothesis =>
      simp only [HOLLeibnizRepresentationSemantics.expand, interpret]
      apply congrArg ZFSetUniformListTraceTypeInterpretation.lam
      funext argument
      exact inductionHypothesis (extend valuation argument)
  | and left right leftInduction rightInduction
  | or left right leftInduction rightInduction
  | imp left right leftInduction rightInduction =>
      simp only [HOLLeibnizRepresentationSemantics.expand, interpret,
        leftInduction valuation, rightInduction valuation]
  | not formula inductionHypothesis =>
      simp only [HOLLeibnizRepresentationSemantics.expand, interpret,
        inductionHypothesis valuation]
  | all formula inductionHypothesis =>
      simp only [HOLLeibnizRepresentationSemantics.expand, interpret]
      apply congrArg ZFSetHOLTypeInterpretation.truth
      apply propext
      constructor <;> intro hypothesis argument
      · simpa only [inductionHypothesis (extend valuation argument)] using
          hypothesis argument
      · simpa only [inductionHypothesis (extend valuation argument)] using
          hypothesis argument
  | ex formula inductionHypothesis =>
      simp only [HOLLeibnizRepresentationSemantics.expand, interpret]
      apply congrArg ZFSetHOLTypeInterpretation.truth
      apply propext
      constructor
      · rintro ⟨argument, hypothesis⟩
        exact ⟨argument, by
          simpa only [inductionHypothesis (extend valuation argument)] using hypothesis⟩
      · rintro ⟨argument, hypothesis⟩
        exact ⟨argument, by
          simpa only [inductionHypothesis (extend valuation argument)] using hypothesis⟩
  | @eq gamma type left right leftInduction rightInduction =>
      simp only [HOLLeibnizRepresentationSemantics.expand, interpret,
        equalityAt_trace_value, NativeHOLUniformListTraceRepresentation.equalityValue_apply,
        leftInduction valuation, rightInduction valuation]

/-- The alternative, Leibniz-based representation commutes with the same
literal source trace interpretation in an arbitrary mixed native context. -/
theorem representation_square {a : ZFSet.{u}}
    {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    (term : HOL.Term Symbol gamma type) {code : Tower.Tm gamma.length}
    (represented : FormationSensitiveHOLInterface.represent
      FormationSensitiveHOLLeibnizInterface.signature term = some code)
    {n : Nat} (context : Context.{u} n)
    (objects : Sub Tower.Head gamma.length n)
    (valuation : context.Environment → Valuation a gamma)
    (components : ∀ {objectType : HOL.Ty BaseSort}
      (index : HOL.Var gamma objectType),
      NativeHOLTraceDisplayedTerms.Denotes a context
        (objects (FormationSensitiveHOLInterface.variableIndex index))
        (fun environment => valuation environment index)) :
    NativeHOLTraceDisplayedTerms.Denotes a context (subst objects code)
      (fun environment => interpret term (valuation environment)) := by
  have oldRepresented : HOLNaturalDeductionNativeTranslation.represent
      (HOLLeibnizRepresentationSemantics.expand term) = some code := by
    exact (HOLLeibnizRepresentationSemantics.representation_expand term).trans represented
  have oldMeaning := NativeHOLTraceDisplayedTerms.representation_square
    (HOLLeibnizRepresentationSemantics.expand term) oldRepresented
    context objects valuation components
  apply NativeHOLTraceDisplayedTerms.Denotes.change_value oldMeaning
  funext environment
  exact expansion_trace_value term (valuation environment)

namespace Controls

/-- The operator does not make distinct trace values equal. -/
theorem distinct_values_rejected {a : ZFSet.{u}} {type : HOL.Ty BaseSort}
    {left right : Value a type} (distinct : left ≠ right) :
    ¬ ZFSetHOLTypeInterpretation.holds
      (ZFSetUniformListTraceTypeInterpretation.app
        (ZFSetUniformListTraceTypeInterpretation.app
          (NativeHOLUniformListTraceRepresentation.equalityValue a type) left) right) := by
  rw [NativeHOLUniformListTraceRepresentation.equalityValue_apply,
    ZFSetHOLTypeInterpretation.holds_truth]
  exact distinct

end Controls

#print axioms sourceEquality_trace_value
#print axioms sourceEquality_represented
#print axioms equality_denotes
#print axioms application_denotes
#print axioms equalityAt_trace_value
#print axioms expansion_trace_value
#print axioms representation_square
#print axioms Controls.distinct_values_rejected

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceLeibnizDisplayed
