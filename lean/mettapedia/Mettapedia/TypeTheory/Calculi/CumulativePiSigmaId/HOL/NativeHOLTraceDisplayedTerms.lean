import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLUniformListTraceRepresentation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.NativeTraceDisplayedSubstitution

/-!
# Constant-bearing native HOL terms in mixed trace contexts

This module extends the native variable/lambda/application trace semantics with
the closed constants of the uniform-list HOL presentation.  The surrounding
semantic context may interleave object variables with other dependent fields;
only a variable carrying the required constant HOL family may be used as an
object variable.

The denotation is a relation on actual cumulative-tower terms.  Constants are
interpreted by the existing trace-coded uniform-list model, while application
and abstraction remain the literal Aczel trace operations.  Displayed native
renaming commutes with this interpretation.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceDisplayedTerms

open Presentation Mettapedia.Logic
open HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open ZFSetContextualInterpretation (SetFamily Section)
open ZFSetUniformListTraceTypeInterpretation
open ZFSetUniformListTraceTermInterpretation
open NativeTraceLambdaSemantics
open NativeTraceContextMorphisms
open NativeTraceDisplayedSubstitution

universe u

@[reducible] noncomputable def typeFamily (a : ZFSet.{u}) {n : Nat}
    (context : Context.{u} n) (type : HOL.Ty BaseSort) :
    SetFamily context.Environment :=
  fun _ => typeCode a type

/-- Constructorwise trace meaning for the actual constant-bearing native term.
The variable premise is the smaller native lambda-fragment judgment, so its
family and projection are fixed by the semantic context rather than supplied
arbitrarily. -/
inductive Denotes (a : ZFSet.{u}) : {n : Nat} → (context : Context.{u} n) →
    {type : HOL.Ty BaseSort} → Tower.Tm n →
      (context.Environment → Value a type) → Prop where
  | variable {n : Nat} {context : Context.{u} n} {type : HOL.Ty BaseSort}
      (index : Fin n) {value : context.Environment → Value a type}
      (meaning : NativeTraceLambdaSemantics.Denotes context (.var index)
        (typeFamily a context type) value) :
      Denotes a context (.var index) value
  | constant {n : Nat} {context : Context.{u} n} {type : HOL.Ty BaseSort}
      (symbol : Symbol type) :
      Denotes a context
        (.const (FormationSensitiveHOLUniformList.symbolName symbol))
        (fun _ => constant a symbol)
  | implication {n : Nat} {context : Context.{u} n} :
      Denotes a context (type := .arr .prop (.arr .prop .prop))
        (.const `HOLUniformList.implication)
        (fun _ => NativeHOLUniformListTraceRepresentation.implicationValue a)
  | universal {n : Nat} {context : Context.{u} n}
      (type : HOL.Ty BaseSort) :
      Denotes a context
        (type := .arr (.arr type .prop) .prop)
        (.app (.const `HOLUniformList.universal)
          (FormationSensitiveHOLInterface.typeAt
            FormationSensitiveHOLUniformList.types n type))
        (fun _ => NativeHOLUniformListTraceRepresentation.universalValue a type)
  | equality {n : Nat} {context : Context.{u} n}
      (type : HOL.Ty BaseSort) :
      Denotes a context
        (type := .arr type (.arr type .prop))
        (.app (.const `HOLUniformList.equality)
          (FormationSensitiveHOLInterface.typeAt
            FormationSensitiveHOLUniformList.types n type))
        (fun _ => NativeHOLUniformListTraceRepresentation.equalityValue a type)
  | application {n : Nat} {context : Context.{u} n}
      {domain codomain : HOL.Ty BaseSort}
      {function argument : Tower.Tm n}
      {functionValue : context.Environment → Value a (.arr domain codomain)}
      {argumentValue : context.Environment → Value a domain} :
      Denotes a context function functionValue →
      Denotes a context argument argumentValue →
      Denotes a context (.app function argument)
        (fun environment => app (functionValue environment) (argumentValue environment))
  | abstraction {n : Nat} {context : Context.{u} n}
      {domain codomain : HOL.Ty BaseSort}
      {body : Tower.Tm (n + 1)}
      {bodyValue : (context.snoc (typeFamily a context domain)).Environment →
        Value a codomain} :
      Denotes a (context.snoc (typeFamily a context domain)) body bodyValue →
      Denotes a context (.lam body)
        (fun environment => lam (fun argument => bodyValue ⟨environment, argument⟩))

theorem Denotes.change_value {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {type : HOL.Ty BaseSort} {term : Tower.Tm n}
    {first second : context.Environment → Value a type}
    (meaning : Denotes a context term first) (equal : first = second) :
    Denotes a context term second := by
  cases equal
  exact meaning

/-- Constant-bearing native denotation is natural under a displayed de Bruijn
renaming, including beneath object binders. -/
theorem Denotes.rename {a : ZFSet.{u}} {n : Nat} {source : Context.{u} n}
    {type : HOL.Ty BaseSort} {term : Tower.Tm n}
    {value : source.Environment → Value a type}
    (meaning : Denotes a source term value) {m : Nat} {target : Context.{u} m}
    {rho : Ren n m} {morphism : Morphism source target}
    (displayed : NativeTraceDisplayedSubstitution.Renaming source target rho morphism) :
    Denotes a target (Presentation.rename rho term)
      (fun environment => value (morphism.environment environment)) := by
  induction meaning generalizing m with
  | @«variable» n context type index value variableMeaning =>
      have moved := NativeTraceDisplayedSubstitution.rename_denotes displayed variableMeaning
      exact Denotes.variable (a := a) (type := type) (rho index) moved
  | constant symbol => exact .constant symbol
  | implication => exact .implication
  | universal type =>
      simpa only [Presentation.rename,
        FormationSensitiveHOLInterface.typeAt_rename] using
        (Denotes.universal (a := a) (context := target) type)
  | equality type =>
      simpa only [Presentation.rename,
        FormationSensitiveHOLInterface.typeAt_rename] using
        (Denotes.equality (a := a) (context := target) type)
  | application functionMeaning argumentMeaning functionInduction argumentInduction =>
      exact .application (functionInduction displayed) (argumentInduction displayed)
  | @abstraction n context domain codomain body bodyValue bodyMeaning inductionHypothesis =>
      have bodyMoved := inductionHypothesis
        (NativeTraceDisplayedSubstitution.Renaming.lift displayed
          (typeFamily a context domain))
      apply Denotes.change_value (Denotes.abstraction bodyMoved)
      rfl

theorem Denotes.weaken {a : ZFSet.{u}} {n : Nat} {context : Context.{u} n}
    {type : HOL.Ty BaseSort} {term : Tower.Tm n}
    {value : context.Environment → Value a type}
    (meaning : Denotes a context term value)
    (family : SetFamily context.Environment) :
    Denotes a (context.snoc family) (Presentation.rename wk term)
      (fun point => value point.1) :=
  meaning.rename (NativeTraceDisplayedSubstitution.Renaming.weaken context family)

/-- Substitute represented source variables by constant-bearing native object
terms in an arbitrary mixed context.  The semantic valuation and every native
component are supplied independently of the source denotation. -/
theorem display_source_denotation {a : ZFSet.{u}}
    {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    {code : Tower.Tm gamma.length}
    {value : NativeHOLUniformListTraceRepresentation.Valuation a gamma → Value a type}
    (meaning : NativeHOLUniformListTraceRepresentation.Denotes a code value)
    {n : Nat} (context : Context.{u} n)
    (objects : Sub Tower.Head gamma.length n)
    (valuation : context.Environment →
      NativeHOLUniformListTraceRepresentation.Valuation a gamma)
    (components : ∀ {objectType : HOL.Ty BaseSort}
      (index : HOL.Var gamma objectType),
      Denotes a context (objects (FormationSensitiveHOLInterface.variableIndex index))
        (fun environment => valuation environment index)) :
    Denotes a context (Presentation.subst objects code)
      (fun environment => value (valuation environment)) := by
  induction meaning generalizing n with
  | index index => exact components index
  | constant symbol => exact .constant symbol
  | implication => exact .implication
  | universal type =>
      simpa only [Presentation.subst,
        FormationSensitiveHOLInterface.typeAt_subst] using
        (Denotes.universal (a := a) (context := context) type)
  | equality type =>
      simpa only [Presentation.subst,
        FormationSensitiveHOLInterface.typeAt_subst] using
        (Denotes.equality (a := a) (context := context) type)
  | application functionMeaning argumentMeaning functionInduction argumentInduction =>
      exact .application
        (functionInduction context objects valuation components)
        (argumentInduction context objects valuation components)
  | @abstraction gamma domain codomain body bodyValue bodyMeaning inductionHypothesis =>
      let extended := context.snoc (typeFamily a context domain)
      let extendedValuation : extended.Environment →
          NativeHOLUniformListTraceRepresentation.Valuation a (domain :: gamma) :=
        fun point => ZFSetUniformListTraceTermInterpretation.extend
          (valuation point.1) point.2
      have extendedComponents : ∀ {objectType : HOL.Ty BaseSort}
          (index : HOL.Var (domain :: gamma) objectType),
          Denotes a extended
            (liftSub objects (FormationSensitiveHOLInterface.variableIndex index))
            (fun environment => extendedValuation environment index) := by
        intro objectType index
        cases index with
        | vz =>
            exact Denotes.variable 0
              (NativeTraceLambdaSemantics.Denotes.var extended 0)
        | vs prior =>
            exact (components prior).weaken (typeFamily a context domain)
      have bodyDisplayed := inductionHypothesis extended (liftSub objects)
        extendedValuation extendedComponents
      apply Denotes.change_value (Denotes.abstraction bodyDisplayed)
      rfl

/-- Every successful original HOL representation continues to denote its
source trace meaning after substitution into an arbitrary mixed native
context. -/
theorem representation_square {a : ZFSet.{u}} {gamma : HOL.Ctx BaseSort}
    {type : HOL.Ty BaseSort} (term : HOL.Term Symbol gamma type)
    {code : Tower.Tm gamma.length}
    (represented : HOLNaturalDeductionNativeTranslation.represent term = some code)
    {n : Nat} (context : Context.{u} n)
    (objects : Sub Tower.Head gamma.length n)
    (valuation : context.Environment →
      NativeHOLUniformListTraceRepresentation.Valuation a gamma)
    (components : ∀ {objectType : HOL.Ty BaseSort}
      (index : HOL.Var gamma objectType),
      Denotes a context (objects (FormationSensitiveHOLInterface.variableIndex index))
        (fun environment => valuation environment index)) :
    Denotes a context (Presentation.subst objects code)
      (fun environment => ZFSetUniformListTraceTermInterpretation.interpret term
        (valuation environment)) :=
  display_source_denotation
    (NativeHOLUniformListTraceRepresentation.representation_square term represented)
    context objects valuation components

namespace Controls

def emptyContext : Context.{u} 0 := Context.nil

theorem nil_constant_denotes (a : ZFSet.{u}) :
    Denotes a emptyContext
      (.const (FormationSensitiveHOLUniformList.symbolName Symbol.nil))
      (fun _ => constant a Symbol.nil) :=
  .constant Symbol.nil

theorem newest_object_variable_denotes {n : Nat} (a : ZFSet.{u})
    (context : Context.{u} n) (type : HOL.Ty BaseSort) :
    Denotes a (context.snoc (typeFamily a context type)) (.var 0)
      (fun point => point.2) :=
  .variable 0 (NativeTraceLambdaSemantics.Denotes.var _ 0)

end Controls

#print axioms Denotes.rename
#print axioms Denotes.change_value
#print axioms Denotes.weaken
#print axioms display_source_denotation
#print axioms representation_square
#print axioms Controls.nil_constant_denotes
#print axioms Controls.newest_object_variable_denotes

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceDisplayedTerms
