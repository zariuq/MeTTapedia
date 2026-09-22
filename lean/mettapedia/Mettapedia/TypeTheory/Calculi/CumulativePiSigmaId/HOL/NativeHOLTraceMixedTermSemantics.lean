import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceLeibnizDisplayed
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding

/-!
# Mixed object and proof terms in trace contexts

A native proof term may apply a proof to an object-level predicate, so neither
an object-only interpretation nor a lambda-only fragment is closed under the
actual compiler output.  This judgment combines the independently established
HOL object denotation with generic dependent trace products.  The only leaf
beyond variables is a fully denoted HOL object term; proof abstractions and
applications remain ordinary native syntax.

The judgment is natural under displayed native renaming.  Proof fibres are
the canonical separated truth codes, with implication and universal decoding
inherited from the trace model.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceMixedTermSemantics

open Presentation Mettapedia.Logic HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (Elements)
open ZFSetContextualInterpretation (SetFamily Section Extension)
open NativeTraceLambdaSemantics NativeTraceContextMorphisms
open NativeTraceDisplayedSubstitution

universe u

/-- A heterogeneous semantic judgment for actual native terms. -/
inductive Denotes (a : ZFSet.{u}) : {n : Nat} → (context : Context.{u} n) →
    (term : Tower.Tm n) → (family : SetFamily context.Environment) →
      Section family → Prop where
  | variable {n : Nat} (context : Context.{u} n) (index : Fin n) :
      Denotes a context (.var index) (context.family index) (context.projection index)
  | object {n : Nat} {context : Context.{u} n} {type : HOL.Ty BaseSort}
      {term : Tower.Tm n} {value : context.Environment →
        ZFSetUniformListTraceTypeInterpretation.Value a type}
      (meaning : NativeHOLTraceDisplayedTerms.Denotes a context term value) :
      Denotes a context term (NativeHOLTraceDisplayedTerms.typeFamily a context type) value
  | abstraction {n : Nat} {context : Context.{u} n}
      {domain : SetFamily context.Environment}
      {codomain : SetFamily (Extension domain)} {body : Tower.Tm (n + 1)}
      {bodyValue : Section codomain} :
      Denotes a (context.snoc domain) body codomain bodyValue →
      Denotes a context (.lam body) (ZFSetTraceContextual.piFamily domain codomain)
        (ZFSetTraceContextual.lam bodyValue)
  | application {n : Nat} {context : Context.{u} n}
      {domain : SetFamily context.Environment}
      {codomain : SetFamily (Extension domain)} {function argument : Tower.Tm n}
      {functionValue : Section (ZFSetTraceContextual.piFamily domain codomain)}
      {argumentValue : Section domain} :
      Denotes a context function (ZFSetTraceContextual.piFamily domain codomain)
          functionValue →
      Denotes a context argument domain argumentValue →
      Denotes a context (.app function argument)
        (fun environment => codomain ⟨environment, argumentValue environment⟩)
        (ZFSetTraceContextual.app functionValue argumentValue)

theorem Denotes.cast_family {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {term : Tower.Tm n}
    {first second : SetFamily context.Environment} {value : Section first}
    (meaning : Denotes a context term first value) (equal : first = second) :
    Denotes a context term second (castSection equal value) := by
  cases equal
  exact meaning

theorem Denotes.change_value {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {term : Tower.Tm n}
    {family : SetFamily context.Environment} {first second : Section family}
    (meaning : Denotes a context term family first) (equal : first = second) :
    Denotes a context term family second := by
  cases equal
  exact meaning

/-- Heterogeneous denotation commutes with displayed de Bruijn renaming. -/
theorem Denotes.rename {a : ZFSet.{u}} {n : Nat} {source : Context.{u} n}
    {term : Tower.Tm n} {family : SetFamily source.Environment}
    {value : Section family} (meaning : Denotes a source term family value)
    {m : Nat} {target : Context.{u} m} {rho : Ren n m}
    {morphism : Morphism source target}
    (displayed : NativeTraceDisplayedSubstitution.Renaming source target rho morphism) :
    Denotes a target (Presentation.rename rho term)
      (morphism.reindexFamily family) (morphism.reindexSection value) := by
  induction meaning generalizing m with
  | «variable» context index =>
      have selected := Denotes.variable (a := a) target (rho index)
      have transported := selected.cast_family (displayed.familyEq index)
      exact transported.change_value (displayed.projectionEq index)
  | object objectMeaning =>
      exact Denotes.object (objectMeaning.rename displayed)
  | @abstraction n context domain codomain body bodyValue bodyMeaning inductionHypothesis =>
      exact Denotes.abstraction (inductionHypothesis (displayed.lift domain))
  | @application n context domain codomain function argument functionValue argumentValue
      functionMeaning argumentMeaning functionInduction argumentInduction =>
      have functionMoved := functionInduction displayed
      have argumentMoved := argumentInduction displayed
      have functionForApplication :
          Denotes a target (Presentation.rename rho function)
            (ZFSetTraceContextual.piFamily (morphism.reindexFamily domain)
              (codomain ∘ (morphism.lift domain).environment))
            (morphism.reindexSection functionValue) :=
        functionMoved.cast_family (by rfl)
      exact Denotes.application functionForApplication argumentMoved

theorem Denotes.weaken {a : ZFSet.{u}} {n : Nat} {context : Context.{u} n}
    {term : Tower.Tm n} {family : SetFamily context.Environment}
    {value : Section family} (meaning : Denotes a context term family value)
    (extension : SetFamily context.Environment) :
    Denotes a (context.snoc extension) (Presentation.rename wk term)
      (family ∘ Sigma.fst) (fun point => value point.1) :=
  meaning.rename (NativeTraceDisplayedSubstitution.Renaming.weaken context extension)

/-- The proof family of an interpreted HOL proposition. -/
noncomputable def proofFamily {a : ZFSet.{u}} {Gamma : Type (u + 1)}
    (proposition : Gamma → ZFSetUniformListTraceTypeInterpretation.Value a .prop) :
    SetFamily Gamma :=
  ZFSetTraceProofDecoding.truthFamily
    (fun environment => ZFSetHOLTypeInterpretation.holds (proposition environment))

theorem proofFamily_truth {a : ZFSet.{u}} {Gamma : Type (u + 1)}
    (proposition : Gamma → Prop) :
    proofFamily (a := a) (fun environment =>
      ZFSetHOLTypeInterpretation.truth (proposition environment)) =
      ZFSetTraceProofDecoding.truthFamily proposition := by
  funext environment
  apply congrArg ZFSetTraceProofDecoding.truthCode
  exact propext (ZFSetHOLTypeInterpretation.holds_truth _)

/-- Decoding implication is literal equality of dependent trace families. -/
theorem implication_decoder {a : ZFSet.{u}} {Gamma : Type (u + 1)}
    (premise conclusion : Gamma →
      ZFSetUniformListTraceTypeInterpretation.Value a .prop) :
    proofFamily (a := a) (fun environment => ZFSetHOLTypeInterpretation.truth
        (ZFSetHOLTypeInterpretation.holds (premise environment) →
          ZFSetHOLTypeInterpretation.holds (conclusion environment))) =
      ZFSetTraceContextual.piFamily (proofFamily premise)
        (proofFamily (fun point : Extension (proofFamily premise) => conclusion point.1)) := by
  rw [proofFamily_truth]
  exact ZFSetTraceProofDecoding.implication_decoder _ _

/-- Decoding universal quantification is literal equality of dependent trace
families over the interpreted object domain. -/
theorem universal_decoder {a : ZFSet.{u}} {Gamma : Type (u + 1)}
    (domain : SetFamily Gamma)
    (body : Extension domain → ZFSetUniformListTraceTypeInterpretation.Value a .prop) :
    proofFamily (a := a) (fun environment => ZFSetHOLTypeInterpretation.truth
        (∀ argument : Elements (domain environment),
          ZFSetHOLTypeInterpretation.holds (body ⟨environment, argument⟩))) =
      ZFSetTraceContextual.piFamily domain (proofFamily body) := by
  rw [proofFamily_truth]
  change ZFSetTraceProofDecoding.truthFamily
      (fun environment => ∀ argument : Elements (domain environment),
        ZFSetHOLTypeInterpretation.holds (body ⟨environment, argument⟩)) =
    ZFSetTraceContextual.piFamily domain
      (ZFSetTraceProofDecoding.truthFamily
        (fun point => ZFSetHOLTypeInterpretation.holds (body point)))
  exact ZFSetTraceProofDecoding.forall_decoder domain
    (fun point : Extension domain => ZFSetHOLTypeInterpretation.holds (body point))

namespace Controls

theorem object_nil_is_mixed (a : ZFSet.{u}) :
    Denotes a NativeHOLTraceDisplayedTerms.Controls.emptyContext
      (.const (FormationSensitiveHOLUniformList.symbolName Symbol.nil))
      (NativeHOLTraceDisplayedTerms.typeFamily a
        NativeHOLTraceDisplayedTerms.Controls.emptyContext sequence)
      (fun _ => ZFSetUniformListTraceTypeInterpretation.constant a Symbol.nil) :=
  .object (NativeHOLTraceDisplayedTerms.Controls.nil_constant_denotes a)

theorem false_proof_family_empty :
    proofFamily (a := (∅ : ZFSet.{u}))
      (fun _ : PUnit => ZFSetHOLTypeInterpretation.truth False) = fun _ => ∅ := by
  funext environment
  apply ZFSet.ext
  intro value
  rw [show proofFamily (a := (∅ : ZFSet.{u}))
    (fun _ : PUnit => ZFSetHOLTypeInterpretation.truth False) environment =
      ZFSetTraceProofDecoding.truthCode False by
        apply congrArg ZFSetTraceProofDecoding.truthCode
        exact propext (ZFSetHOLTypeInterpretation.holds_truth False)]
  simp only [ZFSetTraceProofDecoding.mem_truthCode, and_false, ZFSet.notMem_empty]

end Controls

#print axioms Denotes.cast_family
#print axioms Denotes.change_value
#print axioms Denotes.rename
#print axioms Denotes.weaken
#print axioms proofFamily_truth
#print axioms implication_decoder
#print axioms universal_decoder
#print axioms Controls.object_nil_is_mixed
#print axioms Controls.false_proof_family_empty

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceMixedTermSemantics
