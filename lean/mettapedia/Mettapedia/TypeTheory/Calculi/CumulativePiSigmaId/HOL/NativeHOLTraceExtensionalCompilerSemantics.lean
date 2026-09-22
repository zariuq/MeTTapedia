import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizNativeExtensionalProofTranslation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceExtensionalRuleSemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceLeibnizCompilerSemantics

/-!
# Trace semantics of the qualified extensional HOL attachments

This module relates the exact native applications emitted for source
propositional and function extensionality to the canonical Aczel-trace proof
sections.  It deliberately qualifies the semantic judgment to fully applied
compiled rule nodes.  The existing mixed-term semantics remains the meaning
of the constructive fragment; no interpretation of arbitrary partial
applications of the extensional constants is claimed here.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceExtensionalCompilerSemantics

open Presentation Mettapedia.Logic HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open ZFSetContextualInterpretation (Section)
open ZFSetUniformListTraceTypeInterpretation
open NativeTraceLambdaSemantics
open NativeHOLTraceLeibnizProofSemantics
open NativeHOLTraceLeibnizCompilerSemantics
open HOLLeibnizNativeExtensionalProofTranslation

universe u

abbrev SourceContext := HOLLeibnizNativeProofTranslation.SourceContext
abbrev Formula := HOLLeibnizNativeProofTranslation.Formula
abbrev Valuation := NativeHOLTraceLeibnizCompilerSemantics.Valuation

/-- A retained proof section witnesses the proposition at every environment. -/
theorem proofDenotes_valid {a : ZFSet.{u}} {n : Nat}
    {context : Context.{u} n} {term : Tower.Tm n}
    {proposition : context.Environment → Prop}
    (meaning : ProofDenotes a context term proposition) :
    ∀ environment, proposition environment := by
  obtain ⟨value, _⟩ := meaning
  intro environment
  exact (ZFSetTraceProofDecoding.mem_truthCode
    (proposition environment) (value environment).1).mp
      (value environment).2 |>.2

/-- Exact denotation of a compiled extensional root.  The result value in each
new constructor is the literal canonical section from the trace rule model. -/
inductive RootDenotes (a : ZFSet.{u}) :
    {n : Nat} → (context : Context.{u} n) → (term : Tower.Tm n) →
      (proposition : context.Environment → Prop) →
      Section (ZFSetTraceProofDecoding.truthFamily proposition) → Prop where
  | constructive {n : Nat} {context : Context.{u} n} {term : Tower.Tm n}
      {proposition : context.Environment → Prop}
      {value : Section (ZFSetTraceProofDecoding.truthFamily proposition)} :
      NativeHOLTraceMixedTermSemantics.Denotes a context term
        (ZFSetTraceProofDecoding.truthFamily proposition) value →
      RootDenotes a context term proposition value
  | propositionExtensionality {n : Nat} {context : Context.{u} n}
      {leftTerm rightTerm forwardTerm backwardTerm : Tower.Tm n}
      {left right : context.Environment → Value a .prop}
      (leftMeaning : NativeHOLTraceDisplayedTerms.Denotes a context leftTerm left)
      (rightMeaning : NativeHOLTraceDisplayedTerms.Denotes a context rightTerm right)
      (forwardMeaning : ProofDenotes a context forwardTerm
        (fun environment => ZFSetHOLTypeInterpretation.holds (left environment) →
          ZFSetHOLTypeInterpretation.holds (right environment)))
      (backwardMeaning : ProofDenotes a context backwardTerm
        (fun environment => ZFSetHOLTypeInterpretation.holds (right environment) →
          ZFSetHOLTypeInterpretation.holds (left environment))) :
      RootDenotes a context
        (FormationSensitiveHOLExtensionalApplications.propositionExtensionalityApp
          leftTerm rightTerm forwardTerm backwardTerm)
        (equalityProposition left right)
        (NativeHOLTraceExtensionalRuleSemantics.propositionExtensionalitySection
          left right (proofDenotes_valid forwardMeaning)
          (proofDenotes_valid backwardMeaning))
  | functionExtensionality {n : Nat} {context : Context.{u} n}
      {domain codomain : HOL.Ty BaseSort}
      {leftTerm rightTerm pointwiseTerm : Tower.Tm n}
      {left right : context.Environment → Value a (.arr domain codomain)}
      (leftMeaning : NativeHOLTraceDisplayedTerms.Denotes a context leftTerm left)
      (rightMeaning : NativeHOLTraceDisplayedTerms.Denotes a context rightTerm right)
      (pointwiseMeaning : ProofDenotes a context pointwiseTerm
        (fun environment => ∀ argument : Value a domain,
          app (left environment) argument = app (right environment) argument)) :
      RootDenotes a context
        (FormationSensitiveHOLExtensionalApplications.functionExtensionalityApp
          (FormationSensitiveHOLInterface.typeAt
            FormationSensitiveHOLUniformList.types n domain)
          (FormationSensitiveHOLInterface.typeAt
            FormationSensitiveHOLUniformList.types n codomain)
          leftTerm rightTerm pointwiseTerm)
        (equalityProposition left right)
        (NativeHOLTraceExtensionalRuleSemantics.functionExtensionalitySection
          left right (proofDenotes_valid pointwiseMeaning))

/-- A term has a qualified extensional-root meaning when it retains an actual
section of the exact source proposition's canonical truth family. -/
def ProofDenotesRoot {a : ZFSet.{u}} {n : Nat} (context : Context.{u} n)
    (term : Tower.Tm n) (proposition : context.Environment → Prop) : Prop :=
  ∃ value, RootDenotes a context term proposition value

/-- The retained HOL universal premise of function extensionality means
pointwise equality over every element of the actual Aczel trace domain. -/
theorem formulaMeaning_pointwiseFormula {a : ZFSet.{u}}
    {gamma : SourceContext} {domain codomain : HOL.Ty BaseSort}
    (function other : HOL.Term Symbol gamma (.arr domain codomain))
    {n : Nat} (context : Context.{u} n)
    (valuation : context.Environment → Valuation a gamma) :
    formulaMeaning (pointwiseFormula function other) context valuation =
      fun environment => ∀ argument : Value a domain,
        app (ZFSetUniformListTraceTermInterpretation.interpret function
              (valuation environment)) argument =
          app (ZFSetUniformListTraceTermInterpretation.interpret other
              (valuation environment)) argument := by
  funext environment
  apply propext
  simp [pointwiseFormula, formulaMeaning,
    ZFSetUniformListTraceTermInterpretation.interpret,
    ZFSetUniformListTraceTermInterpretation.extend, interpret_weaken]

/-- The proposition-extensionality attachment commutes with the source trace
meaning.  Both compiled constructive premises are the actual source proofs. -/
theorem compilePropositionExtensionality_denotes
    {a : ZFSet.{u}} {gamma : SourceContext}
    {delta : List (Formula gamma)} {left right : Formula gamma}
    (forward : HOL.ProofSyntax Symbol delta (.imp left right))
    (backward : HOL.ProofSyntax Symbol delta (.imp right left))
    {n : Nat} {context : Context.{u} n}
    {objects : Sub Tower.Head gamma.length n}
    {valuation : context.Environment → Valuation a gamma}
    {hypotheses : Fin delta.length → Tower.Tm n} {native : Tower.Tm n}
    (objectsMeaning : ObjectsDenote context objects valuation)
    (hypothesesMeaning : HypothesesDenote context valuation hypotheses)
    (success : compilePropositionExtensionality forward backward objects hypotheses =
      some native) :
    ProofDenotesRoot (a := a) context native
      (formulaMeaning (.eq left right) context valuation) := by
  cases hl : HOLLeibnizNativeProofTranslation.represent left with
  | none => simp [compilePropositionExtensionality, hl] at success
  | some leftCode =>
      cases hr : HOLLeibnizNativeProofTranslation.represent right with
      | none => simp [compilePropositionExtensionality, hl, hr] at success
      | some rightCode =>
          cases hf : HOLLeibnizNativeProofTranslation.compile forward objects hypotheses with
          | none => simp [compilePropositionExtensionality, hl, hr, hf] at success
          | some forwardCode =>
              cases hb : HOLLeibnizNativeProofTranslation.compile backward objects hypotheses with
              | none =>
                  simp [compilePropositionExtensionality, hl, hr, hf, hb] at success
              | some backwardCode =>
                  simp [compilePropositionExtensionality, hl, hr, hf, hb] at success
                  subst native
                  let leftValue := fun environment =>
                    ZFSetUniformListTraceTermInterpretation.interpret left
                      (valuation environment)
                  let rightValue := fun environment =>
                    ZFSetUniformListTraceTermInterpretation.interpret right
                      (valuation environment)
                  have leftMeaning := represented_denotes left hl context objects
                    valuation objectsMeaning
                  have rightMeaning := represented_denotes right hr context objects
                    valuation objectsMeaning
                  have forwardMeaning :=
                    compile_denotes forward objectsMeaning hypothesesMeaning hf
                  have backwardMeaning :=
                    compile_denotes backward objectsMeaning hypothesesMeaning hb
                  have forwardDecoded : ProofDenotes a context forwardCode
                      (fun environment =>
                        ZFSetHOLTypeInterpretation.holds (leftValue environment) →
                          ZFSetHOLTypeInterpretation.holds
                            (rightValue environment)) :=
                    forwardMeaning.cast_proposition
                      (formulaMeaning_imp left right context valuation)
                  have backwardDecoded : ProofDenotes a context backwardCode
                      (fun environment =>
                        ZFSetHOLTypeInterpretation.holds (rightValue environment) →
                          ZFSetHOLTypeInterpretation.holds
                            (leftValue environment)) :=
                    backwardMeaning.cast_proposition
                      (formulaMeaning_imp right left context valuation)
                  rw [formulaMeaning_eq left right context valuation]
                  exact ⟨_, RootDenotes.propositionExtensionality
                    (left := leftValue) (right := rightValue)
                    leftMeaning rightMeaning forwardDecoded backwardDecoded⟩

/-- The function-extensionality attachment also commutes literally.  The
compiled universal premise supplies equality at every trace argument, and the
result is the canonical section obtained from equality of the Aczel traces. -/
theorem compileFunctionExtensionality_denotes
    {a : ZFSet.{u}} {gamma : SourceContext}
    {delta : List (Formula gamma)} {domain codomain : HOL.Ty BaseSort}
    {function other : HOL.Term Symbol gamma (.arr domain codomain)}
    (pointwise : HOL.ProofSyntax Symbol delta
      (pointwiseFormula function other))
    {n : Nat} {context : Context.{u} n}
    {objects : Sub Tower.Head gamma.length n}
    {valuation : context.Environment → Valuation a gamma}
    {hypotheses : Fin delta.length → Tower.Tm n} {native : Tower.Tm n}
    (objectsMeaning : ObjectsDenote context objects valuation)
    (hypothesesMeaning : HypothesesDenote context valuation hypotheses)
    (success : compileFunctionExtensionality pointwise objects hypotheses =
      some native) :
    ProofDenotesRoot (a := a) context native
      (formulaMeaning (.eq function other) context valuation) := by
  cases hf : HOLLeibnizNativeProofTranslation.represent function with
  | none => simp [compileFunctionExtensionality, hf] at success
  | some functionCode =>
      cases hg : HOLLeibnizNativeProofTranslation.represent other with
      | none => simp [compileFunctionExtensionality, hf, hg] at success
      | some otherCode =>
          cases hp : HOLLeibnizNativeProofTranslation.compile pointwise
              objects hypotheses with
          | none => simp [compileFunctionExtensionality, hf, hg, hp] at success
          | some pointwiseCode =>
              simp [compileFunctionExtensionality, hf, hg, hp] at success
              subst native
              let functionValue := fun environment =>
                ZFSetUniformListTraceTermInterpretation.interpret function
                  (valuation environment)
              let otherValue := fun environment =>
                ZFSetUniformListTraceTermInterpretation.interpret other
                  (valuation environment)
              have functionMeaning := represented_denotes function hf context objects
                valuation objectsMeaning
              have otherMeaning := represented_denotes other hg context objects
                valuation objectsMeaning
              have pointwiseMeaning :=
                compile_denotes pointwise objectsMeaning hypothesesMeaning hp
              have pointwiseDecoded : ProofDenotes a context pointwiseCode
                  (fun environment => ∀ argument : Value a domain,
                    app (functionValue environment) argument =
                      app (otherValue environment) argument) :=
                pointwiseMeaning.cast_proposition
                  (formulaMeaning_pointwiseFormula function other context valuation)
              rw [formulaMeaning_eq function other context valuation]
              exact ⟨_, RootDenotes.functionExtensionality
                (left := functionValue) (right := otherValue)
                functionMeaning otherMeaning pointwiseDecoded⟩

#print axioms proofDenotes_valid
#print axioms formulaMeaning_pointwiseFormula
#print axioms compilePropositionExtensionality_denotes
#print axioms compileFunctionExtensionality_denotes

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceExtensionalCompilerSemantics
