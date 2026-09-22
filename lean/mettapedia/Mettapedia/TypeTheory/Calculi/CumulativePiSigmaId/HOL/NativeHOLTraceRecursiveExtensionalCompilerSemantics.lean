import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizNativeRecursiveExtensionalCompiler
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceQualifiedExtensionalSemantics

/-!
# Trace correctness of recursive qualified HOL compilation

This module closes the compiler/semantics square over the advertised recursive
fragment.  Source premises are compiled by the same compiler at every depth,
and their exact output terms inhabit the compositional qualified trace
judgment.  In particular, an extensional proof may occur below implication,
quantification, equality transport, or another extensional rule.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceRecursiveExtensionalCompilerSemantics

open Presentation Mettapedia.Logic HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (Elements)
open ZFSetContextualInterpretation (SetFamily)
open ZFSetUniformListTraceTypeInterpretation
open NativeTraceLambdaSemantics
open HOLLeibnizNativeRecursiveExtensionalCompiler

universe u

abbrev SourceContext := HOLLeibnizNativeProofTranslation.SourceContext
abbrev Formula := HOLLeibnizNativeProofTranslation.Formula
abbrev Valuation (a : ZFSet.{u}) (gamma : SourceContext) :=
  NativeHOLTraceLeibnizCompilerSemantics.Valuation a gamma

abbrev formulaMeaning {a : ZFSet.{u}} {gamma : SourceContext}
    (formula : Formula gamma) {n : Nat} (context : Context.{u} n)
    (valuation : context.Environment → Valuation a gamma) :
    context.Environment → Prop :=
  NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning
    formula context valuation

abbrev ObjectsDenote {a : ZFSet.{u}} {gamma : SourceContext} {n : Nat}
    (context : Context.{u} n) (objects : Sub Tower.Head gamma.length n)
    (valuation : context.Environment → Valuation a gamma) : Prop :=
  NativeHOLTraceLeibnizCompilerSemantics.ObjectsDenote
    context objects valuation

abbrev ProofDenotes (a : ZFSet.{u}) {n : Nat} (context : Context.{u} n)
    (term : Tower.Tm n) (proposition : context.Environment → Prop) : Prop :=
  NativeHOLTraceQualifiedExtensionalSemantics.ProofDenotes
    a context term proposition

/-- Every supplied proof variable already has the qualified meaning needed by
recursive compilation.  Constructive proof variables embed through
`Qualified.ProofDenotes.ofMixed`. -/
def HypothesesDenote {a : ZFSet.{u}} {gamma : SourceContext}
    {delta : List (Formula gamma)} {n : Nat} (context : Context.{u} n)
    (valuation : context.Environment → Valuation a gamma)
    (hypotheses : Fin delta.length → Tower.Tm n) : Prop :=
  ∀ index, ProofDenotes a context (hypotheses index)
    (formulaMeaning (delta.get index) context valuation)

theorem HypothesesDenote.ofConstructive {a : ZFSet.{u}}
    {gamma : SourceContext} {delta : List (Formula gamma)}
    {n : Nat} {context : Context.{u} n}
    {valuation : context.Environment → Valuation a gamma}
    {hypotheses : Fin delta.length → Tower.Tm n}
    (meaning : NativeHOLTraceLeibnizCompilerSemantics.HypothesesDenote
      context valuation hypotheses) :
    HypothesesDenote context valuation hypotheses := by
  intro index
  exact NativeHOLTraceQualifiedExtensionalSemantics.ProofDenotes.ofMixed
    (meaning index)

theorem HypothesesDenote.prepend {a : ZFSet.{u}} {gamma : SourceContext}
    {delta : List (Formula gamma)} {n : Nat} {context : Context.{u} n}
    {valuation : context.Environment → Valuation a gamma}
    {hypotheses : Fin delta.length → Tower.Tm n}
    (meaning : HypothesesDenote context valuation hypotheses)
    (premise : Formula gamma) :
    let premiseMeaning := formulaMeaning premise context valuation
    let family := ZFSetTraceProofDecoding.truthFamily premiseMeaning
    HypothesesDenote (delta := premise :: delta) (context.snoc family)
      (fun point => valuation point.1)
      (Fin.cases (.var 0)
        (fun index => Presentation.rename wk (hypotheses index))) := by
  dsimp only
  intro index
  refine Fin.cases ?_ (fun prior => ?_) index
  · exact NativeHOLTraceQualifiedExtensionalSemantics.proofVariableZero
      (formulaMeaning premise context valuation)
  · exact (meaning prior).weaken
      (ZFSetTraceProofDecoding.truthFamily
        (formulaMeaning premise context valuation))

theorem HypothesesDenote.lift {a : ZFSet.{u}} {gamma : SourceContext}
    {delta : List (Formula gamma)} {n : Nat} {context : Context.{u} n}
    {valuation : context.Environment → Valuation a gamma}
    {hypotheses : Fin delta.length → Tower.Tm n}
    (meaning : HypothesesDenote context valuation hypotheses)
    (type : HOL.Ty BaseSort) :
    let family := NativeHOLTraceDisplayedTerms.typeFamily a context type
    HypothesesDenote (delta := HOL.weakenHyps (σ := type) delta)
      (context.snoc family)
      (fun point => ZFSetUniformListTraceTermInterpretation.extend
        (valuation point.1) point.2)
      (fun index => Presentation.rename wk
        (hypotheses (index.cast (by simp [HOL.weakenHyps])))) := by
  dsimp only
  intro index
  let prior : Fin delta.length := index.cast (by simp [HOL.weakenHyps])
  have weakened := (meaning prior).weaken
    (NativeHOLTraceDisplayedTerms.typeFamily a context type)
  apply NativeHOLTraceQualifiedExtensionalSemantics.ProofDenotes.cast_proposition
    weakened
  have entry : (HOL.weakenHyps (σ := type) delta).get index =
      HOL.weaken (delta.get prior) := by
    have indexValid : index.val < delta.length := by
      simpa [HOL.weakenHyps] using index.isLt
    change (delta.map (HOL.weaken (σ := type)))[index.val] =
      HOL.weaken delta[index.val]
    simp only [List.getElem_map]
  funext point
  unfold formulaMeaning NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning
  rw [entry, NativeHOLTraceLeibnizCompilerSemantics.interpret_weaken]

/-- A represented source body, inserted under the lifted object environment
and abstracted, denotes the source lambda itself. -/
theorem representedLambda_denotes {a : ZFSet.{u}} {gamma : SourceContext}
    {domain codomain : HOL.Ty BaseSort}
    (body : HOL.Term Symbol (domain :: gamma) codomain)
    {bodyCode : Tower.Tm (domain :: gamma).length}
    (represented : HOLLeibnizNativeProofTranslation.represent body = some bodyCode)
    {n : Nat} (context : Context.{u} n)
    (objects : Sub Tower.Head gamma.length n)
    (valuation : context.Environment → Valuation a gamma)
    (objectsMeaning : ObjectsDenote context objects valuation) :
    NativeHOLTraceDisplayedTerms.Denotes a context
      (.lam (subst (liftSub objects) bodyCode))
      (fun environment =>
        ZFSetUniformListTraceTermInterpretation.interpret (.lam body)
          (valuation environment)) := by
  let family := NativeHOLTraceDisplayedTerms.typeFamily a context domain
  have bodyMeaning := NativeHOLTraceLeibnizCompilerSemantics.represented_denotes
    body represented (context.snoc family) (liftSub objects)
    (fun point => ZFSetUniformListTraceTermInterpretation.extend
      (valuation point.1) point.2)
    (objectsMeaning.lift domain)
  simpa [ZFSetUniformListTraceTermInterpretation.interpret] using
    (NativeHOLTraceDisplayedTerms.Denotes.abstraction bodyMeaning)

/-- The exact native eta expansion denotes the source eta expansion. -/
theorem etaExpansion_denotes {a : ZFSet.{u}} {gamma : SourceContext}
    {domain codomain : HOL.Ty BaseSort}
    (function : HOL.Term Symbol gamma (.arr domain codomain))
    {functionCode : Tower.Tm gamma.length}
    (represented : HOLLeibnizNativeProofTranslation.represent function =
      some functionCode)
    {n : Nat} (context : Context.{u} n)
    (objects : Sub Tower.Head gamma.length n)
    (valuation : context.Environment → Valuation a gamma)
    (objectsMeaning : ObjectsDenote context objects valuation) :
    NativeHOLTraceDisplayedTerms.Denotes a context
      (.lam (.app (Presentation.rename wk (subst objects functionCode)) (.var 0)))
      (fun environment =>
        ZFSetUniformListTraceTermInterpretation.interpret
          (.lam (.app (HOL.weaken function) (.var .vz)))
          (valuation environment)) := by
  let family := NativeHOLTraceDisplayedTerms.typeFamily a context domain
  have functionMeaning := NativeHOLTraceLeibnizCompilerSemantics.represented_denotes
    function represented context objects valuation objectsMeaning
  have argumentMeaning : NativeHOLTraceDisplayedTerms.Denotes a
      (context.snoc family) (.var 0) (fun point => point.2) :=
    .variable 0 (NativeTraceLambdaSemantics.Denotes.var _ 0)
  have applicationMeaning := NativeHOLTraceDisplayedTerms.Denotes.application
    (functionMeaning.weaken family) argumentMeaning
  have abstracted := NativeHOLTraceDisplayedTerms.Denotes.abstraction
    applicationMeaning
  apply NativeHOLTraceDisplayedTerms.Denotes.change_value abstracted
  funext environment
  apply congrArg ZFSetUniformListTraceTypeInterpretation.lam
  funext argument
  change app
      (ZFSetUniformListTraceTermInterpretation.interpret function
        (valuation environment)) argument =
    app (ZFSetUniformListTraceTermInterpretation.interpret
      (HOL.weaken function)
      (ZFSetUniformListTraceTermInterpretation.extend
        (valuation environment) argument)) argument
  rw [NativeHOLTraceLeibnizCompilerSemantics.interpret_weaken]

/-- Every successful recursive compiler result retains the canonical trace
section of its exact source conclusion. -/
theorem compile_denotes {a : ZFSet.{u}} {gamma : SourceContext}
    {delta : List (Formula gamma)} {phi : Formula gamma}
    (source : HOL.ProofSyntax Symbol delta phi)
    {n : Nat} {context : Context.{u} n}
    {objects : Sub Tower.Head gamma.length n}
    {valuation : context.Environment → Valuation a gamma}
    {hypotheses : Fin delta.length → Tower.Tm n} {native : Tower.Tm n}
    (objectsMeaning : ObjectsDenote context objects valuation)
    (hypothesesMeaning : HypothesesDenote context valuation hypotheses)
    (success : compile source objects hypotheses = some native) :
    ProofDenotes a context native (formulaMeaning phi context valuation) := by
  induction source generalizing n with
  | hyp occurrence =>
      simp only [compile, Option.some.injEq] at success
      subst native
      exact hypothesesMeaning occurrence
  | @impI gamma delta premise conclusion body inductionHypothesis =>
      cases premiseRepresentation : HOLLeibnizNativeProofTranslation.represent premise with
      | none => simp [compile, premiseRepresentation] at success
      | some premiseCode =>
          cases bodyCompilation : compile body
              (fun index => Presentation.rename wk (objects index))
              (Fin.cases (.var 0)
                (fun index => Presentation.rename wk (hypotheses index))) with
          | none => simp [compile, premiseRepresentation, bodyCompilation] at success
          | some bodyCode =>
              simp [compile, premiseRepresentation, bodyCompilation] at success
              subst native
              let premiseMeaning := formulaMeaning premise context valuation
              let proofFamily := ZFSetTraceProofDecoding.truthFamily premiseMeaning
              have bodyMeaning := inductionHypothesis
                (context := context.snoc proofFamily)
                (objectsMeaning.weaken proofFamily)
                (hypothesesMeaning.prepend premise) bodyCompilation
              have introduced :=
                NativeHOLTraceQualifiedExtensionalSemantics.implicationIntro premiseMeaning
                (formulaMeaning conclusion context valuation) bodyMeaning
              exact introduced.cast_proposition
                (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_imp
                  premise conclusion context valuation).symm
  | @impE gamma delta premise conclusion function argument functionInduction
      argumentInduction =>
      cases functionCompilation : compile function objects hypotheses with
      | none => simp [compile, functionCompilation] at success
      | some functionCode =>
          cases argumentCompilation : compile argument objects hypotheses with
          | none => simp [compile, functionCompilation, argumentCompilation] at success
          | some argumentCode =>
              simp [compile, functionCompilation, argumentCompilation] at success
              subst native
              have functionMeaning := functionInduction objectsMeaning hypothesesMeaning
                functionCompilation
              have functionDecoded := functionMeaning.cast_proposition
                (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_imp
                  premise conclusion context valuation)
              have argumentMeaning := argumentInduction objectsMeaning hypothesesMeaning
                argumentCompilation
              exact NativeHOLTraceQualifiedExtensionalSemantics.implicationElim
                functionDecoded argumentMeaning
  | @allI gamma delta type body proof inductionHypothesis =>
      cases bodyCompilation : compile proof (liftSub objects)
          (fun index => Presentation.rename wk
            (hypotheses (index.cast (by simp [HOL.weakenHyps])))) with
      | none => simp [compile, bodyCompilation] at success
      | some bodyCode =>
          simp [compile, bodyCompilation] at success
          subst native
          let domain := NativeHOLTraceDisplayedTerms.typeFamily a context type
          have bodyMeaning := inductionHypothesis
            (context := context.snoc domain)
            (objectsMeaning.lift type) (hypothesesMeaning.lift type) bodyCompilation
          have introduced := NativeHOLTraceQualifiedExtensionalSemantics.universalIntro
            domain
            (formulaMeaning body (context.snoc domain)
              (fun point => ZFSetUniformListTraceTermInterpretation.extend
                (valuation point.1) point.2)) bodyMeaning
          exact introduced.cast_proposition
            (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_all
              type body context valuation).symm
  | @allE gamma delta type body term function inductionHypothesis =>
      cases termRepresentation : HOLLeibnizNativeProofTranslation.represent term with
      | none => simp [compile, termRepresentation] at success
      | some termCode =>
          cases functionCompilation : compile function objects hypotheses with
          | none => simp [compile, termRepresentation, functionCompilation] at success
          | some functionCode =>
              simp [compile, termRepresentation, functionCompilation] at success
              subst native
              let domain := NativeHOLTraceDisplayedTerms.typeFamily a context type
              have functionMeaning := inductionHypothesis objectsMeaning hypothesesMeaning
                functionCompilation
              have functionDecoded := functionMeaning.cast_proposition
                (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_all
                  type body context valuation)
              have argumentMeaning :=
                NativeHOLTraceLeibnizCompilerSemantics.represented_denotes
                  term termRepresentation
                context objects valuation objectsMeaning
              have eliminated :=
                NativeHOLTraceQualifiedExtensionalSemantics.universalElim
                  functionDecoded
                (NativeHOLTraceLeibnizProofSemantics.object argumentMeaning)
              exact eliminated.cast_proposition
                (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_instantiate
                  term body context valuation).symm
  | @eqRefl gamma delta type term =>
      cases termRepresentation : HOLLeibnizNativeProofTranslation.represent term with
      | none => simp [compile, termRepresentation] at success
      | some termCode =>
          simp [compile, termRepresentation] at success
          subst native
          have reflexive :=
            NativeHOLTraceQualifiedExtensionalSemantics.reflTerm_denotes (a := a)
            (fun environment => ZFSetUniformListTraceTermInterpretation.interpret term
              (valuation environment))
          exact reflexive.cast_proposition
            (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
              term term context valuation).symm
  | @eqSymm gamma delta type left right comparison inductionHypothesis =>
      cases leftRepresentation : HOLLeibnizNativeProofTranslation.represent left with
      | none => simp [compile, leftRepresentation] at success
      | some leftCode =>
          cases rightRepresentation : HOLLeibnizNativeProofTranslation.represent right with
          | none => simp [compile, leftRepresentation, rightRepresentation] at success
          | some rightCode =>
              cases comparisonCompilation : compile comparison objects hypotheses with
              | none =>
                  simp [compile, leftRepresentation, rightRepresentation,
                    comparisonCompilation] at success
              | some comparisonCode =>
                  simp [compile, leftRepresentation, rightRepresentation,
                    comparisonCompilation] at success
                  subst native
                  have leftMeaning :=
                    NativeHOLTraceLeibnizCompilerSemantics.represented_denotes
                      left leftRepresentation context objects valuation objectsMeaning
                  have comparisonMeaning := inductionHypothesis objectsMeaning
                    hypothesesMeaning comparisonCompilation
                  have comparisonDecoded := comparisonMeaning.cast_proposition
                    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
                      left right context valuation)
                  have symmetric :=
                    NativeHOLTraceQualifiedExtensionalSemantics.symmetry_denotes
                      leftMeaning comparisonDecoded
                  exact symmetric.cast_proposition
                    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
                      right left context valuation).symm
  | @eqTrans gamma delta type left middle right first second firstInduction
      secondInduction =>
      cases leftRepresentation : HOLLeibnizNativeProofTranslation.represent left with
      | none => simp [compile, leftRepresentation] at success
      | some leftCode =>
          cases middleRepresentation : HOLLeibnizNativeProofTranslation.represent middle with
          | none =>
              simp [compile, leftRepresentation, middleRepresentation] at success
          | some middleCode =>
              cases rightRepresentation : HOLLeibnizNativeProofTranslation.represent right with
              | none =>
                  simp [compile, leftRepresentation, middleRepresentation,
                    rightRepresentation] at success
              | some rightCode =>
                  cases firstCompilation : compile first objects hypotheses with
                  | none =>
                      simp [compile, leftRepresentation, middleRepresentation,
                        rightRepresentation, firstCompilation] at success
                  | some firstCode =>
                      cases secondCompilation : compile second objects hypotheses with
                      | none =>
                          simp [compile, leftRepresentation, middleRepresentation,
                            rightRepresentation, firstCompilation,
                            secondCompilation] at success
                      | some secondCode =>
                          simp [compile, leftRepresentation, middleRepresentation,
                            rightRepresentation, firstCompilation,
                            secondCompilation] at success
                          subst native
                          have leftMeaning :=
                            NativeHOLTraceLeibnizCompilerSemantics.represented_denotes
                              left leftRepresentation context objects valuation
                              objectsMeaning
                          have firstMeaning :=
                            (firstInduction objectsMeaning hypothesesMeaning
                              firstCompilation).cast_proposition
                                (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
                                  left middle context valuation)
                          have secondMeaning :=
                            (secondInduction objectsMeaning hypothesesMeaning
                              secondCompilation).cast_proposition
                                (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
                                  middle right context valuation)
                          have transitive :=
                            NativeHOLTraceQualifiedExtensionalSemantics.transitivity_denotes
                              leftMeaning firstMeaning secondMeaning
                          exact transitive.cast_proposition
                            (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
                              left right context valuation).symm
  | @eqPropI gamma delta left right forward backward forwardInduction
      backwardInduction =>
      cases leftRepresentation : HOLLeibnizNativeProofTranslation.represent left with
      | none => simp [compile, leftRepresentation] at success
      | some leftCode =>
          cases rightRepresentation : HOLLeibnizNativeProofTranslation.represent right with
          | none => simp [compile, leftRepresentation, rightRepresentation] at success
          | some rightCode =>
              cases forwardCompilation : compile forward objects hypotheses with
              | none =>
                  simp [compile, leftRepresentation, rightRepresentation,
                    forwardCompilation] at success
              | some forwardCode =>
                  cases backwardCompilation : compile backward objects hypotheses with
                  | none =>
                      simp [compile, leftRepresentation, rightRepresentation,
                        forwardCompilation, backwardCompilation] at success
                  | some backwardCode =>
                      simp [compile, leftRepresentation, rightRepresentation,
                        forwardCompilation, backwardCompilation] at success
                      subst native
                      let leftValue := fun environment =>
                        ZFSetUniformListTraceTermInterpretation.interpret left
                          (valuation environment)
                      let rightValue := fun environment =>
                        ZFSetUniformListTraceTermInterpretation.interpret right
                          (valuation environment)
                      have leftMeaning :=
                        NativeHOLTraceLeibnizCompilerSemantics.represented_denotes
                          left leftRepresentation context objects valuation objectsMeaning
                      have rightMeaning :=
                        NativeHOLTraceLeibnizCompilerSemantics.represented_denotes
                          right rightRepresentation context objects valuation objectsMeaning
                      have forwardMeaning := forwardInduction objectsMeaning
                        hypothesesMeaning forwardCompilation
                      have backwardMeaning := backwardInduction objectsMeaning
                        hypothesesMeaning backwardCompilation
                      have forwardDecoded : ProofDenotes a context forwardCode
                          (fun environment =>
                            ZFSetHOLTypeInterpretation.holds (leftValue environment) →
                              ZFSetHOLTypeInterpretation.holds
                                (rightValue environment)) :=
                        forwardMeaning.cast_proposition
                          (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_imp
                            left right context valuation)
                      have backwardDecoded : ProofDenotes a context backwardCode
                          (fun environment =>
                            ZFSetHOLTypeInterpretation.holds (rightValue environment) →
                              ZFSetHOLTypeInterpretation.holds
                                (leftValue environment)) :=
                        backwardMeaning.cast_proposition
                          (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_imp
                            right left context valuation)
                      have extensional :=
                        NativeHOLTraceQualifiedExtensionalSemantics.propositionExtensionality_denotes
                            (left := leftValue) (right := rightValue)
                            leftMeaning rightMeaning forwardDecoded backwardDecoded
                      exact extensional.cast_proposition
                        (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
                          left right context valuation).symm
  | @eqPropEL gamma delta left right comparison inductionHypothesis =>
      cases leftRepresentation : HOLLeibnizNativeProofTranslation.represent left with
      | none => simp [compile, leftRepresentation] at success
      | some leftCode =>
          cases rightRepresentation : HOLLeibnizNativeProofTranslation.represent right with
          | none => simp [compile, leftRepresentation, rightRepresentation] at success
          | some rightCode =>
              cases comparisonCompilation : compile comparison objects hypotheses with
              | none =>
                  simp [compile, leftRepresentation, rightRepresentation,
                    comparisonCompilation] at success
              | some comparisonCode =>
                  simp [compile, leftRepresentation, rightRepresentation,
                    comparisonCompilation] at success
                  subst native
                  have comparisonMeaning :=
                    (inductionHypothesis objectsMeaning hypothesesMeaning
                      comparisonCompilation).cast_proposition
                        (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
                          left right context valuation)
                  have forward :=
                    NativeHOLTraceQualifiedExtensionalSemantics.propForward_denotes
                      comparisonMeaning
                  exact forward.cast_proposition
                    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_imp
                      left right context valuation).symm
  | @eqPropER gamma delta left right comparison inductionHypothesis =>
      cases leftRepresentation : HOLLeibnizNativeProofTranslation.represent left with
      | none => simp [compile, leftRepresentation] at success
      | some leftCode =>
          cases rightRepresentation : HOLLeibnizNativeProofTranslation.represent right with
          | none => simp [compile, leftRepresentation, rightRepresentation] at success
          | some rightCode =>
              cases comparisonCompilation : compile comparison objects hypotheses with
              | none =>
                  simp [compile, leftRepresentation, rightRepresentation,
                    comparisonCompilation] at success
              | some comparisonCode =>
                  simp [compile, leftRepresentation, rightRepresentation,
                    comparisonCompilation] at success
                  subst native
                  have leftMeaning :=
                    NativeHOLTraceLeibnizCompilerSemantics.represented_denotes
                      left leftRepresentation context objects valuation objectsMeaning
                  have comparisonMeaning :=
                    (inductionHypothesis objectsMeaning hypothesesMeaning
                      comparisonCompilation).cast_proposition
                        (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
                          left right context valuation)
                  have symmetric :=
                    NativeHOLTraceQualifiedExtensionalSemantics.symmetry_denotes
                      leftMeaning comparisonMeaning
                  have backward :=
                    NativeHOLTraceQualifiedExtensionalSemantics.propForward_denotes
                      symmetric
                  exact backward.cast_proposition
                    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_imp
                      right left context valuation).symm
  | @eqApp gamma delta domain result left right argument comparison
      inductionHypothesis =>
      cases leftRepresentation : HOLLeibnizNativeProofTranslation.represent left with
      | none => simp [compile, leftRepresentation] at success
      | some leftCode =>
          cases rightRepresentation : HOLLeibnizNativeProofTranslation.represent right with
          | none => simp [compile, leftRepresentation, rightRepresentation] at success
          | some rightCode =>
              cases argumentRepresentation :
                  HOLLeibnizNativeProofTranslation.represent argument with
              | none =>
                  simp [compile, leftRepresentation, rightRepresentation,
                    argumentRepresentation] at success
              | some argumentCode =>
                  cases comparisonCompilation : compile comparison objects hypotheses with
                  | none =>
                      simp [compile, leftRepresentation, rightRepresentation,
                        argumentRepresentation, comparisonCompilation] at success
                  | some comparisonCode =>
                      simp [compile, leftRepresentation, rightRepresentation,
                        argumentRepresentation, comparisonCompilation] at success
                      subst native
                      have leftMeaning :=
                        NativeHOLTraceLeibnizCompilerSemantics.represented_denotes
                          left leftRepresentation context objects valuation objectsMeaning
                      have argumentMeaning :=
                        NativeHOLTraceLeibnizCompilerSemantics.represented_denotes
                          argument argumentRepresentation context objects valuation
                          objectsMeaning
                      have comparisonMeaning :=
                        (inductionHypothesis objectsMeaning hypothesesMeaning
                          comparisonCompilation).cast_proposition
                            (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
                              left right context valuation)
                      have congruent :=
                        NativeHOLTraceQualifiedExtensionalSemantics.functionCongruence_denotes
                            leftMeaning argumentMeaning comparisonMeaning
                      exact congruent.cast_proposition
                        (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
                          (.app left argument) (.app right argument)
                          context valuation).symm
  | @eqAppArg gamma delta domain result function left right comparison
      inductionHypothesis =>
      cases functionRepresentation :
          HOLLeibnizNativeProofTranslation.represent function with
      | none => simp [compile, functionRepresentation] at success
      | some functionCode =>
          cases leftRepresentation : HOLLeibnizNativeProofTranslation.represent left with
          | none =>
              simp [compile, functionRepresentation, leftRepresentation] at success
          | some leftCode =>
              cases rightRepresentation : HOLLeibnizNativeProofTranslation.represent right with
              | none =>
                  simp [compile, functionRepresentation, leftRepresentation,
                    rightRepresentation] at success
              | some rightCode =>
                  cases comparisonCompilation : compile comparison objects hypotheses with
                  | none =>
                      simp [compile, functionRepresentation, leftRepresentation,
                        rightRepresentation, comparisonCompilation] at success
                  | some comparisonCode =>
                      simp [compile, functionRepresentation, leftRepresentation,
                        rightRepresentation, comparisonCompilation] at success
                      subst native
                      have functionMeaning :=
                        NativeHOLTraceLeibnizCompilerSemantics.represented_denotes
                          function functionRepresentation context objects valuation
                          objectsMeaning
                      have leftMeaning :=
                        NativeHOLTraceLeibnizCompilerSemantics.represented_denotes
                          left leftRepresentation context objects valuation objectsMeaning
                      have comparisonMeaning :=
                        (inductionHypothesis objectsMeaning hypothesesMeaning
                          comparisonCompilation).cast_proposition
                            (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
                              left right context valuation)
                      have congruent :=
                        NativeHOLTraceQualifiedExtensionalSemantics.congruence_denotes
                          functionMeaning leftMeaning comparisonMeaning
                      exact congruent.cast_proposition
                        (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
                          (.app function left) (.app function right)
                          context valuation).symm
  | @eqLam gamma delta domain codomain left right comparison
      inductionHypothesis =>
      cases leftRepresentation : HOLLeibnizNativeProofTranslation.represent left with
      | none => simp [compile, leftRepresentation] at success
      | some leftCode =>
          cases rightRepresentation : HOLLeibnizNativeProofTranslation.represent right with
          | none => simp [compile, leftRepresentation, rightRepresentation] at success
          | some rightCode =>
              cases comparisonCompilation : compile comparison (liftSub objects)
                  (fun index => Presentation.rename wk
                    (hypotheses (index.cast (by simp [HOL.weakenHyps])))) with
              | none =>
                  simp [compile, leftRepresentation, rightRepresentation,
                    comparisonCompilation] at success
              | some comparisonCode =>
                  simp [compile, leftRepresentation, rightRepresentation,
                    comparisonCompilation] at success
                  subst native
                  let domainFamily :=
                    NativeHOLTraceDisplayedTerms.typeFamily a context domain
                  let extendedValuation :
                      (context.snoc domainFamily).Environment →
                        Valuation a (domain :: gamma) :=
                    fun point => ZFSetUniformListTraceTermInterpretation.extend
                      (valuation point.1) point.2
                  let leftBodyValue : (context.snoc domainFamily).Environment →
                      Value a codomain :=
                    fun point => ZFSetUniformListTraceTermInterpretation.interpret
                      left (extendedValuation point)
                  let rightBodyValue : (context.snoc domainFamily).Environment →
                      Value a codomain :=
                    fun point => ZFSetUniformListTraceTermInterpretation.interpret
                      right (extendedValuation point)
                  let leftFunctionValue : context.Environment →
                      Value a (.arr domain codomain) :=
                    fun environment => ZFSetUniformListTraceTermInterpretation.interpret
                      (.lam left) (valuation environment)
                  let rightFunctionValue : context.Environment →
                      Value a (.arr domain codomain) :=
                    fun environment => ZFSetUniformListTraceTermInterpretation.interpret
                      (.lam right) (valuation environment)
                  have leftMeaning := representedLambda_denotes left
                    leftRepresentation context objects valuation objectsMeaning
                  have rightMeaning := representedLambda_denotes right
                    rightRepresentation context objects valuation objectsMeaning
                  have comparisonMeaning := inductionHypothesis
                    (context := context.snoc domainFamily)
                    (objectsMeaning.lift domain)
                    (hypothesesMeaning.lift domain) comparisonCompilation
                  have comparisonDecoded : ProofDenotes a
                      (context.snoc domainFamily) comparisonCode
                      (NativeHOLTraceLeibnizProofSemantics.equalityProposition
                        leftBodyValue rightBodyValue) :=
                    comparisonMeaning.cast_proposition
                      (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
                        left right (context.snoc domainFamily) extendedValuation)
                  have introduced :=
                    NativeHOLTraceQualifiedExtensionalSemantics.universalIntro
                      domainFamily
                      (NativeHOLTraceLeibnizProofSemantics.equalityProposition
                        leftBodyValue rightBodyValue)
                      comparisonDecoded
                  have pointwiseDecoded : ProofDenotes a context
                      (.lam comparisonCode)
                      (fun environment => ∀ argument : Value a domain,
                        app (leftFunctionValue environment) argument =
                          app (rightFunctionValue environment) argument) := by
                    apply introduced.cast_proposition
                    funext environment
                    apply propext
                    simp [leftFunctionValue, rightFunctionValue, leftBodyValue,
                      rightBodyValue, extendedValuation, domainFamily,
                      NativeHOLTraceDisplayedTerms.typeFamily,
                      NativeHOLTraceLeibnizProofSemantics.equalityProposition,
                      ZFSetUniformListTraceTermInterpretation.interpret]
                  have extensional :=
                    NativeHOLTraceQualifiedExtensionalSemantics.functionExtensionality_denotes
                      (FormationSensitiveHOLInterface.typeAt
                        FormationSensitiveHOLUniformList.types n domain)
                      (FormationSensitiveHOLInterface.typeAt
                        FormationSensitiveHOLUniformList.types n codomain)
                      (left := leftFunctionValue) (right := rightFunctionValue)
                      leftMeaning rightMeaning pointwiseDecoded
                  exact extensional.cast_proposition
                    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
                      (.lam left) (.lam right) context valuation).symm
  | @funExt gamma delta domain codomain function other pointwise
      inductionHypothesis =>
      cases functionRepresentation :
          HOLLeibnizNativeProofTranslation.represent function with
      | none => simp [compile, functionRepresentation] at success
      | some functionCode =>
          cases otherRepresentation : HOLLeibnizNativeProofTranslation.represent other with
          | none =>
              simp [compile, functionRepresentation, otherRepresentation] at success
          | some otherCode =>
              cases pointwiseCompilation : compile pointwise objects hypotheses with
              | none =>
                  simp [compile, functionRepresentation, otherRepresentation,
                    pointwiseCompilation] at success
              | some pointwiseCode =>
                  simp [compile, functionRepresentation, otherRepresentation,
                    pointwiseCompilation] at success
                  subst native
                  let functionValue := fun environment =>
                    ZFSetUniformListTraceTermInterpretation.interpret function
                      (valuation environment)
                  let otherValue := fun environment =>
                    ZFSetUniformListTraceTermInterpretation.interpret other
                      (valuation environment)
                  have functionMeaning :=
                    NativeHOLTraceLeibnizCompilerSemantics.represented_denotes
                      function functionRepresentation context objects valuation
                      objectsMeaning
                  have otherMeaning :=
                    NativeHOLTraceLeibnizCompilerSemantics.represented_denotes
                      other otherRepresentation context objects valuation objectsMeaning
                  have pointwiseMeaning := inductionHypothesis objectsMeaning
                    hypothesesMeaning pointwiseCompilation
                  have pointwiseDecoded : ProofDenotes a context pointwiseCode
                      (fun environment => ∀ argument : Value a domain,
                        app (functionValue environment) argument =
                          app (otherValue environment) argument) :=
                    pointwiseMeaning.cast_proposition
                      (NativeHOLTraceExtensionalCompilerSemantics.formulaMeaning_pointwiseFormula
                          function other context valuation)
                  have extensional :=
                    NativeHOLTraceQualifiedExtensionalSemantics.functionExtensionality_denotes
                        (FormationSensitiveHOLInterface.typeAt
                          FormationSensitiveHOLUniformList.types n domain)
                        (FormationSensitiveHOLInterface.typeAt
                          FormationSensitiveHOLUniformList.types n codomain)
                        (left := functionValue) (right := otherValue)
                        functionMeaning otherMeaning pointwiseDecoded
                  exact extensional.cast_proposition
                    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
                      function other context valuation).symm
  | @beta gamma delta domain result argument body =>
      cases argumentRepresentation :
          HOLLeibnizNativeProofTranslation.represent argument with
      | none => simp [compile, argumentRepresentation] at success
      | some argumentCode =>
          cases bodyRepresentation : HOLLeibnizNativeProofTranslation.represent body with
          | none => simp [compile, argumentRepresentation, bodyRepresentation] at success
          | some bodyCode =>
              simp [compile, argumentRepresentation, bodyRepresentation] at success
              subst native
              let leftValue : context.Environment → Value a result :=
                fun environment => ZFSetUniformListTraceTermInterpretation.interpret
                  (.app (.lam body) argument) (valuation environment)
              let rightValue : context.Environment → Value a result :=
                fun environment => ZFSetUniformListTraceTermInterpretation.interpret
                  (HOL.instantiate argument body) (valuation environment)
              have betaEqual : leftValue = rightValue := by
                funext environment
                simp [leftValue, rightValue,
                  ZFSetUniformListTraceTermInterpretation.interpret,
                  NativeHOLTraceLeibnizCompilerSemantics.interpret_instantiate]
              have reflexive :=
                NativeHOLTraceQualifiedExtensionalSemantics.reflTerm_denotes_of_equal
                  (a := a) betaEqual
              exact reflexive.cast_proposition
                (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
                  (.app (.lam body) argument) (HOL.instantiate argument body)
                  context valuation).symm
  | @eta gamma delta domain codomain function =>
      cases functionRepresentation :
          HOLLeibnizNativeProofTranslation.represent function with
      | none => simp [compile, functionRepresentation] at success
      | some functionCode =>
          simp [compile, functionRepresentation] at success
          subst native
          let domainFamily :=
            NativeHOLTraceDisplayedTerms.typeFamily a context domain
          let functionValue : context.Environment →
              Value a (.arr domain codomain) :=
            fun environment => ZFSetUniformListTraceTermInterpretation.interpret
              function (valuation environment)
          let expandedValue : context.Environment →
              Value a (.arr domain codomain) :=
            fun environment => ZFSetUniformListTraceTermInterpretation.interpret
              (.lam (.app (HOL.weaken function) (.var .vz)))
              (valuation environment)
          let applicationValue : (context.snoc domainFamily).Environment →
              Value a codomain :=
            fun point => app (functionValue point.1) point.2
          have functionMeaning :=
            NativeHOLTraceLeibnizCompilerSemantics.represented_denotes
              function functionRepresentation context objects valuation objectsMeaning
          have expandedMeaning := etaExpansion_denotes function
            functionRepresentation context objects valuation objectsMeaning
          have reflexive :=
            NativeHOLTraceQualifiedExtensionalSemantics.reflTerm_denotes
              (a := a) applicationValue
          have introduced :=
            NativeHOLTraceQualifiedExtensionalSemantics.universalIntro
              domainFamily
              (NativeHOLTraceLeibnizProofSemantics.equalityProposition
                applicationValue applicationValue)
              reflexive
          have pointwiseDecoded : ProofDenotes a context
              (.lam FormationSensitiveHOLLeibnizDerived.reflTerm)
              (fun environment => ∀ argument : Value a domain,
                app (expandedValue environment) argument =
                  app (functionValue environment) argument) := by
            apply introduced.cast_proposition
            funext environment
            apply propext
            simp [expandedValue, functionValue, applicationValue, domainFamily,
              NativeHOLTraceDisplayedTerms.typeFamily,
              NativeHOLTraceLeibnizProofSemantics.equalityProposition,
              ZFSetUniformListTraceTermInterpretation.interpret,
              NativeHOLTraceLeibnizCompilerSemantics.interpret_weaken]
            intro value membership
            rfl
          have extensional :=
            NativeHOLTraceQualifiedExtensionalSemantics.functionExtensionality_denotes
              (FormationSensitiveHOLInterface.typeAt
                FormationSensitiveHOLUniformList.types n domain)
              (FormationSensitiveHOLInterface.typeAt
                FormationSensitiveHOLUniformList.types n codomain)
              (left := expandedValue) (right := functionValue)
              expandedMeaning functionMeaning pointwiseDecoded
          exact extensional.cast_proposition
            (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
              (.lam (.app (HOL.weaken function) (.var .vz))) function
              context valuation).symm
  | _ => simp [compile] at success

/-- Closed successful compilation needs no semantic environment assumptions. -/
theorem compile_closed_denotes {a : ZFSet.{u}} {phi : Formula []}
    (source : HOL.ProofSyntax Symbol [] phi) {native : Tower.Tm 0}
    (success : compile source Fin.elim0 Fin.elim0 = some native) :
    ProofDenotes a NativeHOLTraceDisplayedTerms.Controls.emptyContext native
      (formulaMeaning (a := a) phi
        NativeHOLTraceDisplayedTerms.Controls.emptyContext
        (fun _ => ZFSetUniformListTraceTermInterpretation.emptyValuation
          (a := a))) := by
  apply compile_denotes source (success := success)
  · intro type index
    exact Fin.elim0 (FormationSensitiveHOLInterface.variableIndex index)
  · intro index
    exact Fin.elim0 index

namespace Controls

open HOLLeibnizNativeRecursiveExtensionalCompiler.Controls
open HOLLeibnizNativeExtensionalProofTranslation.Controls

theorem nested_function_extensionality_denotes (a : ZFSet.{u}) :
    ∃ native,
      compile symmetricFunctionExtensionality Fin.elim0 Fin.elim0 = some native ∧
      ProofDenotes a NativeHOLTraceDisplayedTerms.Controls.emptyContext native
        (formulaMeaning (a := a)
          (.eq propositionIdentityFunction propositionIdentityFunction)
          NativeHOLTraceDisplayedTerms.Controls.emptyContext
          (fun _ => ZFSetUniformListTraceTermInterpretation.emptyValuation
            (a := a))) := by
  obtain ⟨native, success⟩ := nested_function_extensionality_succeeds
  exact ⟨native, success, compile_closed_denotes symmetricFunctionExtensionality
    success⟩

theorem eta_denotes (a : ZFSet.{u}) :
    ∃ native, compile identityEta Fin.elim0 Fin.elim0 = some native ∧
      ProofDenotes a NativeHOLTraceDisplayedTerms.Controls.emptyContext native
        (formulaMeaning (a := a)
          (.eq
            (.lam (.app (HOL.weaken propositionIdentityFunction) (.var .vz)))
            propositionIdentityFunction)
          NativeHOLTraceDisplayedTerms.Controls.emptyContext
          (fun _ => ZFSetUniformListTraceTermInterpretation.emptyValuation
            (a := a))) := by
  obtain ⟨native, success⟩ := eta_succeeds
  exact ⟨native, success, compile_closed_denotes identityEta success⟩

theorem lambda_congruence_denotes (a : ZFSet.{u}) :
    ∃ native,
      compile reflexiveLambdaCongruence Fin.elim0 Fin.elim0 = some native ∧
      ProofDenotes a NativeHOLTraceDisplayedTerms.Controls.emptyContext native
        (formulaMeaning (a := a)
          (.eq propositionIdentityFunction propositionIdentityFunction)
          NativeHOLTraceDisplayedTerms.Controls.emptyContext
          (fun _ => ZFSetUniformListTraceTermInterpretation.emptyValuation
            (a := a))) := by
  obtain ⟨native, success⟩ := lambda_congruence_succeeds
  exact ⟨native, success,
    compile_closed_denotes reflexiveLambdaCongruence success⟩

end Controls

#print axioms HypothesesDenote.ofConstructive
#print axioms HypothesesDenote.prepend
#print axioms HypothesesDenote.lift
#print axioms compile_denotes
#print axioms compile_closed_denotes
#print axioms Controls.nested_function_extensionality_denotes
#print axioms Controls.eta_denotes
#print axioms Controls.lambda_congruence_denotes

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceRecursiveExtensionalCompilerSemantics
