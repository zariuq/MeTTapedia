import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceLeibnizProofSemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizNativeProofTranslation

/-!
# Trace soundness of the native Leibniz proof compiler

The source proof environment is displayed in an arbitrary mixed dependent
context.  Object variables denote trace values and proof variables denote
retained sections of the corresponding truth families.  Successful compiler
output will therefore acquire the trace proof family of the original source
conclusion, rather than merely a second proof of semantic validity.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceLeibnizCompilerSemantics

open Presentation Mettapedia.Logic HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (Elements)
open ZFSetContextualInterpretation (SetFamily Section)
open ZFSetUniformListTraceTypeInterpretation
open ZFSetUniformListTraceTermInterpretation
open NativeTraceLambdaSemantics
open NativeHOLTraceLeibnizProofSemantics

universe u

abbrev SourceContext := HOL.Ctx BaseSort
abbrev Formula (gamma : SourceContext) := HOL.Formula Symbol gamma
abbrev Valuation (a : ZFSet.{u}) (gamma : SourceContext) :=
  ZFSetUniformListTraceTermInterpretation.Valuation a gamma

def formulaMeaning {a : ZFSet.{u}} {gamma : SourceContext}
    (formula : Formula gamma) {n : Nat} (context : Context.{u} n)
    (valuation : context.Environment → Valuation a gamma) :
    context.Environment → Prop :=
  fun environment => ZFSetHOLTypeInterpretation.holds
    (ZFSetUniformListTraceTermInterpretation.interpret formula
      (valuation environment))

theorem formulaMeaning_imp {a : ZFSet.{u}} {gamma : SourceContext}
    (left right : Formula gamma) {n : Nat} (context : Context.{u} n)
    (valuation : context.Environment → Valuation a gamma) :
    formulaMeaning (.imp left right) context valuation =
      fun environment => formulaMeaning left context valuation environment →
        formulaMeaning right context valuation environment := by
  funext environment
  apply propext
  simp [formulaMeaning, ZFSetUniformListTraceTermInterpretation.interpret]

theorem formulaMeaning_all {a : ZFSet.{u}} {gamma : SourceContext}
    (type : HOL.Ty BaseSort) (body : Formula (type :: gamma))
    {n : Nat} (context : Context.{u} n)
    (valuation : context.Environment → Valuation a gamma) :
    let domain := NativeHOLTraceDisplayedTerms.typeFamily a context type
    formulaMeaning (.all body) context valuation =
      fun environment => ∀ argument : Elements (domain environment),
        formulaMeaning body (context.snoc domain)
          (fun point => ZFSetUniformListTraceTermInterpretation.extend
            (valuation point.1) point.2) ⟨environment, argument⟩ := by
  dsimp only [NativeHOLTraceDisplayedTerms.typeFamily]
  funext environment
  apply propext
  change ZFSetHOLTypeInterpretation.holds
      (ZFSetHOLTypeInterpretation.truth
        (∀ argument : Value a type,
          ZFSetHOLTypeInterpretation.holds
            (ZFSetUniformListTraceTermInterpretation.interpret body
              (ZFSetUniformListTraceTermInterpretation.extend
                (valuation environment) argument)))) ↔
    ∀ argument : Value a type,
      ZFSetHOLTypeInterpretation.holds
        (ZFSetUniformListTraceTermInterpretation.interpret body
          (ZFSetUniformListTraceTermInterpretation.extend
            (valuation environment) argument))
  exact ZFSetHOLTypeInterpretation.holds_truth _

theorem formulaMeaning_eq {a : ZFSet.{u}} {gamma : SourceContext}
    {type : HOL.Ty BaseSort} (left right : HOL.Term Symbol gamma type)
    {n : Nat} (context : Context.{u} n)
    (valuation : context.Environment → Valuation a gamma) :
    formulaMeaning (.eq left right) context valuation =
      equalityProposition
        (fun environment => ZFSetUniformListTraceTermInterpretation.interpret left
          (valuation environment))
        (fun environment => ZFSetUniformListTraceTermInterpretation.interpret right
          (valuation environment)) := by
  funext environment
  apply propext
  simp [formulaMeaning, equalityProposition,
    ZFSetUniformListTraceTermInterpretation.interpret]

/-- Source weakening is literal in the trace interpretation. -/
theorem interpret_weaken {a : ZFSet.{u}} {gamma : SourceContext}
    {type extension : HOL.Ty BaseSort}
    (term : HOL.Term Symbol gamma type) (valuation : Valuation a gamma)
    (value : Value a extension) :
    ZFSetUniformListTraceTermInterpretation.interpret
        (HOL.weaken (σ := extension) term)
        (ZFSetUniformListTraceTermInterpretation.extend valuation value) =
      ZFSetUniformListTraceTermInterpretation.interpret term valuation := by
  apply (ZFSetUniformListTraceTypeInterpretation.decode a type).injective
  rw [ZFSetUniformListTraceTermInterpretation.term_agreement,
    ZFSetUniformListTraceTermInterpretation.term_agreement,
    ZFSetUniformListTraceTermInterpretation.decodeValuation_extend]
  exact HOL.Soundness.denote_weaken (ZFSetUniformListModel.model a)
    term (ZFSetUniformListTraceTermInterpretation.decodeValuation valuation)
    (ZFSetUniformListTraceTypeInterpretation.decode a extension value)

/-- Source single substitution is literal in the trace interpretation. -/
theorem interpret_instantiate {a : ZFSet.{u}} {gamma : SourceContext}
    {domain result : HOL.Ty BaseSort}
    (argument : HOL.Term Symbol gamma domain)
    (body : HOL.Term Symbol (domain :: gamma) result)
    (valuation : Valuation a gamma) :
    ZFSetUniformListTraceTermInterpretation.interpret
        (HOL.instantiate argument body) valuation =
      ZFSetUniformListTraceTermInterpretation.interpret body
        (ZFSetUniformListTraceTermInterpretation.extend valuation
          (ZFSetUniformListTraceTermInterpretation.interpret argument valuation)) := by
  apply (ZFSetUniformListTraceTypeInterpretation.decode a result).injective
  rw [ZFSetUniformListTraceTermInterpretation.term_agreement,
    ZFSetUniformListTraceTermInterpretation.term_agreement,
    ZFSetUniformListTraceTermInterpretation.decodeValuation_extend,
    ZFSetUniformListTraceTermInterpretation.term_agreement]
  exact HOL.Soundness.denote_instantiate_term (ZFSetUniformListModel.model a)
    argument body
    (ZFSetUniformListTraceTermInterpretation.decodeValuation valuation)

theorem formulaMeaning_instantiate {a : ZFSet.{u}} {gamma : SourceContext}
    {domain : HOL.Ty BaseSort} (argument : HOL.Term Symbol gamma domain)
    (body : Formula (domain :: gamma)) {n : Nat} (context : Context.{u} n)
    (valuation : context.Environment → Valuation a gamma) :
    let family := NativeHOLTraceDisplayedTerms.typeFamily a context domain
    formulaMeaning (HOL.instantiate argument body) context valuation =
      fun environment => formulaMeaning body (context.snoc family)
        (fun point => ZFSetUniformListTraceTermInterpretation.extend
          (valuation point.1) point.2)
        ⟨environment, ZFSetUniformListTraceTermInterpretation.interpret argument
          (valuation environment)⟩ := by
  dsimp only [NativeHOLTraceDisplayedTerms.typeFamily]
  funext environment
  unfold formulaMeaning
  rw [interpret_instantiate]

/-- Every supplied native object variable denotes the corresponding component
of one source trace valuation. -/
def ObjectsDenote {a : ZFSet.{u}} {gamma : SourceContext} {n : Nat}
    (context : Context.{u} n) (objects : Sub Tower.Head gamma.length n)
    (valuation : context.Environment → Valuation a gamma) : Prop :=
  ∀ {type : HOL.Ty BaseSort} (index : HOL.Var gamma type),
    NativeHOLTraceDisplayedTerms.Denotes a context
      (objects (FormationSensitiveHOLInterface.variableIndex index))
      (fun environment => valuation environment index)

/-- Every supplied native proof variable retains a section of the source
assumption's trace truth family. -/
def HypothesesDenote {a : ZFSet.{u}} {gamma : SourceContext}
    {delta : List (Formula gamma)} {n : Nat} (context : Context.{u} n)
    (valuation : context.Environment → Valuation a gamma)
    (hypotheses : Fin delta.length → Tower.Tm n) : Prop :=
  ∀ index, ProofDenotes a context (hypotheses index)
    (formulaMeaning (delta.get index) context valuation)

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
      (Fin.cases (.var 0) (fun index => Presentation.rename wk (hypotheses index))) := by
  dsimp only
  intro index
  refine Fin.cases ?_ (fun prior => ?_) index
  · exact proofVariableZero (formulaMeaning premise context valuation)
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
  apply ProofDenotes.cast_proposition weakened
  have entry : (HOL.weakenHyps (σ := type) delta).get index =
      HOL.weaken (delta.get prior) := by
    have indexValid : index.val < delta.length := by
      simpa [HOL.weakenHyps] using index.isLt
    change (delta.map (HOL.weaken (σ := type)))[index.val] =
      HOL.weaken delta[index.val]
    simp only [List.getElem_map]
  funext point
  unfold formulaMeaning
  rw [entry, interpret_weaken]

theorem ObjectsDenote.weaken {a : ZFSet.{u}} {gamma : SourceContext}
    {n : Nat} {context : Context.{u} n}
    {objects : Sub Tower.Head gamma.length n}
    {valuation : context.Environment → Valuation a gamma}
    (meaning : ObjectsDenote context objects valuation)
    (family : SetFamily context.Environment) :
    ObjectsDenote (context.snoc family) (fun index => Presentation.rename wk (objects index))
      (fun point => valuation point.1) := by
  intro type index
  exact (meaning index).weaken family

theorem ObjectsDenote.lift {a : ZFSet.{u}} {gamma : SourceContext}
    {n : Nat} {context : Context.{u} n}
    {objects : Sub Tower.Head gamma.length n}
    {valuation : context.Environment → Valuation a gamma}
    (meaning : ObjectsDenote context objects valuation)
    (type : HOL.Ty BaseSort) :
    let family := NativeHOLTraceDisplayedTerms.typeFamily a context type
    ObjectsDenote (gamma := type :: gamma) (context.snoc family)
      (liftSub objects)
      (fun point => ZFSetUniformListTraceTermInterpretation.extend
        (valuation point.1) point.2) := by
  dsimp only
  intro objectType index
  cases index with
  | vz =>
      exact NativeHOLTraceDisplayedTerms.Denotes.variable 0
        (NativeTraceLambdaSemantics.Denotes.var _ 0)
  | vs prior =>
      exact (meaning prior).weaken
        (NativeHOLTraceDisplayedTerms.typeFamily a context type)

/-- A successful object representation has its original source trace
denotation after insertion into the mixed native context. -/
theorem represented_denotes {a : ZFSet.{u}} {gamma : SourceContext}
    {type : HOL.Ty BaseSort} (term : HOL.Term Symbol gamma type)
    {code : Tower.Tm gamma.length}
    (represented : HOLLeibnizNativeProofTranslation.represent term = some code)
    {n : Nat} (context : Context.{u} n)
    (objects : Sub Tower.Head gamma.length n)
    (valuation : context.Environment → Valuation a gamma)
    (objectsMeaning : ObjectsDenote context objects valuation) :
    NativeHOLTraceDisplayedTerms.Denotes a context (Presentation.subst objects code)
      (fun environment => ZFSetUniformListTraceTermInterpretation.interpret term
        (valuation environment)) :=
  NativeHOLTraceLeibnizDisplayed.representation_square term represented
    context objects valuation objectsMeaning

/-- Every successful output of the supported compiler fragment denotes the
trace truth family of the exact source conclusion. -/
theorem compile_denotes {a : ZFSet.{u}} {gamma : SourceContext}
    {delta : List (Formula gamma)} {phi : Formula gamma}
    (source : HOL.ProofSyntax Symbol delta phi)
    {n : Nat} {context : Context.{u} n}
    {objects : Sub Tower.Head gamma.length n}
    {valuation : context.Environment → Valuation a gamma}
    {hypotheses : Fin delta.length → Tower.Tm n} {native : Tower.Tm n}
    (objectsMeaning : ObjectsDenote context objects valuation)
    (hypothesesMeaning : HypothesesDenote context valuation hypotheses)
    (success : HOLLeibnizNativeProofTranslation.compile source objects hypotheses =
      some native) :
    ProofDenotes a context native (formulaMeaning phi context valuation) := by
  induction source generalizing n with
  | hyp occurrence =>
      simp only [HOLLeibnizNativeProofTranslation.compile, Option.some.injEq] at success
      subst native
      exact hypothesesMeaning occurrence
  | @impI gamma delta premise conclusion body inductionHypothesis =>
      cases premiseRepresentation : HOLLeibnizNativeProofTranslation.represent premise with
      | none =>
          simp [HOLLeibnizNativeProofTranslation.compile, premiseRepresentation] at success
      | some premiseCode =>
          cases bodyCompilation : HOLLeibnizNativeProofTranslation.compile body
              (fun index => Presentation.rename wk (objects index))
              (Fin.cases (.var 0)
                (fun index => Presentation.rename wk (hypotheses index))) with
          | none =>
              simp [HOLLeibnizNativeProofTranslation.compile, premiseRepresentation,
                bodyCompilation] at success
          | some bodyCode =>
              simp [HOLLeibnizNativeProofTranslation.compile, premiseRepresentation,
                bodyCompilation] at success
              subst native
              let premiseMeaning := formulaMeaning premise context valuation
              let proofFamily := ZFSetTraceProofDecoding.truthFamily premiseMeaning
              have bodyMeaning := inductionHypothesis
                (context := context.snoc proofFamily)
                (objectsMeaning.weaken proofFamily)
                (hypothesesMeaning.prepend premise) bodyCompilation
              have introduced := implicationIntro premiseMeaning
                (formulaMeaning conclusion context valuation) bodyMeaning
              exact introduced.cast_proposition
                (formulaMeaning_imp premise conclusion context valuation).symm
  | @impE gamma delta premise conclusion function argument functionInduction
      argumentInduction =>
      cases functionCompilation : HOLLeibnizNativeProofTranslation.compile function
          objects hypotheses with
      | none =>
          simp [HOLLeibnizNativeProofTranslation.compile, functionCompilation] at success
      | some functionCode =>
          cases argumentCompilation : HOLLeibnizNativeProofTranslation.compile argument
              objects hypotheses with
          | none =>
              simp [HOLLeibnizNativeProofTranslation.compile, functionCompilation,
                argumentCompilation] at success
          | some argumentCode =>
              simp [HOLLeibnizNativeProofTranslation.compile, functionCompilation,
                argumentCompilation] at success
              subst native
              have functionMeaning := functionInduction objectsMeaning hypothesesMeaning
                functionCompilation
              have functionDecoded := functionMeaning.cast_proposition
                (formulaMeaning_imp premise conclusion context valuation)
              have argumentMeaning := argumentInduction objectsMeaning hypothesesMeaning
                argumentCompilation
              exact implicationElim functionDecoded argumentMeaning
  | @allI gamma delta type body proof inductionHypothesis =>
      cases bodyCompilation : HOLLeibnizNativeProofTranslation.compile proof
          (liftSub objects)
          (fun index => Presentation.rename wk
            (hypotheses (index.cast (by simp [HOL.weakenHyps])))) with
      | none =>
          simp [HOLLeibnizNativeProofTranslation.compile, bodyCompilation] at success
      | some bodyCode =>
          simp [HOLLeibnizNativeProofTranslation.compile, bodyCompilation] at success
          subst native
          let domain := NativeHOLTraceDisplayedTerms.typeFamily a context type
          have bodyMeaning := inductionHypothesis
            (context := context.snoc domain)
            (objectsMeaning.lift type) (hypothesesMeaning.lift type) bodyCompilation
          have introduced := universalIntro domain
            (formulaMeaning body (context.snoc domain)
              (fun point => ZFSetUniformListTraceTermInterpretation.extend
                (valuation point.1) point.2)) bodyMeaning
          exact introduced.cast_proposition
            (formulaMeaning_all type body context valuation).symm
  | @allE gamma delta type body term function inductionHypothesis =>
      cases termRepresentation : HOLLeibnizNativeProofTranslation.represent term with
      | none =>
          simp [HOLLeibnizNativeProofTranslation.compile, termRepresentation] at success
      | some termCode =>
          cases functionCompilation : HOLLeibnizNativeProofTranslation.compile function
              objects hypotheses with
          | none =>
              simp [HOLLeibnizNativeProofTranslation.compile, termRepresentation,
                functionCompilation] at success
          | some functionCode =>
              simp [HOLLeibnizNativeProofTranslation.compile, termRepresentation,
                functionCompilation] at success
              subst native
              let domain := NativeHOLTraceDisplayedTerms.typeFamily a context type
              let bodyMeaning : (context.snoc domain).Environment → Prop :=
                formulaMeaning body (context.snoc domain)
                  (fun point => ZFSetUniformListTraceTermInterpretation.extend
                    (valuation point.1) point.2)
              have functionMeaning := inductionHypothesis objectsMeaning hypothesesMeaning
                functionCompilation
              have functionDecoded := functionMeaning.cast_proposition
                (formulaMeaning_all type body context valuation)
              have argumentMeaning := represented_denotes term termRepresentation
                context objects valuation objectsMeaning
              have eliminated := universalElim functionDecoded (object argumentMeaning)
              exact eliminated.cast_proposition
                (formulaMeaning_instantiate term body context valuation).symm
  | @eqRefl gamma delta type term =>
      cases termRepresentation : HOLLeibnizNativeProofTranslation.represent term with
      | none =>
          simp [HOLLeibnizNativeProofTranslation.compile, termRepresentation] at success
      | some termCode =>
          simp [HOLLeibnizNativeProofTranslation.compile, termRepresentation] at success
          subst native
          have termMeaning := represented_denotes term termRepresentation
            context objects valuation objectsMeaning
          have reflexive := reflTerm_denotes (a := a)
            (fun environment => ZFSetUniformListTraceTermInterpretation.interpret term
              (valuation environment))
          exact reflexive.cast_proposition
            (formulaMeaning_eq term term context valuation).symm
  | @eqSymm gamma delta type left right comparison inductionHypothesis =>
      cases leftRepresentation : HOLLeibnizNativeProofTranslation.represent left with
      | none =>
          simp [HOLLeibnizNativeProofTranslation.compile, leftRepresentation] at success
      | some leftCode =>
          cases rightRepresentation : HOLLeibnizNativeProofTranslation.represent right with
          | none =>
              simp [HOLLeibnizNativeProofTranslation.compile, leftRepresentation,
                rightRepresentation] at success
          | some rightCode =>
              cases comparisonCompilation : HOLLeibnizNativeProofTranslation.compile
                  comparison objects hypotheses with
              | none =>
                  simp [HOLLeibnizNativeProofTranslation.compile, leftRepresentation,
                    rightRepresentation, comparisonCompilation] at success
              | some comparisonCode =>
                  simp [HOLLeibnizNativeProofTranslation.compile, leftRepresentation,
                    rightRepresentation, comparisonCompilation] at success
                  subst native
                  have leftMeaning := represented_denotes left leftRepresentation
                    context objects valuation objectsMeaning
                  have comparisonMeaning := inductionHypothesis objectsMeaning
                    hypothesesMeaning comparisonCompilation
                  have comparisonDecoded := comparisonMeaning.cast_proposition
                    (formulaMeaning_eq left right context valuation)
                  have symmetric := symmetry_denotes leftMeaning comparisonDecoded
                  exact symmetric.cast_proposition
                    (formulaMeaning_eq right left context valuation).symm
  | @eqTrans gamma delta type left middle right first second firstInduction
      secondInduction =>
      cases leftRepresentation : HOLLeibnizNativeProofTranslation.represent left with
      | none =>
          simp [HOLLeibnizNativeProofTranslation.compile, leftRepresentation] at success
      | some leftCode =>
          cases middleRepresentation : HOLLeibnizNativeProofTranslation.represent middle with
          | none =>
              simp [HOLLeibnizNativeProofTranslation.compile, leftRepresentation,
                middleRepresentation] at success
          | some middleCode =>
              cases rightRepresentation : HOLLeibnizNativeProofTranslation.represent right with
              | none =>
                  simp [HOLLeibnizNativeProofTranslation.compile, leftRepresentation,
                    middleRepresentation, rightRepresentation] at success
              | some rightCode =>
                  cases firstCompilation : HOLLeibnizNativeProofTranslation.compile first
                      objects hypotheses with
                  | none =>
                      simp [HOLLeibnizNativeProofTranslation.compile, leftRepresentation,
                        middleRepresentation, rightRepresentation, firstCompilation] at success
                  | some firstCode =>
                      cases secondCompilation : HOLLeibnizNativeProofTranslation.compile second
                          objects hypotheses with
                      | none =>
                          simp [HOLLeibnizNativeProofTranslation.compile,
                            leftRepresentation, middleRepresentation, rightRepresentation,
                            firstCompilation, secondCompilation] at success
                      | some secondCode =>
                          simp [HOLLeibnizNativeProofTranslation.compile,
                            leftRepresentation, middleRepresentation, rightRepresentation,
                            firstCompilation, secondCompilation] at success
                          subst native
                          have leftMeaning := represented_denotes left leftRepresentation
                            context objects valuation objectsMeaning
                          have firstMeaning := (firstInduction objectsMeaning hypothesesMeaning
                            firstCompilation).cast_proposition
                              (formulaMeaning_eq left middle context valuation)
                          have secondMeaning := (secondInduction objectsMeaning hypothesesMeaning
                            secondCompilation).cast_proposition
                              (formulaMeaning_eq middle right context valuation)
                          have transitive := transitivity_denotes leftMeaning firstMeaning
                            secondMeaning
                          exact transitive.cast_proposition
                            (formulaMeaning_eq left right context valuation).symm
  | @eqApp gamma delta domain result left right argument comparison inductionHypothesis =>
      cases leftRepresentation : HOLLeibnizNativeProofTranslation.represent left with
      | none =>
          simp [HOLLeibnizNativeProofTranslation.compile, leftRepresentation] at success
      | some leftCode =>
          cases rightRepresentation : HOLLeibnizNativeProofTranslation.represent right with
          | none =>
              simp [HOLLeibnizNativeProofTranslation.compile, leftRepresentation,
                rightRepresentation] at success
          | some rightCode =>
              cases argumentRepresentation : HOLLeibnizNativeProofTranslation.represent
                  argument with
              | none =>
                  simp [HOLLeibnizNativeProofTranslation.compile, leftRepresentation,
                    rightRepresentation, argumentRepresentation] at success
              | some argumentCode =>
                  cases comparisonCompilation : HOLLeibnizNativeProofTranslation.compile
                      comparison objects hypotheses with
                  | none =>
                      simp [HOLLeibnizNativeProofTranslation.compile, leftRepresentation,
                        rightRepresentation, argumentRepresentation,
                        comparisonCompilation] at success
                  | some comparisonCode =>
                      simp [HOLLeibnizNativeProofTranslation.compile, leftRepresentation,
                        rightRepresentation, argumentRepresentation,
                        comparisonCompilation] at success
                      subst native
                      have leftMeaning := represented_denotes left leftRepresentation
                        context objects valuation objectsMeaning
                      have argumentMeaning := represented_denotes argument argumentRepresentation
                        context objects valuation objectsMeaning
                      have comparisonMeaning := (inductionHypothesis objectsMeaning
                        hypothesesMeaning comparisonCompilation).cast_proposition
                          (formulaMeaning_eq left right context valuation)
                      have congruent := functionCongruence_denotes leftMeaning argumentMeaning
                        comparisonMeaning
                      exact congruent.cast_proposition
                        (formulaMeaning_eq (.app left argument) (.app right argument)
                          context valuation).symm
  | @eqAppArg gamma delta domain result function left right comparison
      inductionHypothesis =>
      cases functionRepresentation : HOLLeibnizNativeProofTranslation.represent function with
      | none =>
          simp [HOLLeibnizNativeProofTranslation.compile, functionRepresentation] at success
      | some functionCode =>
          cases leftRepresentation : HOLLeibnizNativeProofTranslation.represent left with
          | none =>
              simp [HOLLeibnizNativeProofTranslation.compile, functionRepresentation,
                leftRepresentation] at success
          | some leftCode =>
              cases rightRepresentation : HOLLeibnizNativeProofTranslation.represent right with
              | none =>
                  simp [HOLLeibnizNativeProofTranslation.compile, functionRepresentation,
                    leftRepresentation, rightRepresentation] at success
              | some rightCode =>
                  cases comparisonCompilation : HOLLeibnizNativeProofTranslation.compile
                      comparison objects hypotheses with
                  | none =>
                      simp [HOLLeibnizNativeProofTranslation.compile, functionRepresentation,
                        leftRepresentation, rightRepresentation,
                        comparisonCompilation] at success
                  | some comparisonCode =>
                      simp [HOLLeibnizNativeProofTranslation.compile, functionRepresentation,
                        leftRepresentation, rightRepresentation,
                        comparisonCompilation] at success
                      subst native
                      have functionMeaning := represented_denotes function
                        functionRepresentation context objects valuation objectsMeaning
                      have leftMeaning := represented_denotes left leftRepresentation
                        context objects valuation objectsMeaning
                      have comparisonMeaning := (inductionHypothesis objectsMeaning
                        hypothesesMeaning comparisonCompilation).cast_proposition
                          (formulaMeaning_eq left right context valuation)
                      have congruent := congruence_denotes functionMeaning leftMeaning
                        comparisonMeaning
                      exact congruent.cast_proposition
                        (formulaMeaning_eq (.app function left) (.app function right)
                          context valuation).symm
  | @eqPropEL gamma delta left right comparison inductionHypothesis =>
      cases leftRepresentation : HOLLeibnizNativeProofTranslation.represent left with
      | none =>
          simp [HOLLeibnizNativeProofTranslation.compile, leftRepresentation] at success
      | some leftCode =>
          cases rightRepresentation : HOLLeibnizNativeProofTranslation.represent right with
          | none =>
              simp [HOLLeibnizNativeProofTranslation.compile, leftRepresentation,
                rightRepresentation] at success
          | some rightCode =>
              cases comparisonCompilation : HOLLeibnizNativeProofTranslation.compile
                  comparison objects hypotheses with
              | none =>
                  simp [HOLLeibnizNativeProofTranslation.compile, leftRepresentation,
                    rightRepresentation, comparisonCompilation] at success
              | some comparisonCode =>
                  simp [HOLLeibnizNativeProofTranslation.compile, leftRepresentation,
                    rightRepresentation, comparisonCompilation] at success
                  subst native
                  have comparisonMeaning := (inductionHypothesis objectsMeaning
                    hypothesesMeaning comparisonCompilation).cast_proposition
                      (formulaMeaning_eq left right context valuation)
                  have forward := propForward_denotes comparisonMeaning
                  exact forward.cast_proposition
                    (formulaMeaning_imp left right context valuation).symm
  | @eqPropER gamma delta left right comparison inductionHypothesis =>
      cases leftRepresentation : HOLLeibnizNativeProofTranslation.represent left with
      | none =>
          simp [HOLLeibnizNativeProofTranslation.compile, leftRepresentation] at success
      | some leftCode =>
          cases rightRepresentation : HOLLeibnizNativeProofTranslation.represent right with
          | none =>
              simp [HOLLeibnizNativeProofTranslation.compile, leftRepresentation,
                rightRepresentation] at success
          | some rightCode =>
              cases comparisonCompilation : HOLLeibnizNativeProofTranslation.compile
                  comparison objects hypotheses with
              | none =>
                  simp [HOLLeibnizNativeProofTranslation.compile, leftRepresentation,
                    rightRepresentation, comparisonCompilation] at success
              | some comparisonCode =>
                  simp [HOLLeibnizNativeProofTranslation.compile, leftRepresentation,
                    rightRepresentation, comparisonCompilation] at success
                  subst native
                  have leftMeaning := represented_denotes left leftRepresentation
                    context objects valuation objectsMeaning
                  have comparisonMeaning := (inductionHypothesis objectsMeaning
                    hypothesesMeaning comparisonCompilation).cast_proposition
                      (formulaMeaning_eq left right context valuation)
                  have symmetric := symmetry_denotes leftMeaning comparisonMeaning
                  have backward := propForward_denotes symmetric
                  exact backward.cast_proposition
                    (formulaMeaning_imp right left context valuation).symm
  | @beta gamma delta domain result argument body =>
      cases argumentRepresentation : HOLLeibnizNativeProofTranslation.represent argument with
      | none =>
          simp [HOLLeibnizNativeProofTranslation.compile, argumentRepresentation] at success
      | some argumentCode =>
          cases bodyRepresentation : HOLLeibnizNativeProofTranslation.represent body with
          | none =>
              simp [HOLLeibnizNativeProofTranslation.compile, argumentRepresentation,
                bodyRepresentation] at success
          | some bodyCode =>
              simp [HOLLeibnizNativeProofTranslation.compile, argumentRepresentation,
                bodyRepresentation] at success
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
                  interpret_instantiate]
              have reflexive := reflTerm_denotes_of_equal (a := a) betaEqual
              exact reflexive.cast_proposition
                (formulaMeaning_eq (.app (.lam body) argument)
                  (HOL.instantiate argument body) context valuation).symm
  | _ => simp [HOLLeibnizNativeProofTranslation.compile] at success

#print axioms interpret_weaken
#print axioms interpret_instantiate
#print axioms compile_denotes

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceLeibnizCompilerSemantics
