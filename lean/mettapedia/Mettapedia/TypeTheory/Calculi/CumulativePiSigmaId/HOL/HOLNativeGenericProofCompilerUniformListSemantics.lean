import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerSemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerUniformList
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceQualifiedExtensionalSemantics
import Mettapedia.Logic.HOL.Embedding.ZFSetUniformListTraceProofBridge

/-!
# The uniform-List trace model as a displayed compiler algebra

The generic HOL proof compiler has one recursive fold.  This module equips
that fold with the independently defined Aczel-trace semantics of the
uniform-List source theory.  A state packages a mixed native context, a source
HOL valuation over that context, and evidence that the compiler's object
substitution realizes the valuation.

Nothing in the semantic relation invokes the compiler.  Local introduction,
elimination, equality, and extensionality laws are supplied by the trace model;
the generic fusion theorem then establishes denotation for the term emitted by
the one compiler.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler
namespace UniformListSemantics

open Presentation Mettapedia.Logic
open FormationSensitiveHOLInterface
open HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (Elements)
open ZFSetContextualInterpretation (SetFamily Section codedCwf)
open ZFSetUniformListTraceTypeInterpretation
open NativeTraceLambdaSemantics
open NativeHOLTraceLeibnizProofSemantics

universe u

abbrev SourceContext := HOL.Ctx BaseSort
abbrev Formula (gamma : SourceContext) := HOL.Formula Symbol gamma
abbrev Valuation (a : ZFSet.{u}) (gamma : SourceContext) :=
  NativeHOLTraceLeibnizCompilerSemantics.Valuation a gamma

/-- A semantic state over the exact object substitution supplied to the
compiler.  `objectsDenote` is the non-vacuous connection: every native object
variable denotes the corresponding source valuation component. -/
structure State (a : ZFSet.{u}) {gamma : SourceContext} {n : Nat}
    (objects : Sub Tower.Head gamma.length n) where
  context : Context.{u} n
  valuation : context.Environment → Valuation a gamma
  objectsDenote : NativeHOLTraceLeibnizCompilerSemantics.ObjectsDenote
    context objects valuation

/-- The independently defined trace proof-family denotation at one state. -/
def Denotes (a : ZFSet.{u}) {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} (state : State a objects)
    (native : Tower.Tm n) (formula : Formula gamma) : Prop :=
  NativeHOLTraceQualifiedExtensionalSemantics.ProofDenotes a state.context native
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning
      formula state.context state.valuation)

/-- Adding a proof assumption extends only the native semantic telescope. -/
noncomputable def proofExtension (a : ZFSet.{u}) {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} (state : State a objects)
    (premise : Formula gamma) :
    State a (fun index => Presentation.rename wk (objects index)) :=
  let premiseMeaning := NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning
    premise state.context state.valuation
  let family := ZFSetTraceProofDecoding.truthFamily premiseMeaning
  { context := state.context.snoc family
    valuation := fun point => state.valuation point.1
    objectsDenote :=
      NativeHOLTraceLeibnizCompilerSemantics.ObjectsDenote.weaken
        state.objectsDenote family }

/-- Adding a quantified object extends the source valuation and native
semantic telescope together. -/
noncomputable def objectExtension (a : ZFSet.{u}) {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} (state : State a objects)
    (type : HOL.Ty BaseSort) : State a (gamma := type :: gamma) (liftSub objects) :=
  let family := NativeHOLTraceDisplayedTerms.typeFamily a state.context type
  { context := state.context.snoc family
    valuation := fun point =>
      ZFSetUniformListTraceTermInterpretation.extend
        (state.valuation point.1) point.2
    objectsDenote :=
      NativeHOLTraceLeibnizCompilerSemantics.ObjectsDenote.lift
        state.objectsDenote type }

theorem proofVariable (a : ZFSet.{u}) {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} (state : State a objects)
    (premise : Formula gamma) :
    Denotes a (proofExtension a state premise) (.var 0) premise := by
  exact NativeHOLTraceQualifiedExtensionalSemantics.proofVariableZero
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning
      premise state.context state.valuation)

theorem proofWeakening (a : ZFSet.{u}) {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} {native : Tower.Tm n}
    {formula : Formula gamma} (state : State a objects) (premise : Formula gamma)
    (meaning : Denotes a state native formula) :
    Denotes a (proofExtension a state premise) (Presentation.rename wk native)
      formula := by
  exact NativeHOLTraceQualifiedExtensionalSemantics.ProofDenotes.weaken meaning
    (ZFSetTraceProofDecoding.truthFamily
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning
      premise state.context state.valuation))

theorem objectWeakening (a : ZFSet.{u}) {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} {native : Tower.Tm n}
    {formula : Formula gamma} (state : State a objects) (type : HOL.Ty BaseSort)
    (meaning : Denotes a state native formula) :
    Denotes a (objectExtension a state type) (Presentation.rename wk native)
      (HOL.weaken (σ := type) formula) := by
  unfold Denotes objectExtension
  have weakened :=
    NativeHOLTraceQualifiedExtensionalSemantics.ProofDenotes.weaken meaning
    (NativeHOLTraceDisplayedTerms.typeFamily a state.context type)
  apply NativeHOLTraceQualifiedExtensionalSemantics.ProofDenotes.cast_proposition
    weakened
  funext point
  unfold NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning
  rw [NativeHOLTraceLeibnizCompilerSemantics.interpret_weaken]

theorem implicationIntro (a : ZFSet.{u}) {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    {premise conclusion : Formula gamma} {body : Tower.Tm (n + 1)}
    (state : State a objects)
    (bodyMeaning : Denotes a (proofExtension a state premise) body conclusion) :
    Denotes a state (.lam body) (.imp premise conclusion) := by
  have introduced := NativeHOLTraceQualifiedExtensionalSemantics.implicationIntro
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning
      premise state.context state.valuation)
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning
      conclusion state.context state.valuation) bodyMeaning
  exact introduced.cast_proposition
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_imp
      premise conclusion state.context state.valuation).symm

theorem implicationElim (a : ZFSet.{u}) {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    {premise conclusion : Formula gamma} {function argument : Tower.Tm n}
    (state : State a objects)
    (functionMeaning : Denotes a state function (.imp premise conclusion))
    (argumentMeaning : Denotes a state argument premise) :
    Denotes a state (.app function argument) conclusion := by
  have decoded := functionMeaning.cast_proposition
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_imp
      premise conclusion state.context state.valuation)
  exact NativeHOLTraceQualifiedExtensionalSemantics.implicationElim
    decoded argumentMeaning

theorem universalIntro (a : ZFSet.{u}) {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} {type : HOL.Ty BaseSort}
    {formula : Formula (type :: gamma)} {body : Tower.Tm (n + 1)}
    (state : State a objects)
    (bodyMeaning : Denotes a (objectExtension a state type) body formula) :
    Denotes a state (.lam body) (.all formula) := by
  let domain := NativeHOLTraceDisplayedTerms.typeFamily a state.context type
  have introduced := NativeHOLTraceQualifiedExtensionalSemantics.universalIntro
    domain
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning formula
      (state.context.snoc domain)
      (fun point => ZFSetUniformListTraceTermInterpretation.extend
        (state.valuation point.1) point.2)) bodyMeaning
  exact introduced.cast_proposition
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_all
      type formula state.context state.valuation).symm

theorem universalElim (a : ZFSet.{u}) {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} {type : HOL.Ty BaseSort}
    {formula : Formula (type :: gamma)} {argument : HOL.Term Symbol gamma type}
    {argumentCode : Tower.Tm gamma.length} {function : Tower.Tm n}
    (state : State a objects)
    (represented : represent FormationSensitiveHOLLeibnizInterface.signature
      argument = some argumentCode)
    (functionMeaning : Denotes a state function (.all formula)) :
    Denotes a state (.app function (subst objects argumentCode))
      (HOL.instantiate argument formula) := by
  have representedLegacy :
      HOLLeibnizNativeProofTranslation.represent argument = some argumentCode := by
    simpa only [UniformList.represent_eq_legacy] using represented
  let domain := NativeHOLTraceDisplayedTerms.typeFamily a state.context type
  have functionDecoded := functionMeaning.cast_proposition
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_all
      type formula state.context state.valuation)
  have argumentMeaning :=
    NativeHOLTraceLeibnizCompilerSemantics.represented_denotes
      argument representedLegacy state.context objects state.valuation
      state.objectsDenote
  have eliminated := NativeHOLTraceQualifiedExtensionalSemantics.universalElim
    functionDecoded (NativeHOLTraceLeibnizProofSemantics.object argumentMeaning)
  exact eliminated.cast_proposition
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_instantiate
      argument formula state.context state.valuation).symm

/-- A successful object representation denotes the source object in the
semantic state indexed by the same substitution used by the compiler. -/
theorem representedObject (a : ZFSet.{u}) {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} {type : HOL.Ty BaseSort}
    (state : State a objects) (term : HOL.Term Symbol gamma type)
    {code : Tower.Tm gamma.length}
    (represented : represent FormationSensitiveHOLLeibnizInterface.signature
      term = some code) :
    NativeHOLTraceDisplayedTerms.Denotes a state.context (subst objects code)
      (fun environment => ZFSetUniformListTraceTermInterpretation.interpret
        term (state.valuation environment)) := by
  apply NativeHOLTraceLeibnizCompilerSemantics.represented_denotes
    term (context := state.context) (objects := objects)
    (valuation := state.valuation) (objectsMeaning := state.objectsDenote)
  simpa only [UniformList.represent_eq_legacy] using represented

theorem reflexivity (a : ZFSet.{u}) {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} {type : HOL.Ty BaseSort}
    {term : HOL.Term Symbol gamma type} {code : Tower.Tm gamma.length}
    {out : Tower.Tm n} (state : State a objects)
    (_represented : represent FormationSensitiveHOLLeibnizInterface.signature
      term = some code)
    (emitted : UniformList.operations.raw.reflexivity = some out) :
    Denotes a state out (term.eq term) := by
  simp only [UniformList.operations, UniformList.rawOperations,
    Option.some.injEq] at emitted
  subst out
  have reflexive :=
    NativeHOLTraceQualifiedExtensionalSemantics.reflTerm_denotes (a := a)
      (fun environment => ZFSetUniformListTraceTermInterpretation.interpret
        term (state.valuation environment))
  exact reflexive.cast_proposition
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
      term term state.context state.valuation).symm

theorem symmetry (a : ZFSet.{u}) {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} {type : HOL.Ty BaseSort}
    {left right : HOL.Term Symbol gamma type}
    {leftCode rightCode : Tower.Tm gamma.length}
    {comparison out : Tower.Tm n} (state : State a objects)
    (leftRepresented : represent FormationSensitiveHOLLeibnizInterface.signature
      left = some leftCode)
    (_rightRepresented : represent FormationSensitiveHOLLeibnizInterface.signature
      right = some rightCode)
    (emitted : UniformList.operations.raw.symmetry type
      (subst objects leftCode) comparison = some out)
    (comparisonMeaning : Denotes a state comparison (left.eq right)) :
    Denotes a state out (right.eq left) := by
  simp only [UniformList.operations, UniformList.rawOperations,
    Option.some.injEq] at emitted
  subst out
  have leftMeaning := representedObject a state left leftRepresented
  have comparisonDecoded := comparisonMeaning.cast_proposition
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
      left right state.context state.valuation)
  have symmetric :=
    NativeHOLTraceQualifiedExtensionalSemantics.symmetry_denotes
      leftMeaning comparisonDecoded
  exact symmetric.cast_proposition
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
      right left state.context state.valuation).symm

theorem transitivity (a : ZFSet.{u}) {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} {type : HOL.Ty BaseSort}
    {left middle right : HOL.Term Symbol gamma type}
    {leftCode middleCode rightCode : Tower.Tm gamma.length}
    {first second out : Tower.Tm n} (state : State a objects)
    (leftRepresented : represent FormationSensitiveHOLLeibnizInterface.signature
      left = some leftCode)
    (_middleRepresented : represent FormationSensitiveHOLLeibnizInterface.signature
      middle = some middleCode)
    (_rightRepresented : represent FormationSensitiveHOLLeibnizInterface.signature
      right = some rightCode)
    (emitted : UniformList.operations.raw.transitivity type
      (subst objects leftCode) first second = some out)
    (firstMeaning : Denotes a state first (left.eq middle))
    (secondMeaning : Denotes a state second (middle.eq right)) :
    Denotes a state out (left.eq right) := by
  simp only [UniformList.operations, UniformList.rawOperations,
    Option.some.injEq] at emitted
  subst out
  have leftMeaning := representedObject a state left leftRepresented
  have firstDecoded := firstMeaning.cast_proposition
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
      left middle state.context state.valuation)
  have secondDecoded := secondMeaning.cast_proposition
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
      middle right state.context state.valuation)
  have transitive :=
    NativeHOLTraceQualifiedExtensionalSemantics.transitivity_denotes
      leftMeaning firstDecoded secondDecoded
  exact transitive.cast_proposition
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
      left right state.context state.valuation).symm

theorem propositionExtensionality (a : ZFSet.{u})
    {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    {left right : Formula gamma}
    {leftCode rightCode : Tower.Tm gamma.length}
    {forward backward out : Tower.Tm n} (state : State a objects)
    (leftRepresented : represent FormationSensitiveHOLLeibnizInterface.signature
      left = some leftCode)
    (rightRepresented : represent FormationSensitiveHOLLeibnizInterface.signature
      right = some rightCode)
    (emitted : UniformList.operations.raw.propositionExtensionality
      (subst objects leftCode) (subst objects rightCode) forward backward = some out)
    (forwardMeaning : Denotes a state forward (.imp left right))
    (backwardMeaning : Denotes a state backward (.imp right left)) :
    Denotes a state out (left.eq right) := by
  simp only [UniformList.operations, UniformList.rawOperations,
    Option.some.injEq] at emitted
  subst out
  let leftValue := fun environment =>
    ZFSetUniformListTraceTermInterpretation.interpret left
      (state.valuation environment)
  let rightValue := fun environment =>
    ZFSetUniformListTraceTermInterpretation.interpret right
      (state.valuation environment)
  have leftMeaning := representedObject a state left leftRepresented
  have rightMeaning := representedObject a state right rightRepresented
  have forwardDecoded := forwardMeaning.cast_proposition
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_imp
      left right state.context state.valuation)
  have backwardDecoded := backwardMeaning.cast_proposition
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_imp
      right left state.context state.valuation)
  have extensional :=
    NativeHOLTraceQualifiedExtensionalSemantics.propositionExtensionality_denotes
      (left := leftValue) (right := rightValue)
      leftMeaning rightMeaning forwardDecoded backwardDecoded
  exact extensional.cast_proposition
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
      left right state.context state.valuation).symm

theorem propositionForward (a : ZFSet.{u})
    {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    {left right : Formula gamma} {comparison out : Tower.Tm n}
    (state : State a objects)
    (emitted : UniformList.operations.raw.propositionForward comparison = some out)
    (comparisonMeaning : Denotes a state comparison (left.eq right)) :
    Denotes a state out (.imp left right) := by
  simp only [UniformList.operations, UniformList.rawOperations,
    Option.some.injEq] at emitted
  subst out
  have comparisonDecoded := comparisonMeaning.cast_proposition
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
      left right state.context state.valuation)
  have forward :=
    NativeHOLTraceQualifiedExtensionalSemantics.propForward_denotes
      comparisonDecoded
  exact forward.cast_proposition
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_imp
      left right state.context state.valuation).symm

theorem functionCongruence (a : ZFSet.{u})
    {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} {domain result : HOL.Ty BaseSort}
    {function other : HOL.Term Symbol gamma (.arr domain result)}
    {argument : HOL.Term Symbol gamma domain}
    {functionCode otherCode argumentCode : Tower.Tm gamma.length}
    {comparison out : Tower.Tm n} (state : State a objects)
    (functionRepresented :
      represent FormationSensitiveHOLLeibnizInterface.signature function =
        some functionCode)
    (_otherRepresented :
      represent FormationSensitiveHOLLeibnizInterface.signature other =
        some otherCode)
    (argumentRepresented :
      represent FormationSensitiveHOLLeibnizInterface.signature argument =
        some argumentCode)
    (emitted : UniformList.operations.raw.functionCongruence result
      (subst objects functionCode) (subst objects argumentCode) comparison = some out)
    (comparisonMeaning : Denotes a state comparison (function.eq other)) :
    Denotes a state out
      ((HOL.Term.app function argument).eq (HOL.Term.app other argument)) := by
  simp only [UniformList.operations, UniformList.rawOperations,
    Option.some.injEq] at emitted
  subst out
  have functionMeaning := representedObject a state function functionRepresented
  have argumentMeaning := representedObject a state argument argumentRepresented
  have comparisonDecoded := comparisonMeaning.cast_proposition
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
      function other state.context state.valuation)
  have congruent :=
    NativeHOLTraceQualifiedExtensionalSemantics.functionCongruence_denotes
      functionMeaning argumentMeaning comparisonDecoded
  exact congruent.cast_proposition
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
      (.app function argument) (.app other argument)
      state.context state.valuation).symm

theorem argumentCongruence (a : ZFSet.{u})
    {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} {domain result : HOL.Ty BaseSort}
    {function : HOL.Term Symbol gamma (.arr domain result)}
    {left right : HOL.Term Symbol gamma domain}
    {functionCode leftCode rightCode : Tower.Tm gamma.length}
    {comparison out : Tower.Tm n} (state : State a objects)
    (functionRepresented :
      represent FormationSensitiveHOLLeibnizInterface.signature function =
        some functionCode)
    (leftRepresented :
      represent FormationSensitiveHOLLeibnizInterface.signature left = some leftCode)
    (_rightRepresented :
      represent FormationSensitiveHOLLeibnizInterface.signature right = some rightCode)
    (emitted : UniformList.operations.raw.argumentCongruence result
      (subst objects functionCode) (subst objects leftCode) comparison = some out)
    (comparisonMeaning : Denotes a state comparison (left.eq right)) :
    Denotes a state out
      ((HOL.Term.app function left).eq (HOL.Term.app function right)) := by
  simp only [UniformList.operations, UniformList.rawOperations,
    Option.some.injEq] at emitted
  subst out
  have functionMeaning := representedObject a state function functionRepresented
  have leftMeaning := representedObject a state left leftRepresented
  have comparisonDecoded := comparisonMeaning.cast_proposition
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
      left right state.context state.valuation)
  have congruent :=
    NativeHOLTraceQualifiedExtensionalSemantics.congruence_denotes
      functionMeaning leftMeaning comparisonDecoded
  exact congruent.cast_proposition
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
      (.app function left) (.app function right)
      state.context state.valuation).symm

/-- Representing a body in the lifted object state and abstracting it gives
the trace meaning of the source lambda. -/
theorem representedLambda (a : ZFSet.{u})
    {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} {domain codomain : HOL.Ty BaseSort}
    (state : State a objects) (body : HOL.Term Symbol (domain :: gamma) codomain)
    {bodyCode : Tower.Tm (domain :: gamma).length}
    (represented : represent FormationSensitiveHOLLeibnizInterface.signature
      body = some bodyCode) :
    NativeHOLTraceDisplayedTerms.Denotes a state.context
      (.lam (subst (liftSub objects) bodyCode))
      (fun environment => ZFSetUniformListTraceTermInterpretation.interpret
        (.lam body) (state.valuation environment)) := by
  have bodyMeaning := representedObject a (objectExtension a state domain)
    body represented
  simpa [objectExtension, ZFSetUniformListTraceTermInterpretation.interpret] using
    (NativeHOLTraceDisplayedTerms.Denotes.abstraction bodyMeaning)

/-- The native eta expansion built from a represented function denotes the
source eta expansion in the same state. -/
theorem etaExpansion (a : ZFSet.{u})
    {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} {domain codomain : HOL.Ty BaseSort}
    (state : State a objects)
    (function : HOL.Term Symbol gamma (.arr domain codomain))
    {functionCode : Tower.Tm gamma.length}
    (represented : represent FormationSensitiveHOLLeibnizInterface.signature
      function = some functionCode) :
    NativeHOLTraceDisplayedTerms.Denotes a state.context
      (.lam (.app (Presentation.rename wk (subst objects functionCode)) (.var 0)))
      (fun environment => ZFSetUniformListTraceTermInterpretation.interpret
        (.lam (.app (HOL.weaken function) (.var .vz)))
        (state.valuation environment)) := by
  let family := NativeHOLTraceDisplayedTerms.typeFamily a state.context domain
  have functionMeaning := representedObject a state function represented
  have argumentMeaning : NativeHOLTraceDisplayedTerms.Denotes a
      (state.context.snoc family) (.var 0) (fun point => point.2) :=
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
        (state.valuation environment)) argument =
    app (ZFSetUniformListTraceTermInterpretation.interpret
      (HOL.weaken function)
      (ZFSetUniformListTraceTermInterpretation.extend
        (state.valuation environment) argument)) argument
  rw [NativeHOLTraceLeibnizCompilerSemantics.interpret_weaken]

theorem lambdaCongruence (a : ZFSet.{u})
    {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} {domain codomain : HOL.Ty BaseSort}
    {left right : HOL.Term Symbol (domain :: gamma) codomain}
    {leftCode rightCode : Tower.Tm (domain :: gamma).length}
    {comparison : Tower.Tm (n + 1)} {out : Tower.Tm n}
    (state : State a objects)
    (leftRepresented :
      represent FormationSensitiveHOLLeibnizInterface.signature left = some leftCode)
    (rightRepresented :
      represent FormationSensitiveHOLLeibnizInterface.signature right = some rightCode)
    (emitted : UniformList.operations.raw.functionExtensionality
      (typeAt FormationSensitiveHOLLeibnizInterface.signature.types n domain)
      (typeAt FormationSensitiveHOLLeibnizInterface.signature.types n codomain)
      (.lam (subst (liftSub objects) leftCode))
      (.lam (subst (liftSub objects) rightCode)) (.lam comparison) = some out)
    (comparisonMeaning : Denotes a (objectExtension a state domain) comparison
      (left.eq right)) :
    Denotes a state out ((HOL.Term.lam left).eq (HOL.Term.lam right)) := by
  simp only [UniformList.operations, UniformList.rawOperations,
    Option.some.injEq] at emitted
  subst out
  let domainFamily :=
    NativeHOLTraceDisplayedTerms.typeFamily a state.context domain
  let extendedValuation : (state.context.snoc domainFamily).Environment →
      Valuation a (domain :: gamma) :=
    fun point => ZFSetUniformListTraceTermInterpretation.extend
      (state.valuation point.1) point.2
  let leftBodyValue : (state.context.snoc domainFamily).Environment →
      Value a codomain :=
    fun point => ZFSetUniformListTraceTermInterpretation.interpret left
      (extendedValuation point)
  let rightBodyValue : (state.context.snoc domainFamily).Environment →
      Value a codomain :=
    fun point => ZFSetUniformListTraceTermInterpretation.interpret right
      (extendedValuation point)
  let leftFunctionValue : state.context.Environment →
      Value a (.arr domain codomain) :=
    fun environment => ZFSetUniformListTraceTermInterpretation.interpret
      (.lam left) (state.valuation environment)
  let rightFunctionValue : state.context.Environment →
      Value a (.arr domain codomain) :=
    fun environment => ZFSetUniformListTraceTermInterpretation.interpret
      (.lam right) (state.valuation environment)
  have leftMeaning := representedLambda a state left leftRepresented
  have rightMeaning := representedLambda a state right rightRepresented
  have comparisonDecoded :
      NativeHOLTraceQualifiedExtensionalSemantics.ProofDenotes a
        (state.context.snoc domainFamily) comparison
        (NativeHOLTraceLeibnizProofSemantics.equalityProposition
          leftBodyValue rightBodyValue) := by
    apply comparisonMeaning.cast_proposition
    exact NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
      left right (state.context.snoc domainFamily) extendedValuation
  have introduced :=
    NativeHOLTraceQualifiedExtensionalSemantics.universalIntro domainFamily
      (NativeHOLTraceLeibnizProofSemantics.equalityProposition
        leftBodyValue rightBodyValue) comparisonDecoded
  have pointwiseDecoded :
      NativeHOLTraceQualifiedExtensionalSemantics.ProofDenotes a state.context
        (.lam comparison)
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
      (typeAt FormationSensitiveHOLLeibnizInterface.signature.types n domain)
      (typeAt FormationSensitiveHOLLeibnizInterface.signature.types n codomain)
      (left := leftFunctionValue) (right := rightFunctionValue)
      leftMeaning rightMeaning pointwiseDecoded
  exact extensional.cast_proposition
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
      (.lam left) (.lam right) state.context state.valuation).symm

theorem functionExtensionality (a : ZFSet.{u})
    {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} {domain codomain : HOL.Ty BaseSort}
    {function other : HOL.Term Symbol gamma (.arr domain codomain)}
    {functionCode otherCode : Tower.Tm gamma.length}
    {pointwise out : Tower.Tm n} (state : State a objects)
    (functionRepresented :
      represent FormationSensitiveHOLLeibnizInterface.signature function =
        some functionCode)
    (otherRepresented :
      represent FormationSensitiveHOLLeibnizInterface.signature other =
        some otherCode)
    (emitted : UniformList.operations.raw.functionExtensionality
      (typeAt FormationSensitiveHOLLeibnizInterface.signature.types n domain)
      (typeAt FormationSensitiveHOLLeibnizInterface.signature.types n codomain)
      (subst objects functionCode) (subst objects otherCode) pointwise = some out)
    (pointwiseMeaning : Denotes a state pointwise
      (.all (.eq
        (HOL.Term.app (HOL.weaken function) (.var .vz))
        (HOL.Term.app (HOL.weaken other) (.var .vz))))) :
    Denotes a state out (function.eq other) := by
  simp only [UniformList.operations, UniformList.rawOperations,
    Option.some.injEq] at emitted
  subst out
  let functionValue := fun environment =>
    ZFSetUniformListTraceTermInterpretation.interpret function
      (state.valuation environment)
  let otherValue := fun environment =>
    ZFSetUniformListTraceTermInterpretation.interpret other
      (state.valuation environment)
  have functionMeaning := representedObject a state function functionRepresented
  have otherMeaning := representedObject a state other otherRepresented
  have pointwiseDecoded :
      NativeHOLTraceQualifiedExtensionalSemantics.ProofDenotes a state.context
        pointwise
        (fun environment => ∀ argument : Value a domain,
          app (functionValue environment) argument =
            app (otherValue environment) argument) := by
    apply pointwiseMeaning.cast_proposition
    exact NativeHOLTraceExtensionalCompilerSemantics.formulaMeaning_pointwiseFormula
      function other state.context state.valuation
  have extensional :=
    NativeHOLTraceQualifiedExtensionalSemantics.functionExtensionality_denotes
      (typeAt FormationSensitiveHOLLeibnizInterface.signature.types n domain)
      (typeAt FormationSensitiveHOLLeibnizInterface.signature.types n codomain)
      (left := functionValue) (right := otherValue)
      functionMeaning otherMeaning pointwiseDecoded
  exact extensional.cast_proposition
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
      function other state.context state.valuation).symm

theorem beta (a : ZFSet.{u}) {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} {domain codomain : HOL.Ty BaseSort}
    {argument : HOL.Term Symbol gamma domain}
    {body : HOL.Term Symbol (domain :: gamma) codomain}
    {argumentCode : Tower.Tm gamma.length}
    {bodyCode : Tower.Tm (domain :: gamma).length}
    {out : Tower.Tm n} (state : State a objects)
    (_argumentRepresented :
      represent FormationSensitiveHOLLeibnizInterface.signature argument =
        some argumentCode)
    (_bodyRepresented :
      represent FormationSensitiveHOLLeibnizInterface.signature body = some bodyCode)
    (emitted : UniformList.operations.raw.reflexivity = some out) :
    Denotes a state out
      ((HOL.Term.app (HOL.Term.lam body) argument).eq
        (HOL.instantiate argument body)) := by
  simp only [UniformList.operations, UniformList.rawOperations,
    Option.some.injEq] at emitted
  subst out
  let leftValue : state.context.Environment → Value a codomain :=
    fun environment => ZFSetUniformListTraceTermInterpretation.interpret
      (.app (.lam body) argument) (state.valuation environment)
  let rightValue : state.context.Environment → Value a codomain :=
    fun environment => ZFSetUniformListTraceTermInterpretation.interpret
      (HOL.instantiate argument body) (state.valuation environment)
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
      state.context state.valuation).symm

theorem eta (a : ZFSet.{u}) {gamma : SourceContext} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} {domain codomain : HOL.Ty BaseSort}
    {function : HOL.Term Symbol gamma (.arr domain codomain)}
    {functionCode : Tower.Tm gamma.length}
    {pointwise : Tower.Tm (n + 1)} {out : Tower.Tm n}
    (state : State a objects)
    (functionRepresented :
      represent FormationSensitiveHOLLeibnizInterface.signature function =
        some functionCode)
    (pointwiseEmitted : UniformList.operations.raw.reflexivity = some pointwise)
    (emitted : UniformList.operations.raw.functionExtensionality
      (typeAt FormationSensitiveHOLLeibnizInterface.signature.types n domain)
      (typeAt FormationSensitiveHOLLeibnizInterface.signature.types n codomain)
      (.lam (.app (Presentation.rename wk (subst objects functionCode)) (.var 0)))
      (subst objects functionCode) (.lam pointwise) = some out) :
    Denotes a state out
      ((HOL.Term.lam (HOL.Term.app (HOL.weaken function) (.var .vz))).eq
        function) := by
  simp only [UniformList.operations, UniformList.rawOperations,
    Option.some.injEq] at pointwiseEmitted
  subst pointwise
  simp only [UniformList.operations, UniformList.rawOperations,
    Option.some.injEq] at emitted
  subst out
  let domainFamily :=
    NativeHOLTraceDisplayedTerms.typeFamily a state.context domain
  let functionValue : state.context.Environment →
      Value a (.arr domain codomain) :=
    fun environment => ZFSetUniformListTraceTermInterpretation.interpret
      function (state.valuation environment)
  let expandedValue : state.context.Environment →
      Value a (.arr domain codomain) :=
    fun environment => ZFSetUniformListTraceTermInterpretation.interpret
      (.lam (.app (HOL.weaken function) (.var .vz)))
      (state.valuation environment)
  let applicationValue : (state.context.snoc domainFamily).Environment →
      Value a codomain :=
    fun point => app (functionValue point.1) point.2
  have functionMeaning := representedObject a state function functionRepresented
  have expandedMeaning := etaExpansion a state function functionRepresented
  have reflexive :=
    NativeHOLTraceQualifiedExtensionalSemantics.reflTerm_denotes
      (a := a) applicationValue
  have introduced :=
    NativeHOLTraceQualifiedExtensionalSemantics.universalIntro domainFamily
      (NativeHOLTraceLeibnizProofSemantics.equalityProposition
        applicationValue applicationValue) reflexive
  have pointwiseDecoded :
      NativeHOLTraceQualifiedExtensionalSemantics.ProofDenotes a state.context
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
      (typeAt FormationSensitiveHOLLeibnizInterface.signature.types n domain)
      (typeAt FormationSensitiveHOLLeibnizInterface.signature.types n codomain)
      (left := expandedValue) (right := functionValue)
      expandedMeaning functionMeaning pointwiseDecoded
  exact extensional.cast_proposition
    (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning_eq
      (.lam (.app (HOL.weaken function) (.var .vz))) function
      state.context state.valuation).symm

/-- The uniform-List Aczel interpretation is a displayed semantic algebra over
the one signature-generic compiler. -/
noncomputable def algebra (a : ZFSet.{u}) :
    GenericSemantics.Algebra FormationSensitiveHOLLeibnizInterface.signature
      UniformList.proofName UniformList.operations where
  State := State a
  Denotes := Denotes a
  proofExtension := proofExtension a
  objectExtension := objectExtension a
  proofVariable := proofVariable a
  proofWeakening := proofWeakening a
  objectWeakening := objectWeakening a
  implicationIntro := by
    intro _ _ _ _ _ _ _ state _ bodyMeaning
    exact implicationIntro a state bodyMeaning
  implicationElim := implicationElim a
  universalIntro := universalIntro a
  universalElim := universalElim a
  reflexivity := reflexivity a
  symmetry := symmetry a
  transitivity := transitivity a
  propositionExtensionality := propositionExtensionality a
  propositionForward := propositionForward a
  functionCongruence := functionCongruence a
  argumentCongruence := argumentCongruence a
  lambdaCongruence := lambdaCongruence a
  functionExtensionality := functionExtensionality a
  beta := beta a
  eta := eta a

/-- Every successful output of the one generic compiler has the exact Aczel
trace proof-family denotation of its retained source conclusion. -/
theorem compile_denotes (a : ZFSet.{u})
    {gamma : SourceContext} {delta : List (Formula gamma)}
    {conclusion : Formula gamma}
    (source : HOL.ProofSyntax Symbol delta conclusion)
    {n : Nat} {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n} {native : Tower.Tm n}
    (success : compile FormationSensitiveHOLLeibnizInterface.signature
      UniformList.proofName UniformList.operations source objects hypotheses =
        some native)
    (state : State a objects)
    (hypothesesMeaning : ∀ index,
      Denotes a state (hypotheses index) (delta.get index)) :
    Denotes a state native conclusion := by
  apply GenericSemantics.compile_denotes
    FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
    UniformList.operations (algebra a) source success state
  exact hypothesesMeaning

/-! ## Retained map-fusion proof and a wrong-target control -/

namespace Controls

open HOL.UniformListMapFusion
open ZFSetUniformListTraceTermInterpretation
open Mettapedia.Logic.HOL.Embedding.ZFSetUniformListTraceProofBridge
open ZFSetContextualIdentity

/-- The meaning of a closed source formula in the uniform-List trace model. -/
def closedFormulaMeaning (a : ZFSet.{u})
    (formula : Formula []) : Prop :=
  ZFSetHOLTypeInterpretation.holds
    (ZFSetUniformListTraceTermInterpretation.interpret formula
      (ZFSetUniformListTraceTermInterpretation.emptyValuation :
        ZFSetUniformListTraceTermInterpretation.Valuation a []))

/-- A semantic telescope for an arbitrary ordered list of closed source
assumptions.  Native de Bruijn index `i` denotes source assumption `i`. -/
noncomputable def proofContext (a : ZFSet.{u}) :
    (delta : List (Formula [])) → Context.{u} delta.length
  | [] => Context.nil
  | formula :: tail =>
      let prior := proofContext a tail
      prior.snoc (fun _ =>
        ZFSetTraceProofDecoding.truthCode (closedFormulaMeaning a formula))

theorem proofContext_family (a : ZFSet.{u})
    (delta : List (Formula [])) (index : Fin delta.length)
    (environment : (proofContext a delta).Environment) :
    (proofContext a delta).family index environment =
      ZFSetTraceProofDecoding.truthCode
        (closedFormulaMeaning a (delta.get index)) := by
  induction delta with
  | nil => exact Fin.elim0 index
  | cons formula tail inductionHypothesis =>
      refine Fin.cases ?_ (fun prior => ?_) index
      · rfl
      · exact inductionHypothesis prior environment.1

/-- The displayed state for closed source terms under an arbitrary source
proof context.  There are no object variables to realize, so only the proof
telescope has semantic content. -/
noncomputable def assumptionState (a : ZFSet.{u})
    (delta : List (Formula [])) :
    State a (gamma := []) (n := delta.length) Fin.elim0 where
  context := proofContext a delta
  valuation := fun _ =>
    (ZFSetUniformListTraceTermInterpretation.emptyValuation :
      ZFSetUniformListTraceTermInterpretation.Valuation a [])
  objectsDenote := by
    intro type index
    exact nomatch index

/-- Every native variable in the semantic telescope denotes the corresponding
source assumption.  This is the non-vacuous premise needed by the compiler
fusion theorem. -/
theorem assumptionHypotheses (a : ZFSet.{u})
    (delta : List (Formula [])) :
    ∀ index, Denotes a (assumptionState a delta) (.var index)
      (delta.get index) := by
  intro index
  apply NativeHOLTraceQualifiedExtensionalSemantics.ProofDenotes.ofMixed
  let context := proofContext a delta
  have familyEquality : context.family index =
      ZFSetTraceProofDecoding.truthFamily
        (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning
          (delta.get index) context
          (fun _ =>
            (ZFSetUniformListTraceTermInterpretation.emptyValuation :
              ZFSetUniformListTraceTermInterpretation.Valuation a []))) := by
    funext environment
    exact proofContext_family a delta index environment
  have variableMeaning := NativeHOLTraceMixedTermSemantics.Denotes.variable
    (a := a) context index
  exact ⟨_, variableMeaning.cast_family familyEquality⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem mapFusion_compiles :
    (compile FormationSensitiveHOLLeibnizInterface.signature
      UniformList.proofName UniformList.operations
      (HOL.UniformListMapFusion.mapFusionProof (Γ := []))
      (n := 5) Fin.elim0 (fun index => .var index)).isSome = true := by
  decide

/-- The actual output of the signature-generic compiler on the retained
induction proof, before its five theory assumptions are abstracted. -/
def mapFusionNative : Tower.Tm 5 :=
  (compile FormationSensitiveHOLLeibnizInterface.signature
    UniformList.proofName UniformList.operations
    (HOL.UniformListMapFusion.mapFusionProof (Γ := []))
    (n := 5) Fin.elim0 (fun index => .var index)).get mapFusion_compiles

theorem compiler_emits_mapFusionNative :
    compile FormationSensitiveHOLLeibnizInterface.signature
      UniformList.proofName UniformList.operations
      (HOL.UniformListMapFusion.mapFusionProof (Γ := []))
      Fin.elim0 (fun index => .var index) = some mapFusionNative :=
  (Option.some_get mapFusion_compiles).symm

/-- The retained induction proof crosses the one generic compiler and denotes
map fusion itself under the exact five assumptions it actually uses. -/
theorem mapFusionNative_denotes (a : ZFSet.{u}) :
    Denotes a (assumptionState a (theory (Γ := []))) mapFusionNative
      (HOL.UniformListMapFusion.mapFusion (Γ := [])) := by
  exact compile_denotes a
    (HOL.UniformListMapFusion.mapFusionProof (Γ := []))
    compiler_emits_mapFusionNative
    (assumptionState a (theory (Γ := [])))
    (assumptionHypotheses a (theory (Γ := [])))

/-- Actual witnesses for a semantic telescope, provided only when every
source assumption is true in the trace model. -/
noncomputable def proofContextEnvironment (a : ZFSet.{u}) :
    (delta : List (Formula [])) →
      (∀ formula ∈ delta, closedFormulaMeaning a formula) →
        (proofContext a delta).Environment
  | [], _ => PUnit.unit
  | formula :: tail, valid =>
      let priorValid : ∀ entry ∈ tail, closedFormulaMeaning a entry :=
        fun entry member => valid entry (List.mem_cons_of_mem formula member)
      let prior := proofContextEnvironment a tail priorValid
      let witness : Elements
          (ZFSetTraceProofDecoding.truthCode (closedFormulaMeaning a formula)) :=
        ⟨∅, (ZFSetTraceProofDecoding.mem_truthCode _ ∅).mpr
          ⟨rfl, valid formula (by simp)⟩⟩
      ⟨prior, witness⟩

theorem uniformTheory_valid (a : ZFSet.{u})
    (formula : Formula []) (member : formula ∈ theory) :
    closedFormulaMeaning a formula := by
  unfold closedFormulaMeaning
  apply (formula_agreement formula
    (ZFSetUniformListTraceTermInterpretation.emptyValuation :
      ZFSetUniformListTraceTermInterpretation.Valuation a [])).mpr
  refine Eq.mp ?_ (ZFSetUniformListModel.theory_valid a formula member)
  unfold HOL.HenkinModel.models HOL.PreModel.models
  apply congrArg ULift.down
  apply congrArg (HOL.PreModel.denote (ZFSetUniformListModel.model a).toPreModel formula)
  funext type index
  exact nomatch index

noncomputable def theoryEnvironment (a : ZFSet.{u}) :
    (proofContext a (theory (Γ := []))).Environment :=
  proofContextEnvironment a theory (uniformTheory_valid a)

/-- Wrong-target control: even the successful map-fusion compiler output
cannot be assigned the reversed-composition formula in the same model and
under the same source theory assumptions. -/
theorem mapFusionNative_not_wrongFusion :
    ¬ Denotes ZFSetUniformListProofConsumption.Controls.two
      (assumptionState ZFSetUniformListProofConsumption.Controls.two
        (theory (Γ := [])))
      mapFusionNative
      (HOL.UniformListMapFusion.Controls.wrongFusion (Γ := [])) := by
  intro wrongMeaning
  unfold Denotes at wrongMeaning
  obtain ⟨proofSection, _⟩ := wrongMeaning
  apply wrongFusion_trace_uninhabited
  refine ⟨?_⟩
  exact proofSection
    (theoryEnvironment ZFSetUniformListProofConsumption.Controls.two)

/-- The concrete semantic section retained by the generic compiler theorem. -/
noncomputable def mapFusionProofSection (a : ZFSet.{u}) :
    Section (ZFSetTraceProofDecoding.truthFamily
      (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning
        (HOL.UniformListMapFusion.mapFusion (Γ := []))
        (proofContext a (theory (Γ := [])))
        (fun _ =>
          (ZFSetUniformListTraceTermInterpretation.emptyValuation :
            ZFSetUniformListTraceTermInterpretation.Valuation a [])))) :=
  Classical.choose (mapFusionNative_denotes a)

theorem mapFusionProofSection_denoted (a : ZFSet.{u}) :
    NativeHOLTraceQualifiedExtensionalSemantics.Denotes a
      (proofContext a (theory (Γ := []))) mapFusionNative
      (ZFSetTraceProofDecoding.truthFamily
        (NativeHOLTraceLeibnizCompilerSemantics.formulaMeaning
          (HOL.UniformListMapFusion.mapFusion (Γ := []))
          (proofContext a (theory (Γ := [])))
          (fun _ =>
            (ZFSetUniformListTraceTermInterpretation.emptyValuation :
              ZFSetUniformListTraceTermInterpretation.Valuation a []))))
      (mapFusionProofSection a) :=
  Classical.choose_spec (mapFusionNative_denotes a)

/-- Evaluating the retained native section at the five genuine source-theory
witnesses yields the universal map-fusion proof value. -/
noncomputable def compiledMapFusionRoot (a : ZFSet.{u}) :
    Elements (truthFibre
      (HOL.UniformListMapFusion.mapFusion (Γ := []))
      (ZFSetUniformListTraceTermInterpretation.emptyValuation :
        ZFSetUniformListTraceTermInterpretation.Valuation a [])) :=
  mapFusionProofSection a (theoryEnvironment a)

/-- Three source-level universal eliminations instantiate the compiler's
retained proof at two functions and one list. -/
noncomputable def compiledFusionProofValue {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence) :
    Elements (truthFibre fusionBody (fusionValuation f g xs)) := by
  let root := compiledMapFusionRoot a
  let atFunction := universalValueApp
    ZFSetUniformListTraceTermInterpretation.emptyValuation root f
  let atSecond := universalValueApp
    (ZFSetUniformListTraceTermInterpretation.extend
      ZFSetUniformListTraceTermInterpretation.emptyValuation f) atFunction g
  let atSequence := universalValueApp
    (ZFSetUniformListTraceTermInterpretation.extend
      (ZFSetUniformListTraceTermInterpretation.extend
        ZFSetUniformListTraceTermInterpretation.emptyValuation f) g)
    atSecond xs
  exact atSequence

/-- The instantiated compiler witness inhabits the contextual identity fibre
of the two map programs. -/
noncomputable def compiledFusionIdentityWitness {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence) :
    Elements (identityFamily (sequenceFamily a)
      (beforeSection f g xs) (afterSection f g xs) PUnit.unit) :=
  ⟨(compiledFusionProofValue f g xs).1,
    fusion_fibre_identity f g xs ▸
      (compiledFusionProofValue f g xs).2⟩

noncomputable def compiledFusionIdentityPoint {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence) :
    formation.identityContext (sequenceFamily a) :=
  ⟨⟨⟨PUnit.unit, beforeSection f g xs PUnit.unit⟩,
      afterSection f g xs PUnit.unit⟩,
    compiledFusionIdentityWitness f g xs⟩

/-- Full dependent identity elimination consumes the equality produced by the
one generic compiler and semantic algebra. -/
noncomputable def consumeCompiledFusionEquality {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence)
    (motive : SetFamily (formation.identityContext (sequenceFamily a)))
    (base : Section (codedCwf.tySub motive
      (elimination.reflexivitySubstitution (sequenceFamily a)))) :
    Elements (motive (compiledFusionIdentityPoint f g xs)) :=
  elimination.j motive base (compiledFusionIdentityPoint f g xs)

noncomputable def compiledConsumedEndpoint {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence) :
    Elements (endpointMotive (compiledFusionIdentityPoint f g xs)) :=
  consumeCompiledFusionEquality f g xs endpointMotive endpointBase

theorem compiledConsumedEndpoint_value {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence) :
    (compiledConsumedEndpoint f g xs).1 =
      (compiledFusionIdentityPoint f g xs).1.1.2.1 :=
  endpointMotive_value (compiledConsumedEndpoint f g xs)

#print axioms proofContext_family
#print axioms assumptionHypotheses
#print axioms mapFusion_compiles
#print axioms compiler_emits_mapFusionNative
#print axioms mapFusionNative_denotes
#print axioms uniformTheory_valid
#print axioms mapFusionNative_not_wrongFusion
#print axioms mapFusionProofSection_denoted
#print axioms compiledMapFusionRoot
#print axioms compiledFusionProofValue
#print axioms consumeCompiledFusionEquality
#print axioms compiledConsumedEndpoint_value

end Controls

#print axioms proofVariable
#print axioms proofWeakening
#print axioms objectWeakening
#print axioms implicationIntro
#print axioms implicationElim
#print axioms universalIntro
#print axioms universalElim
#print axioms representedObject
#print axioms reflexivity
#print axioms symmetry
#print axioms transitivity
#print axioms propositionExtensionality
#print axioms propositionForward
#print axioms functionCongruence
#print axioms argumentCongruence
#print axioms representedLambda
#print axioms etaExpansion
#print axioms lambdaCongruence
#print axioms functionExtensionality
#print axioms beta
#print axioms eta
#print axioms algebra
#print axioms compile_denotes

end UniformListSemantics
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler
