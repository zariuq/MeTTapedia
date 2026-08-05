import Mettapedia.GSLT.LanguageDef.CanonicalSection

/-!
# Supported substitution for authored contextual equations

This module relates two support-indexed structural substitutions without
introducing another syntax or equation theory.  The source typing derivation
provides every variable lookup, while the pointwise hypothesis is stable under
the exact de Bruijn weakening performed when an assigned value crosses
additional binders.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open EquationSemantics

namespace ReflectiveContextSupport

/-- Transport a structural one-hole context through reflective supported
substitution.  The second component is the exact quotation-aware binder depth
at the transported hole.  Keeping that depth as output is load-bearing:
quotation resets it, whereas ordinary binders extend it. -/
def substituteContextAt (language : LanguageDef)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment) :
    Nat → OneHoleContext → OneHoleContext × Nat
  | availableDepth, .hole => (.hole, availableDepth)
  | availableDepth, .apply constructor before inner after =>
      let childDepth :=
        if isQuoteConstructor language constructor then 0 else availableDepth
      let transported := substituteContextAt language support assignment
        childDepth inner
      (.apply constructor
          (before.map (substituteAt language support assignment childDepth))
          transported.1
          (after.map (substituteAt language support assignment childDepth)),
        transported.2)
  | availableDepth, .lambda binder inner =>
      let transported := substituteContextAt language support assignment
        (availableDepth + 1) inner
      (.lambda binder transported.1, transported.2)
  | availableDepth, .multiLambda arity binders inner =>
      let transported := substituteContextAt language support assignment
        (availableDepth + arity) inner
      (.multiLambda arity binders transported.1, transported.2)
  | availableDepth, .substBody inner replacement =>
      let transported := substituteContextAt language support assignment
        (availableDepth + 1) inner
      (.substBody transported.1
          (substituteAt language support assignment availableDepth replacement),
        transported.2)
  | availableDepth, .substReplacement body inner =>
      let transported := substituteContextAt language support assignment
        availableDepth inner
      (.substReplacement
          (substituteAt language support assignment (availableDepth + 1) body)
          transported.1,
        transported.2)
  | availableDepth, .collection collectionType before inner after rest =>
      let transported := substituteContextAt language support assignment
        availableDepth inner
      (.collection collectionType
          (before.map
            (substituteAt language support assignment availableDepth))
          transported.1
          (after.map
            (substituteAt language support assignment availableDepth)) rest,
        transported.2)

/-- Substitution through a filled context is exactly filling the transported
context with the hole term substituted at the transported hole depth. -/
theorem substituteAt_fill (language : LanguageDef)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment) (availableDepth : Nat)
    (context : OneHoleContext) (pattern : Pattern) :
    substituteAt language support assignment availableDepth
        (context.fill pattern) =
      let transported :=
        substituteContextAt language support assignment availableDepth context
      transported.1.fill
        (substituteAt language support assignment transported.2 pattern) := by
  induction context generalizing availableDepth with
  | hole => rfl
  | apply constructor before inner after inductionHypothesis =>
      simp only [OneHoleContext.fill, substituteAt, List.map_append, List.map_cons,
        substituteContextAt]
      split <;> simp only [inductionHypothesis]
  | lambda binder inner inductionHypothesis =>
      simp only [OneHoleContext.fill, substituteAt, substituteContextAt,
        inductionHypothesis]
  | multiLambda arity binders inner inductionHypothesis =>
      simp only [OneHoleContext.fill, substituteAt, substituteContextAt,
        inductionHypothesis]
  | substBody inner replacement inductionHypothesis =>
      simp only [OneHoleContext.fill, substituteAt, substituteContextAt,
        inductionHypothesis]
  | substReplacement body inner inductionHypothesis =>
      simp only [OneHoleContext.fill, substituteAt, substituteContextAt,
        inductionHypothesis]
  | collection collectionType before inner after rest inductionHypothesis =>
      simp only [OneHoleContext.fill, substituteAt, List.map_append, List.map_cons,
        substituteContextAt, inductionHypothesis]

end ReflectiveContextSupport

namespace EquationSemantics

/-- Compose one authored generator with a syntax-derived outer context without
passing through the contextual-equivalence closure. -/
private theorem equationContextStep_fillDirect
    {base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator}
    {language : LanguageDef} (context : OneHoleContext)
    {left right : Pattern}
    (step : EquationContextStep base language left right) :
    EquationContextStep base language (context.fill left) (context.fill right) := by
  cases step with
  | inContext inner equationWitness =>
      simpa [OneHoleContext.fill_comp] using
        (EquationContextStep.inContext (context.comp inner) equationWitness)
  | reflectiveInContext inner membership representatives =>
      simpa [OneHoleContext.fill_comp] using
        (EquationContextStep.reflectiveInContext (context.comp inner)
          membership representatives)

/-- If both root generator families survive support-aware substitution as
single generators, then every contextual generator survives as one generator.
The transported context retains the exact quote-aware depth at its hole. -/
theorem equationContextStep_substituteAt_of_generatorRoots
    {base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator}
    {language : LanguageDef}
    {support : ContextSupport.Support}
    {assignment : ContextSupport.Assignment}
    (equationInstancePreserves : ∀ availableDepth {left right},
      EquationInstance base language left right →
        EquationContextStep base language
          (ReflectiveContextSupport.substituteAt language support assignment
            availableDepth left)
          (ReflectiveContextSupport.substituteAt language support assignment
            availableDepth right))
    (reflectivePreserves : ∀ availableDepth
      {declaration : ReflectivePresentationDecl} {left right},
      declaration ∈ language.reflectivePresentations →
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          declaration left =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          declaration right →
        EquationContextStep base language
          (ReflectiveContextSupport.substituteAt language support assignment
            availableDepth left)
          (ReflectiveContextSupport.substituteAt language support assignment
            availableDepth right))
    (availableDepth : Nat) {left right : Pattern}
    (step : EquationContextStep base language left right) :
    EquationContextStep base language
      (ReflectiveContextSupport.substituteAt language support assignment
        availableDepth left)
      (ReflectiveContextSupport.substituteAt language support assignment
        availableDepth right) := by
  cases step with
  | @inContext context redex contractum equationWitness =>
      let transported := ReflectiveContextSupport.substituteContextAt
        language support assignment availableDepth context
      have root := equationInstancePreserves transported.2 equationWitness
      have filled := equationContextStep_fillDirect transported.1 root
      simpa only [ReflectiveContextSupport.substituteAt_fill] using filled
  | @reflectiveInContext context declaration left right membership representatives =>
      let transported := ReflectiveContextSupport.substituteContextAt
        language support assignment availableDepth context
      have root := reflectivePreserves transported.2 membership representatives
      have filled := equationContextStep_fillDirect transported.1 root
      simpa only [ReflectiveContextSupport.substituteAt_fill] using filled

/-- Once root equation instances and reflective representative equalities are
known to survive substitution at every quotation-aware depth, contextual
closure survives automatically.  The structural context is transported by
`ReflectiveContextSupport.substituteContextAt`; no extra congruence policy is
assumed. -/
theorem equationContextStep_substituteAt_of_root
    {base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator}
    {language : LanguageDef}
    {support : ContextSupport.Support}
    {assignment : ContextSupport.Assignment}
    (equationInstancePreserves : ∀ availableDepth {left right},
      EquationInstance base language left right →
        EquationEquiv base language
          (ReflectiveContextSupport.substituteAt language support assignment
            availableDepth left)
          (ReflectiveContextSupport.substituteAt language support assignment
            availableDepth right))
    (reflectivePreserves : ∀ availableDepth
      {declaration : ReflectivePresentationDecl} {left right},
      declaration ∈ language.reflectivePresentations →
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          declaration left =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          declaration right →
        EquationEquiv base language
          (ReflectiveContextSupport.substituteAt language support assignment
            availableDepth left)
          (ReflectiveContextSupport.substituteAt language support assignment
            availableDepth right))
    (availableDepth : Nat) {left right : Pattern}
    (step : EquationContextStep base language left right) :
    EquationEquiv base language
      (ReflectiveContextSupport.substituteAt language support assignment
        availableDepth left)
      (ReflectiveContextSupport.substituteAt language support assignment
        availableDepth right) := by
  cases step with
  | @inContext context redex contractum equationWitness =>
      let transported := ReflectiveContextSupport.substituteContextAt
        language support assignment availableDepth context
      have root := equationInstancePreserves transported.2 equationWitness
      have filled := equationEquiv_fill transported.1 root
      simpa only [ReflectiveContextSupport.substituteAt_fill] using filled
  | @reflectiveInContext context declaration left right membership representatives =>
      let transported := ReflectiveContextSupport.substituteContextAt
        language support assignment availableDepth context
      have root := reflectivePreserves transported.2 membership representatives
      have filled := equationEquiv_fill transported.1 root
      simpa only [ReflectiveContextSupport.substituteAt_fill] using filled

/-- Generator preservation at every quotation-aware depth lifts to the full
least contextual equivalence at that depth. -/
theorem equationEquiv_substituteAt_of_root
    {base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator}
    {language : LanguageDef}
    {support : ContextSupport.Support}
    {assignment : ContextSupport.Assignment}
    (equationInstancePreserves : ∀ availableDepth {left right},
      EquationInstance base language left right →
        EquationEquiv base language
          (ReflectiveContextSupport.substituteAt language support assignment
            availableDepth left)
          (ReflectiveContextSupport.substituteAt language support assignment
            availableDepth right))
    (reflectivePreserves : ∀ availableDepth
      {declaration : ReflectivePresentationDecl} {left right},
      declaration ∈ language.reflectivePresentations →
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          declaration left =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          declaration right →
        EquationEquiv base language
          (ReflectiveContextSupport.substituteAt language support assignment
            availableDepth left)
          (ReflectiveContextSupport.substituteAt language support assignment
            availableDepth right))
    (availableDepth : Nat) {left right : Pattern}
    (equivalent : EquationEquiv base language left right) :
    EquationEquiv base language
      (ReflectiveContextSupport.substituteAt language support assignment
        availableDepth left)
      (ReflectiveContextSupport.substituteAt language support assignment
        availableDepth right) := by
  exact equationEquiv_map_of_contextStep
    (ReflectiveContextSupport.substituteAt language support assignment
      availableDepth)
    (equationContextStep_substituteAt_of_root equationInstancePreserves
      reflectivePreserves availableDepth)
    equivalent

/-- One contextual generator remains a single generator after composition
with another syntax-derived context. -/
theorem equationContextStep_fill
    {base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator}
    {language : LanguageDef} (context : OneHoleContext)
    {left right : Pattern}
    (step : EquationContextStep base language left right) :
    EquationContextStep base language (context.fill left) (context.fill right) := by
  exact equationContextStep_fillDirect context step

end EquationSemantics

namespace WellSorted

/-! ## The exact support-safe equation carrier -/

mutual
  /-- Every typed term is safe for the support assignment that declares each
  free parameter independent of surrounding binders.  This is shared
  support infrastructure, not a Cost-specific fact. -/
  theorem HasType.reflectiveSupportSafeAt_empty
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType language free bound pattern type)
      (available : List TypeExpr) :
      typed.ReflectiveSupportSafeAt (fun _ => []) available := by
    cases typed with
    | bvar lookup => exact .bvar lookup available
    | fvar lookup => exact .fvar lookup available ⟨available, by simp⟩
    | @constructor bound rule arguments membership notBare argumentsTyped =>
        by_cases quoted : ReflectiveContextSupport.isQuoteConstructor
            language rule.label = true
        · exact .constructorQuote (membership := membership)
            (notBare := notBare) quoted
            (argumentsTyped.reflectiveSupportSafeAt_empty [])
        · exact .constructorOrdinary (membership := membership)
            (notBare := notBare) (Bool.eq_false_of_not_eq_true quoted)
            (argumentsTyped.reflectiveSupportSafeAt_empty available)
    | lambda bodyTyped =>
        exact .lambda
          (bodyTyped.reflectiveSupportSafeAt_empty (_ :: available))
    | @multiLambda bound arity binders body domain codomain bodyTyped =>
        exact .multiLambda
          (bodyTyped.reflectiveSupportSafeAt_empty
            (List.replicate arity domain ++ available))
    | subst bodyTyped replacementTyped =>
        exact .subst
          (bodyTyped.reflectiveSupportSafeAt_empty (_ :: available))
          (replacementTyped.reflectiveSupportSafeAt_empty available)
    | collection elementsTyped =>
        exact .collection
          (elementsTyped.reflectiveSupportSafeAt_empty available)
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType membership parameterShape elementsTyped =>
        exact .collectionConstructor (membership := membership)
          (parameterShape := parameterShape)
          (elementsTyped.reflectiveSupportSafeAt_empty available)

  /-- Argument-spine companion to empty reflective support. -/
  theorem ArgumentsHaveTypes.reflectiveSupportSafeAt_empty
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free bound arguments parameters)
      (available : List TypeExpr) :
      typed.ReflectiveSupportSafeAt (fun _ => []) available := by
    cases typed with
    | nil => exact .nil _ available
    | cons representation parameterType argumentTyped argumentsTyped =>
        exact .cons (representation := representation)
          (parameterType := parameterType)
          (argumentTyped.reflectiveSupportSafeAt_empty available)
          (argumentsTyped.reflectiveSupportSafeAt_empty available)

  /-- Collection-spine companion to empty reflective support. -/
  theorem ElementsHaveType.reflectiveSupportSafeAt_empty
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (typed : ElementsHaveType language free bound elements elementType)
      (available : List TypeExpr) :
      typed.ReflectiveSupportSafeAt (fun _ => []) available := by
    cases typed with
    | nil => exact .nil _ _ available
    | cons elementTyped elementsTyped =>
        exact .cons
          (elementTyped.reflectiveSupportSafeAt_empty available)
          (elementsTyped.reflectiveSupportSafeAt_empty available)
end

/-- Concatenate two independently typed constructor-argument spines.  This
is the proof-relevant list operation used by one-position congruence; it
retains the authored parameter order rather than rechecking a raw list. -/
theorem ArgumentsHaveTypes.append
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr}
    {leftArguments rightArguments : List Pattern}
    {leftParameters rightParameters : List TermParam}
    (left : ArgumentsHaveTypes language free bound leftArguments leftParameters)
    (right : ArgumentsHaveTypes language free bound rightArguments
      rightParameters) :
    ArgumentsHaveTypes language free bound
      (leftArguments ++ rightArguments) (leftParameters ++ rightParameters) := by
  induction leftArguments generalizing leftParameters with
  | nil =>
      cases left
      simpa using right
  | cons argument arguments inductionHypothesis =>
      cases left with
      | cons representation parameterType argumentTyped argumentsTyped =>
          exact .cons representation parameterType argumentTyped
            (inductionHypothesis argumentsTyped)

/-- Rebuild an authored application after replacing exactly one argument by
another inhabitant of the same declared parameter fiber.  Prefix and suffix
typing derivations are reused verbatim, so the theorem localizes all
dependent list transport to one position. -/
theorem HasType.applyUpdateOne
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {rule : GrammarRule}
    {before after : List Pattern}
    {beforeParameters afterParameters : List TermParam}
    {parameter : TermParam} {replacement : Pattern} {expected : TypeExpr}
    (membership : rule ∈ language.terms)
    (notBare : ¬ UsesBareCollection rule)
    (parameterShape : rule.params =
      beforeParameters ++ parameter :: afterParameters)
    (beforeTyped : ArgumentsHaveTypes language free bound before
      beforeParameters)
    (representation : MatchesParameterRepresentation parameter replacement)
    (parameterType : parameterType? parameter = some expected)
    (replacementTyped : HasType language free bound replacement expected)
    (afterTyped : ArgumentsHaveTypes language free bound after afterParameters) :
    HasType language free bound
      (.apply rule.label (before ++ replacement :: after))
      (.base rule.category) := by
  apply HasType.constructor membership notBare
  rw [parameterShape]
  exact beforeTyped.append
    (.cons representation parameterType replacementTyped afterTyped)

/-- Every constructor returning the name sort of an authored reflective
presentation is itself that presentation's quotation boundary, and therefore
cannot use the bare-collection representation.

This is a structural signature condition, not substitution stability stated
as an assumption.  It excludes the precise binder-occurrence counterexample
in which an ordinary constructor returns a name while one of its arguments
introduces another equal-typed name binder. -/
def ReflectiveNameResultSealed (language : LanguageDef) : Prop :=
  ∀ (declaration : ReflectivePresentationDecl),
    declaration ∈ language.reflectivePresentations →
      ∀ (rule : GrammarRule), rule ∈ language.terms →
        rule.category = declaration.nameSort →
          rule.label = declaration.quoteConstructor ∧
            ¬ UsesBareCollection rule

/-- Every constructor returning a reflective name sort is some quotation
boundary of the same authored language, though not necessarily the quotation
constructor of the declaration that shares that result sort.

This weaker condition is the one stable under the two-colour Cost
construction: distinct coloured quotation declarations may share the image of
a non-interacting name sort, while both labels remain genuine quotation
boundaries. -/
def ReflectiveNameResultsQuoted (language : LanguageDef) : Prop :=
  ∀ (declaration : ReflectivePresentationDecl),
    declaration ∈ language.reflectivePresentations →
      ∀ (rule : GrammarRule), rule ∈ language.terms →
        rule.category = declaration.nameSort →
          ReflectiveContextSupport.isQuoteConstructor language rule.label =
              true ∧
            ¬ UsesBareCollection rule

/-- Canonicalization of a well-sorted process may expose the selected Drop
constructor only with a name argument that remains in the same exact typing
and reflective-support fiber.  This is the weakest support-preservation fact
needed by Quote/Drop substitution: it does not require canonicalization to
preserve arbitrary collection-typed terms. -/
def ReflectiveDropCanonicalSupportStable (language : LanguageDef) : Prop :=
  ∀ (declaration : ReflectivePresentationDecl),
    declaration ∈ language.reflectivePresentations →
      ∀ {free : FreeTypeContext} {support : ContextSupport.Support}
        {bound available : List TypeExpr} {pattern name : Pattern}
        {binderImage : TypeExpr → TypeExpr}
        (typed : HasType language free bound pattern
          (.base declaration.processSort)),
        typed.ReflectiveSupportSafeAt support available binderImage →
        isObjectPattern pattern = true →
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
            pattern = .apply declaration.dropConstructor [name] →
          ∃ nameTyped : HasType language free bound name
              (.base declaration.nameSort),
            nameTyped.ReflectiveSupportSafeAt support available binderImage ∧
              isObjectPattern name = true

/-- The single-declaration sealing condition implies the language-wide quote
boundary condition. -/
theorem ReflectiveNameResultSealed.resultsQuoted
    {language : LanguageDef} (sealed : ReflectiveNameResultSealed language) :
    ReflectiveNameResultsQuoted language := by
  intro declaration declarationMembership rule ruleMembership categoryEquality
  have sealedRule := sealed declaration declarationMembership rule
    ruleMembership categoryEquality
  refine ⟨?_, sealedRule.2⟩
  simp only [ReflectiveContextSupport.isQuoteConstructor, List.any_eq_true]
  exact ⟨declaration, declarationMembership, by simp [sealedRule.1]⟩

/-- Invert the exact unary process argument of one selected, validated quote
constructor while keeping its reflective-support witness attached to the
typing derivation it certifies. -/
theorem ArgumentsHaveTypes.selectedQuoteArgument
    {language : LanguageDef} (valid : language.validate = [])
    {free : FreeTypeContext} {support : ContextSupport.Support}
    {bound available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    {declaration : ReflectivePresentationDecl}
    (declarationMembership : declaration ∈ language.reflectivePresentations)
    {rule : GrammarRule} {arguments : List Pattern}
    (membership : rule ∈ language.terms)
    (selected : rule.label = declaration.quoteConstructor)
    (typed : ArgumentsHaveTypes language free bound arguments rule.params)
    (safe : typed.ReflectiveSupportSafeAt support available binderImage) :
    ∃ (argument : Pattern)
        (argumentTyped : HasType language free bound argument
          (.base declaration.processSort)),
      arguments = [argument] ∧
        argumentTyped.ReflectiveSupportSafeAt support available binderImage := by
  have declarationValid :=
    LanguageDef.reflectivePresentation_validate_of_validate_eq_nil language
      valid declaration declarationMembership
  obtain ⟨witness⟩ :=
    LanguageDef.reflectivePresentationWitness_of_validate_eq_nil language
      declaration declarationValid
  have quoteFiltered : witness.quote ∈
      language.terms.filter
        (fun candidate => candidate.label == declaration.quoteConstructor) := by
    rw [witness.quoteUnique]
    simp
  have quoteMembership : witness.quote ∈ language.terms :=
    (List.mem_filter.mp quoteFiltered).1
  have quoteLabel : witness.quote.label = rule.label :=
    (beq_iff_eq.mp (List.mem_filter.mp quoteFiltered).2).trans selected.symm
  have ruleEquality : witness.quote = rule :=
    List.inj_on_of_nodup_map
      (LanguageDef.constructorLabels_nodup_of_validate_eq_nil language valid)
      quoteMembership membership quoteLabel
  have argumentsLength : arguments.length = 1 := by
    calc
      arguments.length = rule.params.length := typed.length_eq
      _ = witness.quote.params.length := by rw [ruleEquality.symm]
      _ = 1 := by simp [witness.quoteParameters]
  obtain ⟨argument, argumentsShape⟩ := List.length_eq_one_iff.mp argumentsLength
  subst arguments
  have parameterShape : rule.params =
      [.simple witness.quoteParameter (.base declaration.processSort)] := by
    rw [← ruleEquality, witness.quoteParameters]
  have exactTyped : ArgumentsHaveTypes language free bound [argument]
      [.simple witness.quoteParameter (.base declaration.processSort)] := by
    simpa only [parameterShape] using typed
  have exactSafe : exactTyped.ReflectiveSupportSafeAt support available
      binderImage := by
    apply ArgumentsHaveTypes.ReflectiveSupportSafeAt.castTyping
    simpa only [parameterShape] using safe
  cases exactTyped with
  | @cons _ argument arguments parameter parameters expected representation
      parameterType argumentTyped tailTyped =>
      cases tailTyped
      have expectedEquality : expected = .base declaration.processSort := by
        simpa [parameterType?] using parameterType.symm
      subst expected
      let emptyTyped : ArgumentsHaveTypes language free bound [] [] := .nil
      let exactSpine := ArgumentsHaveTypes.cons representation parameterType
        argumentTyped emptyTyped
      have exactSpineSafe : exactSpine.ReflectiveSupportSafeAt support available
          binderImage :=
        ArgumentsHaveTypes.ReflectiveSupportSafeAt.castTyping
          (target := exactSpine) exactSafe
      exact ⟨argument, argumentTyped, rfl,
        ArgumentsHaveTypes.ReflectiveSupportSafeAt.head
          (representation := representation) (parameterType := parameterType)
          (argumentTyped := argumentTyped) (argumentsTyped := emptyTyped)
          exactSpineSafe⟩

/-- Invert a support-safe application of one selected quote constructor
without performing dependent elimination on its typing derivation.  The
argument is checked beneath the quotation reset, so its support witness is
returned at the empty available context. -/
theorem HasType.selectedQuoteArgument
    {language : LanguageDef} (valid : language.validate = [])
    {free : FreeTypeContext} {support : ContextSupport.Support}
    {bound available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    {declaration : ReflectivePresentationDecl}
    (declarationMembership : declaration ∈ language.reflectivePresentations)
    {arguments : List Pattern} {type : TypeExpr}
    (typed : HasType language free bound
      (.apply declaration.quoteConstructor arguments) type)
    (safe : typed.ReflectiveSupportSafeAt support available binderImage) :
    ∃ (argument : Pattern)
        (argumentTyped : HasType language free bound argument
          (.base declaration.processSort)),
      arguments = [argument] ∧
        argumentTyped.ReflectiveSupportSafeAt support [] binderImage := by
  exact HasType.ReflectiveSupportSafeAt.rec
    (motive_1 := fun {bound pattern type} typed available binderImage safe =>
      ∀ requestedArguments,
        pattern = .apply declaration.quoteConstructor requestedArguments →
          ∃ (argument : Pattern)
              (argumentTyped : HasType language free bound argument
                (.base declaration.processSort)),
            requestedArguments = [argument] ∧
              argumentTyped.ReflectiveSupportSafeAt support [] binderImage)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (by
      intro bound index resultType lookup sourceAvailable currentImage
        requestedArguments patternEquality
      cases patternEquality)
    (by
      intro bound name resultType lookup sourceAvailable currentImage shape
        requestedArguments patternEquality
      cases patternEquality)
    (by
      intro bound rule actualArguments membership notBare argumentsTyped
        sourceAvailable currentImage quoted argumentsSafe argumentsIH
        requestedArguments patternEquality
      injection patternEquality with labelEquality argumentsEquality
      obtain ⟨argument, argumentTyped, actualShape, argumentSafe⟩ :=
        argumentsTyped.selectedQuoteArgument valid declarationMembership
          membership labelEquality argumentsSafe
      exact ⟨argument, argumentTyped,
        argumentsEquality.symm.trans actualShape, argumentSafe⟩)
    (by
      intro bound rule actualArguments membership notBare argumentsTyped
        sourceAvailable currentImage ordinary argumentsSafe argumentsIH
        requestedArguments patternEquality
      injection patternEquality with labelEquality argumentsEquality
      have quoted : ReflectiveContextSupport.isQuoteConstructor language
          rule.label = true := by
        simp only [ReflectiveContextSupport.isQuoteConstructor,
          List.any_eq_true]
        exact ⟨declaration, declarationMembership,
          by simpa using labelEquality.symm⟩
      rw [quoted] at ordinary
      contradiction)
    (by
      intro bound binder body domain codomain bodyTyped sourceAvailable
        currentImage bodySafe bodyIH requestedArguments patternEquality
      cases patternEquality)
    (by
      intro bound arity binders body domain codomain bodyTyped sourceAvailable
        currentImage bodySafe bodyIH requestedArguments patternEquality
      cases patternEquality)
    (by
      intro bound body replacement domain codomain bodyTyped replacementTyped
        sourceAvailable currentImage bodySafe replacementSafe bodyIH replacementIH
        requestedArguments patternEquality
      cases patternEquality)
    (by
      intro bound collectionType elements rest elementType elementsTyped
        sourceAvailable currentImage elementsSafe elementsIH requestedArguments
        patternEquality
      cases patternEquality)
    (by
      intro bound rule parameterName collectionType elements rest elementType
        membership parameterShape elementsTyped sourceAvailable currentImage
        elementsSafe elementsIH requestedArguments patternEquality
      cases patternEquality)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    safe arguments rfl

/-- Invert the exact unary name argument of one selected, validated drop
constructor while keeping its reflective-support witness attached to the
typing derivation it certifies. -/
theorem ArgumentsHaveTypes.selectedDropArgument
    {language : LanguageDef} (valid : language.validate = [])
    {free : FreeTypeContext} {support : ContextSupport.Support}
    {bound available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    {declaration : ReflectivePresentationDecl}
    (declarationMembership : declaration ∈ language.reflectivePresentations)
    {rule : GrammarRule} {arguments : List Pattern}
    (membership : rule ∈ language.terms)
    (selected : rule.label = declaration.dropConstructor)
    (typed : ArgumentsHaveTypes language free bound arguments rule.params)
    (safe : typed.ReflectiveSupportSafeAt support available binderImage) :
    ∃ (argument : Pattern)
        (argumentTyped : HasType language free bound argument
          (.base declaration.nameSort)),
      arguments = [argument] ∧
        argumentTyped.ReflectiveSupportSafeAt support available binderImage := by
  have declarationValid :=
    LanguageDef.reflectivePresentation_validate_of_validate_eq_nil language
      valid declaration declarationMembership
  obtain ⟨witness⟩ :=
    LanguageDef.reflectivePresentationWitness_of_validate_eq_nil language
      declaration declarationValid
  have dropFiltered : witness.drop ∈
      language.terms.filter
        (fun candidate => candidate.label == declaration.dropConstructor) := by
    rw [witness.dropUnique]
    simp
  have dropMembership : witness.drop ∈ language.terms :=
    (List.mem_filter.mp dropFiltered).1
  have dropLabel : witness.drop.label = rule.label :=
    (beq_iff_eq.mp (List.mem_filter.mp dropFiltered).2).trans selected.symm
  have ruleEquality : witness.drop = rule :=
    List.inj_on_of_nodup_map
      (LanguageDef.constructorLabels_nodup_of_validate_eq_nil language valid)
      dropMembership membership dropLabel
  have argumentsLength : arguments.length = 1 := by
    calc
      arguments.length = rule.params.length := typed.length_eq
      _ = witness.drop.params.length := by rw [ruleEquality.symm]
      _ = 1 := by simp [witness.dropParameters]
  obtain ⟨argument, argumentsShape⟩ := List.length_eq_one_iff.mp argumentsLength
  subst arguments
  have parameterShape : rule.params =
      [.simple witness.dropParameter (.base declaration.nameSort)] := by
    rw [← ruleEquality, witness.dropParameters]
  have exactTyped : ArgumentsHaveTypes language free bound [argument]
      [.simple witness.dropParameter (.base declaration.nameSort)] := by
    simpa only [parameterShape] using typed
  have exactSafe : exactTyped.ReflectiveSupportSafeAt support available
      binderImage := by
    apply ArgumentsHaveTypes.ReflectiveSupportSafeAt.castTyping
    simpa only [parameterShape] using safe
  cases exactTyped with
  | @cons _ argument arguments parameter parameters expected representation
      parameterType argumentTyped tailTyped =>
      cases tailTyped
      have expectedEquality : expected = .base declaration.nameSort := by
        simpa [parameterType?] using parameterType.symm
      subst expected
      let emptyTyped : ArgumentsHaveTypes language free bound [] [] := .nil
      let exactSpine := ArgumentsHaveTypes.cons representation parameterType
        argumentTyped emptyTyped
      have exactSpineSafe : exactSpine.ReflectiveSupportSafeAt support available
          binderImage :=
        ArgumentsHaveTypes.ReflectiveSupportSafeAt.castTyping
          (target := exactSpine) exactSafe
      exact ⟨argument, argumentTyped, rfl,
        ArgumentsHaveTypes.ReflectiveSupportSafeAt.head
          (representation := representation) (parameterType := parameterType)
          (argumentTyped := argumentTyped) (argumentsTyped := emptyTyped)
          exactSpineSafe⟩

/-- Invert a support-safe application of one selected Drop constructor without
performing dependent elimination on its typing derivation.  The explicit
ordinary-constructor premise records the only fact needed to retain the
ambient available context while descending to the Drop argument. -/
theorem HasType.selectedOrdinaryDropArgument
    {language : LanguageDef} (valid : language.validate = [])
    {free : FreeTypeContext} {support : ContextSupport.Support}
    {bound available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    {declaration : ReflectivePresentationDecl}
    (declarationMembership : declaration ∈ language.reflectivePresentations)
    (dropOrdinary : ReflectiveContextSupport.isQuoteConstructor language
      declaration.dropConstructor = false)
    {arguments : List Pattern} {type : TypeExpr}
    (typed : HasType language free bound
      (.apply declaration.dropConstructor arguments) type)
    (safe : typed.ReflectiveSupportSafeAt support available binderImage) :
    ∃ (argument : Pattern)
        (argumentTyped : HasType language free bound argument
          (.base declaration.nameSort)),
      arguments = [argument] ∧
        argumentTyped.ReflectiveSupportSafeAt support available binderImage := by
  exact HasType.ReflectiveSupportSafeAt.rec
    (motive_1 := fun {bound pattern type} typed available binderImage safe =>
      ∀ requestedArguments,
        pattern = .apply declaration.dropConstructor requestedArguments →
          ∃ (argument : Pattern)
              (argumentTyped : HasType language free bound argument
                (.base declaration.nameSort)),
            requestedArguments = [argument] ∧
              argumentTyped.ReflectiveSupportSafeAt support available binderImage)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (by
      intro bound index resultType lookup sourceAvailable currentImage
        requestedArguments patternEquality
      cases patternEquality)
    (by
      intro bound name resultType lookup sourceAvailable currentImage shape
        requestedArguments patternEquality
      cases patternEquality)
    (by
      intro bound rule actualArguments membership notBare argumentsTyped
        sourceAvailable currentImage quoted argumentsSafe argumentsIH
        requestedArguments patternEquality
      injection patternEquality with labelEquality argumentsEquality
      have selectedQuoted : ReflectiveContextSupport.isQuoteConstructor language
          declaration.dropConstructor = true := by
        simpa [labelEquality] using quoted
      rw [dropOrdinary] at selectedQuoted
      contradiction)
    (by
      intro bound rule actualArguments membership notBare argumentsTyped
        sourceAvailable currentImage ordinary argumentsSafe argumentsIH
        requestedArguments patternEquality
      injection patternEquality with labelEquality argumentsEquality
      obtain ⟨argument, argumentTyped, actualShape, argumentSafe⟩ :=
        argumentsTyped.selectedDropArgument valid declarationMembership
          membership labelEquality argumentsSafe
      exact ⟨argument, argumentTyped,
        argumentsEquality.symm.trans actualShape, argumentSafe⟩)
    (by
      intro bound binder body domain codomain bodyTyped sourceAvailable
        currentImage bodySafe bodyIH requestedArguments patternEquality
      cases patternEquality)
    (by
      intro bound arity binders body domain codomain bodyTyped sourceAvailable
        currentImage bodySafe bodyIH requestedArguments patternEquality
      cases patternEquality)
    (by
      intro bound body replacement domain codomain bodyTyped replacementTyped
        sourceAvailable currentImage bodySafe replacementSafe bodyIH replacementIH
        requestedArguments patternEquality
      cases patternEquality)
    (by
      intro bound collectionType elements rest elementType elementsTyped
        sourceAvailable currentImage elementsSafe elementsIH requestedArguments
        patternEquality
      cases patternEquality)
    (by
      intro bound rule parameterName collectionType elements rest elementType
        membership parameterShape elementsTyped sourceAvailable currentImage
        elementsSafe elementsIH requestedArguments patternEquality
      cases patternEquality)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    safe arguments rfl

/-- A term whose reflective name result is protected by some authored quote
boundary is insensitive to the ambient substitution depth immediately below
a quote.  The particular quote declaration is irrelevant to this depth law:
all authored quote constructors reset reflective substitution uniformly. -/
theorem nameResult_substituteAt_eq_of_safeAt_zero_of_resultsQuoted
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {pattern : Pattern} {resultType : TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (quotedResults : ReflectiveNameResultsQuoted language)
    (assignment : SupportedOpenAssignment language source target support)
    (declaration : ReflectivePresentationDecl)
    (declarationMembership : declaration ∈ language.reflectivePresentations)
    (typed : HasType language source bound pattern resultType)
    (resultType_eq : resultType = .base declaration.nameSort)
    (safeAtZero : typed.ReflectiveSupportSafeAt support [] binderImage)
    (object : isObjectPattern pattern = true)
    (availableDepth : Nat) :
    ReflectiveContextSupport.substituteAt language support
        assignment.assignment 0 pattern =
      ReflectiveContextSupport.substituteAt language support
        assignment.assignment availableDepth pattern := by
  cases typed with
  | @bvar bound index type lookup =>
      simp [ReflectiveContextSupport.substituteAt]
  | @fvar bound freeName type lookup =>
      cases safeAtZero with
      | fvar _ _ shape =>
          obtain ⟨inner, shape⟩ := shape
          have emptyParts : inner = [] ∧ support freeName = [] :=
            List.append_eq_nil_iff.mp shape.symm
          have assignedScoped :
              (assignment.assignment freeName).isWellScopedAt 0 = true := by
            simpa [emptyParts.2] using (assignment.typed lookup).isWellScopedAt
          have liftZero :
              liftBVars 0 0 (assignment.assignment freeName) =
                assignment.assignment freeName :=
            liftBVars_eq_self_of_isWellScopedAt assignedScoped
          have liftAvailable :
              liftBVars 0 availableDepth (assignment.assignment freeName) =
                assignment.assignment freeName :=
            liftBVars_eq_self_of_isWellScopedAt assignedScoped
          simp [ReflectiveContextSupport.substituteAt, emptyParts.2,
            liftZero, liftAvailable]
  | @constructor bound rule arguments membership notBare argumentsTyped =>
      have categoryEquality : rule.category = declaration.nameSort := by
        simpa using resultType_eq
      have quotedRule := quotedResults declaration declarationMembership rule
        membership categoryEquality
      simp [ReflectiveContextSupport.substituteAt, quotedRule.1]
  | lambda bodyTyped => cases resultType_eq
  | multiLambda bodyTyped => cases resultType_eq
  | subst bodyTyped replacementTyped => simp [isObjectPattern] at object
  | collection elementsTyped => cases resultType_eq
  | @collectionConstructor bound rule parameterName collectionType elements rest
      elementType membership parameterShape elementsTyped =>
      have categoryEquality : rule.category = declaration.nameSort := by
        simpa using resultType_eq
      have quotedRule := quotedResults declaration declarationMembership rule
        membership categoryEquality
      apply False.elim
      exact quotedRule.2 ⟨parameterName, collectionType, elementType,
        parameterShape⟩

/-- A term of a sealed reflective name sort that is legal immediately below a
quotation boundary is insensitive to the ambient substitution depth.

The free-variable case uses support safety at the empty context to show that
the assigned value is closed with respect to de Bruijn indices.  Bound
variables are excluded by quote-aware scope safety.  Every remaining name
constructor is a quotation boundary by `ReflectiveNameResultSealed`, so both
substitutions recurse at depth zero. -/
theorem nameResult_substituteAt_eq_of_safeAt_zero
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {pattern : Pattern} {resultType : TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (sealed : ReflectiveNameResultSealed language)
    (assignment : SupportedOpenAssignment language source target support)
    (declaration : ReflectivePresentationDecl)
    (declarationMembership : declaration ∈ language.reflectivePresentations)
    (typed : HasType language source bound pattern resultType)
    (resultType_eq : resultType = .base declaration.nameSort)
    (safeAtZero : typed.ReflectiveSupportSafeAt support [] binderImage)
    (object : isObjectPattern pattern = true)
    (availableDepth : Nat) :
    ReflectiveContextSupport.substituteAt language support
        assignment.assignment 0 pattern =
      ReflectiveContextSupport.substituteAt language support
        assignment.assignment availableDepth pattern := by
  exact nameResult_substituteAt_eq_of_safeAt_zero_of_resultsQuoted
    sealed.resultsQuoted assignment declaration declarationMembership typed
      resultType_eq safeAtZero object availableDepth

/-- Supported substitution preserves the selected declaration's exact
Quote/Drop representative at every ambient depth when every constructor
returning its name sort is an authored quote boundary.  This is the
proof-relevant leaf behind the direct generator theorem below: the declaration
identity remains explicit rather than being reconstructed from an erased
contextual-equivalence proof. -/
theorem quoteDrop_substituteAt_canonicalize_eq_of_resultsQuoted
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {name : Pattern} {resultType : TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (quotedResults : ReflectiveNameResultsQuoted language)
    (assignment : SupportedOpenAssignment language source target support)
    (declaration : ReflectivePresentationDecl)
    (declarationMembership : declaration ∈ language.reflectivePresentations)
    (quote_ne_drop : declaration.quoteConstructor ≠
      declaration.dropConstructor)
    (typed : HasType language source bound name resultType)
    (resultType_eq : resultType = .base declaration.nameSort)
    (safeAtZero : typed.ReflectiveSupportSafeAt support [] binderImage)
    (object : isObjectPattern name = true)
    (availableDepth : Nat) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
        (ReflectiveContextSupport.substituteAt language support
          assignment.assignment availableDepth
          (.apply declaration.quoteConstructor
            [.apply declaration.dropConstructor [name]])) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
        (ReflectiveContextSupport.substituteAt language support
          assignment.assignment availableDepth name) := by
  have depthIndependent :=
    nameResult_substituteAt_eq_of_safeAt_zero_of_resultsQuoted quotedResults
      assignment declaration declarationMembership typed resultType_eq
      safeAtZero object availableDepth
  have quoteStatus : ReflectiveContextSupport.isQuoteConstructor language
      declaration.quoteConstructor = true := by
    simp only [ReflectiveContextSupport.isQuoteConstructor, List.any_eq_true]
    exact ⟨declaration, declarationMembership, by simp⟩
  have leftSubstitution :
      ReflectiveContextSupport.substituteAt language support
          assignment.assignment availableDepth
          (.apply declaration.quoteConstructor
            [.apply declaration.dropConstructor [name]]) =
        .apply declaration.quoteConstructor
          [.apply declaration.dropConstructor
            [ReflectiveContextSupport.substituteAt language support
              assignment.assignment 0 name]] := by
    simp [ReflectiveContextSupport.substituteAt, quoteStatus]
  rw [leftSubstitution]
  simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
    quote_ne_drop, Ne.symm quote_ne_drop]
    using congrArg
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration)
      depthIndependent

/-- The declaration-authored Quote/Drop generator remains one generator after
supported substitution at every ambient depth when every constructor returning
the declaration's name sort is an authored quote boundary.  No global
canonicalizer-naturality premise is used: support safety at the reset context
makes the substituted name itself depth-independent. -/
theorem quoteDrop_substituteAt_equationContextStep_of_resultsQuoted
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {name : Pattern} {resultType : TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (quotedResults : ReflectiveNameResultsQuoted language)
    (assignment : SupportedOpenAssignment language source target support)
    (declaration : ReflectivePresentationDecl)
    (declarationMembership : declaration ∈ language.reflectivePresentations)
    (quote_ne_drop : declaration.quoteConstructor ≠
      declaration.dropConstructor)
    (typed : HasType language source bound name resultType)
    (resultType_eq : resultType = .base declaration.nameSort)
    (safeAtZero : typed.ReflectiveSupportSafeAt support [] binderImage)
    (object : isObjectPattern name = true)
    (availableDepth : Nat) :
    EquationContextStep defaultBasePremises language
      (ReflectiveContextSupport.substituteAt language support
        assignment.assignment availableDepth
        (.apply declaration.quoteConstructor
          [.apply declaration.dropConstructor [name]]))
      (ReflectiveContextSupport.substituteAt language support
        assignment.assignment availableDepth name) := by
  exact EquationContextStep.reflectiveInContext .hole declarationMembership
    (quoteDrop_substituteAt_canonicalize_eq_of_resultsQuoted quotedResults
      assignment declaration declarationMembership quote_ne_drop typed
      resultType_eq safeAtZero object availableDepth)

/-- Closure-level form of the direct Quote/Drop substitution generator. -/
theorem quoteDrop_substituteAt_equationEquiv_of_resultsQuoted
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {name : Pattern} {resultType : TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (quotedResults : ReflectiveNameResultsQuoted language)
    (assignment : SupportedOpenAssignment language source target support)
    (declaration : ReflectivePresentationDecl)
    (declarationMembership : declaration ∈ language.reflectivePresentations)
    (quote_ne_drop : declaration.quoteConstructor ≠
      declaration.dropConstructor)
    (typed : HasType language source bound name resultType)
    (resultType_eq : resultType = .base declaration.nameSort)
    (safeAtZero : typed.ReflectiveSupportSafeAt support [] binderImage)
    (object : isObjectPattern name = true)
    (availableDepth : Nat) :
    EquationEquiv defaultBasePremises language
      (ReflectiveContextSupport.substituteAt language support
        assignment.assignment availableDepth
        (.apply declaration.quoteConstructor
          [.apply declaration.dropConstructor [name]]))
      (ReflectiveContextSupport.substituteAt language support
        assignment.assignment availableDepth name) := by
  exact Relation.EqvGen.rel _ _
    (quoteDrop_substituteAt_equationContextStep_of_resultsQuoted quotedResults
      assignment declaration declarationMembership quote_ne_drop typed
      resultType_eq safeAtZero object availableDepth)

/-! ## Generic reflective-parallel transport

The following algebra is independent of rho and of Cost.  It says that any
constructor-homomorphic map which preserves one reflective declaration's
parallel constructor and unit transports that declaration's ACU
normalization into the sole authored contextual equation relation.  The map
may replace a variable by a fresh parallel collection or unit, so raw
commutation with deterministic sorting is neither assumed nor true. -/

namespace ReflectiveParallelSubstitution

private theorem equivalentRefl {language : LanguageDef} (pattern : Pattern) :
    EquationEquiv defaultBasePremises language pattern pattern :=
  Relation.EqvGen.refl pattern

private theorem equivalentSymm {language : LanguageDef} {left right : Pattern}
    (equivalent : EquationEquiv defaultBasePremises language left right) :
    EquationEquiv defaultBasePremises language right left :=
  Relation.EqvGen.symm _ _ equivalent

private theorem equivalentTrans {language : LanguageDef}
    {left middle right : Pattern}
    (first : EquationEquiv defaultBasePremises language left middle)
    (second : EquationEquiv defaultBasePremises language middle right) :
    EquationEquiv defaultBasePremises language left right :=
  Relation.EqvGen.trans _ _ _ first second

private theorem rootEquivalent
    {language : LanguageDef} {declaration : ReflectivePresentationDecl}
    (membership : declaration ∈ language.reflectivePresentations)
    {left right : Pattern}
    (representatives :
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          left =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          right) :
    EquationEquiv defaultBasePremises language left right :=
  reflective_fill_equivalent membership .hole representatives

private theorem permutationEquivalent
    {language : LanguageDef} {declaration : ReflectivePresentationDecl}
    (membership : declaration ∈ language.reflectivePresentations)
    {left right : List Pattern} (permutation : left.Perm right) :
    EquationEquiv defaultBasePremises language
      (.collection declaration.parallelCollection left none)
      (.collection declaration.parallelCollection right none) := by
  apply rootEquivalent membership
  exact
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize_parallel_permutation
      declaration permutation

private theorem flattenEquivalent
    {language : LanguageDef} {declaration : ReflectivePresentationDecl}
    (membership : declaration ∈ language.reflectivePresentations)
    (leading nested : List Pattern) :
    EquationEquiv defaultBasePremises language
      (.collection declaration.parallelCollection
        (leading ++
          [.collection declaration.parallelCollection nested none]) none)
      (.collection declaration.parallelCollection (leading ++ nested) none) := by
  apply rootEquivalent membership
  exact
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize_parallel_flatten
      declaration leading nested

private theorem collapseEquivalent
    {language : LanguageDef} {declaration : ReflectivePresentationDecl}
    (membership : declaration ∈ language.reflectivePresentations)
    (patterns : List Pattern) :
    EquationEquiv defaultBasePremises language
      (.collection declaration.parallelCollection patterns none)
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
        declaration patterns) := by
  apply rootEquivalent membership
  exact
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize_parallel_collapse
      declaration patterns

private theorem consEquivalent
    {language : LanguageDef} {declaration : ReflectivePresentationDecl}
    (membership : declaration ∈ language.reflectivePresentations)
    (head : Pattern) {left right : List Pattern}
    (tailEquivalent : EquationEquiv defaultBasePremises language
      (.collection declaration.parallelCollection left none)
      (.collection declaration.parallelCollection right none)) :
    EquationEquiv defaultBasePremises language
      (.collection declaration.parallelCollection (head :: left) none)
      (.collection declaration.parallelCollection (head :: right) none) := by
  have lifted := equationEquiv_fill
    (.collection declaration.parallelCollection [head] .hole [] none)
    tailEquivalent
  have flattenLeft := flattenEquivalent membership [head] left
  have flattenRight := flattenEquivalent membership [head] right
  exact equivalentTrans
    (equivalentSymm flattenLeft)
    (equivalentTrans
      (by simpa [OneHoleContext.fill] using lifted) flattenRight)

private theorem spliceHeadEquivalent
    {language : LanguageDef} {declaration : ReflectivePresentationDecl}
    (membership : declaration ∈ language.reflectivePresentations)
    (nested rest : List Pattern) :
    EquationEquiv defaultBasePremises language
      (.collection declaration.parallelCollection
        (.collection declaration.parallelCollection nested none :: rest) none)
      (.collection declaration.parallelCollection (nested ++ rest) none) := by
  have moveNestedRight : EquationEquiv defaultBasePremises language
      (.collection declaration.parallelCollection
        (.collection declaration.parallelCollection nested none :: rest) none)
      (.collection declaration.parallelCollection
        (rest ++ [.collection declaration.parallelCollection nested none])
          none) := by
    apply permutationEquivalent membership
    simpa using
      (List.perm_append_comm
        (l₁ := [.collection declaration.parallelCollection nested none])
        (l₂ := rest))
  have flatten := flattenEquivalent membership rest nested
  have restoreOrder : EquationEquiv defaultBasePremises language
      (.collection declaration.parallelCollection (rest ++ nested) none)
      (.collection declaration.parallelCollection (nested ++ rest) none) := by
    apply permutationEquivalent membership
    exact List.perm_append_comm (l₁ := rest) (l₂ := nested)
  exact equivalentTrans moveNestedRight
    (equivalentTrans flatten restoreOrder)

private theorem flattenMapEquivalentBetween
    {language : LanguageDef}
    {sourceDeclaration targetDeclaration : ReflectivePresentationDecl}
    (membership : targetDeclaration ∈ language.reflectivePresentations)
    (mapPattern : Pattern → Pattern)
    (mapParallel : ∀ patterns,
      mapPattern
          (.collection sourceDeclaration.parallelCollection patterns none) =
        .collection targetDeclaration.parallelCollection
          (patterns.map mapPattern) none) :
    ∀ patterns : List Pattern,
      EquationEquiv defaultBasePremises language
        (.collection targetDeclaration.parallelCollection
          (patterns.map mapPattern) none)
        (.collection targetDeclaration.parallelCollection
          ((patterns.flatMap
            (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice
              sourceDeclaration)).map mapPattern) none)
  | [] => equivalentRefl _
  | pattern :: patterns => by
      have tailEquivalent := consEquivalent membership (mapPattern pattern)
        (flattenMapEquivalentBetween membership mapPattern mapParallel patterns)
      by_cases isParallel : ∃ nested,
          pattern =
            .collection sourceDeclaration.parallelCollection nested none
      · obtain ⟨nested, rfl⟩ := isParallel
        rw [mapParallel] at tailEquivalent
        have spliced := spliceHeadEquivalent membership
          (nested.map mapPattern)
          ((patterns.flatMap
            (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice
              sourceDeclaration)).map mapPattern)
        simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
          List.map_append, mapParallel] using
          (equivalentTrans tailEquivalent spliced)
      · have singleton :
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice
                sourceDeclaration pattern = [pattern] :=
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice_eq_singleton_of_not_parallel
            sourceDeclaration pattern (by
              intro nested equality
              exact isParallel ⟨nested, equality⟩)
        simpa [List.flatMap_cons, singleton] using tailEquivalent

private theorem filterUnitMapEquivalentBetween
    {language : LanguageDef}
    {sourceDeclaration targetDeclaration : ReflectivePresentationDecl}
    (membership : targetDeclaration ∈ language.reflectivePresentations)
    (mapPattern : Pattern → Pattern)
    (mapUnit :
      mapPattern (.apply sourceDeclaration.parallelUnitConstructor []) =
        .apply targetDeclaration.parallelUnitConstructor []) :
    ∀ patterns : List Pattern,
      EquationEquiv defaultBasePremises language
        (.collection targetDeclaration.parallelCollection
          (patterns.map mapPattern) none)
        (.collection targetDeclaration.parallelCollection
          ((patterns.filter fun pattern =>
            pattern ≠ .apply sourceDeclaration.parallelUnitConstructor []).map
              mapPattern) none)
  | [] => equivalentRefl _
  | pattern :: patterns => by
      have tailEquivalent := consEquivalent membership (mapPattern pattern)
        (filterUnitMapEquivalentBetween membership mapPattern mapUnit patterns)
      by_cases isUnit :
          pattern = .apply sourceDeclaration.parallelUnitConstructor []
      · subst pattern
        rw [mapUnit] at tailEquivalent
        have removeHead : EquationEquiv defaultBasePremises language
            (.collection targetDeclaration.parallelCollection
              (.apply targetDeclaration.parallelUnitConstructor [] ::
                ((patterns.filter fun pattern =>
                  pattern ≠ .apply sourceDeclaration.parallelUnitConstructor []).map
                    mapPattern)) none)
            (.collection targetDeclaration.parallelCollection
              ((patterns.filter fun pattern =>
                pattern ≠ .apply sourceDeclaration.parallelUnitConstructor []).map
                  mapPattern) none) := by
          let tail := (patterns.filter fun pattern =>
            pattern ≠ .apply sourceDeclaration.parallelUnitConstructor []).map
              mapPattern
          have unitToEmpty := equivalentSymm
            (collapseEquivalent membership [])
          have lifted := equationEquiv_fill
            (.collection targetDeclaration.parallelCollection [] .hole tail none)
              unitToEmpty
          exact equivalentTrans
            (by
              simpa [tail, OneHoleContext.fill,
                Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel]
                using lifted)
            (by simpa [tail] using spliceHeadEquivalent membership [] tail)
        simpa [mapUnit] using equivalentTrans tailEquivalent removeHead
      · simpa [isUnit] using tailEquivalent

private theorem sortMapEquivalent
    {language : LanguageDef} {declaration : ReflectivePresentationDecl}
    (membership : declaration ∈ language.reflectivePresentations)
    (mapPattern : Pattern → Pattern) (patterns : List Pattern) :
    EquationEquiv defaultBasePremises language
      (.collection declaration.parallelCollection
        (patterns.map mapPattern) none)
      (.collection declaration.parallelCollection
        ((Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns patterns).map
          mapPattern) none) := by
  apply permutationEquivalent membership
  exact
    ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.sortPatterns_perm
      patterns).map mapPattern).symm

private theorem collapseMapEquivalentBetween
    {language : LanguageDef}
    {sourceDeclaration targetDeclaration : ReflectivePresentationDecl}
    (membership : targetDeclaration ∈ language.reflectivePresentations)
    (mapPattern : Pattern → Pattern)
    (mapParallel : ∀ patterns,
      mapPattern
          (.collection sourceDeclaration.parallelCollection patterns none) =
        .collection targetDeclaration.parallelCollection
          (patterns.map mapPattern) none)
    (mapUnit :
      mapPattern (.apply sourceDeclaration.parallelUnitConstructor []) =
        .apply targetDeclaration.parallelUnitConstructor [])
    (patterns : List Pattern) :
    EquationEquiv defaultBasePremises language
      (.collection targetDeclaration.parallelCollection
        (patterns.map mapPattern) none)
      (mapPattern
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
          sourceDeclaration patterns)) := by
  have collapseMap : mapPattern
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
          sourceDeclaration patterns) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
        targetDeclaration (patterns.map mapPattern) := by
    cases patterns with
    | nil =>
        simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel]
          using mapUnit
    | cons first rest =>
        cases rest with
        | nil => rfl
        | cons second tail =>
            simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel]
              using mapParallel (first :: second :: tail)
  rw [collapseMap]
  exact collapseEquivalent membership (patterns.map mapPattern)

/-- Full ACU normalization of a source reflective parallel collection is
transported by a constructor-homomorphic map into the target declaration's
authored reflective equation relation.  Source and target declarations may
use different constructor names; the two preservation equations are the
entire interface between them. -/
theorem normalizationMapEquivalentBetween
    {language : LanguageDef}
    (sourceDeclaration : ReflectivePresentationDecl)
    {targetDeclaration : ReflectivePresentationDecl}
    (membership : targetDeclaration ∈ language.reflectivePresentations)
    (mapPattern : Pattern → Pattern)
    (mapParallel : ∀ patterns,
      mapPattern
          (.collection sourceDeclaration.parallelCollection patterns none) =
        .collection targetDeclaration.parallelCollection
          (patterns.map mapPattern) none)
    (mapUnit :
      mapPattern (.apply sourceDeclaration.parallelUnitConstructor []) =
        .apply targetDeclaration.parallelUnitConstructor [])
    (patterns : List Pattern) :
    EquationEquiv defaultBasePremises language
      (.collection targetDeclaration.parallelCollection
        (patterns.map mapPattern) none)
      (mapPattern
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
          sourceDeclaration
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements
            sourceDeclaration patterns))) := by
  let flattened := patterns.flatMap
    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice
      sourceDeclaration)
  let filtered := flattened.filter fun pattern =>
    pattern ≠ .apply sourceDeclaration.parallelUnitConstructor []
  have flatten := flattenMapEquivalentBetween membership mapPattern mapParallel
    patterns
  have filter := filterUnitMapEquivalentBetween membership mapPattern mapUnit
    flattened
  have sort := sortMapEquivalent membership mapPattern filtered
  have collapse := collapseMapEquivalentBetween membership mapPattern
    mapParallel mapUnit
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns filtered)
  exact equivalentTrans flatten
    (equivalentTrans
      (by simpa [flattened] using filter)
      (equivalentTrans
        (by simpa [flattened, filtered] using sort)
        (by
          simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements,
            flattened, filtered] using collapse)))

private theorem consMapCanonicalizeEq
    (declaration : ReflectivePresentationDecl)
    (head : Pattern) {left right : List Pattern}
    (tailEquality :
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          (.collection declaration.parallelCollection left none) =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          (.collection declaration.parallelCollection right none)) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
        (.collection declaration.parallelCollection (head :: left) none) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
        (.collection declaration.parallelCollection (head :: right) none) := by
  have lifted := EquationSemantics.canonicalize_fill_congr declaration
    (.collection declaration.parallelCollection [head] .hole [] none)
      tailEquality
  have flattenLeft :=
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize_parallel_flatten
      declaration [head] left
  have flattenRight :=
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize_parallel_flatten
      declaration [head] right
  have lifted' :
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          (.collection declaration.parallelCollection
            [head, .collection declaration.parallelCollection left none]
            none) =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          (.collection declaration.parallelCollection
            [head, .collection declaration.parallelCollection right none]
            none) := by
    simpa [OneHoleContext.fill] using lifted
  exact flattenLeft.symm.trans (lifted'.trans flattenRight)

private theorem spliceHeadMapCanonicalizeEq
    (declaration : ReflectivePresentationDecl)
    (nested rest : List Pattern) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
        (.collection declaration.parallelCollection
          (.collection declaration.parallelCollection nested none :: rest)
          none) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
        (.collection declaration.parallelCollection (nested ++ rest) none) := by
  have moveNestedRight :=
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize_parallel_permutation
      declaration
      (by
        simpa using
          (List.perm_append_comm
            (l₁ := [.collection declaration.parallelCollection nested none])
            (l₂ := rest)))
  have flatten :=
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize_parallel_flatten
      declaration rest nested
  have restoreOrder :=
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize_parallel_permutation
      declaration
      (List.perm_append_comm (l₁ := rest) (l₂ := nested))
  exact moveNestedRight.trans (flatten.trans restoreOrder)

private theorem flattenMapCanonicalizeEqBetween
    (sourceDeclaration targetDeclaration : ReflectivePresentationDecl)
    (mapPattern : Pattern → Pattern)
    (mapParallel : ∀ patterns,
      mapPattern
          (.collection sourceDeclaration.parallelCollection patterns none) =
        .collection targetDeclaration.parallelCollection
          (patterns.map mapPattern) none) :
    ∀ patterns : List Pattern,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          targetDeclaration
          (.collection targetDeclaration.parallelCollection
            (patterns.map mapPattern) none) =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          targetDeclaration
          (.collection targetDeclaration.parallelCollection
            ((patterns.flatMap
              (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice
                sourceDeclaration)).map mapPattern) none)
  | [] => rfl
  | pattern :: patterns => by
      have tailEquality := consMapCanonicalizeEq targetDeclaration
        (mapPattern pattern)
        (flattenMapCanonicalizeEqBetween sourceDeclaration targetDeclaration
          mapPattern mapParallel patterns)
      by_cases isParallel : ∃ nested,
          pattern =
            .collection sourceDeclaration.parallelCollection nested none
      · obtain ⟨nested, rfl⟩ := isParallel
        rw [mapParallel] at tailEquality
        have spliced := spliceHeadMapCanonicalizeEq targetDeclaration
          (nested.map mapPattern)
          ((patterns.flatMap
            (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice
              sourceDeclaration)).map mapPattern)
        simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
          List.map_append, mapParallel] using tailEquality.trans spliced
      · have singleton :
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice
                sourceDeclaration pattern = [pattern] :=
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice_eq_singleton_of_not_parallel
            sourceDeclaration pattern (by
              intro nested equality
              exact isParallel ⟨nested, equality⟩)
        simpa [List.flatMap_cons, singleton] using tailEquality

private theorem filterUnitMapCanonicalizeEqBetween
    (sourceDeclaration targetDeclaration : ReflectivePresentationDecl)
    (mapPattern : Pattern → Pattern)
    (mapUnit :
      mapPattern (.apply sourceDeclaration.parallelUnitConstructor []) =
        .apply targetDeclaration.parallelUnitConstructor []) :
    ∀ patterns : List Pattern,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          targetDeclaration
          (.collection targetDeclaration.parallelCollection
            (patterns.map mapPattern) none) =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          targetDeclaration
          (.collection targetDeclaration.parallelCollection
            ((patterns.filter fun pattern =>
              pattern ≠ .apply sourceDeclaration.parallelUnitConstructor []).map
                mapPattern) none)
  | [] => rfl
  | pattern :: patterns => by
      have tailEquality := consMapCanonicalizeEq targetDeclaration
        (mapPattern pattern)
        (filterUnitMapCanonicalizeEqBetween sourceDeclaration
          targetDeclaration mapPattern mapUnit patterns)
      by_cases isUnit :
          pattern = .apply sourceDeclaration.parallelUnitConstructor []
      · subst pattern
        rw [mapUnit] at tailEquality
        have unitToEmpty :=
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize_parallel_collapse
            targetDeclaration []).symm
        have lifted := EquationSemantics.canonicalize_fill_congr
          targetDeclaration
          (.collection targetDeclaration.parallelCollection [] .hole
            ((patterns.filter fun pattern =>
              pattern ≠ .apply sourceDeclaration.parallelUnitConstructor []).map
                mapPattern) none)
          unitToEmpty
        let tail :=
          (patterns.filter fun pattern =>
            pattern ≠ .apply sourceDeclaration.parallelUnitConstructor []).map
              mapPattern
        have lifted' :
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                targetDeclaration
                (.collection targetDeclaration.parallelCollection
                  ([.apply targetDeclaration.parallelUnitConstructor []] ++
                    tail) none) =
              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                targetDeclaration
                (.collection targetDeclaration.parallelCollection
                  ([.collection targetDeclaration.parallelCollection [] none] ++
                    tail) none) := by
          simpa [tail, OneHoleContext.fill,
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel]
            using lifted
        have removeHead := lifted'.trans
          (spliceHeadMapCanonicalizeEq targetDeclaration [] tail)
        simpa [mapUnit, OneHoleContext.fill,
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel, tail]
          using tailEquality.trans removeHead
      · simpa [isUnit] using tailEquality

private theorem sortMapCanonicalizeEq
    (declaration : ReflectivePresentationDecl)
    (mapPattern : Pattern → Pattern) (patterns : List Pattern) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
        (.collection declaration.parallelCollection
          (patterns.map mapPattern) none) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
        (.collection declaration.parallelCollection
          ((Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns patterns).map
            mapPattern) none) := by
  exact
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize_parallel_permutation
      declaration
      ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.sortPatterns_perm
        patterns).map mapPattern).symm

private theorem collapseMapCanonicalizeEqBetween
    (sourceDeclaration targetDeclaration : ReflectivePresentationDecl)
    (mapPattern : Pattern → Pattern)
    (mapParallel : ∀ patterns,
      mapPattern
          (.collection sourceDeclaration.parallelCollection patterns none) =
        .collection targetDeclaration.parallelCollection
          (patterns.map mapPattern) none)
    (mapUnit :
      mapPattern (.apply sourceDeclaration.parallelUnitConstructor []) =
        .apply targetDeclaration.parallelUnitConstructor [])
    (patterns : List Pattern) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        targetDeclaration
        (.collection targetDeclaration.parallelCollection
          (patterns.map mapPattern) none) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        targetDeclaration
        (mapPattern
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
            sourceDeclaration patterns)) := by
  have collapseMap : mapPattern
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
          sourceDeclaration patterns) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
        targetDeclaration (patterns.map mapPattern) := by
    cases patterns with
    | nil =>
        simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel]
          using mapUnit
    | cons first rest =>
        cases rest with
        | nil => rfl
        | cons second tail =>
            simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel]
              using mapParallel (first :: second :: tail)
  rw [collapseMap]
  exact
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize_parallel_collapse
      targetDeclaration (patterns.map mapPattern)

/-- Re-canonicalization makes full ACU normalization exactly natural for any
map preserving the selected parallel constructor and unit.  Unlike the
relation-valued theorem above, this algebra needs no target language or
membership proof: it speaks only about the two explicit declarations. -/
theorem normalizationMapCanonicalizeEqBetween
    (sourceDeclaration targetDeclaration : ReflectivePresentationDecl)
    (mapPattern : Pattern → Pattern)
    (mapParallel : ∀ patterns,
      mapPattern
          (.collection sourceDeclaration.parallelCollection patterns none) =
        .collection targetDeclaration.parallelCollection
          (patterns.map mapPattern) none)
    (mapUnit :
      mapPattern (.apply sourceDeclaration.parallelUnitConstructor []) =
        .apply targetDeclaration.parallelUnitConstructor [])
    (patterns : List Pattern) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        targetDeclaration
        (.collection targetDeclaration.parallelCollection
          (patterns.map mapPattern) none) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        targetDeclaration
        (mapPattern
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
            sourceDeclaration
            (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements
              sourceDeclaration patterns))) := by
  let flattened := patterns.flatMap
    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice
      sourceDeclaration)
  let filtered := flattened.filter fun pattern =>
    pattern ≠ .apply sourceDeclaration.parallelUnitConstructor []
  have flatten := flattenMapCanonicalizeEqBetween sourceDeclaration
    targetDeclaration mapPattern mapParallel patterns
  have filter := filterUnitMapCanonicalizeEqBetween sourceDeclaration
    targetDeclaration mapPattern mapUnit flattened
  have sort := sortMapCanonicalizeEq targetDeclaration mapPattern filtered
  have collapse := collapseMapCanonicalizeEqBetween sourceDeclaration
    targetDeclaration mapPattern mapParallel mapUnit
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns filtered)
  exact flatten.trans (calc
    _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          targetDeclaration
          (.collection targetDeclaration.parallelCollection
            (filtered.map mapPattern) none) := by
      simpa [flattened, filtered] using filter
    _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          targetDeclaration
          (.collection targetDeclaration.parallelCollection
            ((Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns filtered).map
              mapPattern) none) := by
      simpa [flattened, filtered] using sort
    _ = _ := by
      simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements,
        flattened, filtered] using collapse)

/-- Full ACU normalization of one reflective parallel collection is natural
up to that same authored reflective equation relation. -/
theorem normalizationMapEquivalent
    {language : LanguageDef} {declaration : ReflectivePresentationDecl}
    (membership : declaration ∈ language.reflectivePresentations)
    (mapPattern : Pattern → Pattern)
    (mapParallel : ∀ patterns,
      mapPattern (.collection declaration.parallelCollection patterns none) =
        .collection declaration.parallelCollection
          (patterns.map mapPattern) none)
    (mapUnit :
      mapPattern (.apply declaration.parallelUnitConstructor []) =
        .apply declaration.parallelUnitConstructor [])
    (patterns : List Pattern) :
    EquationEquiv defaultBasePremises language
      (.collection declaration.parallelCollection
        (patterns.map mapPattern) none)
      (mapPattern
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
          declaration
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements
            declaration patterns))) := by
  exact normalizationMapEquivalentBetween declaration membership mapPattern
    mapParallel mapUnit patterns

end ReflectiveParallelSubstitution

private theorem equationEquivTrans {language : LanguageDef}
    {left middle right : Pattern}
    (first : EquationEquiv defaultBasePremises language left middle)
    (second : EquationEquiv defaultBasePremises language middle right) :
    EquationEquiv defaultBasePremises language left right := by
  unfold EquationEquiv at first second ⊢
  exact Relation.EqvGen.trans _ _ _ first second

private theorem finishNormalizeReflectiveApply_quote_eq_of_not_drop
    (declaration : ReflectivePresentationDecl) {argument : Pattern}
    (notDrop : ¬ ∃ name,
      argument = .apply declaration.dropConstructor [name]) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
        declaration declaration.quoteConstructor [argument] =
      .apply declaration.quoteConstructor [argument] := by
  unfold Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
  simp only [beq_self_eq_true, if_true]
  cases argument with
  | apply constructor arguments =>
      cases arguments with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil =>
              by_cases dropLabel : constructor = declaration.dropConstructor
              · subst constructor
                exact False.elim (notDrop ⟨first, rfl⟩)
              · simp [dropLabel]
          | cons second tail => rfl
  | bvar index => rfl
  | fvar name => rfl
  | lambda binder body => rfl
  | multiLambda arity binders body => rfl
  | subst body replacement => rfl
  | collection collectionType elements rest => rfl

/-- Supported substitution is natural, in the sole authored contextual
equation relation, with respect to any validated reflective canonicalizer
whose name results are quote-sealed and whose exposed Drop arguments preserve
their exact support fiber. -/
theorem substituteAt_canonicalize_equationEquiv_of_resultsQuoted
    (language : LanguageDef) (valid : language.validate = [])
    (quotedResults : ReflectiveNameResultsQuoted language)
    (dropSupport : ReflectiveDropCanonicalSupportStable language)
    {source target : FreeTypeContext} {support : ContextSupport.Support}
    {bound available : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (assignment : SupportedOpenAssignment language source target support)
    (declaration : ReflectivePresentationDecl)
    (declarationMembership : declaration ∈ language.reflectivePresentations)
    (typed : HasType language source bound pattern type)
    (safe : typed.ReflectiveSupportSafeAt support available binderImage)
    (object : isObjectPattern pattern = true) :
    EquationEquiv defaultBasePremises language
      (ReflectiveContextSupport.substituteAt language support
        assignment.assignment available.length pattern)
      (ReflectiveContextSupport.substituteAt language support
        assignment.assignment available.length
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          pattern)) := by
  have declarationValid :=
    LanguageDef.reflectivePresentation_validate_of_validate_eq_nil language
      valid declaration declarationMembership
  have quoteNeDrop :=
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.quoteConstructor_ne_dropConstructor_of_validate
      language declaration declarationValid
  have chosenQuote : ReflectiveContextSupport.isQuoteConstructor language
      declaration.quoteConstructor = true := by
    simp only [ReflectiveContextSupport.isQuoteConstructor, List.any_eq_true]
    exact ⟨declaration, declarationMembership, by simp⟩
  exact HasType.ReflectiveSupportSafeAt.rec
    (motive_1 := fun {bound pattern type}
      (typed : HasType language source bound pattern type)
      (available : List TypeExpr)
      (currentImage : TypeExpr → TypeExpr)
      (_ : typed.ReflectiveSupportSafeAt support available currentImage) =>
      isObjectPattern pattern = true →
      EquationEquiv defaultBasePremises language
        (ReflectiveContextSupport.substituteAt language support
          assignment.assignment available.length pattern)
        (ReflectiveContextSupport.substituteAt language support
          assignment.assignment available.length
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
            pattern)))
    (motive_2 := fun {bound arguments parameters}
      (typed : ArgumentsHaveTypes language source bound arguments parameters)
      (available : List TypeExpr)
      (currentImage : TypeExpr → TypeExpr)
      (_ : typed.ReflectiveSupportSafeAt support available currentImage) =>
      isObjectPatternList arguments = true →
      List.Forall₂ (EquationEquiv defaultBasePremises language)
        (arguments.map (ReflectiveContextSupport.substituteAt language support
          assignment.assignment available.length))
        ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
            declaration arguments).map
          (ReflectiveContextSupport.substituteAt language support
            assignment.assignment available.length)))
    (motive_3 := fun {bound elements elementType}
      (typed : ElementsHaveType language source bound elements elementType)
      (available : List TypeExpr)
      (currentImage : TypeExpr → TypeExpr)
      (_ : typed.ReflectiveSupportSafeAt support available currentImage) =>
      isObjectPatternList elements = true →
      List.Forall₂ (EquationEquiv defaultBasePremises language)
        (elements.map (ReflectiveContextSupport.substituteAt language support
          assignment.assignment available.length))
        ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
            declaration elements).map
          (ReflectiveContextSupport.substituteAt language support
            assignment.assignment available.length)))
    (by
      intro bound index resultType lookup sourceAvailable currentImage
        resultObject
      exact Relation.EqvGen.refl _)
    (by
      intro bound freeName resultType lookup sourceAvailable currentImage shape
        resultObject
      exact Relation.EqvGen.refl _)
    (by
      intro bound rule arguments membership notBare argumentsTyped
        sourceAvailable currentImage quoted argumentsSafe argumentsIH
        resultObject
      have argumentsObject : isObjectPatternList arguments = true := by
        simpa [isObjectPattern] using resultObject
      have pointwise := argumentsIH argumentsObject
      have lifted := equationEquiv_apply_of_forall₂ rule.label pointwise
      by_cases selected : rule.label = declaration.quoteConstructor
      · obtain ⟨argument, argumentTyped, rfl, argumentSafe⟩ :=
          argumentsTyped.selectedQuoteArgument valid declarationMembership
            membership selected argumentsSafe
        have argumentObject : isObjectPattern argument = true := by
          simpa [isObjectPatternList] using argumentsObject
        cases pointwise with
        | @cons _ _ _ _ argumentEquivalent tailPointwise =>
            cases tailPointwise
            have lifted' : EquationEquiv defaultBasePremises language
                (.apply declaration.quoteConstructor
                  [ReflectiveContextSupport.substituteAt language support
                    assignment.assignment 0 argument])
                (.apply declaration.quoteConstructor
                  [ReflectiveContextSupport.substituteAt language support
                    assignment.assignment 0
                    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                      declaration argument)]) := by
              simpa [selected,
                Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList]
                using lifted
            by_cases dropShape : ∃ name,
                Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                    declaration argument =
                  .apply declaration.dropConstructor [name]
            · obtain ⟨name, canonicalEquality⟩ := dropShape
              obtain ⟨nameTyped, nameSafe, nameObject⟩ :=
                dropSupport declaration declarationMembership argumentTyped
                  argumentSafe argumentObject canonicalEquality
              have cancellation :=
                quoteDrop_substituteAt_equationEquiv_of_resultsQuoted
                  quotedResults assignment declaration declarationMembership
                    quoteNeDrop nameTyped rfl nameSafe nameObject
                      sourceAvailable.length
              rw [canonicalEquality] at lifted'
              have cancellation' : EquationEquiv defaultBasePremises language
                  (.apply declaration.quoteConstructor
                    [ReflectiveContextSupport.substituteAt language support
                      assignment.assignment 0
                      (.apply declaration.dropConstructor [name])])
                  (ReflectiveContextSupport.substituteAt language support
                    assignment.assignment sourceAvailable.length name) := by
                have leftSubstitution :
                    ReflectiveContextSupport.substituteAt language support
                        assignment.assignment sourceAvailable.length
                        (.apply declaration.quoteConstructor
                          [.apply declaration.dropConstructor [name]]) =
                      .apply declaration.quoteConstructor
                        [ReflectiveContextSupport.substituteAt language support
                          assignment.assignment 0
                          (.apply declaration.dropConstructor [name])] := by
                  simp only [ReflectiveContextSupport.substituteAt, chosenQuote,
                    if_true, List.map_cons, List.map_nil]
                rw [leftSubstitution] at cancellation
                exact cancellation
              simpa [ReflectiveContextSupport.substituteAt,
                Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
                Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
                Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                selected, quoted, chosenQuote, quoteNeDrop,
                canonicalEquality] using
                  (equationEquivTrans lifted' cancellation')
            · have quotedCanonical :=
                finishNormalizeReflectiveApply_quote_eq_of_not_drop
                  declaration dropShape
              simpa [ReflectiveContextSupport.substituteAt,
                Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
                Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
                selected, quoted, chosenQuote, quotedCanonical] using lifted'
      · have selectedFalse : (rule.label == declaration.quoteConstructor) =
            false := by simp [selected]
        simpa [ReflectiveContextSupport.substituteAt,
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
          Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
          quoted, selectedFalse] using lifted)
    (by
      intro bound rule arguments membership notBare argumentsTyped
        sourceAvailable currentImage ordinary argumentsSafe argumentsIH
        resultObject
      have argumentsObject : isObjectPatternList arguments = true := by
        simpa [isObjectPattern] using resultObject
      have pointwise := argumentsIH argumentsObject
      have lifted := equationEquiv_apply_of_forall₂ rule.label pointwise
      have selected : rule.label ≠ declaration.quoteConstructor := by
        intro equality
        have chosenQuote : ReflectiveContextSupport.isQuoteConstructor language
            declaration.quoteConstructor = true := by
          simp only [ReflectiveContextSupport.isQuoteConstructor,
            List.any_eq_true]
          exact ⟨declaration, declarationMembership, by simp⟩
        rw [equality] at ordinary
        exact Bool.noConfusion (ordinary.symm.trans chosenQuote)
      have selectedFalse : (rule.label == declaration.quoteConstructor) = false := by
        simp [selected]
      simpa [ReflectiveContextSupport.substituteAt,
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
        Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
        ordinary, selectedFalse] using lifted)
    (by
      intro bound binder body domain codomain bodyTyped sourceAvailable
        currentImage bodySafe bodyIH resultObject
      have bodyObject : isObjectPattern body = true := by
        simpa [isObjectPattern] using resultObject
      have lifted := equationEquiv_fill (.lambda binder .hole)
        (bodyIH bodyObject)
      simpa [ReflectiveContextSupport.substituteAt,
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
        OneHoleContext.fill] using lifted)
    (by
      intro bound arity binders body domain codomain bodyTyped sourceAvailable
        currentImage bodySafe bodyIH resultObject
      have bodyObject : isObjectPattern body = true := by
        simpa [isObjectPattern] using resultObject
      have lifted := equationEquiv_fill
        (.multiLambda arity binders .hole) (bodyIH bodyObject)
      simpa [ReflectiveContextSupport.substituteAt,
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
        OneHoleContext.fill, List.length_append, Nat.add_comm] using lifted)
    (by
      intro bound body replacement domain codomain bodyTyped replacementTyped
        sourceAvailable currentImage bodySafe replacementSafe bodyIH replacementIH
        resultObject
      simp [isObjectPattern] at resultObject)
    (by
      intro bound collectionType elements rest elementType elementsTyped
        sourceAvailable currentImage elementsSafe elementsIH resultObject
      have objectParts : rest = none ∧ isObjectPatternList elements = true := by
        simpa [isObjectPattern] using resultObject
      rcases objectParts with ⟨rfl, elementsObject⟩
      have pointwise := elementsIH elementsObject
      have lifted := equationEquiv_collection_of_forall₂ collectionType none
        pointwise
      by_cases parallelShape :
          collectionType = declaration.parallelCollection
      · subst collectionType
        let mapPattern := ReflectiveContextSupport.substituteAt language support
          assignment.assignment sourceAvailable.length
        have mapParallel : ∀ patterns,
            mapPattern
                (.collection declaration.parallelCollection patterns none) =
              .collection declaration.parallelCollection
                (patterns.map mapPattern) none := by
          intro patterns
          simp [mapPattern, ReflectiveContextSupport.substituteAt]
        have mapUnit :
            mapPattern (.apply declaration.parallelUnitConstructor []) =
              .apply declaration.parallelUnitConstructor [] := by
          simp [mapPattern, ReflectiveContextSupport.substituteAt]
        have normalized :=
          ReflectiveParallelSubstitution.normalizationMapEquivalent
            declarationMembership mapPattern mapParallel mapUnit
              (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                declaration elements)
        have lifted' : EquationEquiv defaultBasePremises language
            (mapPattern
              (.collection declaration.parallelCollection elements none))
            (.collection declaration.parallelCollection
              ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                declaration elements).map mapPattern) none) := by
          simpa [mapPattern, ReflectiveContextSupport.substituteAt] using lifted
        have normalized' : EquationEquiv defaultBasePremises language
            (.collection declaration.parallelCollection
              ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                declaration elements).map mapPattern) none)
            (mapPattern
              (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
                declaration
                (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements
                  declaration
                  (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                    declaration elements)))) := normalized
        exact equationEquivTrans lifted' (by
          simpa [mapPattern, ReflectiveContextSupport.substituteAt,
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize] using
              normalized')
      · have selectedFalse :
            (collectionType == declaration.parallelCollection) = false := by
          simp [parallelShape]
        simpa [ReflectiveContextSupport.substituteAt,
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
          selectedFalse] using lifted)
    (by
      intro bound rule parameterName collectionType elements rest elementType
        membership parameterShape elementsTyped sourceAvailable currentImage
        elementsSafe elementsIH resultObject
      have objectParts : rest = none ∧ isObjectPatternList elements = true := by
        simpa [isObjectPattern] using resultObject
      rcases objectParts with ⟨rfl, elementsObject⟩
      have pointwise := elementsIH elementsObject
      have lifted := equationEquiv_collection_of_forall₂ collectionType none
        pointwise
      by_cases parallelShape :
          collectionType = declaration.parallelCollection
      · subst collectionType
        let mapPattern := ReflectiveContextSupport.substituteAt language support
          assignment.assignment sourceAvailable.length
        have mapParallel : ∀ patterns,
            mapPattern
                (.collection declaration.parallelCollection patterns none) =
              .collection declaration.parallelCollection
                (patterns.map mapPattern) none := by
          intro patterns
          simp [mapPattern, ReflectiveContextSupport.substituteAt]
        have mapUnit :
            mapPattern (.apply declaration.parallelUnitConstructor []) =
              .apply declaration.parallelUnitConstructor [] := by
          simp [mapPattern, ReflectiveContextSupport.substituteAt]
        have normalized :=
          ReflectiveParallelSubstitution.normalizationMapEquivalent
            declarationMembership mapPattern mapParallel mapUnit
              (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                declaration elements)
        have lifted' : EquationEquiv defaultBasePremises language
            (mapPattern
              (.collection declaration.parallelCollection elements none))
            (.collection declaration.parallelCollection
              ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                declaration elements).map mapPattern) none) := by
          simpa [mapPattern, ReflectiveContextSupport.substituteAt] using lifted
        have normalized' : EquationEquiv defaultBasePremises language
            (.collection declaration.parallelCollection
              ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                declaration elements).map mapPattern) none)
            (mapPattern
              (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
                declaration
                (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements
                  declaration
                  (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                    declaration elements)))) := normalized
        exact equationEquivTrans lifted' (by
          simpa [mapPattern, ReflectiveContextSupport.substituteAt,
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize] using
              normalized')
      · have selectedFalse :
            (collectionType == declaration.parallelCollection) = false := by
          simp [parallelShape]
        simpa [ReflectiveContextSupport.substituteAt,
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
          selectedFalse] using lifted)
    (by
      intro bound sourceAvailable currentImage argumentsObject
      exact .nil)
    (by
      intro bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped
        sourceAvailable currentImage argumentSafe argumentsSafe argumentIH
        argumentsIH argumentsObject
      have objectParts : isObjectPattern argument = true ∧
          isObjectPatternList arguments = true := by
        simpa [isObjectPatternList] using argumentsObject
      exact .cons (argumentIH objectParts.1) (argumentsIH objectParts.2))
    (by
      intro bound elementType sourceAvailable currentImage elementsObject
      exact .nil)
    (by
      intro bound element elements elementType elementTyped elementsTyped
        sourceAvailable currentImage elementSafe elementsSafe elementIH
        elementsIH elementsObject
      have objectParts : isObjectPattern element = true ∧
          isObjectPatternList elements = true := by
        simpa [isObjectPatternList] using elementsObject
      exact .cons (elementIH objectParts.1) (elementsIH objectParts.2))
    safe object

/-- An open object together with the reflective-support certificate for the
particular structural substitution being considered.  The raw pattern,
typing judgment, and equation generators remain those of the sole authored
`LanguageDef`; this structure only prevents an equivalence chain from passing
through an intermediate vertex at which that substitution is not licensed. -/
structure SupportSafeOpenPattern (language : LanguageDef)
    (free : FreeTypeContext) (support : ContextSupport.Support)
    (bound : List TypeExpr) (type : TypeExpr) where
  term : OpenPattern language free bound type
  safe : term.2.1.ReflectiveSupportSafeAt support bound

namespace SupportSafeOpenPattern

/-- One fiber-internal authored equation edge between support-safe vertices. -/
def equationGenerator {language : LanguageDef}
    {free : FreeTypeContext} {support : ContextSupport.Support}
    {bound : List TypeExpr} {type : TypeExpr}
    (left right : SupportSafeOpenPattern language free support bound type) : Prop :=
  EquationContextStep defaultBasePremises language left.term.1 right.term.1

/-- Least authored contextual equivalence whose every intermediate vertex is
typed and safe for the same support-indexed substitution. -/
def equationSetoid (language : LanguageDef) (free : FreeTypeContext)
    (support : ContextSupport.Support) (bound : List TypeExpr)
    (type : TypeExpr) :
    Setoid (SupportSafeOpenPattern language free support bound type) where
  r := Relation.EqvGen equationGenerator
  iseqv :=
    { refl := Relation.EqvGen.refl
      symm := fun relation => Relation.EqvGen.symm _ _ relation
      trans := fun first second => Relation.EqvGen.trans _ _ _ first second }

/-- Forgetting the support witness maps the restricted relation into the
ordinary typed open equation relation generated by the same authored edges. -/
theorem equationSetoid_to_openPatternEquationSetoid
    {language : LanguageDef} {free : FreeTypeContext}
    {support : ContextSupport.Support} {bound : List TypeExpr}
    {type : TypeExpr}
    {left right : SupportSafeOpenPattern language free support bound type}
    (equivalent :
      (equationSetoid language free support bound type).r left right) :
    (openPatternEquationSetoid language free bound type).r
      left.term right.term := by
  induction equivalent with
  | rel left right generator =>
      exact Relation.EqvGen.rel _ _ generator
  | refl term =>
      exact Relation.EqvGen.refl term.term
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

/-- Forget all proof-relevant fiber data while retaining the exact authored
raw contextual equivalence. -/
theorem equationSetoid_to_equationEquiv
    {language : LanguageDef} {free : FreeTypeContext}
    {support : ContextSupport.Support} {bound : List TypeExpr}
    {type : TypeExpr}
    {left right : SupportSafeOpenPattern language free support bound type}
    (equivalent :
      (equationSetoid language free support bound type).r left right) :
    EquationEquiv defaultBasePremises language left.term.1 right.term.1 :=
  openPatternEquationSetoid_to_equationEquiv
    (equationSetoid_to_openPatternEquationSetoid equivalent)

/-- Apply a support-certified structural assignment to the stored open term. -/
def substitute {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support} {bound : List TypeExpr}
    {type : TypeExpr}
    (pattern : SupportSafeOpenPattern language source support bound type)
    (assignment : SupportedOpenAssignment language source target support) :
    OpenPattern language target bound type :=
  pattern.term.substituteReflectiveSupported assignment pattern.safe

@[simp]
theorem substitute_pattern {language : LanguageDef}
    {source target : FreeTypeContext} {support : ContextSupport.Support}
    {bound : List TypeExpr} {type : TypeExpr}
    (pattern : SupportSafeOpenPattern language source support bound type)
    (assignment : SupportedOpenAssignment language source target support) :
    (pattern.substitute assignment).1 =
      ReflectiveContextSupport.substitute language support
        assignment.assignment bound pattern.term.1 :=
  rfl

end SupportSafeOpenPattern

/-- Reflective canonical equality is stable under one support-certified
substitution when it is interpreted in the sole authored contextual equation
relation.

This is a genuine property of a language presentation, not a second equation
theory or an executable policy.  Validation, sorting, and the current
type-suffix support discipline do not imply it: a reflective presentation may
move a free parameter between distinct equal-typed binder occurrences.  Cost
therefore admits a language only after this law has been proved for its exact
authored presentation. -/
def ReflectiveEquationSubstitutionStable (language : LanguageDef) : Prop :=
  ∀ {source target : FreeTypeContext} {support : ContextSupport.Support}
    {bound : List TypeExpr} {type : TypeExpr}
    (assignment : SupportedOpenAssignment language source target support)
    {declaration : ReflectivePresentationDecl},
    declaration ∈ language.reflectivePresentations →
    ∀ (left right :
      SupportSafeOpenPattern language source support bound type),
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          declaration left.term.1 =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          declaration right.term.1 →
      EquationEquiv defaultBasePremises language
        (left.substitute assignment).1 (right.substitute assignment).1

/-- Constructor-only presentations satisfy reflective substitution stability
because they contain no reflective equality generator. -/
theorem reflectiveEquationSubstitutionStable_of_empty
    {language : LanguageDef}
    (empty : language.reflectivePresentations = []) :
    ReflectiveEquationSubstitutionStable language := by
  intro source target support bound type assignment declaration membership
    left right representatives
  rw [empty] at membership
  cases membership

/-- Every ordinary authored equation instance remains valid after one
support-certified substitution, including when the instance occurs inside a
structural one-hole context.  Premise-freeness, exact matcher reconstruction,
and schema-instantiation stability are sufficient data from which concrete
Cost presentations prove this property; none of them is silently built into
the definition. -/
def AuthoredEquationSubstitutionStable (language : LanguageDef) : Prop :=
  ∀ {source target : FreeTypeContext} {support : ContextSupport.Support}
    {bound : List TypeExpr} {type : TypeExpr}
    (assignment : SupportedOpenAssignment language source target support)
    (left right : SupportSafeOpenPattern language source support bound type),
    (∃ (context : OneHoleContext) (redex contractum : Pattern),
      EquationInstance defaultBasePremises language redex contractum ∧
        left.term.1 = context.fill redex ∧
        right.term.1 = context.fill contractum) →
      EquationEquiv defaultBasePremises language
        (left.substitute assignment).1 (right.substitute assignment).1

/-- Exact language-level boundary needed to transport every generator of the
support-safe contextual equation relation. -/
def SupportedEquationSubstitutionStable (language : LanguageDef) : Prop :=
  AuthoredEquationSubstitutionStable language ∧
    ReflectiveEquationSubstitutionStable language

/-! ## Naturality under ambient binder embeddings

Supported free-variable substitution and ambient binder renaming are distinct
context actions.  The latter fixes binders introduced inside the traversed
syntax and embeds only the surrounding de Bruijn context.  Exact canonical
representatives need not commute with such an embedding: a reflective
parallel canonicalizer may choose a different deterministic order after
indices move.  The semantic requirement is consequently stated in the sole
authored `EquationEquiv`, one generator family at a time. -/

private theorem renameAmbientBVarsAt_finishNormalizeReflectiveApply
    (declaration : ReflectivePresentationDecl) (rename : Nat → Nat)
    (depth : Nat) (constructor : String) (arguments : List Pattern) :
    ContextSubstitution.renameAmbientBVarsAt rename depth
        (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
          declaration constructor arguments) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
        declaration constructor
        (arguments.map
          (ContextSubstitution.renameAmbientBVarsAt rename depth)) := by
  by_cases quoted : constructor = declaration.quoteConstructor
  · subst constructor
    cases arguments with
    | nil =>
        simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
          ContextSubstitution.renameAmbientBVarsAt]
    | cons first rest =>
        cases rest with
        | nil =>
            cases first with
            | apply nestedConstructor nestedArguments =>
                cases nestedArguments with
                | nil =>
                    simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                      ContextSubstitution.renameAmbientBVarsAt]
                | cons name tail =>
                    cases tail with
                    | nil =>
                        by_cases dropped :
                            nestedConstructor = declaration.dropConstructor
                        · subst nestedConstructor
                          simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                            ContextSubstitution.renameAmbientBVarsAt]
                        · simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                            ContextSubstitution.renameAmbientBVarsAt, dropped]
                    | cons second tail =>
                        simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                          ContextSubstitution.renameAmbientBVarsAt]
            | bvar index =>
                by_cases inside : index < depth <;>
                  simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                    ContextSubstitution.renameAmbientBVarsAt, inside]
            | fvar name =>
                simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                  ContextSubstitution.renameAmbientBVarsAt]
            | lambda binder body =>
                simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                  ContextSubstitution.renameAmbientBVarsAt]
            | multiLambda arity binders body =>
                simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                  ContextSubstitution.renameAmbientBVarsAt]
            | subst body replacement =>
                simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                  ContextSubstitution.renameAmbientBVarsAt]
            | collection collectionType elements rest =>
                simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                  ContextSubstitution.renameAmbientBVarsAt]
        | cons second tail =>
            simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
              ContextSubstitution.renameAmbientBVarsAt]
  · simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
      quoted, ContextSubstitution.renameAmbientBVarsAt]

private theorem canonicalize_finishNormalizeReflectiveApply
    (declaration : ReflectivePresentationDecl) (constructor : String)
    (quote_ne_drop : declaration.quoteConstructor ≠
      declaration.dropConstructor) (arguments : List Pattern) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
        (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
          declaration constructor arguments) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
        (.apply constructor arguments) := by
  by_cases quoted : constructor = declaration.quoteConstructor
  · subst constructor
    cases arguments with
    | nil =>
        simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
    | cons first rest =>
        cases rest with
        | nil =>
            cases first with
            | apply nestedConstructor nestedArguments =>
                cases nestedArguments with
                | nil =>
                    simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
                | cons name tail =>
                    cases tail with
                    | nil =>
                        by_cases dropped :
                            nestedConstructor = declaration.dropConstructor
                        · subst nestedConstructor
                          have dropCanonical :
                              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                                  declaration
                                  (.apply declaration.dropConstructor [name]) =
                                .apply declaration.dropConstructor
                                  [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                                    declaration name] := by
                            simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
                              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
                              Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                              Ne.symm quote_ne_drop]
                          rw [show
                            Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
                                declaration declaration.quoteConstructor
                                [.apply declaration.dropConstructor [name]] =
                              name by
                            simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]]
                          change
                            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                                declaration name =
                              Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
                                declaration declaration.quoteConstructor
                                (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                                  declaration
                                  [.apply declaration.dropConstructor [name]])
                          rw [show
                            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                                declaration
                                [.apply declaration.dropConstructor [name]] =
                              [.apply declaration.dropConstructor
                                [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                                  declaration name]] by
                            simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
                              dropCanonical]]
                          simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]
                        · simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
                            dropped]
                    | cons second tail =>
                        simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
            | bvar index =>
                simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                  Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
            | fvar name =>
                simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                  Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
            | lambda binder body =>
                simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                  Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
            | multiLambda arity binders body =>
                simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                  Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
            | subst body replacement =>
                simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                  Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
            | collection collectionType elements rest =>
                simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                  Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
        | cons second tail =>
            simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
  · simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
      quoted,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]

private theorem renameAmbientBVarsAt_eq_nullary_apply_iff
    (rename : Nat → Nat) (depth : Nat) (constructor : String)
    (pattern : Pattern) :
    ContextSubstitution.renameAmbientBVarsAt rename depth pattern =
        .apply constructor [] ↔
      pattern = .apply constructor [] := by
  cases pattern with
  | bvar index =>
      by_cases inside : index < depth <;>
        simp [ContextSubstitution.renameAmbientBVarsAt, inside]
  | fvar name => simp [ContextSubstitution.renameAmbientBVarsAt]
  | apply label arguments =>
      simp [ContextSubstitution.renameAmbientBVarsAt]
  | lambda binder body => simp [ContextSubstitution.renameAmbientBVarsAt]
  | multiLambda arity binders body =>
      simp [ContextSubstitution.renameAmbientBVarsAt]
  | subst body replacement =>
      simp [ContextSubstitution.renameAmbientBVarsAt]
  | collection collectionType elements rest =>
      simp [ContextSubstitution.renameAmbientBVarsAt]

private theorem renameAmbientBVarsAt_parallelSplice
    (declaration : ReflectivePresentationDecl) (rename : Nat → Nat)
    (depth : Nat) (pattern : Pattern) :
    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice
        declaration pattern).map
          (ContextSubstitution.renameAmbientBVarsAt rename depth) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice declaration
        (ContextSubstitution.renameAmbientBVarsAt rename depth pattern) := by
  cases pattern with
  | bvar index =>
      by_cases inside : index < depth <;>
        simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
          ContextSubstitution.renameAmbientBVarsAt, inside]
  | fvar name =>
      simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
        ContextSubstitution.renameAmbientBVarsAt]
  | apply constructor arguments =>
      simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
        ContextSubstitution.renameAmbientBVarsAt]
  | lambda binder body =>
      simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
        ContextSubstitution.renameAmbientBVarsAt]
  | multiLambda arity binders body =>
      simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
        ContextSubstitution.renameAmbientBVarsAt]
  | subst body replacement =>
      simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
        ContextSubstitution.renameAmbientBVarsAt]
  | collection collectionType elements rest =>
      cases rest with
      | none =>
          by_cases selected :
              collectionType = declaration.parallelCollection <;>
            simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
              ContextSubstitution.renameAmbientBVarsAt, selected]
      | some restName =>
          simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
            ContextSubstitution.renameAmbientBVarsAt]

private theorem filter_renameAmbientBVarsAt_ne_nullary_apply
    (rename : Nat → Nat) (depth : Nat) (constructor : String) :
    ∀ patterns : List Pattern,
      ((patterns.map
          (ContextSubstitution.renameAmbientBVarsAt rename depth)).filter
            (fun pattern => pattern ≠ .apply constructor [])) =
        (patterns.filter
          (fun pattern => pattern ≠ .apply constructor [])).map
            (ContextSubstitution.renameAmbientBVarsAt rename depth)
  | [] => rfl
  | pattern :: patterns => by
      have preserved := renameAmbientBVarsAt_eq_nullary_apply_iff
        rename depth constructor pattern
      by_cases unit : pattern = .apply constructor []
      · subst pattern
        have mappedUnit :
            ContextSubstitution.renameAmbientBVarsAt rename depth
                (.apply constructor []) =
              .apply constructor [] := preserved.mpr rfl
        simp only [List.map_cons]
        rw [mappedUnit]
        simpa using
          (filter_renameAmbientBVarsAt_ne_nullary_apply rename depth
            constructor patterns)
      · simpa [preserved, unit] using
          congrArg (List.cons
            (ContextSubstitution.renameAmbientBVarsAt rename depth pattern))
            (filter_renameAmbientBVarsAt_ne_nullary_apply rename depth
              constructor patterns)

private theorem parallelContents_renameAmbientBVarsAt
    (declaration : ReflectivePresentationDecl) (rename : Nat → Nat)
    (depth : Nat) (patterns : List Pattern) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents declaration
        (patterns.map
          (ContextSubstitution.renameAmbientBVarsAt rename depth)) =
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents
        declaration patterns).map
          (ContextSubstitution.renameAmbientBVarsAt rename depth) := by
  unfold Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents
  rw [List.flatMap_map]
  have splices :
      (patterns.flatMap
          (fun pattern =>
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice
              declaration
              (ContextSubstitution.renameAmbientBVarsAt rename depth pattern))) =
        (patterns.flatMap
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice
            declaration)).map
              (ContextSubstitution.renameAmbientBVarsAt rename depth) := by
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro pattern membership
    exact (renameAmbientBVarsAt_parallelSplice declaration rename depth
      pattern).symm
  rw [splices]
  exact filter_renameAmbientBVarsAt_ne_nullary_apply rename depth
    declaration.parallelUnitConstructor _

private theorem normalizeParallelElements_renameAmbientBVarsAt_perm
    (declaration : ReflectivePresentationDecl) (rename : Nat → Nat)
    (depth : Nat) (patterns : List Pattern) :
    List.Perm
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements
        declaration
        (patterns.map
          (ContextSubstitution.renameAmbientBVarsAt rename depth)))
      ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements
        declaration patterns).map
          (ContextSubstitution.renameAmbientBVarsAt rename depth)) := by
  rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements_eq_sort_parallelContents,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements_eq_sort_parallelContents]
  let targetContents :=
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents declaration
      (patterns.map
        (ContextSubstitution.renameAmbientBVarsAt rename depth))
  let sourceContents :=
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents declaration
      patterns
  have contentsEquality : targetContents =
      sourceContents.map
        (ContextSubstitution.renameAmbientBVarsAt rename depth) := by
    exact parallelContents_renameAmbientBVarsAt declaration rename depth
      patterns
  exact
    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.sortPatterns_perm
      targetContents).trans
      ((List.Perm.of_eq contentsEquality).trans
        ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.sortPatterns_perm
          sourceContents |>.map
            (ContextSubstitution.renameAmbientBVarsAt rename depth)).symm))

private theorem renameAmbientBVarsAt_collapseParallel
    (declaration : ReflectivePresentationDecl) (rename : Nat → Nat)
    (depth : Nat) (patterns : List Pattern) :
    ContextSubstitution.renameAmbientBVarsAt rename depth
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
          declaration patterns) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel declaration
        (patterns.map
          (ContextSubstitution.renameAmbientBVarsAt rename depth)) := by
  cases patterns with
  | nil =>
      simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel,
        ContextSubstitution.renameAmbientBVarsAt]
  | cons first rest =>
      cases rest with
      | nil =>
          simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel]
      | cons second tail =>
          simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel,
            ContextSubstitution.renameAmbientBVarsAt]

/-- Ambient de Bruijn renaming may change the deterministic order selected
by a reflective parallel canonicalizer, but re-canonicalizing the renamed
source representative always recovers the same representative.  This is the
semantic factor law; it deliberately does not claim syntactic commutation
with canonicalization. -/
theorem canonicalize_renameAmbientBVarsAt_factor
    (declaration : ReflectivePresentationDecl)
    (quote_ne_drop : declaration.quoteConstructor ≠
      declaration.dropConstructor)
    (rename : Nat → Nat) (depth : Nat) (pattern : Pattern) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
        (ContextSubstitution.renameAmbientBVarsAt rename depth pattern) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
        (ContextSubstitution.renameAmbientBVarsAt rename depth
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
            declaration pattern)) := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      by_cases inside : index < depth <;>
        simp [ContextSubstitution.renameAmbientBVarsAt,
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize, inside]
  | hfvar name =>
      rfl
  | happly constructor arguments inductionHypothesis =>
      have listFactor :
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
              declaration
              (arguments.map
                (ContextSubstitution.renameAmbientBVarsAt rename depth)) =
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
              declaration
              ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                declaration arguments).map
                  (ContextSubstitution.renameAmbientBVarsAt rename depth)) := by
        simp only [
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList_eq_map,
          List.map_map]
        apply List.map_congr_left
        intro argument membership
        exact inductionHypothesis argument membership depth
      simp only [ContextSubstitution.renameAmbientBVarsAt,
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
      rw [listFactor,
        renameAmbientBVarsAt_finishNormalizeReflectiveApply,
        canonicalize_finishNormalizeReflectiveApply declaration constructor
          quote_ne_drop]
      rfl
  | hlambda binder body inductionHypothesis =>
      simp [ContextSubstitution.renameAmbientBVarsAt,
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
        inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [ContextSubstitution.renameAmbientBVarsAt,
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
        inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [ContextSubstitution.renameAmbientBVarsAt,
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
        bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      have listFactor :
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
              declaration
              (elements.map
                (ContextSubstitution.renameAmbientBVarsAt rename depth)) =
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
              declaration
              ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                declaration elements).map
                  (ContextSubstitution.renameAmbientBVarsAt rename depth)) := by
        simp only [
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList_eq_map,
          List.map_map]
        apply List.map_congr_left
        intro element membership
        exact inductionHypothesis element membership depth
      cases rest with
      | some restName =>
          simp only [ContextSubstitution.renameAmbientBVarsAt,
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
          exact congrArg
            (fun normalized =>
              Pattern.collection collectionType normalized (some restName))
            listFactor
      | none =>
          by_cases isParallel :
              collectionType = declaration.parallelCollection
          · subst collectionType
            simp only [ContextSubstitution.renameAmbientBVarsAt,
              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
              beq_self_eq_true, if_true]
            rw [listFactor]
            let sourceCanonical :=
              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                declaration elements
            let sourceNormalized :=
              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements
                declaration sourceCanonical
            calc
              _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                    declaration
                    (.collection declaration.parallelCollection
                      (sourceCanonical.map
                        (ContextSubstitution.renameAmbientBVarsAt rename depth))
                      none) := by
                  dsimp [sourceCanonical]
                  simp only [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
                    beq_self_eq_true, if_true]
              _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                    declaration
                    (.collection declaration.parallelCollection
                      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements
                        declaration
                        (sourceCanonical.map
                          (ContextSubstitution.renameAmbientBVarsAt rename depth)))
                      none) :=
                  Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize_parallel_normalize_input
                    declaration _
              _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                    declaration
                    (.collection declaration.parallelCollection
                      (sourceNormalized.map
                        (ContextSubstitution.renameAmbientBVarsAt rename depth))
                      none) :=
                  Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize_parallel_permutation
                    declaration
                      (by
                        simpa [sourceNormalized] using
                          (normalizeParallelElements_renameAmbientBVarsAt_perm
                            declaration rename depth sourceCanonical))
              _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                    declaration
                    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
                      declaration
                      (sourceNormalized.map
                        (ContextSubstitution.renameAmbientBVarsAt rename depth))) :=
                  Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize_parallel_collapse
                    declaration _
              _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                    declaration
                    (ContextSubstitution.renameAmbientBVarsAt rename depth
                      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
                        declaration sourceNormalized)) := by
                  exact congrArg
                    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                      declaration)
                    (renameAmbientBVarsAt_collapseParallel declaration rename
                      depth sourceNormalized).symm
          · have selectedFalse :
                (collectionType == declaration.parallelCollection) = false := by
              simp [isParallel]
            simpa [ContextSubstitution.renameAmbientBVarsAt,
              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
              selectedFalse] using congrArg
              (fun normalized =>
                Pattern.collection collectionType normalized none)
              listFactor

/-- Ordinary authored equation instances remain valid, up to the authored
contextual equation relation, after any order-preserving embedding of the
ambient binder context. -/
def AuthoredEquationAmbientRenamingStable (language : LanguageDef) : Prop :=
  ∀ (rename : Nat → Nat), StrictMono rename → ∀ (depth : Nat)
    (context : OneHoleContext) {redex contractum : Pattern},
    EquationInstance defaultBasePremises language redex contractum →
      EquationEquiv defaultBasePremises language
        (ContextSubstitution.renameAmbientBVarsAt rename depth
          (context.fill redex))
        (ContextSubstitution.renameAmbientBVarsAt rename depth
          (context.fill contractum))

/-- Equality generated by one authored reflective presentation remains valid,
up to that same authored equation relation, after an order-preserving ambient
binder embedding.  This deliberately does not demand equality of the two
deterministic representatives after embedding. -/
def ReflectiveEquationAmbientRenamingStable (language : LanguageDef) : Prop :=
  ∀ (rename : Nat → Nat), StrictMono rename → ∀ (depth : Nat)
    (context : OneHoleContext) {declaration : ReflectivePresentationDecl}
    {left right : Pattern},
    declaration ∈ language.reflectivePresentations →
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        declaration left =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        declaration right →
      EquationEquiv defaultBasePremises language
        (ContextSubstitution.renameAmbientBVarsAt rename depth
          (context.fill left))
        (ContextSubstitution.renameAmbientBVarsAt rename depth
          (context.fill right))

/-- A validated reflective generator remains one authored generator after an
ambient binder embedding.  The transported one-hole context records the
binder depth at its hole, while the canonical factor law absorbs any change
in deterministic parallel ordering. -/
theorem reflectiveEquationContextStep_renameAmbientBVarsAt_of_validate_eq_nil
    (language : LanguageDef) (valid : language.validate = []) :
    ∀ (rename : Nat → Nat) (depth : Nat) (context : OneHoleContext)
      {declaration : ReflectivePresentationDecl} {left right : Pattern},
      declaration ∈ language.reflectivePresentations →
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          declaration left =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          declaration right →
      EquationContextStep defaultBasePremises language
        (ContextSubstitution.renameAmbientBVarsAt rename depth
          (context.fill left))
        (ContextSubstitution.renameAmbientBVarsAt rename depth
          (context.fill right)) := by
  intro rename depth context declaration left right membership representatives
  let transported :=
    ContextSubstitution.renameAmbientContextAt rename depth context
  have declarationValid :=
    LanguageDef.reflectivePresentation_validate_of_validate_eq_nil
      language valid declaration membership
  have quote_ne_drop :=
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.quoteConstructor_ne_dropConstructor_of_validate
      language declaration declarationValid
  have transportedRepresentatives :
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          (ContextSubstitution.renameAmbientBVarsAt rename transported.2 left) =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
          (ContextSubstitution.renameAmbientBVarsAt rename transported.2 right) := by
    calc
      _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
            (ContextSubstitution.renameAmbientBVarsAt rename transported.2
              (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                declaration left)) :=
          canonicalize_renameAmbientBVarsAt_factor declaration quote_ne_drop
            rename transported.2 left
      _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
            (ContextSubstitution.renameAmbientBVarsAt rename transported.2
              (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                declaration right)) := by rw [representatives]
      _ = _ :=
          (canonicalize_renameAmbientBVarsAt_factor declaration quote_ne_drop
            rename transported.2 right).symm
  have transportedStep : EquationContextStep defaultBasePremises language
      (transported.1.fill
        (ContextSubstitution.renameAmbientBVarsAt rename transported.2 left))
      (transported.1.fill
        (ContextSubstitution.renameAmbientBVarsAt rename transported.2 right)) :=
    EquationContextStep.reflectiveInContext transported.1 membership
      transportedRepresentatives
  simpa only [ContextSubstitution.renameAmbientBVarsAt_fill] using
    transportedStep

/-- Validation is sufficient for reflective ambient-renaming stability.
Canonicalization need not commute syntactically with renaming: the factor law
shows that re-canonicalization absorbs any change in deterministic ordering,
and transported one-hole contexts supply the contextual closure. -/
theorem reflectiveEquationAmbientRenamingStable_of_validate_eq_nil
    (language : LanguageDef) (valid : language.validate = []) :
    ReflectiveEquationAmbientRenamingStable language := by
  intro rename _strict depth context declaration left right membership
    representatives
  exact Relation.EqvGen.rel _ _
    (reflectiveEquationContextStep_renameAmbientBVarsAt_of_validate_eq_nil
      language valid rename depth context membership representatives)

/-- Exact pair of generator obligations making the authored contextual
equation setoid natural under ambient binder embeddings. -/
def SupportedEquationAmbientRenamingStable (language : LanguageDef) : Prop :=
  AuthoredEquationAmbientRenamingStable language ∧
    ReflectiveEquationAmbientRenamingStable language

/-- The two ambient-renaming obligations cover exactly the constructors of
one authored contextual equation generator. -/
theorem equationContextStep_renameAmbientBVarsAt
    {language : LanguageDef}
    (stable : SupportedEquationAmbientRenamingStable language)
    (rename : Nat → Nat) (strict : StrictMono rename) (depth : Nat)
    {left right : Pattern}
    (step : EquationContextStep defaultBasePremises language left right) :
    EquationEquiv defaultBasePremises language
      (ContextSubstitution.renameAmbientBVarsAt rename depth left)
      (ContextSubstitution.renameAmbientBVarsAt rename depth right) := by
  cases step with
  | inContext context equationWitness =>
      exact stable.1 rename strict depth context equationWitness
  | reflectiveInContext context membership representatives =>
      exact stable.2 rename strict depth context membership representatives

/-- The full least authored equation equivalence is natural under every
certified ambient binder embedding. -/
theorem equationEquiv_renameAmbientBVarsAt
    {language : LanguageDef}
    (stable : SupportedEquationAmbientRenamingStable language)
    (rename : Nat → Nat) (strict : StrictMono rename) (depth : Nat)
    {left right : Pattern}
    (equivalent : EquationEquiv defaultBasePremises language left right) :
    EquationEquiv defaultBasePremises language
      (ContextSubstitution.renameAmbientBVarsAt rename depth left)
      (ContextSubstitution.renameAmbientBVarsAt rename depth right) := by
  exact equationEquiv_map_of_contextStep
    (ContextSubstitution.renameAmbientBVarsAt rename depth)
    (fun step => equationContextStep_renameAmbientBVarsAt
      stable rename strict depth step)
    equivalent

/-- Ordinary capture-avoiding weakening is the affine specialization of
ambient-renaming naturality.  This form is consumed by finite Cost boundary
assignments, whose semantic agreement must persist under every extra binder
inserted by a surrounding skeleton. -/
theorem equationEquiv_liftBVars
    {language : LanguageDef}
    (stable : SupportedEquationAmbientRenamingStable language)
    (cutoff shift : Nat) {left right : Pattern}
    (equivalent : EquationEquiv defaultBasePremises language left right) :
    EquationEquiv defaultBasePremises language
      (liftBVars cutoff shift left) (liftBVars cutoff shift right) := by
  have strict : StrictMono (fun index : Nat => index + shift) := by
    intro first second order
    exact Nat.add_lt_add_right order shift
  simpa only [ContextSubstitution.renameAmbientBVarsAt_add_eq_liftBVars] using
    equationEquiv_renameAmbientBVarsAt stable
      (fun index : Nat => index + shift) strict cutoff equivalent

/-! ### Typed ambient weakening

Raw ambient-renaming naturality is useful for compiler erasure, but it cannot
certify that every intermediate representative remains in one typed open
fiber.  The following carrier operation keeps the weakening and all four
open-object certificates together. -/

/-- Insert an exact block of inner binders at the root of a typed open
pattern.  De Bruijn indices are shifted by precisely the inserted length;
locally nameless metadata, the object boundary, and reflective scope are
transported by the same operation. -/
def OpenPattern.weakenRoot
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {type : TypeExpr}
    (pattern : OpenPattern language free bound type)
    (inner : List TypeExpr) :
    OpenPattern language free (inner ++ bound) type := by
  refine ⟨liftBVars 0 inner.length pattern.1, ?_, ?_, ?_, ?_⟩
  · simpa using pattern.2.1.liftBVars_insert
      (inner := []) (outer := bound) (inserted := inner)
  · simpa using pattern.2.2.1
  · simpa using pattern.2.2.2.1
  · intro presentation membership
    have lifted := ContextSubstitution.binderSafeAt_liftBVars
      presentation.quoteConstructor
      (ambient := bound.length) (cutoff := 0) (shift := inner.length)
      (pattern.2.2.2.2 presentation membership)
    simpa only [List.length_append, Nat.add_zero, Nat.add_comm] using lifted

@[simp]
theorem OpenPattern.weakenRoot_pattern
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {type : TypeExpr}
    (pattern : OpenPattern language free bound type)
    (inner : List TypeExpr) :
    (pattern.weakenRoot inner).1 = liftBVars 0 inner.length pattern.1 :=
  rfl

/-- Extend the outer binder suffix of a typed open pattern without changing
its raw syntax.  Existing de Bruijn indices keep their meaning because the
new binders are strictly outside the represented term. -/
def OpenPattern.extendOuter
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {type : TypeExpr}
    (pattern : OpenPattern language free bound type)
    (outer : List TypeExpr) :
    OpenPattern language free (bound ++ outer) type := by
  refine ⟨pattern.1, pattern.2.1.extendOuter outer,
    pattern.2.2.1, pattern.2.2.2.1, ?_⟩
  intro presentation membership
  exact binderSafeAt_mono presentation.quoteConstructor
    (pattern.2.2.2.2 presentation membership) (by simp)

@[simp]
theorem OpenPattern.extendOuter_pattern
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {type : TypeExpr}
    (pattern : OpenPattern language free bound type)
    (outer : List TypeExpr) :
    (pattern.extendOuter outer).1 = pattern.1 :=
  rfl

/-- Map a typed equation path through an operation that preserves one
authored generator.  This is the carrier-level counterpart of the usual
`EqvGen` map: every intermediate vertex is produced by `map`, so its typing
and object certificates are retained rather than reconstructed from a raw
equation path. -/
theorem openPatternEquationSetoid_map
    {language : LanguageDef}
    {sourceFree targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {sourceType targetType : TypeExpr}
    (map : OpenPattern language sourceFree sourceBound sourceType →
      OpenPattern language targetFree targetBound targetType)
    (preserves : ∀ {left right},
      openPatternEquationGenerator language sourceFree sourceBound sourceType
          left right →
        openPatternEquationGenerator language targetFree targetBound targetType
          (map left) (map right))
    {left right : OpenPattern language sourceFree sourceBound sourceType}
    (equivalent :
      (openPatternEquationSetoid language sourceFree sourceBound sourceType).r
        left right) :
    (openPatternEquationSetoid language targetFree targetBound targetType).r
      (map left) (map right) := by
  induction equivalent with
  | rel left right generator =>
      exact Relation.EqvGen.rel _ _ (preserves generator)
  | refl pattern =>
      exact Relation.EqvGen.refl (map pattern)
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

/-- Inject one authored contextual generator whose two endpoints are already
packaged in the same typed open fiber.  The endpoint certificates are the
entire distinction from the false operation that attempts to lift an opaque
raw equivalence path after the fact. -/
theorem openPatternEquationSetoid_of_contextStep
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {type : TypeExpr}
    {left right : OpenPattern language free bound type}
    (step : EquationContextStep defaultBasePremises language left.1 right.1) :
    (openPatternEquationSetoid language free bound type).r left right :=
  Relation.EqvGen.rel left right step

/-- Lift a typed equation path through one syntax-derived context once the
caller supplies the typed packaging of every possible hole inhabitant.  The
packaging hypothesis is intentionally proof-relevant: it prevents a
contextual congruence proof from manufacturing ill-typed intermediate
applications or binder forms. -/
theorem openPatternEquationSetoid_fill_congr
    {language : LanguageDef}
    {sourceFree targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {sourceType targetType : TypeExpr}
    (context : OneHoleContext)
    (fill : OpenPattern language sourceFree sourceBound sourceType →
      OpenPattern language targetFree targetBound targetType)
    (fill_pattern : ∀ pattern, (fill pattern).1 = context.fill pattern.1)
    {left right : OpenPattern language sourceFree sourceBound sourceType}
    (equivalent :
      (openPatternEquationSetoid language sourceFree sourceBound sourceType).r
        left right) :
    (openPatternEquationSetoid language targetFree targetBound targetType).r
      (fill left) (fill right) := by
  apply openPatternEquationSetoid_map fill (equivalent := equivalent)
  intro first second generator
  unfold openPatternEquationGenerator at generator ⊢
  simpa only [fill_pattern] using
    EquationSemantics.equationContextStep_fill context generator

/-- Extending the inert outer binder suffix maps every typed equation path
to the correspondingly extended typed fiber.  Raw syntax and authored edges
are unchanged; only the proof-relevant binder index is enlarged. -/
theorem openPatternEquationSetoid_extendOuter
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {type : TypeExpr}
    {left right : OpenPattern language free bound type}
    (equivalent :
      (openPatternEquationSetoid language free bound type).r left right)
    (outer : List TypeExpr) :
    (openPatternEquationSetoid language free (bound ++ outer) type).r
      (left.extendOuter outer) (right.extendOuter outer) := by
  apply openPatternEquationSetoid_map (map := fun pattern =>
    pattern.extendOuter outer) (equivalent := equivalent)
  intro first second generator
  simpa [openPatternEquationGenerator] using generator

/-- Apply a support-certified structural assignment while retaining a
possibly sealed outer binder suffix.  `available` is precisely the prefix
visible since the nearest quote; unlike the root-only operation, this carrier
therefore also packages recursive substitution below quotation boundaries. -/
def OpenPattern.substituteReflectiveSupportedAt
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound available sealed : List TypeExpr} {type : TypeExpr}
    (pattern : OpenPattern language source bound type)
    (boundShape : bound = available ++ sealed)
    (assignment : SupportedOpenAssignment language source target support)
    (safe : pattern.2.1.ReflectiveSupportSafeAt support available) :
    OpenPattern language target bound type := by
  refine ⟨ReflectiveContextSupport.substituteAt language support
      assignment.assignment available.length pattern.1, ?_, ?_, ?_, ?_⟩
  · exact safe.substitute boundShape assignment.toSupportedAssignment
  · exact safe.substituteCanonicalBinderMetadata assignment pattern.2.2.1
  · exact safe.substituteObjectPattern assignment pattern.2.2.2.1
  · intro presentation membership
    exact safe.substituteBinderSafeAt assignment presentation membership
      (by rw [boundShape]; simp)
      (pattern.2.2.2.2 presentation membership)

@[simp]
theorem OpenPattern.substituteReflectiveSupportedAt_pattern
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound available sealed : List TypeExpr} {type : TypeExpr}
    (pattern : OpenPattern language source bound type)
    (boundShape : bound = available ++ sealed)
    (assignment : SupportedOpenAssignment language source target support)
    (safe : pattern.2.1.ReflectiveSupportSafeAt support available) :
    (pattern.substituteReflectiveSupportedAt boundShape assignment safe).1 =
      ReflectiveContextSupport.substituteAt language support
        assignment.assignment available.length pattern.1 :=
  rfl

/-! ### Split binder-fiber carrier

Quotation resets the binder prefix visible to reflective substitution without
removing the lexically present outer suffix from typing.  `OpenPattern` stores
only their concatenation; the following proof refinement retains the split.
Its equation generator is still exactly the authored `LanguageDef` generator.
-/

/-- A well-sorted open object whose binder context is split into the prefix
visible since the nearest quote and the sealed outer suffix. -/
structure AvailableOpenPattern (language : LanguageDef)
    (free : FreeTypeContext) (available outer : List TypeExpr)
    (type : TypeExpr) where
  pattern : Pattern
  typed : HasType language free (available ++ outer) pattern type
  canonicalBinderMetadata : pattern.hasCanonicalBinderMetadata = true
  objectPattern : isObjectPattern pattern = true
  reflectiveScope : ReflectiveScopeSafeAt language available.length pattern

namespace AvailableOpenPattern

/-- Package the four independently checked open-object certificates without
changing their sole authored typing judgment. -/
def ofCertificates
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language free (available ++ outer) pattern type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (objectPattern : isObjectPattern pattern = true)
    (reflectiveScope : ReflectiveScopeSafeAt language available.length
      pattern) :
    AvailableOpenPattern language free available outer type :=
  ⟨pattern, typed, canonical, objectPattern, reflectiveScope⟩

@[simp]
theorem ofCertificates_pattern
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language free (available ++ outer) pattern type)
    (canonical : pattern.hasCanonicalBinderMetadata = true)
    (objectPattern : isObjectPattern pattern = true)
    (reflectiveScope : ReflectiveScopeSafeAt language available.length
      pattern) :
    (ofCertificates typed canonical objectPattern reflectiveScope).pattern =
      pattern :=
  rfl

@[ext]
theorem ext
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {type : TypeExpr}
    {left right : AvailableOpenPattern language free available outer type}
    (patterns : left.pattern = right.pattern) : left = right := by
  cases left
  cases right
  cases patterns
  rfl

/-- Reindex only the free-context proof of a split-fiber open pattern.  The
raw pattern, binder split, type, and all four admission certificates are
unchanged. -/
def castFree
    {language : LanguageDef} {sourceFree targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {type : TypeExpr}
    (freeEquality : sourceFree = targetFree)
    (term : AvailableOpenPattern language sourceFree available outer type) :
    AvailableOpenPattern language targetFree available outer type := by
  cases freeEquality
  exact term

/-- Reindex the proof-relevant split-binder fiber of an open pattern.

The raw pattern is unchanged.  Only propositionally equal available/outer
contexts and result types are transported, so this operation cannot invent a
typing derivation or alter reflective scope. -/
def reindexFiber
    {language : LanguageDef} {free : FreeTypeContext}
    {sourceAvailable targetAvailable sourceOuter targetOuter : List TypeExpr}
    {sourceType targetType : TypeExpr}
    (availableEquality : sourceAvailable = targetAvailable)
    (outerEquality : sourceOuter = targetOuter)
    (typeEquality : sourceType = targetType)
    (term : AvailableOpenPattern language free sourceAvailable sourceOuter
      sourceType) :
    AvailableOpenPattern language free targetAvailable targetOuter targetType := by
  cases availableEquality
  cases outerEquality
  cases typeEquality
  exact term

@[simp]
theorem reindexFiber_pattern
    {language : LanguageDef} {free : FreeTypeContext}
    {sourceAvailable targetAvailable sourceOuter targetOuter : List TypeExpr}
    {sourceType targetType : TypeExpr}
    (availableEquality : sourceAvailable = targetAvailable)
    (outerEquality : sourceOuter = targetOuter)
    (typeEquality : sourceType = targetType)
    (term : AvailableOpenPattern language free sourceAvailable sourceOuter
      sourceType) :
    (term.reindexFiber availableEquality outerEquality typeEquality).pattern =
      term.pattern := by
  cases availableEquality
  cases outerEquality
  cases typeEquality
  rfl

@[simp]
theorem castFree_pattern
    {language : LanguageDef} {sourceFree targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {type : TypeExpr}
    (freeEquality : sourceFree = targetFree)
    (term : AvailableOpenPattern language sourceFree available outer type) :
    (term.castFree freeEquality).pattern = term.pattern := by
  cases freeEquality
  rfl

/-- Free-context reindexing preserves the support derivation paired with the
split-fiber object. -/
theorem castFree_supportSafe
    {language : LanguageDef} {sourceFree targetFree : FreeTypeContext}
    {support : ContextSupport.Support}
    {available outer : List TypeExpr} {type : TypeExpr}
    (freeEquality : sourceFree = targetFree)
    (term : AvailableOpenPattern language sourceFree available outer type)
    (safe : term.typed.ReflectiveSupportSafeAt support available) :
    (term.castFree freeEquality).typed.ReflectiveSupportSafeAt support
      available := by
  cases freeEquality
  exact safe

/-- Forget only the binder split.  Reflective scope weakens monotonically
from the visible prefix to the complete lexical binder context. -/
def toOpenPattern
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {type : TypeExpr}
    (pattern : AvailableOpenPattern language free available outer type) :
    OpenPattern language free (available ++ outer) type :=
  ⟨pattern.pattern, pattern.typed, pattern.canonicalBinderMetadata,
    pattern.objectPattern, by
      intro presentation membership
      exact binderSafeAt_mono presentation.quoteConstructor
        (pattern.reflectiveScope presentation membership) (by simp)⟩

@[simp]
theorem toOpenPattern_pattern
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {type : TypeExpr}
    (pattern : AvailableOpenPattern language free available outer type) :
    pattern.toOpenPattern.1 = pattern.pattern :=
  rfl

/-- An ordinary open pattern is the specialization with no sealed suffix. -/
def ofOpenPattern
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {type : TypeExpr}
    (pattern : OpenPattern language free bound type) :
    AvailableOpenPattern language free bound [] type :=
  ⟨pattern.1, by simpa using pattern.2.1, pattern.2.2.1,
    pattern.2.2.2.1, pattern.2.2.2.2⟩

/-- Retain an open pattern's visible binder prefix while adjoining a sealed
outer suffix.  The raw term is unchanged and the new binders are strictly
outside every existing de Bruijn occurrence. -/
def ofOpenPatternWithOuter
    {language : LanguageDef} {free : FreeTypeContext}
    {available : List TypeExpr} {type : TypeExpr}
    (pattern : OpenPattern language free available type)
    (outer : List TypeExpr) :
    AvailableOpenPattern language free available outer type where
  pattern := pattern.1
  typed := pattern.2.1.extendOuter outer
  canonicalBinderMetadata := pattern.2.2.1
  objectPattern := pattern.2.2.2.1
  reflectiveScope := pattern.2.2.2.2

@[simp]
theorem ofOpenPatternWithOuter_pattern
    {language : LanguageDef} {free : FreeTypeContext}
    {available : List TypeExpr} {type : TypeExpr}
    (pattern : OpenPattern language free available type)
    (outer : List TypeExpr) :
    (ofOpenPatternWithOuter pattern outer).pattern = pattern.1 :=
  rfl

@[simp]
theorem ofOpenPattern_pattern
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {type : TypeExpr}
    (pattern : OpenPattern language free bound type) :
    (ofOpenPattern pattern).pattern = pattern.1 :=
  rfl

/-- One authored contextual edge internal to an exact split binder fiber. -/
def equationGenerator
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {type : TypeExpr}
    (left right : AvailableOpenPattern language free available outer type) :
    Prop :=
  EquationContextStep defaultBasePremises language left.pattern right.pattern

/-- Least authored contextual equivalence retaining the quote-visible binder
prefix at every intermediate vertex. -/
def equationSetoid (language : LanguageDef) (free : FreeTypeContext)
    (available outer : List TypeExpr) (type : TypeExpr) :
    Setoid (AvailableOpenPattern language free available outer type) where
  r := Relation.EqvGen equationGenerator
  iseqv :=
    { refl := Relation.EqvGen.refl
      symm := fun relation => Relation.EqvGen.symm _ _ relation
      trans := fun first second => Relation.EqvGen.trans _ _ _ first second }

/-- Forgetting the binder split maps the refined relation into the ordinary
typed open relation without changing a single authored generator. -/
theorem equationSetoid_to_openPatternEquationSetoid
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {type : TypeExpr}
    {left right : AvailableOpenPattern language free available outer type}
    (equivalent :
      (equationSetoid language free available outer type).r left right) :
    (openPatternEquationSetoid language free (available ++ outer) type).r
      left.toOpenPattern right.toOpenPattern := by
  induction equivalent with
  | rel left right generator =>
      exact Relation.EqvGen.rel _ _ generator
  | refl pattern =>
      exact Relation.EqvGen.refl pattern.toOpenPattern
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

/-- Adjoining the same sealed outer suffix maps a typed open equation path
into the split binder carrier without altering any authored generator. -/
theorem openPatternEquationSetoid_to_availableWithOuter
    {language : LanguageDef} {free : FreeTypeContext}
    {available : List TypeExpr} {type : TypeExpr}
    {left right : OpenPattern language free available type}
    (outer : List TypeExpr)
    (equivalent :
      (openPatternEquationSetoid language free available type).r left right) :
    (equationSetoid language free available outer type).r
      (ofOpenPatternWithOuter left outer)
      (ofOpenPatternWithOuter right outer) := by
  induction equivalent with
  | rel left right generator =>
      exact Relation.EqvGen.rel _ _ generator
  | refl pattern =>
      exact Relation.EqvGen.refl (ofOpenPatternWithOuter pattern outer)
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

/-- Map a split-fiber equation path through an operation preserving each
authored generator. -/
theorem equationSetoid_map
    {language : LanguageDef}
    {sourceFree targetFree : FreeTypeContext}
    {sourceAvailable sourceOuter targetAvailable targetOuter : List TypeExpr}
    {sourceType targetType : TypeExpr}
    (map : AvailableOpenPattern language sourceFree sourceAvailable sourceOuter
        sourceType →
      AvailableOpenPattern language targetFree targetAvailable targetOuter
        targetType)
    (preserves : ∀ {left right}, equationGenerator left right →
      equationGenerator (map left) (map right))
    {left right : AvailableOpenPattern language sourceFree sourceAvailable
      sourceOuter sourceType}
    (equivalent :
      (equationSetoid language sourceFree sourceAvailable sourceOuter
        sourceType).r left right) :
    (equationSetoid language targetFree targetAvailable targetOuter
      targetType).r (map left) (map right) := by
  induction equivalent with
  | rel left right generator =>
      exact Relation.EqvGen.rel _ _ (preserves generator)
  | refl pattern =>
      exact Relation.EqvGen.refl (map pattern)
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

/-- Typed contextual congruence in the split binder carrier.  The supplied
packager is responsible only for typing the enclosing syntax; generator
composition remains the sole authored contextual relation. -/
theorem equationSetoid_fill_congr
    {language : LanguageDef}
    {sourceFree targetFree : FreeTypeContext}
    {sourceAvailable sourceOuter targetAvailable targetOuter : List TypeExpr}
    {sourceType targetType : TypeExpr}
    (context : OneHoleContext)
    (fill : AvailableOpenPattern language sourceFree sourceAvailable sourceOuter
        sourceType →
      AvailableOpenPattern language targetFree targetAvailable targetOuter
        targetType)
    (fill_pattern : ∀ pattern,
      (fill pattern).pattern = context.fill pattern.pattern)
    {left right : AvailableOpenPattern language sourceFree sourceAvailable
      sourceOuter sourceType}
    (equivalent :
      (equationSetoid language sourceFree sourceAvailable sourceOuter
        sourceType).r left right) :
    (equationSetoid language targetFree targetAvailable targetOuter
      targetType).r (fill left) (fill right) := by
  apply equationSetoid_map fill (equivalent := equivalent)
  intro first second generator
  unfold equationGenerator at generator ⊢
  simpa only [fill_pattern] using
    EquationSemantics.equationContextStep_fill context generator

/-- Enclose one split-fiber object in an ordinary single binder. -/
def lambda
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {domain codomain : TypeExpr}
    (binder : Option String) (binderCanonical : binder.isNone = true)
    (body : AvailableOpenPattern language free (domain :: available) outer
      codomain) :
    AvailableOpenPattern language free available outer
      (.arrow domain codomain) where
  pattern := .lambda binder body.pattern
  typed := .lambda body.typed
  canonicalBinderMetadata := by
    simp [Pattern.hasCanonicalBinderMetadata, binderCanonical,
      body.canonicalBinderMetadata]
  objectPattern := by
    simpa [isObjectPattern] using body.objectPattern
  reflectiveScope := by
    intro presentation membership
    simpa [binderSafeAt, List.length_cons] using
      body.reflectiveScope presentation membership

@[simp]
theorem lambda_pattern
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {domain codomain : TypeExpr}
    (binder : Option String) (binderCanonical : binder.isNone = true)
    (body : AvailableOpenPattern language free (domain :: available) outer
      codomain) :
    (body.lambda binder binderCanonical).pattern = .lambda binder body.pattern :=
  rfl

/-- Typed equation congruence beneath one ordinary binder. -/
theorem equationSetoid_lambda_congr
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {domain codomain : TypeExpr}
    (binder : Option String) (binderCanonical : binder.isNone = true)
    {left right : AvailableOpenPattern language free (domain :: available)
      outer codomain}
    (equivalent :
      (equationSetoid language free (domain :: available) outer codomain).r
        left right) :
    (equationSetoid language free available outer (.arrow domain codomain)).r
      (left.lambda binder binderCanonical)
      (right.lambda binder binderCanonical) := by
  exact equationSetoid_fill_congr (.lambda binder .hole)
    (fun body => body.lambda binder binderCanonical) (fun _ => rfl) equivalent

/-- Enclose one split-fiber object in a fixed-arity multi-binder. -/
def multiLambda
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {domain codomain : TypeExpr}
    (arity : Nat) (binders : List String) (bindersCanonical : binders = [])
    (body : AvailableOpenPattern language free
      (List.replicate arity domain ++ available) outer codomain) :
    AvailableOpenPattern language free available outer
      (.arrow (.multiBinder domain) codomain) where
  pattern := .multiLambda arity binders body.pattern
  typed := .multiLambda (by
    simpa only [List.append_assoc] using body.typed)
  canonicalBinderMetadata := by
    subst binders
    simp [Pattern.hasCanonicalBinderMetadata, body.canonicalBinderMetadata]
  objectPattern := by
    simpa [isObjectPattern] using body.objectPattern
  reflectiveScope := by
    intro presentation membership
    simpa [binderSafeAt, List.length_append, List.length_replicate,
      Nat.add_comm] using body.reflectiveScope presentation membership

@[simp]
theorem multiLambda_pattern
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {domain codomain : TypeExpr}
    (arity : Nat) (binders : List String) (bindersCanonical : binders = [])
    (body : AvailableOpenPattern language free
      (List.replicate arity domain ++ available) outer codomain) :
    (body.multiLambda arity binders bindersCanonical).pattern =
      .multiLambda arity binders body.pattern :=
  rfl

/-- Typed equation congruence beneath one fixed-arity multi-binder. -/
theorem equationSetoid_multiLambda_congr
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {domain codomain : TypeExpr}
    (arity : Nat) (binders : List String) (bindersCanonical : binders = [])
    {left right : AvailableOpenPattern language free
      (List.replicate arity domain ++ available) outer codomain}
    (equivalent :
      (equationSetoid language free
        (List.replicate arity domain ++ available) outer codomain).r
        left right) :
    (equationSetoid language free available outer
      (.arrow (.multiBinder domain) codomain)).r
      (left.multiLambda arity binders bindersCanonical)
      (right.multiLambda arity binders bindersCanonical) := by
  exact equationSetoid_fill_congr (.multiLambda arity binders .hole)
    (fun body => body.multiLambda arity binders bindersCanonical)
    (fun _ => rfl) equivalent

/-- Supported substitution acts inside the exact split binder fiber. -/
def substitute
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {available outer : List TypeExpr} {type : TypeExpr}
    (pattern : AvailableOpenPattern language source available outer type)
    (assignment : SupportedOpenAssignment language source target support)
    (safe : pattern.typed.ReflectiveSupportSafeAt support available) :
    AvailableOpenPattern language target available outer type where
  pattern := ReflectiveContextSupport.substituteAt language support
    assignment.assignment available.length pattern.pattern
  typed := safe.substitute rfl assignment.toSupportedAssignment
  canonicalBinderMetadata :=
    safe.substituteCanonicalBinderMetadata assignment
      pattern.canonicalBinderMetadata
  objectPattern := safe.substituteObjectPattern assignment pattern.objectPattern
  reflectiveScope := by
    intro presentation membership
    exact safe.substituteBinderSafeAt assignment presentation membership
      (Nat.le_refl available.length)
      (pattern.reflectiveScope presentation membership)

@[simp]
theorem substitute_pattern
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {available outer : List TypeExpr} {type : TypeExpr}
    (pattern : AvailableOpenPattern language source available outer type)
    (assignment : SupportedOpenAssignment language source target support)
    (safe : pattern.typed.ReflectiveSupportSafeAt support available) :
    (pattern.substitute assignment safe).pattern =
      ReflectiveContextSupport.substituteAt language support
        assignment.assignment available.length pattern.pattern :=
  rfl

end AvailableOpenPattern

/-! ### Typed constructor spines

Constructor arguments need one certificate beyond ordinary open typing:
abstraction parameters must remain represented by lambda syntax at every
intermediate equation vertex.  These carriers retain that authored
representation discipline while reusing the same contextual generator.
-/

/-- One typed argument in the exact representation required by an authored
constructor parameter. -/
structure AvailableOpenArgument (language : LanguageDef)
    (free : FreeTypeContext) (available outer : List TypeExpr)
    (parameter : TermParam) (expected : TypeExpr) where
  term : AvailableOpenPattern language free available outer expected
  representation : MatchesParameterRepresentation parameter term.pattern
  parameterType : parameterType? parameter = some expected

namespace AvailableOpenArgument

/-- Reindex an authored constructor argument across equal split fibers.
Concrete binder representation is transported with the term, never
reconstructed from its raw syntax. -/
def reindexFiber
    {language : LanguageDef} {free : FreeTypeContext}
    {sourceAvailable targetAvailable sourceOuter targetOuter : List TypeExpr}
    {parameter : TermParam} {sourceExpected targetExpected : TypeExpr}
    (availableEquality : sourceAvailable = targetAvailable)
    (outerEquality : sourceOuter = targetOuter)
    (expectedEquality : sourceExpected = targetExpected)
    (argument : AvailableOpenArgument language free sourceAvailable sourceOuter
      parameter sourceExpected) :
    AvailableOpenArgument language free targetAvailable targetOuter parameter
      targetExpected := by
  cases availableEquality
  cases outerEquality
  cases expectedEquality
  exact argument

@[simp]
theorem reindexFiber_pattern
    {language : LanguageDef} {free : FreeTypeContext}
    {sourceAvailable targetAvailable sourceOuter targetOuter : List TypeExpr}
    {parameter : TermParam} {sourceExpected targetExpected : TypeExpr}
    (availableEquality : sourceAvailable = targetAvailable)
    (outerEquality : sourceOuter = targetOuter)
    (expectedEquality : sourceExpected = targetExpected)
    (argument : AvailableOpenArgument language free sourceAvailable sourceOuter
      parameter sourceExpected) :
    (argument.reindexFiber availableEquality outerEquality expectedEquality
      ).term.pattern = argument.term.pattern := by
  cases availableEquality
  cases outerEquality
  cases expectedEquality
  rfl

@[ext]
theorem ext
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {parameter : TermParam}
    {expected : TypeExpr}
    {left right : AvailableOpenArgument language free available outer parameter
      expected}
    (patterns : left.term.pattern = right.term.pattern) : left = right := by
  cases left with
  | mk leftTerm leftRepresentation leftParameterType =>
      cases right with
      | mk rightTerm rightRepresentation rightParameterType =>
          have terms : leftTerm = rightTerm :=
            AvailableOpenPattern.ext patterns
          cases terms
          rfl

def equationGenerator
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {parameter : TermParam}
    {expected : TypeExpr}
    (left right : AvailableOpenArgument language free available outer parameter
      expected) : Prop :=
  EquationContextStep defaultBasePremises language
    left.term.pattern right.term.pattern

def equationSetoid (language : LanguageDef) (free : FreeTypeContext)
    (available outer : List TypeExpr) (parameter : TermParam)
    (expected : TypeExpr) :
    Setoid (AvailableOpenArgument language free available outer parameter
      expected) where
  r := Relation.EqvGen equationGenerator
  iseqv :=
    { refl := Relation.EqvGen.refl
      symm := fun relation => Relation.EqvGen.symm _ _ relation
      trans := fun first second => Relation.EqvGen.trans _ _ _ first second }

/-- Forget parameter representation while retaining the exact split typed
equation path. -/
theorem equationSetoid_to_available
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {parameter : TermParam}
    {expected : TypeExpr}
    {left right : AvailableOpenArgument language free available outer parameter
      expected}
    (equivalent :
      (equationSetoid language free available outer parameter expected).r
        left right) :
    (AvailableOpenPattern.equationSetoid language free available outer
      expected).r left.term right.term := by
  induction equivalent with
  | rel left right generator =>
      exact Relation.EqvGen.rel _ _ generator
  | refl argument =>
      exact Relation.EqvGen.refl argument.term
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

/-- Map a representation-preserving argument path into any split-fiber
carrier operation that preserves one authored generator. -/
theorem equationSetoid_mapAvailable
    {language : LanguageDef}
    {sourceFree targetFree : FreeTypeContext}
    {sourceAvailable sourceOuter targetAvailable targetOuter : List TypeExpr}
    {parameter : TermParam} {expected targetType : TypeExpr}
    (map : AvailableOpenArgument language sourceFree sourceAvailable sourceOuter
        parameter expected →
      AvailableOpenPattern language targetFree targetAvailable targetOuter
        targetType)
    (preserves : ∀ {left right}, equationGenerator left right →
      AvailableOpenPattern.equationGenerator (map left) (map right))
    {left right : AvailableOpenArgument language sourceFree sourceAvailable
      sourceOuter parameter expected}
    (equivalent :
      (equationSetoid language sourceFree sourceAvailable sourceOuter parameter
        expected).r left right) :
    (AvailableOpenPattern.equationSetoid language targetFree targetAvailable
      targetOuter targetType).r (map left) (map right) := by
  induction equivalent with
  | rel left right generator =>
      exact Relation.EqvGen.rel _ _ (preserves generator)
  | refl argument =>
      exact Relation.EqvGen.refl (map argument)
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

/-- Map a split-fiber term path into a representation-preserving argument
operation.  The caller supplies the representation evidence for every
intermediate vertex, so abstraction parameters cannot be widened to arbitrary
arrow-typed terms. -/
theorem equationSetoid_of_term_map
    {language : LanguageDef}
    {sourceFree targetFree : FreeTypeContext}
    {sourceAvailable sourceOuter targetAvailable targetOuter : List TypeExpr}
    {parameter : TermParam} {sourceType expected : TypeExpr}
    (map : AvailableOpenPattern language sourceFree sourceAvailable sourceOuter
        sourceType →
      AvailableOpenArgument language targetFree targetAvailable targetOuter
        parameter expected)
    (preserves : ∀ {left right},
      AvailableOpenPattern.equationGenerator left right →
        equationGenerator (map left) (map right))
    {left right : AvailableOpenPattern language sourceFree sourceAvailable
      sourceOuter sourceType}
    (equivalent :
      (AvailableOpenPattern.equationSetoid language sourceFree sourceAvailable
        sourceOuter sourceType).r left right) :
    (equationSetoid language targetFree targetAvailable targetOuter parameter
      expected).r (map left) (map right) := by
  induction equivalent with
  | rel left right generator =>
      exact Relation.EqvGen.rel _ _ (preserves generator)
  | refl term => exact Relation.EqvGen.refl (map term)
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

/-- Supported substitution preserves an authored parameter's concrete binder
representation as well as its exact split typed fiber. -/
def substitute
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {available outer : List TypeExpr} {parameter : TermParam}
    {expected : TypeExpr}
    (argument : AvailableOpenArgument language source available outer parameter
      expected)
    (assignment : SupportedOpenAssignment language source target support)
    (safe : argument.term.typed.ReflectiveSupportSafeAt support available) :
    AvailableOpenArgument language target available outer parameter expected where
  term := argument.term.substitute assignment safe
  representation :=
    MatchesParameterRepresentation.substituteReflectiveAt
      language parameter argument.term.pattern support assignment.assignment
        available.length argument.representation
  parameterType := argument.parameterType

@[simp]
theorem substitute_pattern
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {available outer : List TypeExpr} {parameter : TermParam}
    {expected : TypeExpr}
    (argument : AvailableOpenArgument language source available outer parameter
      expected)
    (assignment : SupportedOpenAssignment language source target support)
    (safe : argument.term.typed.ReflectiveSupportSafeAt support available) :
    (argument.substitute assignment safe).term.pattern =
      ReflectiveContextSupport.substituteAt language support
        assignment.assignment available.length argument.term.pattern :=
  rfl

end AvailableOpenArgument

/-- An authored constructor argument list whose typing, representation,
object, metadata, and quote-visible scope certificates travel together. -/
structure AvailableOpenArguments (language : LanguageDef)
    (free : FreeTypeContext) (available outer : List TypeExpr)
    (parameters : List TermParam) where
  patterns : List Pattern
  typed : ArgumentsHaveTypes language free (available ++ outer)
    patterns parameters
  canonicalBinderMetadata :
    Pattern.hasCanonicalBinderMetadataList patterns = true
  objectPatterns : isObjectPatternList patterns = true
  reflectiveScope : ∀ presentation ∈ language.reflectivePresentations,
    binderSafeListAt presentation.quoteConstructor available.length
      patterns = true

namespace AvailableOpenArguments

/-- Package one exact authored argument spine together with its object and
reflective-scope certificates. -/
def ofCertificates
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {patterns : List Pattern}
    {parameters : List TermParam}
    (typed : ArgumentsHaveTypes language free (available ++ outer) patterns
      parameters)
    (canonical : Pattern.hasCanonicalBinderMetadataList patterns = true)
    (objects : isObjectPatternList patterns = true)
    (scope : ∀ presentation ∈ language.reflectivePresentations,
      binderSafeListAt presentation.quoteConstructor available.length
        patterns = true) :
    AvailableOpenArguments language free available outer parameters :=
  ⟨patterns, typed, canonical, objects, scope⟩

@[simp]
theorem ofCertificates_patterns
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {patterns : List Pattern}
    {parameters : List TermParam}
    (typed : ArgumentsHaveTypes language free (available ++ outer) patterns
      parameters)
    (canonical : Pattern.hasCanonicalBinderMetadataList patterns = true)
    (objects : isObjectPatternList patterns = true)
    (scope : ∀ presentation ∈ language.reflectivePresentations,
      binderSafeListAt presentation.quoteConstructor available.length
        patterns = true) :
    (ofCertificates typed canonical objects scope).patterns = patterns :=
  rfl

@[ext]
theorem ext
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {parameters : List TermParam}
    {left right : AvailableOpenArguments language free available outer
      parameters}
    (patterns : left.patterns = right.patterns) : left = right := by
  cases left
  cases right
  cases patterns
  rfl

def nil (language : LanguageDef) (free : FreeTypeContext)
    (available outer : List TypeExpr) :
    AvailableOpenArguments language free available outer [] where
  patterns := []
  typed := .nil
  canonicalBinderMetadata := by simp [Pattern.hasCanonicalBinderMetadataList]
  objectPatterns := by simp [isObjectPatternList]
  reflectiveScope := by simp [binderSafeListAt]

@[simp]
theorem nil_patterns (language : LanguageDef) (free : FreeTypeContext)
    (available outer : List TypeExpr) :
    (nil language free available outer).patterns = [] :=
  rfl

def cons
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr}
    {parameter : TermParam} {parameters : List TermParam}
    {expected : TypeExpr}
    (head : AvailableOpenArgument language free available outer parameter
      expected)
    (tail : AvailableOpenArguments language free available outer parameters) :
    AvailableOpenArguments language free available outer
      (parameter :: parameters) where
  patterns := head.term.pattern :: tail.patterns
  typed := .cons head.representation head.parameterType head.term.typed
    tail.typed
  canonicalBinderMetadata := by
    simp [Pattern.hasCanonicalBinderMetadataList,
      head.term.canonicalBinderMetadata, tail.canonicalBinderMetadata]
  objectPatterns := by
    simp [isObjectPatternList, head.term.objectPattern, tail.objectPatterns]
  reflectiveScope := by
    intro presentation membership
    simp [binderSafeListAt, head.term.reflectiveScope presentation membership,
      tail.reflectiveScope presentation membership]

@[simp]
theorem cons_patterns
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr}
    {parameter : TermParam} {parameters : List TermParam}
    {expected : TypeExpr}
    (head : AvailableOpenArgument language free available outer parameter
      expected)
    (tail : AvailableOpenArguments language free available outer parameters) :
    (cons head tail).patterns = head.term.pattern :: tail.patterns :=
  rfl

theorem canonical_append_true
    (left right : List Pattern)
    (leftCanonical : Pattern.hasCanonicalBinderMetadataList left = true)
    (rightCanonical : Pattern.hasCanonicalBinderMetadataList right = true) :
    Pattern.hasCanonicalBinderMetadataList (left ++ right) = true := by
  induction left with
  | nil => simpa using rightCanonical
  | cons head tail inductionHypothesis =>
      rw [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true]
        at leftCanonical
      rw [List.cons_append, Pattern.hasCanonicalBinderMetadataList,
        Bool.and_eq_true]
      exact ⟨leftCanonical.1,
        inductionHypothesis leftCanonical.2⟩

theorem object_append_true
    (left right : List Pattern)
    (leftObject : isObjectPatternList left = true)
    (rightObject : isObjectPatternList right = true) :
    isObjectPatternList (left ++ right) = true := by
  induction left with
  | nil => simpa using rightObject
  | cons head tail inductionHypothesis =>
      rw [isObjectPatternList, Bool.and_eq_true] at leftObject
      rw [List.cons_append, isObjectPatternList, Bool.and_eq_true]
      exact ⟨leftObject.1, inductionHypothesis leftObject.2⟩

theorem scope_append_true
    (quote : String) (depth : Nat) (left right : List Pattern)
    (leftScope : binderSafeListAt quote depth left = true)
    (rightScope : binderSafeListAt quote depth right = true) :
    binderSafeListAt quote depth (left ++ right) = true := by
  induction left with
  | nil => simpa using rightScope
  | cons head tail inductionHypothesis =>
      rw [binderSafeListAt, Bool.and_eq_true] at leftScope
      rw [List.cons_append, binderSafeListAt, Bool.and_eq_true]
      exact ⟨leftScope.1, inductionHypothesis leftScope.2⟩

/-- Concatenate certified argument spines without rechecking their syntax. -/
def append
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr}
    {leftParameters rightParameters : List TermParam}
    (left : AvailableOpenArguments language free available outer leftParameters)
    (right : AvailableOpenArguments language free available outer
      rightParameters) :
    AvailableOpenArguments language free available outer
      (leftParameters ++ rightParameters) where
  patterns := left.patterns ++ right.patterns
  typed := left.typed.append right.typed
  canonicalBinderMetadata := canonical_append_true _ _
    left.canonicalBinderMetadata right.canonicalBinderMetadata
  objectPatterns := object_append_true _ _ left.objectPatterns
    right.objectPatterns
  reflectiveScope := by
    intro presentation membership
    exact scope_append_true presentation.quoteConstructor available.length
      _ _ (left.reflectiveScope presentation membership)
      (right.reflectiveScope presentation membership)

@[simp]
theorem append_patterns
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr}
    {leftParameters rightParameters : List TermParam}
    (left : AvailableOpenArguments language free available outer leftParameters)
    (right : AvailableOpenArguments language free available outer
      rightParameters) :
    (left.append right).patterns = left.patterns ++ right.patterns :=
  rfl

/-- Reindex only the authored parameter-list index.  The raw argument spine
and every certificate are unchanged. -/
def reindexParameters
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr}
    {sourceParameters targetParameters : List TermParam}
    (equality : sourceParameters = targetParameters)
    (arguments : AvailableOpenArguments language free available outer
      sourceParameters) :
    AvailableOpenArguments language free available outer targetParameters := by
  subst targetParameters
  exact arguments

@[simp]
theorem reindexParameters_patterns
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr}
    {sourceParameters targetParameters : List TermParam}
    (equality : sourceParameters = targetParameters)
    (arguments : AvailableOpenArguments language free available outer
      sourceParameters) :
    (arguments.reindexParameters equality).patterns = arguments.patterns := by
  subst targetParameters
  rfl

/-- Pointwise authored equation paths for a complete constructor spine.  The
head path lives in the representation-preserving argument carrier; hence
every hybrid list produced by a one-position proof remains a valid authored
application. -/
inductive EquationForall₂
    (language : LanguageDef) (free : FreeTypeContext)
    (available outer : List TypeExpr) :
    {parameters : List TermParam} →
      AvailableOpenArguments language free available outer parameters →
      AvailableOpenArguments language free available outer parameters →
      Prop where
  | nil : EquationForall₂ language free available outer
      (AvailableOpenArguments.nil language free available outer)
      (AvailableOpenArguments.nil language free available outer)
  | cons
      {parameter : TermParam} {parameters : List TermParam}
      {expected : TypeExpr}
      {leftHead rightHead : AvailableOpenArgument language free available outer
        parameter expected}
      {leftTail rightTail : AvailableOpenArguments language free available outer
        parameters} :
      (AvailableOpenArgument.equationSetoid language free available outer
        parameter expected).r leftHead rightHead →
      EquationForall₂ language free available outer leftTail rightTail →
      EquationForall₂ language free available outer
        (AvailableOpenArguments.cons leftHead leftTail)
        (AvailableOpenArguments.cons rightHead rightTail)

/-- Fold pointwise representation-preserving paths into one application path.
The prefix accumulator makes every intermediate list differ at exactly one
position; all dependent typing transport is confined to `append` and
`reindexParameters`. -/
theorem EquationForall₂.assembleWithPrefix
    {language : LanguageDef}
    {argumentFree resultFree : FreeTypeContext}
    {argumentAvailable argumentOuter resultAvailable resultOuter :
      List TypeExpr}
    {resultType : TypeExpr} {constructor : String}
    {parameters prefixParameters fullParameters : List TermParam}
    {left right : AvailableOpenArguments language argumentFree
      argumentAvailable argumentOuter parameters}
    (equivalent : EquationForall₂ language argumentFree argumentAvailable
      argumentOuter left right)
    (leading : AvailableOpenArguments language argumentFree argumentAvailable
      argumentOuter prefixParameters)
    (parameterShape : prefixParameters ++ parameters = fullParameters)
    (assemble : AvailableOpenArguments language argumentFree argumentAvailable
        argumentOuter fullParameters →
      AvailableOpenPattern language resultFree resultAvailable resultOuter
        resultType)
    (assemble_pattern : ∀ arguments,
      (assemble arguments).pattern = .apply constructor arguments.patterns) :
    (AvailableOpenPattern.equationSetoid language resultFree resultAvailable
      resultOuter resultType).r
      (assemble ((leading.append left).reindexParameters parameterShape))
      (assemble ((leading.append right).reindexParameters parameterShape)) := by
  induction equivalent generalizing prefixParameters fullParameters with
  | nil =>
      exact Relation.EqvGen.refl _
  | @cons parameter parameters expected leftHead rightHead leftTail rightTail
      headEquivalent tailEquivalent inductionHypothesis =>
      let headMap := fun
          (middle : AvailableOpenArgument language argumentFree
            argumentAvailable argumentOuter parameter expected) =>
        assemble
          ((leading.append (AvailableOpenArguments.cons middle leftTail)
            ).reindexParameters parameterShape)
      have headStep :
          (AvailableOpenPattern.equationSetoid language resultFree
            resultAvailable resultOuter resultType).r
            (headMap leftHead) (headMap rightHead) := by
        apply AvailableOpenArgument.equationSetoid_mapAvailable headMap
          (equivalent := headEquivalent)
        intro first second generator
        unfold AvailableOpenArgument.equationGenerator at generator
        unfold AvailableOpenPattern.equationGenerator
        rw [assemble_pattern, assemble_pattern]
        simp only [reindexParameters_patterns, append_patterns, cons_patterns]
        simpa [OneHoleContext.fill, List.append_assoc] using
          EquationSemantics.equationContextStep_fill
            (.apply constructor leading.patterns .hole leftTail.patterns)
            generator
      let singleton := AvailableOpenArguments.cons rightHead
        (AvailableOpenArguments.nil language argumentFree argumentAvailable
          argumentOuter)
      let nextPrefix := leading.append singleton
      have nextShape :
          (prefixParameters ++ [parameter]) ++ parameters = fullParameters := by
        simpa [List.append_assoc] using parameterShape
      have tailStep := inductionHypothesis nextPrefix nextShape assemble
        assemble_pattern
      have middleEquality : headMap rightHead =
          assemble
            ((nextPrefix.append leftTail).reindexParameters nextShape) := by
        apply AvailableOpenPattern.ext
        rw [assemble_pattern, assemble_pattern]
        simp [nextPrefix, singleton, List.append_assoc]
      have finalEquality :
          assemble
              ((nextPrefix.append rightTail).reindexParameters nextShape) =
            assemble
              ((leading.append
                  (AvailableOpenArguments.cons rightHead rightTail)
                ).reindexParameters parameterShape) := by
        apply congrArg assemble
        apply AvailableOpenArguments.ext
        simp [nextPrefix, singleton, List.append_assoc]
      rw [middleEquality] at headStep
      rw [finalEquality] at tailStep
      exact Relation.EqvGen.trans _ _ _ headStep tailStep

private theorem scope_mono (quote : String) {small large : Nat}
    (patterns : List Pattern)
    (safe : binderSafeListAt quote small patterns = true)
    (order : small ≤ large) :
    binderSafeListAt quote large patterns = true := by
  induction patterns with
  | nil => simp [binderSafeListAt]
  | cons head tail inductionHypothesis =>
      simp only [binderSafeListAt, Bool.and_eq_true] at safe ⊢
      exact ⟨binderSafeAt_mono quote safe.1 order,
        inductionHypothesis safe.2⟩

private theorem application_scope (quote constructor : String) (depth : Nat)
    (arguments : List Pattern)
    (resetSafe : constructor = quote →
      binderSafeListAt quote 0 arguments = true)
    (ordinarySafe : binderSafeListAt quote depth arguments = true) :
    binderSafeAt quote depth (.apply constructor arguments) = true := by
  cases arguments with
  | nil => simp [binderSafeAt, binderSafeListAt]
  | cons argument arguments =>
      cases arguments with
      | nil =>
          by_cases quoted : constructor = quote
          · simpa [binderSafeAt, binderSafeListAt, quoted] using
              resetSafe quoted
          · simpa [binderSafeAt, binderSafeListAt, quoted] using ordinarySafe
      | cons second remainder =>
          simpa [binderSafeAt] using ordinarySafe

/-- Assemble an ordinary authored application from a spine whose visible
binder prefix is the application's visible prefix. -/
def applyOrdinary
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {rule : GrammarRule}
    (membership : rule ∈ language.terms)
    (notBare : ¬ UsesBareCollection rule)
    (ordinary : ReflectiveContextSupport.isQuoteConstructor language
      rule.label = false)
    (arguments : AvailableOpenArguments language free available outer
      rule.params) :
    AvailableOpenPattern language free available outer
      (.base rule.category) where
  pattern := .apply rule.label arguments.patterns
  typed := .constructor membership notBare arguments.typed
  canonicalBinderMetadata := by
    simpa [Pattern.hasCanonicalBinderMetadata] using
      arguments.canonicalBinderMetadata
  objectPattern := by
    simpa [isObjectPattern] using arguments.objectPatterns
  reflectiveScope := by
    intro presentation presentationMembership
    have notThisQuote : rule.label ≠ presentation.quoteConstructor := by
      intro equality
      have detected : ReflectiveContextSupport.isQuoteConstructor language
          rule.label = true := by
        unfold ReflectiveContextSupport.isQuoteConstructor
        rw [List.any_eq_true]
        exact ⟨presentation, presentationMembership, by simp [equality]⟩
      rw [detected] at ordinary
      contradiction
    exact application_scope presentation.quoteConstructor rule.label
      available.length arguments.patterns
      (fun equality => (notThisQuote equality).elim)
      (arguments.reflectiveScope presentation presentationMembership)

@[simp]
theorem applyOrdinary_pattern
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {rule : GrammarRule}
    (membership : rule ∈ language.terms)
    (notBare : ¬ UsesBareCollection rule)
    (ordinary : ReflectiveContextSupport.isQuoteConstructor language
      rule.label = false)
    (arguments : AvailableOpenArguments language free available outer
      rule.params) :
    (arguments.applyOrdinary membership notBare ordinary).pattern =
      .apply rule.label arguments.patterns :=
  rfl

/-- Assemble an authored quotation application.  Its argument spine is
checked at visible depth zero while the application's complete lexical
context remains `available ++ outer`. -/
def applyQuote
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {rule : GrammarRule}
    (membership : rule ∈ language.terms)
    (notBare : ¬ UsesBareCollection rule)
    (_quoted : ReflectiveContextSupport.isQuoteConstructor language
      rule.label = true)
    (arguments : AvailableOpenArguments language free [] (available ++ outer)
      rule.params) :
    AvailableOpenPattern language free available outer
      (.base rule.category) where
  pattern := .apply rule.label arguments.patterns
  typed := .constructor membership notBare (by
    simpa only [List.nil_append, List.append_assoc] using arguments.typed)
  canonicalBinderMetadata := by
    simpa [Pattern.hasCanonicalBinderMetadata] using
      arguments.canonicalBinderMetadata
  objectPattern := by
    simpa [isObjectPattern] using arguments.objectPatterns
  reflectiveScope := by
    intro presentation presentationMembership
    have reset := arguments.reflectiveScope presentation presentationMembership
    exact application_scope presentation.quoteConstructor rule.label
      available.length arguments.patterns (fun _ => reset)
      (scope_mono presentation.quoteConstructor arguments.patterns reset
        (Nat.zero_le available.length))

@[simp]
theorem applyQuote_pattern
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {rule : GrammarRule}
    (membership : rule ∈ language.terms)
    (notBare : ¬ UsesBareCollection rule)
    (quoted : ReflectiveContextSupport.isQuoteConstructor language
      rule.label = true)
    (arguments : AvailableOpenArguments language free [] (available ++ outer)
      rule.params) :
    (arguments.applyQuote membership notBare quoted).pattern =
      .apply rule.label arguments.patterns :=
  rfl

/-- Pointwise authored argument equivalence is a congruence for an ordinary
authored constructor. -/
theorem EquationForall₂.assembleOrdinary
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {rule : GrammarRule}
    {left right : AvailableOpenArguments language free available outer
      rule.params}
    (equivalent : EquationForall₂ language free available outer left right)
    (membership : rule ∈ language.terms)
    (notBare : ¬ UsesBareCollection rule)
    (ordinary : ReflectiveContextSupport.isQuoteConstructor language
      rule.label = false) :
    (AvailableOpenPattern.equationSetoid language free available outer
      (.base rule.category)).r
      (left.applyOrdinary membership notBare ordinary)
      (right.applyOrdinary membership notBare ordinary) := by
  exact EquationForall₂.assembleWithPrefix
    (prefixParameters := []) (fullParameters := rule.params)
    equivalent (AvailableOpenArguments.nil language free available outer)
    (by simp)
    (fun arguments => arguments.applyOrdinary membership notBare ordinary)
    (by intro arguments; rfl)

/-- Pointwise authored argument equivalence is a congruence for a quotation
constructor; the argument paths retain the reset visible prefix. -/
theorem EquationForall₂.assembleQuote
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {rule : GrammarRule}
    {left right : AvailableOpenArguments language free [] (available ++ outer)
      rule.params}
    (equivalent : EquationForall₂ language free [] (available ++ outer)
      left right)
    (membership : rule ∈ language.terms)
    (notBare : ¬ UsesBareCollection rule)
    (quoted : ReflectiveContextSupport.isQuoteConstructor language
      rule.label = true) :
    (AvailableOpenPattern.equationSetoid language free available outer
      (.base rule.category)).r
      (left.applyQuote membership notBare quoted)
      (right.applyQuote membership notBare quoted) := by
  exact EquationForall₂.assembleWithPrefix
    (prefixParameters := []) (fullParameters := rule.params)
    equivalent
    (AvailableOpenArguments.nil language free [] (available ++ outer))
    (by simp)
    (fun arguments => arguments.applyQuote membership notBare quoted)
    (by intro arguments; rfl)

/-- Apply one support-safe assignment to a certified constructor spine while
retaining its authored parameter index and quote-visible binder split. -/
def substitute
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {available outer : List TypeExpr} {parameters : List TermParam}
    (arguments : AvailableOpenArguments language source available outer
      parameters)
    (assignment : SupportedOpenAssignment language source target support)
    (safe : arguments.typed.ReflectiveSupportSafeAt support available) :
    AvailableOpenArguments language target available outer parameters where
  patterns := arguments.patterns.map
    (ReflectiveContextSupport.substituteAt language support
      assignment.assignment available.length)
  typed := safe.substitute rfl assignment.toSupportedAssignment
  canonicalBinderMetadata := safe.substituteCanonicalBinderMetadata assignment
    arguments.canonicalBinderMetadata
  objectPatterns := safe.substituteObjectPattern assignment
    arguments.objectPatterns
  reflectiveScope := by
    intro presentation membership
    exact safe.substituteBinderSafeListAt assignment presentation membership
      (Nat.le_refl available.length)
      (arguments.reflectiveScope presentation membership)

@[simp]
theorem substitute_patterns
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {available outer : List TypeExpr} {parameters : List TermParam}
    (arguments : AvailableOpenArguments language source available outer
      parameters)
    (assignment : SupportedOpenAssignment language source target support)
    (safe : arguments.typed.ReflectiveSupportSafeAt support available) :
    (arguments.substitute assignment safe).patterns =
      arguments.patterns.map
        (ReflectiveContextSupport.substituteAt language support
          assignment.assignment available.length) :=
  rfl

end AvailableOpenArguments

/-- Concatenation preserves homogeneous element typing. -/
theorem ElementsHaveType.append
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {elementType : TypeExpr}
    {left right : List Pattern}
    (leftTyped : ElementsHaveType language free bound left elementType)
    (rightTyped : ElementsHaveType language free bound right elementType) :
    ElementsHaveType language free bound (left ++ right) elementType :=
  match leftTyped with
  | .nil _ _ => rightTyped
  | .cons headTyped tailTyped =>
      .cons headTyped (tailTyped.append rightTyped)

/-- A homogeneous bare-collection spine whose typing and quote-visible scope
certificates travel with its raw elements. -/
structure AvailableOpenElements (language : LanguageDef)
    (free : FreeTypeContext) (available outer : List TypeExpr)
    (elementType : TypeExpr) where
  patterns : List Pattern
  typed : ElementsHaveType language free (available ++ outer) patterns
    elementType
  canonicalBinderMetadata :
    Pattern.hasCanonicalBinderMetadataList patterns = true
  objectPatterns : isObjectPatternList patterns = true
  reflectiveScope : ∀ presentation ∈ language.reflectivePresentations,
    binderSafeListAt presentation.quoteConstructor available.length patterns =
      true

namespace AvailableOpenElements

/-- Package one homogeneous element spine at its exact split binder fiber. -/
def ofCertificates
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {patterns : List Pattern}
    {elementType : TypeExpr}
    (typed : ElementsHaveType language free (available ++ outer) patterns
      elementType)
    (canonical : Pattern.hasCanonicalBinderMetadataList patterns = true)
    (objects : isObjectPatternList patterns = true)
    (scope : ∀ presentation ∈ language.reflectivePresentations,
      binderSafeListAt presentation.quoteConstructor available.length
        patterns = true) :
    AvailableOpenElements language free available outer elementType :=
  ⟨patterns, typed, canonical, objects, scope⟩

@[simp]
theorem ofCertificates_patterns
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {patterns : List Pattern}
    {elementType : TypeExpr}
    (typed : ElementsHaveType language free (available ++ outer) patterns
      elementType)
    (canonical : Pattern.hasCanonicalBinderMetadataList patterns = true)
    (objects : isObjectPatternList patterns = true)
    (scope : ∀ presentation ∈ language.reflectivePresentations,
      binderSafeListAt presentation.quoteConstructor available.length
        patterns = true) :
    (ofCertificates typed canonical objects scope).patterns = patterns :=
  rfl

@[ext]
theorem ext
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {elementType : TypeExpr}
    {left right : AvailableOpenElements language free available outer
      elementType}
    (patterns : left.patterns = right.patterns) : left = right := by
  cases left
  cases right
  cases patterns
  rfl

def nil (language : LanguageDef) (free : FreeTypeContext)
    (available outer : List TypeExpr) (elementType : TypeExpr) :
    AvailableOpenElements language free available outer elementType where
  patterns := []
  typed := .nil _ _
  canonicalBinderMetadata := by simp [Pattern.hasCanonicalBinderMetadataList]
  objectPatterns := by simp [isObjectPatternList]
  reflectiveScope := by simp [binderSafeListAt]

@[simp]
theorem nil_patterns (language : LanguageDef) (free : FreeTypeContext)
    (available outer : List TypeExpr) (elementType : TypeExpr) :
    (nil language free available outer elementType).patterns = [] :=
  rfl

def cons
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {elementType : TypeExpr}
    (head : AvailableOpenPattern language free available outer elementType)
    (tail : AvailableOpenElements language free available outer elementType) :
    AvailableOpenElements language free available outer elementType where
  patterns := head.pattern :: tail.patterns
  typed := .cons head.typed tail.typed
  canonicalBinderMetadata := by
    simp [Pattern.hasCanonicalBinderMetadataList,
      head.canonicalBinderMetadata, tail.canonicalBinderMetadata]
  objectPatterns := by
    simp [isObjectPatternList, head.objectPattern, tail.objectPatterns]
  reflectiveScope := by
    intro presentation membership
    simp [binderSafeListAt, head.reflectiveScope presentation membership,
      tail.reflectiveScope presentation membership]

@[simp]
theorem cons_patterns
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {elementType : TypeExpr}
    (head : AvailableOpenPattern language free available outer elementType)
    (tail : AvailableOpenElements language free available outer elementType) :
    (cons head tail).patterns = head.pattern :: tail.patterns :=
  rfl

/-- Concatenate two certified homogeneous element spines. -/
def append
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {elementType : TypeExpr}
    (left right : AvailableOpenElements language free available outer
      elementType) :
    AvailableOpenElements language free available outer elementType where
  patterns := left.patterns ++ right.patterns
  typed := left.typed.append right.typed
  canonicalBinderMetadata :=
    AvailableOpenArguments.canonical_append_true _ _
      left.canonicalBinderMetadata right.canonicalBinderMetadata
  objectPatterns := AvailableOpenArguments.object_append_true _ _
    left.objectPatterns right.objectPatterns
  reflectiveScope := by
    intro presentation membership
    exact AvailableOpenArguments.scope_append_true
      presentation.quoteConstructor available.length _ _
      (left.reflectiveScope presentation membership)
      (right.reflectiveScope presentation membership)

@[simp]
theorem append_patterns
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {elementType : TypeExpr}
    (left right : AvailableOpenElements language free available outer
      elementType) :
    (left.append right).patterns = left.patterns ++ right.patterns :=
  rfl

@[simp]
theorem nil_append
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {elementType : TypeExpr}
    (elements : AvailableOpenElements language free available outer
      elementType) :
    (nil language free available outer elementType).append elements =
      elements := by
  apply ext
  rfl

/-- Package a homogeneous element spine as the corresponding bare collection. -/
def collection
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {elementType : TypeExpr}
    (collectionType : CollType)
    (elements : AvailableOpenElements language free available outer
      elementType) :
    AvailableOpenPattern language free available outer
      (.collection collectionType elementType) where
  pattern := .collection collectionType elements.patterns none
  typed := .collection elements.typed
  canonicalBinderMetadata := by
    simpa [Pattern.hasCanonicalBinderMetadata] using
      elements.canonicalBinderMetadata
  objectPattern := by
    simpa [isObjectPattern] using elements.objectPatterns
  reflectiveScope := by
    intro presentation membership
    simpa [binderSafeAt] using
      elements.reflectiveScope presentation membership

@[simp]
theorem collection_pattern
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {elementType : TypeExpr}
    (collectionType : CollType)
    (elements : AvailableOpenElements language free available outer
      elementType) :
    (elements.collection collectionType).pattern =
      .collection collectionType elements.patterns none :=
  rfl

/-- Package a homogeneous spine through an authored bare-collection
constructor while retaining the declaration identity in its typing proof. -/
def collectionConstructor
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {elementType : TypeExpr}
    {rule : GrammarRule} {parameterName : String}
    {collectionType : CollType}
    (membership : rule ∈ language.terms)
    (parameterShape : rule.params =
      [.simple parameterName (.collection collectionType elementType)])
    (elements : AvailableOpenElements language free available outer
      elementType) :
    AvailableOpenPattern language free available outer
      (.base rule.category) where
  pattern := .collection collectionType elements.patterns none
  typed := .collectionConstructor membership parameterShape elements.typed
  canonicalBinderMetadata := by
    simpa [Pattern.hasCanonicalBinderMetadata] using
      elements.canonicalBinderMetadata
  objectPattern := by
    simpa [isObjectPattern] using elements.objectPatterns
  reflectiveScope := by
    intro presentation presentationMembership
    simpa [binderSafeAt] using
      elements.reflectiveScope presentation presentationMembership

@[simp]
theorem collectionConstructor_pattern
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {elementType : TypeExpr}
    {rule : GrammarRule} {parameterName : String}
    {collectionType : CollType}
    (membership : rule ∈ language.terms)
    (parameterShape : rule.params =
      [.simple parameterName (.collection collectionType elementType)])
    (elements : AvailableOpenElements language free available outer
      elementType) :
    (elements.collectionConstructor membership parameterShape).pattern =
      .collection collectionType elements.patterns none :=
  rfl

/-- Pointwise authored equation paths through a homogeneous element spine. -/
inductive EquationForall₂
    (language : LanguageDef) (free : FreeTypeContext)
    (available outer : List TypeExpr) (elementType : TypeExpr) :
    AvailableOpenElements language free available outer elementType →
      AvailableOpenElements language free available outer elementType → Prop
  where
  | nil : EquationForall₂ language free available outer elementType
      (nil language free available outer elementType)
      (nil language free available outer elementType)
  | cons
      {leftHead rightHead : AvailableOpenPattern language free available outer
        elementType}
      {leftTail rightTail : AvailableOpenElements language free available outer
        elementType} :
      (AvailableOpenPattern.equationSetoid language free available outer
        elementType).r leftHead rightHead →
      EquationForall₂ language free available outer elementType leftTail
        rightTail →
      EquationForall₂ language free available outer elementType
        (cons leftHead leftTail) (cons rightHead rightTail)

/-- Fold pointwise element paths through any typed package whose raw syntax is
the same bare collection.  This covers both collection values and authored
bare-collection constructors without introducing a second equation rule. -/
theorem EquationForall₂.assembleWithPrefix
    {language : LanguageDef} {sourceFree targetFree : FreeTypeContext}
    {sourceAvailable sourceOuter targetAvailable targetOuter : List TypeExpr}
    {elementType targetType : TypeExpr}
    {left right : AvailableOpenElements language sourceFree sourceAvailable
      sourceOuter
      elementType}
    (equivalent : EquationForall₂ language sourceFree sourceAvailable
      sourceOuter elementType left right)
    (collectionType : CollType)
    (leading : AvailableOpenElements language sourceFree sourceAvailable
      sourceOuter elementType)
    (assemble : AvailableOpenElements language sourceFree sourceAvailable
        sourceOuter elementType →
      AvailableOpenPattern language targetFree targetAvailable targetOuter
        targetType)
    (assemble_pattern : ∀ elements,
      (assemble elements).pattern =
        .collection collectionType elements.patterns none) :
    (AvailableOpenPattern.equationSetoid language targetFree targetAvailable
      targetOuter targetType).r
      (assemble (leading.append left))
      (assemble (leading.append right)) := by
  induction equivalent generalizing leading with
  | nil => exact Relation.EqvGen.refl _
  | @cons leftHead rightHead leftTail rightTail headEquivalent tailEquivalent
      inductionHypothesis =>
      let headMap := fun
          (middle : AvailableOpenPattern language sourceFree sourceAvailable
            sourceOuter
            elementType) =>
        assemble (leading.append (AvailableOpenElements.cons middle leftTail))
      have headStep :
          (AvailableOpenPattern.equationSetoid language targetFree
            targetAvailable targetOuter targetType).r
            (headMap leftHead) (headMap rightHead) := by
        apply AvailableOpenPattern.equationSetoid_fill_congr
          (.collection collectionType leading.patterns .hole leftTail.patterns
            none)
          headMap
        · intro middle
          rw [assemble_pattern]
          simp [OneHoleContext.fill]
        · exact headEquivalent
      let singleton := AvailableOpenElements.cons rightHead
        (AvailableOpenElements.nil language sourceFree sourceAvailable
          sourceOuter elementType)
      let nextLeading := leading.append singleton
      have tailStep := inductionHypothesis nextLeading
      have middleEquality : headMap rightHead =
          assemble (nextLeading.append leftTail) := by
        apply AvailableOpenPattern.ext
        rw [assemble_pattern, assemble_pattern]
        simp [nextLeading, singleton, List.append_assoc]
      have finalEquality :
          assemble (nextLeading.append rightTail) =
            assemble (leading.append
              (AvailableOpenElements.cons rightHead rightTail)) := by
        apply congrArg assemble
        apply AvailableOpenElements.ext
        simp [nextLeading, singleton, List.append_assoc]
      rw [middleEquality] at headStep
      rw [finalEquality] at tailStep
      exact Relation.EqvGen.trans _ _ _ headStep tailStep

/-- Pointwise authored element equivalence is a congruence for a bare
collection. -/
theorem EquationForall₂.assemble
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {elementType : TypeExpr}
    {left right : AvailableOpenElements language free available outer
      elementType}
    (equivalent : EquationForall₂ language free available outer elementType
      left right)
    (collectionType : CollType) :
    (AvailableOpenPattern.equationSetoid language free available outer
      (.collection collectionType elementType)).r
      (left.collection collectionType) (right.collection collectionType) := by
  exact equivalent.assembleWithPrefix collectionType
    (AvailableOpenElements.nil language free available outer elementType)
    (fun elements => elements.collection collectionType)
    (by intro elements; rfl)

/-- Pointwise authored element equivalence is a congruence for an authored
bare-collection constructor. -/
theorem EquationForall₂.assembleConstructor
    {language : LanguageDef} {free : FreeTypeContext}
    {available outer : List TypeExpr} {elementType : TypeExpr}
    {rule : GrammarRule} {parameterName : String}
    {collectionType : CollType}
    {left right : AvailableOpenElements language free available outer
      elementType}
    (equivalent : EquationForall₂ language free available outer elementType
      left right)
    (membership : rule ∈ language.terms)
    (parameterShape : rule.params =
      [.simple parameterName (.collection collectionType elementType)]) :
    (AvailableOpenPattern.equationSetoid language free available outer
      (.base rule.category)).r
      (left.collectionConstructor membership parameterShape)
      (right.collectionConstructor membership parameterShape) := by
  exact equivalent.assembleWithPrefix collectionType
    (AvailableOpenElements.nil language free available outer elementType)
    (fun elements => elements.collectionConstructor membership parameterShape)
    (by intro elements; rfl)

/-- Apply one support-safe assignment to a homogeneous collection spine while
retaining its exact element fiber and quote-visible binder split. -/
def substitute
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {available outer : List TypeExpr} {elementType : TypeExpr}
    (elements : AvailableOpenElements language source available outer
      elementType)
    (assignment : SupportedOpenAssignment language source target support)
    (safe : elements.typed.ReflectiveSupportSafeAt support available) :
    AvailableOpenElements language target available outer elementType where
  patterns := elements.patterns.map
    (ReflectiveContextSupport.substituteAt language support
      assignment.assignment available.length)
  typed := safe.substitute rfl assignment.toSupportedAssignment
  canonicalBinderMetadata := safe.substituteCanonicalBinderMetadata assignment
    elements.canonicalBinderMetadata
  objectPatterns := safe.substituteObjectPattern assignment
    elements.objectPatterns
  reflectiveScope := by
    intro presentation membership
    exact safe.substituteBinderSafeListAt assignment presentation membership
      (Nat.le_refl available.length)
      (elements.reflectiveScope presentation membership)

@[simp]
theorem substitute_patterns
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {available outer : List TypeExpr} {elementType : TypeExpr}
    (elements : AvailableOpenElements language source available outer
      elementType)
    (assignment : SupportedOpenAssignment language source target support)
    (safe : elements.typed.ReflectiveSupportSafeAt support available) :
    (elements.substitute assignment safe).patterns =
      elements.patterns.map
        (ReflectiveContextSupport.substituteAt language support
          assignment.assignment available.length) :=
  rfl

end AvailableOpenElements

/-- Typed equation naturality under root weakening.  Unlike the raw
ambient-renaming law, this property certifies every intermediate vertex in
the exact arbitrary-type open fiber. -/
def OpenPatternEquationWeakeningStable (language : LanguageDef) : Prop :=
  ∀ {free : FreeTypeContext} {bound : List TypeExpr} {type : TypeExpr}
    {left right : OpenPattern language free bound type},
    (openPatternEquationSetoid language free bound type).r left right →
      ∀ inner : List TypeExpr,
        (openPatternEquationSetoid language free (inner ++ bound) type).r
          (left.weakenRoot inner) (right.weakenRoot inner)

/-- Strong, directly checkable sufficient condition for typed root weakening:
each authored contextual generator remains one generator after inserting an
arbitrary number of binders at the root.  This property is intentionally
separate from raw `EquationEquiv` naturality, which need not retain typed
intermediate vertices. -/
def EquationContextStepRootWeakeningStable (language : LanguageDef) : Prop :=
  ∀ {left right : Pattern},
    EquationContextStep defaultBasePremises language left right →
      ∀ shift : Nat,
        EquationContextStep defaultBasePremises language
          (liftBVars 0 shift left) (liftBVars 0 shift right)

/-- Generator-level root weakening maps the complete least typed equation
setoid because every intermediate vertex is produced by `weakenRoot`. -/
theorem EquationContextStepRootWeakeningStable.toOpenPattern
    {language : LanguageDef}
    (stable : EquationContextStepRootWeakeningStable language) :
    OpenPatternEquationWeakeningStable language := by
  intro free bound type left right equivalent inner
  apply openPatternEquationSetoid_map
    (map := fun pattern => pattern.weakenRoot inner)
    (equivalent := equivalent)
  intro first second generator
  unfold openPatternEquationGenerator at generator ⊢
  simpa only [OpenPattern.weakenRoot_pattern] using
    stable generator inner.length

/-- Weaken one support-indexed assignment value through an exact list of new
inner binders and retain it in the arbitrary-type open carrier. -/
def SupportedOpenAssignment.weakenedValue
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    (assignment : SupportedOpenAssignment language source target support)
    {name : String} {type : TypeExpr} (lookup : source name = some type)
    (inner : List TypeExpr) :
    OpenPattern language target (inner ++ support name) type := by
  refine ⟨liftBVars 0 inner.length (assignment.assignment name), ?_, ?_, ?_, ?_⟩
  · simpa using (assignment.typed lookup).liftBVars_insert
      (inner := []) (outer := support name) (inserted := inner)
  · simpa using assignment.canonicalBinderMetadata lookup
  · simpa using assignment.objectPattern lookup
  · intro presentation membership
    have lifted := ContextSubstitution.binderSafeAt_liftBVars
      presentation.quoteConstructor
      (ambient := (support name).length) (cutoff := 0)
      (shift := inner.length)
      (assignment.reflectiveScopeSafe lookup presentation membership)
    simpa only [List.length_append, Nat.add_zero, Nat.add_comm] using lifted

@[simp]
theorem SupportedOpenAssignment.weakenedValue_pattern
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    (assignment : SupportedOpenAssignment language source target support)
    {name : String} {type : TypeExpr} (lookup : source name = some type)
    (inner : List TypeExpr) :
    (assignment.weakenedValue lookup inner).1 =
      liftBVars 0 inner.length (assignment.assignment name) :=
  rfl

/-- Two support-indexed open assignments agree semantically when every
source variable is filled by contextually equation-equivalent target terms,
stably under every capture-avoiding weakening used by structural
substitution.

Typing, binder metadata, object shape, and reflective scope remain carried
by each `SupportedOpenAssignment`.  Quantifying the weakening is
load-bearing: equivalence at the declared support alone does not justify the
`liftBVars` performed beneath additional binders. -/
def SupportedOpenAssignment.Equivalent
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    (first second : SupportedOpenAssignment language source target support) :
    Prop :=
  ∀ {name type}, source name = some type → ∀ shift,
    EquationEquiv defaultBasePremises language
      (liftBVars 0 shift (first.assignment name))
      (liftBVars 0 shift (second.assignment name))

namespace SupportedOpenAssignment.Equivalent

theorem refl
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    (assignment : SupportedOpenAssignment language source target support) :
    assignment.Equivalent assignment := by
  intro name type lookup shift
  exact Relation.EqvGen.refl
    (liftBVars 0 shift (assignment.assignment name))

theorem symm
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {first second : SupportedOpenAssignment language source target support}
    (equivalent : first.Equivalent second) : second.Equivalent first := by
  intro name type lookup shift
  exact Relation.EqvGen.symm _ _ (equivalent lookup shift)

theorem trans
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {first second third : SupportedOpenAssignment language source target
      support}
    (firstEquivalent : first.Equivalent second)
    (secondEquivalent : second.Equivalent third) : first.Equivalent third := by
  intro name type lookup shift
  exact Relation.EqvGen.trans _ _ _
    (firstEquivalent lookup shift) (secondEquivalent lookup shift)

end SupportedOpenAssignment.Equivalent

/-- Fiberwise semantic agreement of supported assignments.  Unlike raw
pointwise `Equivalent`, this relation keeps every intermediate equation
vertex in the exact arbitrary-type open carrier after each weakening. -/
def SupportedOpenAssignment.FiberEquivalent
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    (first second : SupportedOpenAssignment language source target support) :
    Prop :=
  ∀ {name type} (lookup : source name = some type) (inner : List TypeExpr),
    (openPatternEquationSetoid language target
      (inner ++ support name) type).r
        (first.weakenedValue lookup inner)
        (second.weakenedValue lookup inner)

namespace SupportedOpenAssignment.FiberEquivalent

theorem refl
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    (assignment : SupportedOpenAssignment language source target support) :
    assignment.FiberEquivalent assignment := by
  intro name type lookup inner
  exact Relation.EqvGen.refl _

theorem symm
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {first second : SupportedOpenAssignment language source target support}
    (equivalent : first.FiberEquivalent second) :
    second.FiberEquivalent first := by
  intro name type lookup inner
  exact (openPatternEquationSetoid language target
    (inner ++ support name) type).iseqv.symm (equivalent lookup inner)

theorem trans
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {first second third : SupportedOpenAssignment language source target
      support}
    (firstEquivalent : first.FiberEquivalent second)
    (secondEquivalent : second.FiberEquivalent third) :
    first.FiberEquivalent third := by
  intro name type lookup inner
  exact (openPatternEquationSetoid language target
    (inner ++ support name) type).iseqv.trans
      (firstEquivalent lookup inner) (secondEquivalent lookup inner)

/-- Fiberwise agreement implies the raw all-weakening relation used by the
structural congruence theorem. -/
theorem toEquivalent
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {first second : SupportedOpenAssignment language source target support}
    (equivalent : first.FiberEquivalent second) : first.Equivalent second := by
  intro name type lookup shift
  have fiberEquivalent :=
    equivalent lookup (List.replicate shift type)
  have rawEquivalent :=
    openPatternEquationSetoid_to_equationEquiv fiberEquivalent
  simpa only [SupportedOpenAssignment.weakenedValue_pattern,
    List.length_replicate] using rawEquivalent

end SupportedOpenAssignment.FiberEquivalent

/-! ### Fiberwise substitution congruence in the split typed carrier

The following mutual induction is deliberately driven by the certified
support derivation.  It reconstructs every intermediate vertex in the exact
visible/sealed binder fiber.  Constructor arguments retain their authored
binder representation throughout the path; a raw `EquationEquiv` endpoint
statement would be too weak for that purpose. -/

mutual
  /-- Lightweight syntax measure for the mutually recursive supported
  substitution proof.  Unlike `sizeOf`, this counts only recursive syntax
  structure, so elaboration does not normalize names, types, or proof
  transports while checking decrease. -/
  private def substitutionPatternMeasure : Pattern → Nat
    | .bvar _ | .fvar _ => 1
    | .apply _ arguments => 1 + substitutionPatternListMeasure arguments
    | .lambda _ body | .multiLambda _ _ body =>
        1 + substitutionPatternMeasure body
    | .subst body replacement =>
        1 + substitutionPatternMeasure body +
          substitutionPatternMeasure replacement
    | .collection _ elements _ =>
        1 + substitutionPatternListMeasure elements

  /-- List companion to `substitutionPatternMeasure`. -/
  private def substitutionPatternListMeasure : List Pattern → Nat
    | [] => 0
    | pattern :: patterns =>
        1 + substitutionPatternMeasure pattern +
          substitutionPatternListMeasure patterns
end

mutual
  theorem HasType.ReflectiveSupportSafeAt.availableEquationSetoid_substitute_pointwise
      {language : LanguageDef} (valid : language.validate = [])
      {source target : FreeTypeContext} {support : ContextSupport.Support}
      {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      {typed : HasType language source (available ++ outer) pattern type}
      (safe : typed.ReflectiveSupportSafeAt support available)
      (canonical : pattern.hasCanonicalBinderMetadata = true)
      (objectPattern : isObjectPattern pattern = true)
      (scope : ReflectiveScopeSafeAt language available.length pattern)
      (first second : SupportedOpenAssignment language source target support)
      (equivalent : first.FiberEquivalent second) :
      let term := AvailableOpenPattern.ofCertificates typed canonical
        objectPattern scope
      (AvailableOpenPattern.equationSetoid language target available outer
        type).r (term.substitute first safe) (term.substitute second safe) := by
    let sourceTerm := AvailableOpenPattern.ofCertificates typed canonical
      objectPattern scope
    let sourceSafe := safe
    change (AvailableOpenPattern.equationSetoid language target available outer
      type).r (sourceTerm.substitute first sourceSafe)
        (sourceTerm.substitute second sourceSafe)
    cases safe with
    | @bvar bound index type lookup available binderImage =>
        have endpoints : sourceTerm.substitute first sourceSafe =
            sourceTerm.substitute second sourceSafe := by
          apply AvailableOpenPattern.ext
          simp [sourceTerm, ReflectiveContextSupport.substituteAt]
        rw [endpoints]
        exact Relation.EqvGen.refl _
    | @fvar bound name type lookup available binderImage shape =>
        obtain ⟨inner, availableShape⟩ := shape
        subst available
        have path :=
          AvailableOpenPattern.openPatternEquationSetoid_to_availableWithOuter
            outer (equivalent lookup inner)
        have leftEndpoint : sourceTerm.substitute first sourceSafe =
            AvailableOpenPattern.ofOpenPatternWithOuter
              (first.weakenedValue lookup inner) outer := by
          apply AvailableOpenPattern.ext
          simp only [sourceTerm, AvailableOpenPattern.substitute_pattern,
            AvailableOpenPattern.ofCertificates_pattern,
            AvailableOpenPattern.ofOpenPatternWithOuter_pattern,
            SupportedOpenAssignment.weakenedValue_pattern,
            ReflectiveContextSupport.substituteAt, List.length_append]
          congr 1
          omega
        have rightEndpoint : sourceTerm.substitute second sourceSafe =
            AvailableOpenPattern.ofOpenPatternWithOuter
              (second.weakenedValue lookup inner) outer := by
          apply AvailableOpenPattern.ext
          simp only [sourceTerm, AvailableOpenPattern.substitute_pattern,
            AvailableOpenPattern.ofCertificates_pattern,
            AvailableOpenPattern.ofOpenPatternWithOuter_pattern,
            SupportedOpenAssignment.weakenedValue_pattern,
            ReflectiveContextSupport.substituteAt, List.length_append]
          congr 1
          omega
        rw [leftEndpoint, rightEndpoint]
        exact path
    | @constructorQuote bound rule arguments membership notBare argumentsTyped
        available binderImage quoted argumentsSafe =>
        have canonicalArguments :
            Pattern.hasCanonicalBinderMetadataList arguments = true := by
          simpa [Pattern.hasCanonicalBinderMetadata] using canonical
        have objectArguments : isObjectPatternList arguments = true := by
          simpa [isObjectPattern] using objectPattern
        have fullScope : ReflectiveScopeSafeAt language
            (available ++ outer).length (.apply rule.label arguments) := by
          intro presentation presentationMembership
          exact binderSafeAt_mono presentation.quoteConstructor
            (scope presentation presentationMembership) (by simp)
        have resetScope := reflectiveScopeSafeListAt_zero_of_typed_quote
          valid membership argumentsTyped quoted fullScope
        let argumentsTerm : AvailableOpenArguments language source []
            (available ++ outer) rule.params :=
          AvailableOpenArguments.ofCertificates (by
            simpa only [List.nil_append] using argumentsTyped)
            canonicalArguments objectArguments resetScope
        have argumentsSafe' :
            argumentsTerm.typed.ReflectiveSupportSafeAt support [] :=
          argumentsSafe.castTyping
        have argumentsEquivalent :=
          argumentsSafe'.availableEquationForall₂_substitute_pointwise valid
            canonicalArguments objectArguments resetScope first second
              equivalent
        have assembled := argumentsEquivalent.assembleQuote membership notBare
          quoted
        have leftEndpoint :
            (argumentsTerm.substitute first argumentsSafe').applyQuote
                membership notBare quoted =
              sourceTerm.substitute first sourceSafe := by
          apply AvailableOpenPattern.ext
          simp [argumentsTerm, sourceTerm,
            ReflectiveContextSupport.substituteAt, quoted]
        have rightEndpoint :
            (argumentsTerm.substitute second argumentsSafe').applyQuote
                membership notBare quoted =
              sourceTerm.substitute second sourceSafe := by
          apply AvailableOpenPattern.ext
          simp [argumentsTerm, sourceTerm,
            ReflectiveContextSupport.substituteAt, quoted]
        rw [← leftEndpoint, ← rightEndpoint]
        exact assembled
    | @constructorOrdinary bound rule arguments membership notBare
        argumentsTyped available binderImage ordinary argumentsSafe =>
        have canonicalArguments :
            Pattern.hasCanonicalBinderMetadataList arguments = true := by
          simpa [Pattern.hasCanonicalBinderMetadata] using canonical
        have objectArguments : isObjectPatternList arguments = true := by
          simpa [isObjectPattern] using objectPattern
        have argumentScope := reflectiveScopeSafeListAt_of_nonquote ordinary
          scope
        let argumentsTerm : AvailableOpenArguments language source available
            outer rule.params :=
          AvailableOpenArguments.ofCertificates argumentsTyped
            canonicalArguments objectArguments argumentScope
        have argumentsSafe' :
            argumentsTerm.typed.ReflectiveSupportSafeAt support available :=
          argumentsSafe.castTyping
        have argumentsEquivalent :=
          argumentsSafe'.availableEquationForall₂_substitute_pointwise valid
            canonicalArguments objectArguments argumentScope first second
              equivalent
        have assembled := argumentsEquivalent.assembleOrdinary membership
          notBare ordinary
        have leftEndpoint :
            (argumentsTerm.substitute first argumentsSafe').applyOrdinary
                membership notBare ordinary =
              sourceTerm.substitute first sourceSafe := by
          apply AvailableOpenPattern.ext
          simp [argumentsTerm, sourceTerm,
            ReflectiveContextSupport.substituteAt, ordinary]
        have rightEndpoint :
            (argumentsTerm.substitute second argumentsSafe').applyOrdinary
                membership notBare ordinary =
              sourceTerm.substitute second sourceSafe := by
          apply AvailableOpenPattern.ext
          simp [argumentsTerm, sourceTerm,
            ReflectiveContextSupport.substituteAt, ordinary]
        rw [← leftEndpoint, ← rightEndpoint]
        exact assembled
    | @lambda bound binder body domain codomain bodyTyped available binderImage
        bodySafe =>
        have canonicalParts : binder.isNone = true ∧
            body.hasCanonicalBinderMetadata = true := by
          simpa [Pattern.hasCanonicalBinderMetadata] using canonical
        have bodyObject : isObjectPattern body = true := by
          simpa [isObjectPattern] using objectPattern
        have bodyScope : ReflectiveScopeSafeAt language
            (domain :: available).length body := by
          intro presentation presentationMembership
          simpa [binderSafeAt, List.length_cons] using
            scope presentation presentationMembership
        have bodyTyped' : HasType language source
            ((domain :: available) ++ outer) body codomain := by
          simpa only [List.cons_append] using bodyTyped
        have bodySafe' : bodyTyped'.ReflectiveSupportSafeAt support
            (domain :: available) := bodySafe.castTyping
        have bodyEquivalent :=
          bodySafe'.availableEquationSetoid_substitute_pointwise valid
            canonicalParts.2 bodyObject bodyScope first second equivalent
        have assembled := AvailableOpenPattern.equationSetoid_lambda_congr
          binder canonicalParts.1 bodyEquivalent
        let bodyTerm := AvailableOpenPattern.ofCertificates bodyTyped'
          canonicalParts.2 bodyObject bodyScope
        have leftEndpoint :
            (bodyTerm.substitute first bodySafe').lambda binder
                canonicalParts.1 = sourceTerm.substitute first sourceSafe := by
          apply AvailableOpenPattern.ext
          simp [bodyTerm, sourceTerm, ReflectiveContextSupport.substituteAt]
        have rightEndpoint :
            (bodyTerm.substitute second bodySafe').lambda binder
                canonicalParts.1 = sourceTerm.substitute second sourceSafe := by
          apply AvailableOpenPattern.ext
          simp [bodyTerm, sourceTerm, ReflectiveContextSupport.substituteAt]
        rw [← leftEndpoint, ← rightEndpoint]
        exact assembled
    | @multiLambda bound arity binders body domain codomain bodyTyped available
        binderImage bodySafe =>
        have canonicalParts : binders = [] ∧
            body.hasCanonicalBinderMetadata = true := by
          simpa [Pattern.hasCanonicalBinderMetadata] using canonical
        have bodyObject : isObjectPattern body = true := by
          simpa [isObjectPattern] using objectPattern
        have bodyScope : ReflectiveScopeSafeAt language
            (List.replicate arity domain ++ available).length body := by
          intro presentation presentationMembership
          simpa [binderSafeAt, List.length_append, List.length_replicate,
            Nat.add_comm] using scope presentation presentationMembership
        have bodyTyped' : HasType language source
            ((List.replicate arity domain ++ available) ++ outer) body
              codomain := by
          simpa only [List.append_assoc] using bodyTyped
        have bodySafe' : bodyTyped'.ReflectiveSupportSafeAt support
            (List.replicate arity domain ++ available) :=
          by simpa using bodySafe.castTyping
        have bodyEquivalent :=
          bodySafe'.availableEquationSetoid_substitute_pointwise valid
            canonicalParts.2 bodyObject bodyScope first second equivalent
        have assembled :=
          AvailableOpenPattern.equationSetoid_multiLambda_congr arity binders
            canonicalParts.1 bodyEquivalent
        let bodyTerm := AvailableOpenPattern.ofCertificates bodyTyped'
          canonicalParts.2 bodyObject bodyScope
        have leftEndpoint :
            (bodyTerm.substitute first bodySafe').multiLambda arity binders
                canonicalParts.1 = sourceTerm.substitute first sourceSafe := by
          apply AvailableOpenPattern.ext
          simp [bodyTerm, sourceTerm, ReflectiveContextSupport.substituteAt,
            Nat.add_comm]
        have rightEndpoint :
            (bodyTerm.substitute second bodySafe').multiLambda arity binders
                canonicalParts.1 = sourceTerm.substitute second sourceSafe := by
          apply AvailableOpenPattern.ext
          simp [bodyTerm, sourceTerm, ReflectiveContextSupport.substituteAt,
            Nat.add_comm]
        rw [← leftEndpoint, ← rightEndpoint]
        exact assembled
    | @subst bound body replacement domain codomain bodyTyped replacementTyped
        available binderImage bodySafe replacementSafe =>
        simp [isObjectPattern] at objectPattern
    | @collection bound collectionType elements rest elementType elementsTyped
        available binderImage elementsSafe =>
        cases rest with
        | some restName => simp [isObjectPattern] at objectPattern
        | none =>
            have canonicalElements :
                Pattern.hasCanonicalBinderMetadataList elements = true := by
              simpa [Pattern.hasCanonicalBinderMetadata] using canonical
            have objectElements : isObjectPatternList elements = true := by
              simpa [isObjectPattern] using objectPattern
            have elementScope : ∀ presentation ∈
                language.reflectivePresentations,
                binderSafeListAt presentation.quoteConstructor
                  available.length elements = true := by
              intro presentation presentationMembership
              simpa [binderSafeAt] using
                scope presentation presentationMembership
            let elementsTerm : AvailableOpenElements language source available
                outer elementType :=
              AvailableOpenElements.ofCertificates elementsTyped
                canonicalElements objectElements elementScope
            have elementsSafe' :
                elementsTerm.typed.ReflectiveSupportSafeAt support available :=
              elementsSafe.castTyping
            have elementsEquivalent :
                AvailableOpenElements.EquationForall₂ language target
                  available outer elementType
                  (elementsTerm.substitute first elementsSafe')
                  (elementsTerm.substitute second elementsSafe') :=
              ElementsHaveType.ReflectiveSupportSafeAt.availableEquationForall₂_substitute_pointwise
                  (language := language) valid
                  (source := source) (target := target) (support := support)
                  (available := available) (outer := outer)
                  (sourceElements := elements) (elementType := elementType)
                  (typed := elementsTerm.typed) elementsSafe'
                  canonicalElements objectElements elementScope first second
                  equivalent
            have assembled := elementsEquivalent.assemble collectionType
            have leftEndpoint :
                (elementsTerm.substitute first elementsSafe').collection
                    collectionType = sourceTerm.substitute first sourceSafe := by
              apply AvailableOpenPattern.ext
              simp [elementsTerm, sourceTerm,
                ReflectiveContextSupport.substituteAt]
            have rightEndpoint :
                (elementsTerm.substitute second elementsSafe').collection
                    collectionType = sourceTerm.substitute second sourceSafe := by
              apply AvailableOpenPattern.ext
              simp [elementsTerm, sourceTerm,
                ReflectiveContextSupport.substituteAt]
            rw [← leftEndpoint, ← rightEndpoint]
            exact assembled
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType membership parameterShape elementsTyped available
        binderImage elementsSafe =>
        cases rest with
        | some restName => simp [isObjectPattern] at objectPattern
        | none =>
            have canonicalElements :
                Pattern.hasCanonicalBinderMetadataList elements = true := by
              simpa [Pattern.hasCanonicalBinderMetadata] using canonical
            have objectElements : isObjectPatternList elements = true := by
              simpa [isObjectPattern] using objectPattern
            have elementScope : ∀ presentation ∈
                language.reflectivePresentations,
                binderSafeListAt presentation.quoteConstructor
                  available.length elements = true := by
              intro presentation presentationMembership
              simpa [binderSafeAt] using
                scope presentation presentationMembership
            let elementsTerm : AvailableOpenElements language source available
                outer elementType :=
              AvailableOpenElements.ofCertificates elementsTyped
                canonicalElements objectElements elementScope
            have elementsSafe' :
                elementsTerm.typed.ReflectiveSupportSafeAt support available :=
              elementsSafe.castTyping
            have elementsEquivalent :
                AvailableOpenElements.EquationForall₂ language target
                  available outer elementType
                  (elementsTerm.substitute first elementsSafe')
                  (elementsTerm.substitute second elementsSafe') :=
              ElementsHaveType.ReflectiveSupportSafeAt.availableEquationForall₂_substitute_pointwise
                  (language := language) valid
                  (source := source) (target := target) (support := support)
                  (available := available) (outer := outer)
                  (sourceElements := elements) (elementType := elementType)
                  (typed := elementsTerm.typed) elementsSafe'
                  canonicalElements objectElements elementScope first second
                  equivalent
            have assembled := elementsEquivalent.assembleConstructor membership
              parameterShape
            have leftEndpoint :
                (elementsTerm.substitute first
                    elementsSafe').collectionConstructor membership
                      parameterShape = sourceTerm.substitute first sourceSafe := by
              apply AvailableOpenPattern.ext
              simp [elementsTerm, sourceTerm,
                ReflectiveContextSupport.substituteAt]
            have rightEndpoint :
                (elementsTerm.substitute second
                    elementsSafe').collectionConstructor membership
                      parameterShape = sourceTerm.substitute second sourceSafe := by
              apply AvailableOpenPattern.ext
              simp [elementsTerm, sourceTerm,
                ReflectiveContextSupport.substituteAt]
            rw [← leftEndpoint, ← rightEndpoint]
            exact assembled
  termination_by 4 * substitutionPatternMeasure pattern
  decreasing_by
    all_goals try simp_wf
    all_goals try subst pattern
    all_goals try simp only [substitutionPatternMeasure]
    all_goals omega

  theorem AvailableOpenArgument.equationSetoid_substitute_pointwise
      {language : LanguageDef} (valid : language.validate = [])
      {source target : FreeTypeContext} {support : ContextSupport.Support}
      {available outer : List TypeExpr} {parameter : TermParam}
      {expected : TypeExpr}
      (argument : AvailableOpenArgument language source available outer
        parameter expected)
      (safe : argument.term.typed.ReflectiveSupportSafeAt support available)
      (first second : SupportedOpenAssignment language source target support)
      (equivalent : first.FiberEquivalent second) :
      (AvailableOpenArgument.equationSetoid language target available outer
        parameter expected).r
        (argument.substitute first safe) (argument.substitute second safe) := by
    cases argument with
    | mk term representation parameterType =>
        cases term with
        | mk pattern typed canonical objectPattern scope =>
            cases parameter with
            | simple parameterName parameterTypeExpression =>
                have termEquivalent :=
                  safe.availableEquationSetoid_substitute_pointwise valid
                    canonical objectPattern scope first second equivalent
                let pack := fun
                    (term : AvailableOpenPattern language target available outer
                      expected) =>
                  ({ term := term
                     representation := True.intro
                     parameterType := parameterType } :
                    AvailableOpenArgument language target available outer
                      (.simple parameterName parameterTypeExpression) expected)
                have packed := AvailableOpenArgument.equationSetoid_of_term_map
                  pack (by
                    intro left right generator
                    exact generator) termEquivalent
                have leftEndpoint :
                    pack ((AvailableOpenPattern.ofCertificates typed canonical
                      objectPattern scope).substitute first safe) =
                      ({ term := AvailableOpenPattern.ofCertificates typed
                            canonical objectPattern scope
                         representation := True.intro
                         parameterType := parameterType } :
                        AvailableOpenArgument language source available outer
                          (.simple parameterName parameterTypeExpression)
                            expected).substitute first safe := by
                  apply AvailableOpenArgument.ext
                  rfl
                have rightEndpoint :
                    pack ((AvailableOpenPattern.ofCertificates typed canonical
                      objectPattern scope).substitute second safe) =
                      ({ term := AvailableOpenPattern.ofCertificates typed
                            canonical objectPattern scope
                         representation := True.intro
                         parameterType := parameterType } :
                        AvailableOpenArgument language source available outer
                          (.simple parameterName parameterTypeExpression)
                            expected).substitute second safe := by
                  apply AvailableOpenArgument.ext
                  rfl
                change (AvailableOpenArgument.equationSetoid language target
                  available outer
                    (.simple parameterName parameterTypeExpression) expected).r
                  (pack ((AvailableOpenPattern.ofCertificates typed canonical
                    objectPattern scope).substitute first safe))
                  (pack ((AvailableOpenPattern.ofCertificates typed canonical
                    objectPattern scope).substitute second safe)) at packed
                rw [leftEndpoint, rightEndpoint] at packed
                exact packed
            | abstractionNamed binderName bodyName parameterTypeExpression =>
                obtain ⟨body, patternShape⟩ :=
                  (matchesParameterRepresentation_abstractionNamed_iff
                    binderName bodyName parameterTypeExpression pattern).mp
                      representation
                subst pattern
                let originalSafe := safe
                cases safe with
                | @lambda bound binder body domain codomain bodyTyped
                    available binderImage bodySafe =>
                      have bodyCanonical :
                          body.hasCanonicalBinderMetadata = true := by
                        simpa [Pattern.hasCanonicalBinderMetadata] using canonical
                      have bodyObject : isObjectPattern body = true := by
                        simpa [isObjectPattern] using objectPattern
                      have bodyScope : ReflectiveScopeSafeAt language
                          (domain :: available).length body := by
                        intro presentation presentationMembership
                        simpa [binderSafeAt, List.length_cons] using
                          scope presentation presentationMembership
                      have bodyTyped' : HasType language source
                          ((domain :: available) ++ outer) body codomain := by
                        simpa only [List.cons_append] using bodyTyped
                      have bodySafe' :
                          bodyTyped'.ReflectiveSupportSafeAt support
                            (domain :: available) := bodySafe.castTyping
                      have bodyEquivalent :=
                        bodySafe'.availableEquationSetoid_substitute_pointwise
                          valid bodyCanonical bodyObject bodyScope first second
                            equivalent
                      let pack := fun term =>
                        ({ term := AvailableOpenPattern.lambda none rfl term
                           representation := True.intro
                           parameterType := parameterType } :
                          AvailableOpenArgument language target available outer
                            (.abstractionNamed binderName bodyName
                              parameterTypeExpression)
                                (.arrow domain codomain))
                      have packed :=
                        AvailableOpenArgument.equationSetoid_of_term_map pack
                          (by
                            intro left right generator
                            exact EquationSemantics.equationContextStep_fill
                              (.lambda none .hole) generator)
                          bodyEquivalent
                      let bodyTerm := AvailableOpenPattern.ofCertificates
                        bodyTyped' bodyCanonical bodyObject bodyScope
                      let sourceArgument : AvailableOpenArgument language source
                          available outer
                          (.abstractionNamed binderName bodyName
                            parameterTypeExpression) (.arrow domain codomain) :=
                        { term := AvailableOpenPattern.lambda none rfl bodyTerm
                          representation := True.intro
                          parameterType := parameterType }
                      have sourceSafe :
                          sourceArgument.term.typed.ReflectiveSupportSafeAt
                            support available := by
                        exact originalSafe.castTyping
                      have leftEndpoint :
                          pack (bodyTerm.substitute first bodySafe') =
                            sourceArgument.substitute first sourceSafe := by
                        apply AvailableOpenArgument.ext
                        simp [pack, sourceArgument, bodyTerm,
                          ReflectiveContextSupport.substituteAt]
                      have rightEndpoint :
                          pack (bodyTerm.substitute second bodySafe') =
                            sourceArgument.substitute second sourceSafe := by
                        apply AvailableOpenArgument.ext
                        simp [pack, sourceArgument, bodyTerm,
                          ReflectiveContextSupport.substituteAt]
                      rw [leftEndpoint, rightEndpoint] at packed
                      exact packed
            | multiAbstractionNamed binderNames bodyName
                parameterTypeExpression =>
                obtain ⟨arity, body, patternShape⟩ :=
                  (matchesParameterRepresentation_multiAbstractionNamed_iff
                    binderNames bodyName parameterTypeExpression pattern).mp
                      representation
                subst pattern
                let originalSafe := safe
                cases safe with
                | @multiLambda bound arity binders body domain codomain
                    bodyTyped available binderImage bodySafe =>
                      have bodyCanonical :
                          body.hasCanonicalBinderMetadata = true := by
                        simpa [Pattern.hasCanonicalBinderMetadata] using canonical
                      have bodyObject : isObjectPattern body = true := by
                        simpa [isObjectPattern] using objectPattern
                      have bodyScope : ReflectiveScopeSafeAt language
                          (List.replicate arity domain ++ available).length
                            body := by
                        intro presentation presentationMembership
                        simpa [binderSafeAt, List.length_append,
                          List.length_replicate, Nat.add_comm] using
                            scope presentation presentationMembership
                      have bodyTyped' : HasType language source
                          ((List.replicate arity domain ++ available) ++ outer)
                            body codomain := by
                        simpa only [List.append_assoc] using bodyTyped
                      have bodySafe' :
                          bodyTyped'.ReflectiveSupportSafeAt support
                            (List.replicate arity domain ++ available) := by
                        simpa using bodySafe.castTyping
                      have bodyEquivalent :=
                        bodySafe'.availableEquationSetoid_substitute_pointwise
                          valid bodyCanonical bodyObject bodyScope first second
                            equivalent
                      let pack := fun term =>
                        ({ term := AvailableOpenPattern.multiLambda arity [] rfl
                              term
                           representation := True.intro
                           parameterType := parameterType } :
                          AvailableOpenArgument language target available outer
                            (.multiAbstractionNamed binderNames bodyName
                              parameterTypeExpression)
                                (.arrow (.multiBinder domain) codomain))
                      have packed :=
                        AvailableOpenArgument.equationSetoid_of_term_map pack
                          (by
                            intro left right generator
                            exact EquationSemantics.equationContextStep_fill
                              (.multiLambda arity [] .hole) generator)
                          bodyEquivalent
                      let bodyTerm := AvailableOpenPattern.ofCertificates
                        bodyTyped' bodyCanonical bodyObject bodyScope
                      let sourceArgument : AvailableOpenArgument language source
                          available outer
                          (.multiAbstractionNamed binderNames bodyName
                            parameterTypeExpression)
                              (.arrow (.multiBinder domain) codomain) :=
                        { term := AvailableOpenPattern.multiLambda arity [] rfl
                            bodyTerm
                          representation := True.intro
                          parameterType := parameterType }
                      have sourceSafe :
                          sourceArgument.term.typed.ReflectiveSupportSafeAt
                            support available := by
                        exact originalSafe.castTyping
                      have leftEndpoint :
                          pack (bodyTerm.substitute first bodySafe') =
                            sourceArgument.substitute first sourceSafe := by
                        apply AvailableOpenArgument.ext
                        simp [pack, sourceArgument, bodyTerm,
                          ReflectiveContextSupport.substituteAt, Nat.add_comm]
                      have rightEndpoint :
                          pack (bodyTerm.substitute second bodySafe') =
                            sourceArgument.substitute second sourceSafe := by
                        apply AvailableOpenArgument.ext
                        simp [pack, sourceArgument, bodyTerm,
                          ReflectiveContextSupport.substituteAt, Nat.add_comm]
                      rw [leftEndpoint, rightEndpoint] at packed
                      exact packed
  termination_by 4 * substitutionPatternMeasure argument.term.pattern + 2
  decreasing_by
    all_goals try subst argument
    all_goals try subst term
    all_goals try subst pattern
    all_goals try simp only [substitutionPatternMeasure]
    all_goals omega

  theorem ArgumentsHaveTypes.ReflectiveSupportSafeAt.availableEquationForall₂_substitute_pointwise
      {language : LanguageDef} (valid : language.validate = [])
      {source target : FreeTypeContext} {support : ContextSupport.Support}
      {available outer : List TypeExpr} {sourceArguments : List Pattern}
      {parameters : List TermParam}
      {typed : ArgumentsHaveTypes language source (available ++ outer)
        sourceArguments parameters}
      (safe : typed.ReflectiveSupportSafeAt support available)
      (canonical :
        Pattern.hasCanonicalBinderMetadataList sourceArguments = true)
      (objects : isObjectPatternList sourceArguments = true)
      (scope : ∀ presentation ∈ language.reflectivePresentations,
        binderSafeListAt presentation.quoteConstructor available.length
          sourceArguments = true)
      (first second : SupportedOpenAssignment language source target support)
      (equivalent : first.FiberEquivalent second) :
      let spine := AvailableOpenArguments.ofCertificates typed canonical
        objects scope
      AvailableOpenArguments.EquationForall₂ language target available outer
        (spine.substitute first safe) (spine.substitute second safe) := by
    let sourceSpine := AvailableOpenArguments.ofCertificates typed canonical
      objects scope
    let sourceSafe := safe
    change AvailableOpenArguments.EquationForall₂ language target available
      outer (sourceSpine.substitute first sourceSafe)
        (sourceSpine.substitute second sourceSafe)
    cases safe with
    | @nil bound available binderImage =>
        have leftEndpoint : sourceSpine.substitute first sourceSafe =
            AvailableOpenArguments.nil language target available outer := by
          apply AvailableOpenArguments.ext
          rfl
        have rightEndpoint : sourceSpine.substitute second sourceSafe =
            AvailableOpenArguments.nil language target available outer := by
          apply AvailableOpenArguments.ext
          rfl
        rw [leftEndpoint, rightEndpoint]
        exact .nil
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped available
        binderImage argumentSafe argumentsSafe =>
        have canonicalParts : argument.hasCanonicalBinderMetadata = true ∧
            Pattern.hasCanonicalBinderMetadataList arguments = true := by
          simpa [Pattern.hasCanonicalBinderMetadataList] using canonical
        have objectParts : isObjectPattern argument = true ∧
            isObjectPatternList arguments = true := by
          simpa [isObjectPatternList] using objects
        have argumentScope : ReflectiveScopeSafeAt language available.length
            argument := by
          intro presentation presentationMembership
          have full := scope presentation presentationMembership
          have parts :
              binderSafeAt presentation.quoteConstructor available.length
                    argument = true ∧
                binderSafeListAt presentation.quoteConstructor
                    available.length arguments = true := by
            simpa [binderSafeListAt] using full
          exact parts.1
        have tailScope : ∀ presentation ∈ language.reflectivePresentations,
            binderSafeListAt presentation.quoteConstructor available.length
              arguments = true := by
          intro presentation presentationMembership
          have full := scope presentation presentationMembership
          have parts :
              binderSafeAt presentation.quoteConstructor available.length
                    argument = true ∧
                binderSafeListAt presentation.quoteConstructor
                    available.length arguments = true := by
            simpa [binderSafeListAt] using full
          exact parts.2
        let argumentTerm := AvailableOpenPattern.ofCertificates argumentTyped
          canonicalParts.1 objectParts.1 argumentScope
        let tailTerm := AvailableOpenArguments.ofCertificates argumentsTyped
          canonicalParts.2 objectParts.2 tailScope
        have argumentSafe' :
            argumentTerm.typed.ReflectiveSupportSafeAt support available :=
          argumentSafe.castTyping
        let sourceArgument : AvailableOpenArgument language source available
            outer parameter expected :=
          { term := argumentTerm
            representation := by simpa [argumentTerm] using representation
            parameterType := parameterType }
        have sourceArgumentSafe :
            sourceArgument.term.typed.ReflectiveSupportSafeAt support
              available := argumentSafe.castTyping
        have tailEquivalent :=
          ArgumentsHaveTypes.ReflectiveSupportSafeAt.availableEquationForall₂_substitute_pointwise
            valid (available := available) (outer := outer) argumentsSafe
            canonicalParts.2 objectParts.2 tailScope first second equivalent
        have headEquivalent :=
          AvailableOpenArgument.equationSetoid_substitute_pointwise valid
            sourceArgument sourceArgumentSafe first second equivalent
        let leftHead : AvailableOpenArgument language target available outer
            parameter expected :=
          sourceArgument.substitute first sourceArgumentSafe
        let rightHead : AvailableOpenArgument language target available outer
            parameter expected :=
          sourceArgument.substitute second sourceArgumentSafe
        have combined := AvailableOpenArguments.EquationForall₂.cons
          headEquivalent tailEquivalent
        have leftEndpoint :
            AvailableOpenArguments.cons leftHead
                (tailTerm.substitute first argumentsSafe) =
              sourceSpine.substitute first sourceSafe := by
          apply AvailableOpenArguments.ext
          simp [leftHead, sourceArgument, argumentTerm, tailTerm, sourceSpine]
        have rightEndpoint :
            AvailableOpenArguments.cons rightHead
                (tailTerm.substitute second argumentsSafe) =
              sourceSpine.substitute second sourceSafe := by
          apply AvailableOpenArguments.ext
          simp [rightHead, sourceArgument, argumentTerm, tailTerm, sourceSpine]
        rw [← leftEndpoint, ← rightEndpoint]
        exact combined
  termination_by 4 * substitutionPatternListMeasure sourceArguments + 3
  decreasing_by
    all_goals try simp_wf
    all_goals try subst sourceArguments
    all_goals try simp only [substitutionPatternListMeasure]
    all_goals omega

  theorem ElementsHaveType.ReflectiveSupportSafeAt.availableEquationForall₂_substitute_pointwise
      {language : LanguageDef} (valid : language.validate = [])
      {source target : FreeTypeContext} {support : ContextSupport.Support}
      {available outer : List TypeExpr} {sourceElements : List Pattern}
      {elementType : TypeExpr}
      {typed : ElementsHaveType language source (available ++ outer)
        sourceElements elementType}
      (safe : typed.ReflectiveSupportSafeAt support available)
      (canonical :
        Pattern.hasCanonicalBinderMetadataList sourceElements = true)
      (objects : isObjectPatternList sourceElements = true)
      (scope : ∀ presentation ∈ language.reflectivePresentations,
        binderSafeListAt presentation.quoteConstructor available.length
          sourceElements = true)
      (first second : SupportedOpenAssignment language source target support)
      (equivalent : first.FiberEquivalent second) :
      let spine := AvailableOpenElements.ofCertificates typed canonical objects
        scope
      AvailableOpenElements.EquationForall₂ language target available outer
        elementType (spine.substitute first safe)
          (spine.substitute second safe) := by
    let sourceSpine := AvailableOpenElements.ofCertificates typed canonical
      objects scope
    let sourceSafe := safe
    change AvailableOpenElements.EquationForall₂ language target available
      outer elementType (sourceSpine.substitute first sourceSafe)
        (sourceSpine.substitute second sourceSafe)
    cases safe with
    | @nil bound elementType available binderImage =>
        have leftEndpoint : sourceSpine.substitute first sourceSafe =
            AvailableOpenElements.nil language target available outer
              elementType := by
          apply AvailableOpenElements.ext
          rfl
        have rightEndpoint : sourceSpine.substitute second sourceSafe =
            AvailableOpenElements.nil language target available outer
              elementType := by
          apply AvailableOpenElements.ext
          rfl
        rw [leftEndpoint, rightEndpoint]
        exact .nil
    | @cons bound element elements elementType elementTyped elementsTyped
        available binderImage elementSafe elementsSafe =>
        have canonicalParts : element.hasCanonicalBinderMetadata = true ∧
            Pattern.hasCanonicalBinderMetadataList elements = true := by
          simpa [Pattern.hasCanonicalBinderMetadataList] using canonical
        have objectParts : isObjectPattern element = true ∧
            isObjectPatternList elements = true := by
          simpa [isObjectPatternList] using objects
        have elementScope : ReflectiveScopeSafeAt language available.length
            element := by
          intro presentation presentationMembership
          have full := scope presentation presentationMembership
          have parts :
              binderSafeAt presentation.quoteConstructor available.length
                    element = true ∧
                binderSafeListAt presentation.quoteConstructor
                    available.length elements = true := by
            simpa [binderSafeListAt] using full
          exact parts.1
        have tailScope : ∀ presentation ∈ language.reflectivePresentations,
            binderSafeListAt presentation.quoteConstructor available.length
              elements = true := by
          intro presentation presentationMembership
          have full := scope presentation presentationMembership
          have parts :
              binderSafeAt presentation.quoteConstructor available.length
                    element = true ∧
                binderSafeListAt presentation.quoteConstructor
                    available.length elements = true := by
            simpa [binderSafeListAt] using full
          exact parts.2
        let elementTerm := AvailableOpenPattern.ofCertificates elementTyped
          canonicalParts.1 objectParts.1 elementScope
        let tailTerm := AvailableOpenElements.ofCertificates elementsTyped
          canonicalParts.2 objectParts.2 tailScope
        have elementEquivalent :=
          elementSafe.availableEquationSetoid_substitute_pointwise valid
            canonicalParts.1 objectParts.1 elementScope first second equivalent
        have tailEquivalent :=
          ElementsHaveType.ReflectiveSupportSafeAt.availableEquationForall₂_substitute_pointwise
            valid (available := available) (outer := outer) elementsSafe
            canonicalParts.2 objectParts.2 tailScope first second equivalent
        have combined := AvailableOpenElements.EquationForall₂.cons
          elementEquivalent tailEquivalent
        have leftEndpoint :
            AvailableOpenElements.cons
                (elementTerm.substitute first elementSafe)
                (tailTerm.substitute first elementsSafe) =
              sourceSpine.substitute first sourceSafe := by
          apply AvailableOpenElements.ext
          simp [elementTerm, tailTerm, sourceSpine]
        have rightEndpoint :
            AvailableOpenElements.cons
                (elementTerm.substitute second elementSafe)
                (tailTerm.substitute second elementsSafe) =
              sourceSpine.substitute second sourceSafe := by
          apply AvailableOpenElements.ext
          simp [elementTerm, tailTerm, sourceSpine]
        rw [← leftEndpoint, ← rightEndpoint]
        exact combined
  termination_by 4 * substitutionPatternListMeasure sourceElements + 3
  decreasing_by
    all_goals try simp_wf
    all_goals try subst sourceElements
    all_goals try simp only [substitutionPatternListMeasure]
    all_goals omega
end

/-- Fiberwise-equivalent assignments act pointwise on an already packaged
split-fiber object.  This wrapper keeps the caller's proof-relevant package
as the endpoints instead of exposing the internally reconstructed
certificate bundle used by the mutual induction. -/
theorem AvailableOpenPattern.equationSetoid_substitute_pointwise
    {language : LanguageDef} (valid : language.validate = [])
    {source target : FreeTypeContext} {support : ContextSupport.Support}
    {available outer : List TypeExpr} {type : TypeExpr}
    (pattern : AvailableOpenPattern language source available outer type)
    (safe : pattern.typed.ReflectiveSupportSafeAt support available)
    (first second : SupportedOpenAssignment language source target support)
    (equivalent : first.FiberEquivalent second) :
    (AvailableOpenPattern.equationSetoid language target available outer
      type).r (pattern.substitute first safe)
        (pattern.substitute second safe) := by
  have path := safe.availableEquationSetoid_substitute_pointwise valid
    pattern.canonicalBinderMetadata pattern.objectPattern
      pattern.reflectiveScope first second equivalent
  let reconstructed := AvailableOpenPattern.ofCertificates pattern.typed
    pattern.canonicalBinderMetadata pattern.objectPattern
      pattern.reflectiveScope
  change (AvailableOpenPattern.equationSetoid language target available outer
    type).r (reconstructed.substitute first safe)
      (reconstructed.substitute second safe) at path
  have leftEndpoint : reconstructed.substitute first safe =
      pattern.substitute first safe := by
    apply AvailableOpenPattern.ext
    rfl
  have rightEndpoint : reconstructed.substitute second safe =
      pattern.substitute second safe := by
    apply AvailableOpenPattern.ext
    rfl
  rw [leftEndpoint, rightEndpoint] at path
  exact path

mutual
  /-- Pointwise-equivalent supported assignments produce contextually
  equivalent instances of one typed structural skeleton at every reflective
  substitution depth. -/
  theorem HasType.equationEquiv_substituteAt_pointwise
      {language : LanguageDef} {source target : FreeTypeContext}
      {support : ContextSupport.Support}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType language source bound pattern type)
      (first second : SupportedOpenAssignment language source target support)
      (equivalent : first.Equivalent second) (availableDepth : Nat) :
      EquationEquiv defaultBasePremises language
        (ReflectiveContextSupport.substituteAt language support
          first.assignment availableDepth pattern)
        (ReflectiveContextSupport.substituteAt language support
          second.assignment availableDepth pattern) := by
    cases typed with
    | @bvar bound index type lookup =>
        simpa only [ReflectiveContextSupport.substituteAt, EquationEquiv] using
          (Relation.EqvGen.refl
            (r := EquationContextStep defaultBasePremises language)
            (.bvar index))
    | @fvar bound name type lookup =>
        simpa only [ReflectiveContextSupport.substituteAt] using
          equivalent lookup (availableDepth - (support name).length)
    | @constructor bound rule arguments membership notBare argumentsTyped =>
        have argumentsEquivalent :=
          argumentsTyped.equationEquiv_substituteAt_pointwise first second
            equivalent
            (if ReflectiveContextSupport.isQuoteConstructor language rule.label
              then 0 else availableDepth)
        simpa only [ReflectiveContextSupport.substituteAt] using
          equationEquiv_apply_of_forall₂ rule.label argumentsEquivalent
    | @lambda bound binder body domain codomain bodyTyped =>
        have bodyEquivalent :=
          bodyTyped.equationEquiv_substituteAt_pointwise first second
            equivalent (availableDepth + 1)
        simpa only [ReflectiveContextSupport.substituteAt, OneHoleContext.fill]
          using equationEquiv_fill (.lambda binder .hole) bodyEquivalent
    | @multiLambda bound arity binders body domain codomain bodyTyped =>
        have bodyEquivalent :=
          bodyTyped.equationEquiv_substituteAt_pointwise first second
            equivalent (availableDepth + arity)
        simpa only [ReflectiveContextSupport.substituteAt, OneHoleContext.fill]
          using equationEquiv_fill
            (.multiLambda arity binders .hole) bodyEquivalent
    | @subst bound body replacement domain codomain bodyTyped replacementTyped =>
        have bodyEquivalent :=
          bodyTyped.equationEquiv_substituteAt_pointwise first second
            equivalent (availableDepth + 1)
        have replacementEquivalent :=
          replacementTyped.equationEquiv_substituteAt_pointwise first second
            equivalent availableDepth
        have bodyStep := equationEquiv_fill
          (.substBody .hole
            (ReflectiveContextSupport.substituteAt language support
              first.assignment availableDepth replacement))
          bodyEquivalent
        have replacementStep := equationEquiv_fill
          (.substReplacement
            (ReflectiveContextSupport.substituteAt language support
              second.assignment (availableDepth + 1) body) .hole)
          replacementEquivalent
        change Relation.EqvGen
          (EquationContextStep defaultBasePremises language) _ _
        exact Relation.EqvGen.trans _ _ _
          (by simpa only [ReflectiveContextSupport.substituteAt,
              OneHoleContext.fill, EquationEquiv] using bodyStep)
          (by simpa only [ReflectiveContextSupport.substituteAt,
              OneHoleContext.fill, EquationEquiv] using replacementStep)
    | @collection bound collectionType elements rest elementType elementsTyped =>
        have elementsEquivalent :=
          elementsTyped.equationEquiv_substituteAt_pointwise first second
            equivalent availableDepth
        simpa only [ReflectiveContextSupport.substituteAt] using
          equationEquiv_collection_of_forall₂ collectionType rest
            elementsEquivalent
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType membership parameterShape elementsTyped =>
        have elementsEquivalent :=
          elementsTyped.equationEquiv_substituteAt_pointwise first second
            equivalent availableDepth
        simpa only [ReflectiveContextSupport.substituteAt] using
          equationEquiv_collection_of_forall₂ collectionType rest
            elementsEquivalent

  /-- Constructor argument spines inherit the same pointwise substitution
  relation in authored parameter order. -/
  theorem ArgumentsHaveTypes.equationEquiv_substituteAt_pointwise
      {language : LanguageDef} {source target : FreeTypeContext}
      {support : ContextSupport.Support}
      {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language source bound arguments parameters)
      (first second : SupportedOpenAssignment language source target support)
      (equivalent : first.Equivalent second) (availableDepth : Nat) :
      List.Forall₂ (EquationEquiv defaultBasePremises language)
        (arguments.map (ReflectiveContextSupport.substituteAt language support
          first.assignment availableDepth))
        (arguments.map (ReflectiveContextSupport.substituteAt language support
          second.assignment availableDepth)) := by
    cases typed with
    | nil => exact .nil
    | cons representation parameterType argumentTyped argumentsTyped =>
        exact .cons
          (argumentTyped.equationEquiv_substituteAt_pointwise first second
            equivalent availableDepth)
          (argumentsTyped.equationEquiv_substituteAt_pointwise first second
            equivalent availableDepth)

  /-- Collection element spines inherit the same pointwise substitution
  relation without changing their order or multiplicity. -/
  theorem ElementsHaveType.equationEquiv_substituteAt_pointwise
      {language : LanguageDef} {source target : FreeTypeContext}
      {support : ContextSupport.Support}
      {bound : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (typed : ElementsHaveType language source bound elements elementType)
      (first second : SupportedOpenAssignment language source target support)
      (equivalent : first.Equivalent second) (availableDepth : Nat) :
      List.Forall₂ (EquationEquiv defaultBasePremises language)
        (elements.map (ReflectiveContextSupport.substituteAt language support
          first.assignment availableDepth))
        (elements.map (ReflectiveContextSupport.substituteAt language support
          second.assignment availableDepth)) := by
    cases typed with
    | nil => exact .nil
    | cons elementTyped elementsTyped =>
        exact .cons
          (elementTyped.equationEquiv_substituteAt_pointwise first second
            equivalent availableDepth)
          (elementsTyped.equationEquiv_substituteAt_pointwise first second
            equivalent availableDepth)
end

/-- Root-level pointwise substitution congruence in the exact authored bound
fiber. -/
theorem HasType.equationEquiv_substitute_pointwise
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language source bound pattern type)
    (first second : SupportedOpenAssignment language source target support)
    (equivalent : first.Equivalent second) :
    EquationEquiv defaultBasePremises language
      (ReflectiveContextSupport.substitute language support first.assignment
        bound pattern)
      (ReflectiveContextSupport.substitute language support second.assignment
        bound pattern) := by
  simpa only [ReflectiveContextSupport.substitute] using
    typed.equationEquiv_substituteAt_pointwise first second equivalent
      bound.length

/-- Fiberwise-equivalent assignments act identically up to the sole authored
contextual equation relation on any support-safe open object. -/
theorem OpenPattern.equationEquiv_substituteReflectiveSupported_pointwise
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support} {bound : List TypeExpr}
    {type : TypeExpr}
    (pattern : OpenPattern language source bound type)
    (first second : SupportedOpenAssignment language source target support)
    (safe : pattern.2.1.ReflectiveSupportSafeAt support bound)
    (equivalent : first.FiberEquivalent second) :
    EquationEquiv defaultBasePremises language
      (pattern.substituteReflectiveSupported first safe).1
      (pattern.substituteReflectiveSupported second safe).1 := by
  simpa only [OpenPattern.substituteReflectiveSupported_pattern] using
    pattern.2.1.equationEquiv_substitute_pointwise first second
      equivalent.toEquivalent

namespace SupportSafeOpenPattern

private theorem equationContextStep_substitute_of_eq
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support} {bound : List TypeExpr}
    {type : TypeExpr}
    (stable : SupportedEquationSubstitutionStable language)
    (assignment : SupportedOpenAssignment language source target support)
    (left right : SupportSafeOpenPattern language source support bound type)
    {leftPattern rightPattern : Pattern}
    (leftEquality : left.term.1 = leftPattern)
    (rightEquality : right.term.1 = rightPattern)
    (generator : EquationContextStep defaultBasePremises language
      leftPattern rightPattern) :
    EquationEquiv defaultBasePremises language
      (left.substitute assignment).1 (right.substitute assignment).1 := by
  cases generator with
  | @inContext context redex contractum equationWitness =>
      apply stable.1 assignment left right
      exact ⟨context, redex, contractum, equationWitness,
        leftEquality, rightEquality⟩
  | @reflectiveInContext context declaration reflectedLeft reflectedRight
      membership representatives =>
      apply stable.2 assignment membership left right
      rw [leftEquality, rightEquality]
      exact canonicalize_fill_congr declaration context representatives

/-- The two independently checkable substitution-stability obligations cover
exactly the ordinary and reflective constructors of one authored contextual
equation generator. -/
theorem equationGenerator_substitute
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support} {bound : List TypeExpr}
    {type : TypeExpr}
    (stable : SupportedEquationSubstitutionStable language)
    (assignment : SupportedOpenAssignment language source target support)
    (left right : SupportSafeOpenPattern language source support bound type)
    (generator : equationGenerator left right) :
    EquationEquiv defaultBasePremises language
      (left.substitute assignment).1 (right.substitute assignment).1 := by
  exact equationContextStep_substitute_of_eq stable assignment left right
    rfl rfl generator

/-- Supported substitution maps the full least support-safe equation closure
into the sole authored raw contextual equation relation. -/
theorem equationSetoid_substitute
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support} {bound : List TypeExpr}
    {type : TypeExpr}
    (stable : SupportedEquationSubstitutionStable language)
    (assignment : SupportedOpenAssignment language source target support)
    {left right : SupportSafeOpenPattern language source support bound type}
    (equivalent : (equationSetoid language source support bound type).r
      left right) :
    EquationEquiv defaultBasePremises language
      (left.substitute assignment).1 (right.substitute assignment).1 := by
  induction equivalent with
  | rel left right generator =>
      exact equationGenerator_substitute stable assignment left right generator
  | refl pattern =>
      exact Relation.EqvGen.refl _
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

/-- Bivariant form used by region restoration: vary the contextual-equation
representative and the finite boundary assignment independently, then compose
the two proved congruences. -/
theorem equationSetoid_substitute_bivariant
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support} {bound : List TypeExpr}
    {type : TypeExpr}
    (stable : SupportedEquationSubstitutionStable language)
    (first second : SupportedOpenAssignment language source target support)
    (assignmentsEquivalent : first.Equivalent second)
    {left right : SupportSafeOpenPattern language source support bound type}
    (patternsEquivalent :
      (equationSetoid language source support bound type).r left right) :
    EquationEquiv defaultBasePremises language
      (left.substitute first).1 (right.substitute second).1 := by
  have patternStep := equationSetoid_substitute stable first patternsEquivalent
  have assignmentStep :=
    right.term.2.1.equationEquiv_substitute_pointwise first second
      assignmentsEquivalent
  exact Relation.EqvGen.trans _ _ _ patternStep (by
    simpa only [substitute_pattern, EquationEquiv] using assignmentStep)

end SupportSafeOpenPattern

end WellSorted

end Mettapedia.GSLT.LanguageDef
