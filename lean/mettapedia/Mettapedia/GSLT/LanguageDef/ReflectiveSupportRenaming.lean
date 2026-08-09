import Mettapedia.GSLT.LanguageDef.ConstructorSupport
import Mettapedia.GSLT.LanguageDef.ContextSupport

/-!
# Reflective-support-safe free-variable renaming

Semantic atom quotients change only ordinary free-variable names.  They do
not change constructors, locally nameless binders, explicit substitution
structure, or collection tails.  This file isolates that operation from the
more general reflective substitution machinery and proves that it preserves
typing together with an arbitrary binder image in
`ReflectiveSupportSafeAt`.

No injectivity assumption is required: two names may coalesce when their
typing and reflective-support fibres agree.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.Reflection

namespace Pattern

/-- Rename ordinary free-variable nodes structurally.  Collection-tail names
are schema metadata rather than `Pattern.fvar` nodes and remain unchanged. -/
def renameFVars (rename : String -> String) : Pattern -> Pattern
  | .bvar index => .bvar index
  | .fvar name => .fvar (rename name)
  | .apply constructor arguments =>
      .apply constructor (arguments.map (renameFVars rename))
  | .lambda binder body => .lambda binder (renameFVars rename body)
  | .multiLambda arity binders body =>
      .multiLambda arity binders (renameFVars rename body)
  | .subst body replacement =>
      .subst (renameFVars rename body) (renameFVars rename replacement)
  | .collection collectionType elements rest =>
      .collection collectionType (elements.map (renameFVars rename)) rest
termination_by pattern => sizeOf pattern

@[simp]
theorem renameFVars_id (pattern : Pattern) :
    renameFVars id pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [renameFVars]
  | hfvar name => simp [renameFVars]
  | happly constructor arguments inductionHypothesis =>
      simp only [renameFVars, Pattern.apply.injEq, true_and]
      induction arguments with
      | nil => rfl
      | cons argument arguments listInduction =>
          simp only [List.map_cons]
          rw [inductionHypothesis argument (by simp)]
          exact congrArg (argument :: ·)
            (listInduction fun other membership =>
              inductionHypothesis other (by simp [membership]))
  | hlambda binder body inductionHypothesis =>
      simp [renameFVars, inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [renameFVars, inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [renameFVars, bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [renameFVars, Pattern.collection.injEq, true_and, and_true]
      induction elements with
      | nil => rfl
      | cons element elements listInduction =>
          simp only [List.map_cons]
          rw [inductionHypothesis element (by simp)]
          exact congrArg (element :: ·)
            (listInduction fun other membership =>
              inductionHypothesis other (by simp [membership]))

@[simp]
theorem renameFVars_comp (first second : String -> String)
    (pattern : Pattern) :
    renameFVars second (renameFVars first pattern) =
      renameFVars (second ∘ first) pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [renameFVars]
  | hfvar name => simp [renameFVars, Function.comp_apply]
  | happly constructor arguments inductionHypothesis =>
      simp only [renameFVars, List.map_map, Pattern.apply.injEq, true_and]
      exact List.map_congr_left inductionHypothesis
  | hlambda binder body inductionHypothesis =>
      simp [renameFVars, inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [renameFVars, inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [renameFVars, bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [renameFVars, List.map_map, Pattern.collection.injEq,
        true_and, and_true]
      exact List.map_congr_left inductionHypothesis

end Pattern

/-- A fibre-preserving renaming of ordinary free variables.  The support
equation is oriented toward reconstruction of a target support-safe proof. -/
structure ReflectiveFVarRenaming
    (sourceFree targetFree : WellSorted.FreeTypeContext)
    (sourceSupport targetSupport : ContextSupport.Support) where
  name : String -> String
  mapsLookup : forall {sourceName type},
    sourceFree sourceName = some type ->
      targetFree (name sourceName) = some type
  mapsSupport : forall {sourceName type},
    sourceFree sourceName = some type ->
      targetSupport (name sourceName) = sourceSupport sourceName

namespace WellSorted

/-- Renaming ordinary free variables preserves the representation shape of
an authored constructor argument. -/
theorem MatchesParameterRepresentation.renameFVars
    {parameter : TermParam} {pattern : Pattern}
    (rename : String -> String)
    (representation : MatchesParameterRepresentation parameter pattern) :
    MatchesParameterRepresentation parameter
      (Pattern.renameFVars rename pattern) := by
  cases parameter with
  | simple name type => trivial
  | abstractionNamed binderName bodyName type =>
      cases pattern with
      | lambda binder body =>
          cases binder <;>
            simp_all [MatchesParameterRepresentation, Pattern.renameFVars]
      | _ => simp_all [MatchesParameterRepresentation]
  | multiAbstractionNamed binderNames bodyName type =>
      cases pattern with
      | multiLambda arity binders body =>
          cases binders with
          | nil =>
              simp [MatchesParameterRepresentation, Pattern.renameFVars]
          | cons binder binders =>
              simp_all [MatchesParameterRepresentation]
      | _ => simp_all [MatchesParameterRepresentation]

/-- Fibre-preserving free-variable renaming preserves typing and the full
constructor-facing reflective-support certificate for any binder image. -/
theorem HasType.ReflectiveSupportSafeAt.renameFVars
    {profile : ReflectionProfile} {language : LanguageDef}
    {sourceFree targetFree : FreeTypeContext}
    {sourceSupport targetSupport : ContextSupport.Support}
    (mapping : ReflectiveFVarRenaming sourceFree targetFree
      sourceSupport targetSupport)
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {typed : HasType language sourceFree bound pattern type}
    {available : List TypeExpr} {binderImage : TypeExpr -> TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt profile sourceSupport available
      binderImage) :
    exists renamedTyped : HasType language targetFree bound
        (Pattern.renameFVars mapping.name pattern) type,
      renamedTyped.ReflectiveSupportSafeAt profile targetSupport available
        binderImage := by
  exact HasType.ReflectiveSupportSafeAt.rec
    (motive_1 := fun {bound pattern type} _ available currentImage _ =>
      exists renamedTyped : HasType language targetFree bound
          (Pattern.renameFVars mapping.name pattern) type,
        renamedTyped.ReflectiveSupportSafeAt profile targetSupport available
          currentImage)
    (motive_2 := fun {bound arguments parameters} _ available
        currentImage _ =>
      exists renamedTyped : ArgumentsHaveTypes language targetFree bound
          (arguments.map (Pattern.renameFVars mapping.name)) parameters,
        renamedTyped.ReflectiveSupportSafeAt profile targetSupport available
          currentImage)
    (motive_3 := fun {bound elements elementType} _ available
        currentImage _ =>
      exists renamedTyped : ElementsHaveType language targetFree bound
          (elements.map (Pattern.renameFVars mapping.name)) elementType,
        renamedTyped.ReflectiveSupportSafeAt profile targetSupport available
          currentImage)
    (by
      intro bound index type lookup available currentImage
      let renamedTyped := HasType.bvar
        (language := language) (free := targetFree) lookup
      simpa [Pattern.renameFVars] using
        (⟨renamedTyped,
          HasType.ReflectiveSupportSafeAt.bvar lookup available⟩))
    (by
      intro bound name type lookup available currentImage shape
      have renamedLookup := mapping.mapsLookup lookup
      obtain ⟨inner, availableShape⟩ := shape
      let renamedTyped := HasType.fvar
        (language := language) (bound := bound) renamedLookup
      have renamedSafe : renamedTyped.ReflectiveSupportSafeAt
          profile targetSupport available currentImage := by
        refine .fvar renamedLookup available ⟨inner, ?_⟩
        simpa [mapping.mapsSupport lookup] using availableShape
      simpa [Pattern.renameFVars] using ⟨renamedTyped, renamedSafe⟩)
    (by
      intro bound rule arguments membership notBare argumentsTyped available
        currentImage quoted argumentsSafe argumentsIH
      obtain ⟨renamedArguments, renamedSafe⟩ := argumentsIH
      let renamedTyped := HasType.constructor membership notBare
        renamedArguments
      simpa [Pattern.renameFVars] using
        (⟨renamedTyped,
          HasType.ReflectiveSupportSafeAt.constructorQuote
            (membership := membership) (notBare := notBare) quoted
            renamedSafe⟩))
    (by
      intro bound rule arguments membership notBare argumentsTyped available
        currentImage ordinary argumentsSafe argumentsIH
      obtain ⟨renamedArguments, renamedSafe⟩ := argumentsIH
      let renamedTyped := HasType.constructor membership notBare
        renamedArguments
      simpa [Pattern.renameFVars] using
        (⟨renamedTyped,
          HasType.ReflectiveSupportSafeAt.constructorOrdinary
            (membership := membership) (notBare := notBare) ordinary
            renamedSafe⟩))
    (by
      intro bound binder body domain codomain bodyTyped available currentImage
        bodySafe bodyIH
      obtain ⟨renamedBody, renamedSafe⟩ := bodyIH
      let renamedTyped := HasType.lambda (binder := binder) renamedBody
      simpa [Pattern.renameFVars] using
        (⟨renamedTyped,
          HasType.ReflectiveSupportSafeAt.lambda renamedSafe⟩))
    (by
      intro bound arity binders body domain codomain bodyTyped available
        currentImage bodySafe bodyIH
      obtain ⟨renamedBody, renamedSafe⟩ := bodyIH
      let renamedTyped := HasType.multiLambda
        (binders := binders) renamedBody
      simpa [Pattern.renameFVars] using
        (⟨renamedTyped,
          HasType.ReflectiveSupportSafeAt.multiLambda renamedSafe⟩))
    (by
      intro bound body replacement domain codomain bodyTyped replacementTyped
        available currentImage bodySafe replacementSafe bodyIH replacementIH
      obtain ⟨renamedBody, renamedBodySafe⟩ := bodyIH
      obtain ⟨renamedReplacement, renamedReplacementSafe⟩ := replacementIH
      let renamedTyped := HasType.subst renamedBody renamedReplacement
      simpa [Pattern.renameFVars] using
        (⟨renamedTyped,
          HasType.ReflectiveSupportSafeAt.subst renamedBodySafe
            renamedReplacementSafe⟩))
    (by
      intro bound collectionType elements rest elementType elementsTyped
        available currentImage elementsSafe elementsIH
      obtain ⟨renamedElements, renamedSafe⟩ := elementsIH
      let renamedTyped := HasType.collection
        (collectionType := collectionType) (rest := rest) renamedElements
      simpa [Pattern.renameFVars] using
        (⟨renamedTyped,
          HasType.ReflectiveSupportSafeAt.collection renamedSafe⟩))
    (by
      intro bound rule parameterName collectionType elements rest elementType
        membership parameterShape elementsTyped available currentImage
        elementsSafe elementsIH
      obtain ⟨renamedElements, renamedSafe⟩ := elementsIH
      let renamedTyped := HasType.collectionConstructor
        (rest := rest) membership parameterShape renamedElements
      simpa [Pattern.renameFVars] using
        (⟨renamedTyped,
          HasType.ReflectiveSupportSafeAt.collectionConstructor
            (parameterName := parameterName) (membership := membership)
            (parameterShape := parameterShape) renamedSafe⟩))
    (by
      intro bound available currentImage
      let renamedTyped := ArgumentsHaveTypes.nil
        (language := language) (free := targetFree) (bound := bound)
      exact ⟨renamedTyped, .nil bound available⟩)
    (by
      intro bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped available
        currentImage argumentSafe argumentsSafe argumentIH argumentsIH
      obtain ⟨renamedArgument, renamedArgumentSafe⟩ := argumentIH
      obtain ⟨renamedArguments, renamedArgumentsSafe⟩ := argumentsIH
      have renamedRepresentation :=
        representation.renameFVars mapping.name
      let renamedTyped := ArgumentsHaveTypes.cons renamedRepresentation
        parameterType renamedArgument renamedArguments
      refine ⟨renamedTyped, ?_⟩
      exact ArgumentsHaveTypes.ReflectiveSupportSafeAt.cons
        (representation := renamedRepresentation)
        (parameterType := parameterType) renamedArgumentSafe
        renamedArgumentsSafe)
    (by
      intro bound elementType available currentImage
      let renamedTyped := ElementsHaveType.nil
        (language := language) (free := targetFree) bound elementType
      exact ⟨renamedTyped, .nil bound elementType available⟩)
    (by
      intro bound element elements elementType elementTyped elementsTyped
        available currentImage elementSafe elementsSafe elementIH elementsIH
      obtain ⟨renamedElement, renamedElementSafe⟩ := elementIH
      obtain ⟨renamedElements, renamedElementsSafe⟩ := elementsIH
      let renamedTyped := ElementsHaveType.cons renamedElement renamedElements
      exact ⟨renamedTyped,
        ElementsHaveType.ReflectiveSupportSafeAt.cons renamedElementSafe
          renamedElementsSafe⟩)
    safe

end WellSorted

/-- Ordinary free-variable renaming preserves the raw constructor fragment
exactly. -/
theorem ConstructorsWithin.renameFVars
    {allowed : String -> Prop} {pattern : Pattern}
    (rename : String -> String)
    (supported : ConstructorsWithin allowed pattern) :
    ConstructorsWithin allowed (Pattern.renameFVars rename pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [Pattern.renameFVars]
  | hfvar name => simp [Pattern.renameFVars]
  | happly constructor arguments inductionHypothesis =>
      simp only [Pattern.renameFVars, constructorsWithin_apply]
      exact ⟨supported.1, supported.2.map fun argument membership =>
        inductionHypothesis argument membership
          (supported.2.of_mem membership)⟩
  | hlambda binder body inductionHypothesis =>
      simpa only [Pattern.renameFVars, constructorsWithin_lambda] using
        inductionHypothesis supported
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa only [Pattern.renameFVars, constructorsWithin_multiLambda] using
        inductionHypothesis supported
  | hsubst body replacement bodyInduction replacementInduction =>
      simpa only [Pattern.renameFVars, constructorsWithin_subst] using
        And.intro (bodyInduction supported.1)
          (replacementInduction supported.2)
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [Pattern.renameFVars, constructorsWithin_collection]
      exact supported.map fun element membership =>
        inductionHypothesis element membership (supported.of_mem membership)

namespace Pattern

@[simp]
theorem hasCanonicalBinderMetadata_renameFVars
    (rename : String -> String) (pattern : Pattern) :
    (renameFVars rename pattern).hasCanonicalBinderMetadata =
      pattern.hasCanonicalBinderMetadata := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [renameFVars, Pattern.hasCanonicalBinderMetadata]
  | hfvar name => simp [renameFVars, Pattern.hasCanonicalBinderMetadata]
  | happly constructor arguments inductionHypothesis =>
      simp only [renameFVars, Pattern.hasCanonicalBinderMetadata]
      induction arguments with
      | nil => rfl
      | cons argument arguments listInduction =>
          simp only [List.map_cons, Pattern.hasCanonicalBinderMetadataList]
          rw [inductionHypothesis argument (by simp)]
          exact congrArg (Pattern.hasCanonicalBinderMetadata argument && ·)
            (listInduction fun other membership =>
              inductionHypothesis other (by simp [membership]))
  | hlambda binder body inductionHypothesis =>
      simp [renameFVars, Pattern.hasCanonicalBinderMetadata,
        inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [renameFVars, Pattern.hasCanonicalBinderMetadata,
        inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [renameFVars, Pattern.hasCanonicalBinderMetadata, bodyInduction,
        replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [renameFVars, Pattern.hasCanonicalBinderMetadata]
      induction elements with
      | nil => rfl
      | cons element elements listInduction =>
          simp only [List.map_cons, Pattern.hasCanonicalBinderMetadataList]
          rw [inductionHypothesis element (by simp)]
          exact congrArg (Pattern.hasCanonicalBinderMetadata element && ·)
            (listInduction fun other membership =>
              inductionHypothesis other (by simp [membership]))

end Pattern

namespace WellSorted

@[simp]
theorem isObjectPattern_renameFVars
    (rename : String -> String) (pattern : Pattern) :
    isObjectPattern (Pattern.renameFVars rename pattern) =
      isObjectPattern pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [Pattern.renameFVars, isObjectPattern]
  | hfvar name => simp [Pattern.renameFVars, isObjectPattern]
  | happly constructor arguments inductionHypothesis =>
      simp only [Pattern.renameFVars, isObjectPattern]
      induction arguments with
      | nil => rfl
      | cons argument arguments listInduction =>
          simp only [List.map_cons, isObjectPatternList]
          rw [inductionHypothesis argument (by simp)]
          exact congrArg (isObjectPattern argument && ·)
            (listInduction fun other membership =>
              inductionHypothesis other (by simp [membership]))
  | hlambda binder body inductionHypothesis =>
      simpa [Pattern.renameFVars, isObjectPattern] using inductionHypothesis
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa [Pattern.renameFVars, isObjectPattern] using inductionHypothesis
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [Pattern.renameFVars, isObjectPattern]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [Pattern.renameFVars, isObjectPattern]
      apply congrArg (rest.isNone && ·)
      induction elements with
      | nil => rfl
      | cons element elements listInduction =>
          simp only [List.map_cons, isObjectPatternList]
          rw [inductionHypothesis element (by simp)]
          exact congrArg (isObjectPattern element && ·)
            (listInduction fun other membership =>
              inductionHypothesis other (by simp [membership]))

end WellSorted

@[simp]
theorem binderSafeAt_renameFVars
    (rename : String -> String) (quoteConstructor : String)
    (depth : Nat) (pattern : Pattern) :
    binderSafeAt quoteConstructor depth (Pattern.renameFVars rename pattern) =
      binderSafeAt quoteConstructor depth pattern := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index => simp [Pattern.renameFVars, binderSafeAt]
  | hfvar name => simp [Pattern.renameFVars, binderSafeAt]
  | happly constructor arguments inductionHypothesis =>
      have listEquality : forall localDepth,
          binderSafeListAt quoteConstructor localDepth
              (arguments.map (Pattern.renameFVars rename)) =
            binderSafeListAt quoteConstructor localDepth arguments := by
        intro localDepth
        induction arguments with
        | nil => rfl
        | cons argument arguments listInduction =>
            simp only [List.map_cons, binderSafeListAt]
            rw [inductionHypothesis argument (by simp)]
            exact congrArg (binderSafeAt quoteConstructor localDepth argument && ·)
              (listInduction fun other membership otherDepth =>
                inductionHypothesis other (by simp [membership]) otherDepth)
      cases arguments with
      | nil => simp [Pattern.renameFVars, binderSafeAt]
      | cons argument arguments =>
          cases arguments with
          | nil =>
              simp only [Pattern.renameFVars, List.map_cons, List.map_nil,
                binderSafeAt]
              split
              · exact inductionHypothesis argument (by simp) 0
              · exact listEquality depth
          | cons second arguments =>
              simpa [Pattern.renameFVars, binderSafeAt] using listEquality depth
  | hlambda binder body inductionHypothesis =>
      simpa [Pattern.renameFVars, binderSafeAt] using
        inductionHypothesis (depth + 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa [Pattern.renameFVars, binderSafeAt] using
        inductionHypothesis (depth + arity)
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [Pattern.renameFVars, binderSafeAt, bodyInduction,
        replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [Pattern.renameFVars, binderSafeAt]
      induction elements with
      | nil => rfl
      | cons element elements listInduction =>
          simp only [List.map_cons, binderSafeListAt]
          rw [inductionHypothesis element (by simp)]
          exact congrArg (binderSafeAt quoteConstructor depth element && ·)
            (listInduction fun other membership otherDepth =>
              inductionHypothesis other (by simp [membership]) otherDepth)

namespace WellSorted

@[simp]
theorem reflectiveScopeSafeAt_renameFVars
    (profile : ReflectionProfile) (rename : String -> String)
    (depth : Nat) (pattern : Pattern) :
    ReflectiveWellSorted.ReflectiveScopeSafeAt profile depth
        (Pattern.renameFVars rename pattern) <->
      ReflectiveWellSorted.ReflectiveScopeSafeAt profile depth pattern := by
  constructor <;> intro safe presentation membership
  · simpa only [binderSafeAt_renameFVars] using safe presentation membership
  · simpa only [binderSafeAt_renameFVars] using safe presentation membership

end WellSorted

end Mettapedia.GSLT.LanguageDef
