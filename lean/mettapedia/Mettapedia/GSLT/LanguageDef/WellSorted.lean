import Mathlib.Data.List.Nodup
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.MeTTaIL.ScopedPattern

/-!
# Terms sorted by an authored language definition

The shared `Pattern` datatype is intentionally larger than the term language
of any one presentation.  This module derives the admissible, sort-indexed
fragment from the constructor signatures of an exact `LanguageDef`.

Binder and collection nodes remain representation forms rather than becoming
independent constructors.  A binder is accepted only where an authored
parameter has binder shape; a bare collection denotes a carrier term only
where an authored single-collection constructor gives it that result sort.
Closed semantic terms additionally exclude schema metavariables.  Quotation
boundaries belong to the separate reflection extension and are therefore not
part of this core carrier.
-/

namespace Mettapedia.GSLT.LanguageDef.WellSorted

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern

/-- Type assignment for free pattern variables in an authored schema. -/
abbrev FreeTypeContext := String → Option TypeExpr

/-- The empty free-variable assignment used by closed terms. -/
def FreeTypeContext.empty : FreeTypeContext := fun _ => none

/-- Restrict a free-variable typing context to one finite list of names.
This retains the original types and removes every unrelated ambient entry. -/
def FreeTypeContext.restrictTo (context : FreeTypeContext)
    (names : List String) : FreeTypeContext :=
  fun name => if name ∈ names then context name else none

@[simp]
theorem FreeTypeContext.restrictTo_apply_of_mem
    (context : FreeTypeContext) (names : List String) (name : String)
    (membership : name ∈ names) :
    context.restrictTo names name = context name := by
  simp [FreeTypeContext.restrictTo, membership]

theorem FreeTypeContext.mem_of_restrictTo_eq_some
    {context : FreeTypeContext} {names : List String} {name : String}
    {type : TypeExpr}
    (lookup : context.restrictTo names name = some type) :
    name ∈ names := by
  by_contra absent
  simp [FreeTypeContext.restrictTo, absent] at lookup

/-- Apply a presentation's sort action to a free-variable assignment. -/
def FreeTypeContext.map (symbols : PresentationSymbols)
    (context : FreeTypeContext) : FreeTypeContext :=
  fun name => (context name).map (mapTypeExpr symbols)

@[simp]
theorem FreeTypeContext.map_empty (symbols : PresentationSymbols) :
    FreeTypeContext.empty.map symbols = FreeTypeContext.empty := by
  funext name
  rfl

@[simp]
theorem FreeTypeContext.map_id (context : FreeTypeContext) :
    context.map PresentationSymbols.id = context := by
  funext name
  cases value : context name <;>
    simp [FreeTypeContext.map, value]

theorem FreeTypeContext.map_comp (context : FreeTypeContext)
    (first second : PresentationSymbols) :
    context.map (first.comp second) =
      (context.map first).map second := by
  funext name
  cases value : context name <;>
    simp [FreeTypeContext.map, value]

/-- The semantic type expected for one constructor argument.

Single-binder declarations historically admit both an explicit arrow and the
same-sort shorthand used by the LF/HOL language definitions.  Multiple
binders use the corresponding `multiBinder` domain.  Ill-shaped binder
annotations have no induced argument type. -/
def parameterType? : TermParam → Option TypeExpr
  | .simple _ type => some type
  | .abstractionNamed _ _ (.arrow domain codomain) =>
      some (.arrow domain codomain)
  | .abstractionNamed _ _ (.base sort) =>
      some (.arrow (.base sort) (.base sort))
  | .abstractionNamed _ _ _ => none
  | .multiAbstractionNamed _ _ (.arrow (.multiBinder domain) codomain) =>
      some (.arrow (.multiBinder domain) codomain)
  | .multiAbstractionNamed _ _ (.base sort) =>
      some (.arrow (.multiBinder (.base sort)) (.base sort))
  | .multiAbstractionNamed _ _ _ => none

/-- The representation form required by an authored constructor parameter.

Simple parameters accept an ordinary term.  Abstraction parameters require
the corresponding locally nameless binder node; an arbitrary term merely
having an arrow type is not a representation of a binding argument.  Display
names from the declaration are deliberately absent from semantic patterns. -/
def MatchesParameterRepresentation : TermParam → Pattern → Prop
  | .simple _ _, _ => True
  | .abstractionNamed _ _ _, .lambda none _ => True
  | .multiAbstractionNamed _ _ _, .multiLambda _ [] _ => True
  | _, _ => False

/-- Invert the representation certificate for a single abstraction
parameter.  The binder display name is declaration metadata; the semantic
argument uses the unnamed locally nameless binder node. -/
theorem matchesParameterRepresentation_abstractionNamed_iff
    (binderName : Option String) (bodyName : String) (type : TypeExpr)
    (pattern : Pattern) :
    MatchesParameterRepresentation
        (.abstractionNamed binderName bodyName type) pattern ↔
      ∃ body, pattern = .lambda none body := by
  cases pattern <;> simp [MatchesParameterRepresentation]
  case lambda binder body =>
    cases binder <;> simp

/-- Invert the representation certificate for a multiple-abstraction
parameter. -/
theorem matchesParameterRepresentation_multiAbstractionNamed_iff
    (binderNames : List String) (bodyName : String) (type : TypeExpr)
    (pattern : Pattern) :
    MatchesParameterRepresentation
        (.multiAbstractionNamed binderNames bodyName type) pattern ↔
      ∃ arity body, pattern = .multiLambda arity [] body := by
  cases pattern <;> simp [MatchesParameterRepresentation]
  case multiLambda arity binders body =>
    cases binders <;> simp

/-- A grammar rule whose concrete representation is the bare collection node
rather than an application of its label.  This is the representation choice
already used by the generic context compiler. -/
def UsesBareCollection (rule : GrammarRule) : Prop :=
  ∃ parameterName collectionType elementType,
    rule.params =
      [.simple parameterName (.collection collectionType elementType)]

theorem usesBareCollection_mapGrammarRule_iff
    (symbols : PresentationSymbols) (rule : GrammarRule) :
    UsesBareCollection (mapGrammarRule symbols rule) ↔
      UsesBareCollection rule := by
  constructor
  · rintro ⟨parameterName, collectionType, elementType, mappedShape⟩
    cases rule with
    | mk label category parameters syntaxPattern evalPolicy =>
      simp only [mapGrammarRule] at mappedShape
      cases parameters with
      | nil => simp at mappedShape
      | cons parameter parameters =>
          cases parameters with
          | nil =>
              cases parameter with
              | simple originalName originalType =>
                  cases originalType <;>
                    simp_all [mapTermParam, mapTypeExpr, UsesBareCollection]
              | abstractionNamed binder body type =>
                  simp [mapTermParam] at mappedShape
              | multiAbstractionNamed binders body type =>
                  simp [mapTermParam] at mappedShape
          | cons next rest => simp at mappedShape
  · rintro ⟨parameterName, collectionType, elementType, shape⟩
    refine ⟨parameterName, collectionType,
      mapTypeExpr symbols elementType, ?_⟩
    simp [mapGrammarRule, shape, mapTermParam, mapTypeExpr]

mutual
  /-- A raw pattern has a type expression by the constructor declarations of
  `language`, in the supplied free- and bound-variable contexts. -/
  inductive HasType (language : LanguageDef) (free : FreeTypeContext) :
      List TypeExpr → Pattern → TypeExpr → Prop where
    | bvar {bound : List TypeExpr} {index : Nat} {type : TypeExpr} :
        bound[index]? = some type →
        HasType language free bound (.bvar index) type
    | fvar {bound : List TypeExpr} {name : String} {type : TypeExpr} :
        free name = some type →
        HasType language free bound (.fvar name) type
    | constructor
        {bound : List TypeExpr} {rule : GrammarRule} {arguments : List Pattern} :
        rule ∈ language.terms →
        ¬ UsesBareCollection rule →
        ArgumentsHaveTypes language free bound arguments rule.params →
        HasType language free bound (.apply rule.label arguments)
          (.base rule.category)
    | lambda
        {bound : List TypeExpr} {binder : Option String} {body : Pattern}
        {domain codomain : TypeExpr} :
        HasType language free (domain :: bound) body codomain →
        HasType language free bound (.lambda binder body)
          (.arrow domain codomain)
    | multiLambda
        {bound : List TypeExpr} {arity : Nat} {binders : List String}
        {body : Pattern} {domain codomain : TypeExpr} :
        HasType language free (List.replicate arity domain ++ bound) body codomain →
        HasType language free bound (.multiLambda arity binders body)
          (.arrow (.multiBinder domain) codomain)
    | subst
        {bound : List TypeExpr} {body replacement : Pattern}
        {domain codomain : TypeExpr} :
        HasType language free (domain :: bound) body codomain →
        HasType language free bound replacement domain →
        HasType language free bound (.subst body replacement) codomain
    | collection
        {bound : List TypeExpr} {collectionType : CollType}
        {elements : List Pattern} {rest : Option String} {elementType : TypeExpr} :
        ElementsHaveType language free bound elements elementType →
        HasType language free bound
          (.collection collectionType elements rest)
          (.collection collectionType elementType)
    | collectionConstructor
        {bound : List TypeExpr} {rule : GrammarRule} {parameterName : String}
        {collectionType : CollType} {elements : List Pattern}
        {rest : Option String} {elementType : TypeExpr} :
        rule ∈ language.terms →
        rule.params =
          [.simple parameterName (.collection collectionType elementType)] →
        ElementsHaveType language free bound elements elementType →
        HasType language free bound
          (.collection collectionType elements rest) (.base rule.category)

  /-- Constructor arguments match the authored parameter list in order. -/
  inductive ArgumentsHaveTypes (language : LanguageDef)
      (free : FreeTypeContext) :
      List TypeExpr → List Pattern → List TermParam → Prop where
    | nil {bound : List TypeExpr} :
        ArgumentsHaveTypes language free bound [] []
    | cons
        {argument : Pattern} {arguments : List Pattern}
        {parameter : TermParam} {parameters : List TermParam}
        {expected : TypeExpr} :
        MatchesParameterRepresentation parameter argument →
        parameterType? parameter = some expected →
        HasType language free bound argument expected →
        ArgumentsHaveTypes language free bound arguments parameters →
        ArgumentsHaveTypes language free bound
          (argument :: arguments) (parameter :: parameters)

  /-- Pointwise typing for the contents of a collection value. -/
  inductive ElementsHaveType (language : LanguageDef)
      (free : FreeTypeContext) :
      List TypeExpr → List Pattern → TypeExpr → Prop where
    | nil (bound : List TypeExpr) (elementType : TypeExpr) :
        ElementsHaveType language free bound [] elementType
    | cons
        {element : Pattern} {elements : List Pattern} {elementType : TypeExpr} :
        HasType language free bound element elementType →
        ElementsHaveType language free bound elements elementType →
        ElementsHaveType language free bound (element :: elements) elementType
end

/-- Constructor-argument typing preserves the exact authored arity. -/
theorem ArgumentsHaveTypes.length_eq
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {arguments : List Pattern}
    {parameters : List TermParam}
    (typed : ArgumentsHaveTypes language free bound arguments parameters) :
    arguments.length = parameters.length := by
  induction arguments generalizing parameters with
  | nil =>
      cases typed
      rfl
  | cons argument arguments inductionHypothesis =>
      cases typed with
      | cons representation parameterType argumentTyped argumentsTyped =>
          simp [inductionHypothesis argumentsTyped]

/-- Base-sort specialization of the generic type-expression judgment. -/
abbrev HasSort (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (pattern : Pattern) (sort : String) : Prop :=
  HasType language free bound pattern (.base sort)

/-- Ordinary locally nameless scope at an ambient binder depth. -/
def ScopeSafeAt (depth : Nat) (pattern : Pattern) : Prop :=
  pattern.isWellScopedAt depth = true

/-- Top-level locally nameless scope.  The language parameter records the
carrier being checked; the law itself is representation-generic. -/
def ScopeSafe (_language : LanguageDef) (pattern : Pattern) : Prop :=
  ScopeSafeAt 0 pattern

mutual
  /-- Object-language terms contain neither a pending explicit-substitution
  node nor an open collection tail.  Both forms occur in authored schemas and
  are eliminated while a rule is instantiated; neither is a constructor of
  the presented term algebra. -/
  def isObjectPattern : Pattern → Bool
    | .bvar _ | .fvar _ => true
    | .apply _ arguments => isObjectPatternList arguments
    | .lambda _ body => isObjectPattern body
    | .multiLambda _ _ body => isObjectPattern body
    | .subst _ _ => false
    | .collection _ elements rest =>
        rest.isNone && isObjectPatternList elements

  def isObjectPatternList : List Pattern → Bool
    | [] => true
    | pattern :: patterns =>
        isObjectPattern pattern && isObjectPatternList patterns
end

/-- An open object-language pattern at an arbitrary type expression.  Unlike
the raw schema carrier, it excludes pending substitutions and open collection
tails, uses canonical locally nameless binder metadata, and is locally scoped
at the ambient binder depth. -/
def OpenPatternWellSorted (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (type : TypeExpr) (pattern : Pattern) : Prop :=
  HasType language free bound pattern type ∧
    pattern.hasCanonicalBinderMetadata = true ∧
    isObjectPattern pattern = true ∧
    ScopeSafeAt bound.length pattern

/-- The arbitrary-type open object carrier.  `OpenTerm` below is exactly its
base-sort specialization. -/
abbrev OpenPattern (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (type : TypeExpr) :=
  { pattern : Pattern // OpenPatternWellSorted language free bound type pattern }

/-- An open object-language term at one authored carrier sort. -/
def OpenTermWellSorted (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (sort : LangSort language)
    (pattern : Pattern) : Prop :=
  OpenPatternWellSorted language free bound (.base sort.1) pattern

/-- The open, declaration-derived object-language carrier at one authored
sort and exact pair of free and bound typing contexts. -/
abbrev OpenTerm (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (sort : LangSort language) :=
  { pattern : Pattern // OpenTermWellSorted language free bound sort pattern }

/-- Transport an open term between propositionally equal typing fibers of
the same authored language.  The raw object pattern is unchanged; only its
proof-relevant context and sort indices move. -/
def OpenTerm.reindex {language : LanguageDef}
    {sourceFree targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {sourceSort targetSort : LangSort language}
    (freeEquality : sourceFree = targetFree)
    (boundEquality : sourceBound = targetBound)
    (sortEquality : sourceSort = targetSort)
    (term : OpenTerm language sourceFree sourceBound sourceSort) :
    OpenTerm language targetFree targetBound targetSort := by
  cases freeEquality
  cases boundEquality
  cases sortEquality
  exact term

@[simp]
theorem OpenTerm.reindex_pattern {language : LanguageDef}
    {sourceFree targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {sourceSort targetSort : LangSort language}
    (freeEquality : sourceFree = targetFree)
    (boundEquality : sourceBound = targetBound)
    (sortEquality : sourceSort = targetSort)
    (term : OpenTerm language sourceFree sourceBound sourceSort) :
    (term.reindex freeEquality boundEquality sortEquality).1 = term.1 := by
  cases freeEquality
  cases boundEquality
  cases sortEquality
  rfl

/-! ## Free-variable support of open object terms -/

mutual
  /-- Change the ambient free context while preserving every lookup actually
  used by one typing derivation.  Unused entries of the source context impose
  no obligation on the target context. -/
  theorem HasType.recontextualizeFree
      {language : LanguageDef} {source target : FreeTypeContext}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType language source bound pattern type)
      (preserves : ∀ {name freeType},
        name ∈ pattern.freeFvarNames →
        source name = some freeType → target name = some freeType) :
      HasType language target bound pattern type := by
    cases typed with
    | @bvar bound index type lookup => exact HasType.bvar lookup
    | @fvar bound name type lookup =>
        exact HasType.fvar (preserves (by simp [Pattern.freeFvarNames]) lookup)
    | @constructor bound rule arguments membership notBare argumentsTyped =>
        exact HasType.constructor membership notBare
          (argumentsTyped.recontextualizeFree fun nameMembership lookup =>
            preserves (by simpa [Pattern.freeFvarNames] using nameMembership)
              lookup)
    | @lambda bound binder body domain codomain bodyTyped =>
        exact HasType.lambda (binder := binder)
          (bodyTyped.recontextualizeFree fun nameMembership lookup =>
            preserves (by simpa [Pattern.freeFvarNames] using nameMembership)
              lookup)
    | @multiLambda bound arity binders body domain codomain bodyTyped =>
        exact HasType.multiLambda (binders := binders)
          (bodyTyped.recontextualizeFree fun nameMembership lookup =>
            preserves (by simpa [Pattern.freeFvarNames] using nameMembership)
              lookup)
    | @subst bound body replacement domain codomain bodyTyped replacementTyped =>
        exact HasType.subst
          (bodyTyped.recontextualizeFree fun nameMembership lookup =>
            preserves (by
              simp [Pattern.freeFvarNames, nameMembership]) lookup)
          (replacementTyped.recontextualizeFree fun nameMembership lookup =>
            preserves (by
              simp [Pattern.freeFvarNames, nameMembership]) lookup)
    | @collection bound collectionType elements rest elementType elementsTyped =>
        exact HasType.collection (rest := rest)
          (elementsTyped.recontextualizeFree fun nameMembership lookup =>
            preserves (by
              simp [Pattern.freeFvarNames, nameMembership]) lookup)
    | @collectionConstructor bound rule parameterName collectionType elements rest
        elementType membership parameterShape elementsTyped =>
        exact HasType.collectionConstructor membership parameterShape
          (elementsTyped.recontextualizeFree fun nameMembership lookup =>
            preserves (by
              simp [Pattern.freeFvarNames, nameMembership]) lookup)

  /-- Argument-list companion to used-lookup recontextualization. -/
  theorem ArgumentsHaveTypes.recontextualizeFree
      {language : LanguageDef} {source target : FreeTypeContext}
      {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language source bound arguments parameters)
      (preserves : ∀ {name freeType},
        name ∈ arguments.flatMap Pattern.freeFvarNames →
        source name = some freeType → target name = some freeType) :
      ArgumentsHaveTypes language target bound arguments parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation parameterType argumentTyped argumentsTyped =>
        exact .cons representation parameterType
          (argumentTyped.recontextualizeFree fun nameMembership lookup =>
            preserves (by
              simp [nameMembership]) lookup)
          (argumentsTyped.recontextualizeFree fun nameMembership lookup =>
            preserves (by
              simp [nameMembership]) lookup)

  /-- Collection-element companion to used-lookup recontextualization. -/
  theorem ElementsHaveType.recontextualizeFree
      {language : LanguageDef} {source target : FreeTypeContext}
      {bound : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (typed : ElementsHaveType language source bound elements elementType)
      (preserves : ∀ {name freeType},
        name ∈ elements.flatMap Pattern.freeFvarNames →
        source name = some freeType → target name = some freeType) :
      ElementsHaveType language target bound elements elementType := by
    cases typed with
    | nil => exact .nil _ _
    | cons elementTyped elementsTyped =>
        exact .cons
          (elementTyped.recontextualizeFree fun nameMembership lookup =>
            preserves (by
              simp [nameMembership]) lookup)
          (elementsTyped.recontextualizeFree fun nameMembership lookup =>
            preserves (by
              simp [nameMembership]) lookup)

  /-- Every free-variable occurrence in a sorted object pattern is backed by
  the exact free typing context indexing that pattern.  The object boundary
  is load-bearing: raw schema collection tails are names but are not term
  occurrences in the typing derivation. -/
  theorem HasType.freeType_of_mem_freeFvarNames_of_isObjectPattern
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType language free bound pattern type)
      (object : isObjectPattern pattern = true)
      {name : String} (membership : name ∈ pattern.freeFvarNames) :
      ∃ freeType, free name = some freeType := by
    cases typed with
    | @bvar bound index type lookup =>
        simp [Pattern.freeFvarNames] at membership
    | @fvar bound variableName type lookup =>
        simp only [Pattern.freeFvarNames, List.mem_singleton] at membership
        subst name
        exact ⟨type, lookup⟩
    | @constructor bound rule arguments ruleMembership notBare argumentsTyped =>
        exact ArgumentsHaveTypes.freeType_of_mem_freeFvarNames_of_isObjectPatternList
          argumentsTyped (by simpa [isObjectPattern] using object)
          (by simpa [Pattern.freeFvarNames] using membership)
    | @lambda bound binder body domain codomain bodyTyped =>
        exact bodyTyped.freeType_of_mem_freeFvarNames_of_isObjectPattern
          (by simpa [isObjectPattern] using object)
          (by simpa [Pattern.freeFvarNames] using membership)
    | @multiLambda bound arity binders body domain codomain bodyTyped =>
        exact bodyTyped.freeType_of_mem_freeFvarNames_of_isObjectPattern
          (by simpa [isObjectPattern] using object)
          (by simpa [Pattern.freeFvarNames] using membership)
    | @subst bound body replacement domain codomain bodyTyped replacementTyped =>
        simp [isObjectPattern] at object
    | @collection bound collectionType elements rest elementType elementsTyped =>
        have restClosed : rest = none := by
          cases rest <;> simp [isObjectPattern] at object ⊢
        subst rest
        exact ElementsHaveType.freeType_of_mem_freeFvarNames_of_isObjectPatternList
          elementsTyped (by simpa [isObjectPattern] using object)
          (by simpa [Pattern.freeFvarNames] using membership)
    | @collectionConstructor bound rule parameterName collectionType elements rest
        elementType ruleMembership parameterShape elementsTyped =>
        have restClosed : rest = none := by
          cases rest <;> simp [isObjectPattern] at object ⊢
        subst rest
        exact ElementsHaveType.freeType_of_mem_freeFvarNames_of_isObjectPatternList
          elementsTyped (by simpa [isObjectPattern] using object)
          (by simpa [Pattern.freeFvarNames] using membership)

  /-- Argument-list companion to free-variable support of object terms. -/
  theorem ArgumentsHaveTypes.freeType_of_mem_freeFvarNames_of_isObjectPatternList
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free bound arguments parameters)
      (objects : isObjectPatternList arguments = true)
      {name : String}
      (membership : name ∈ arguments.flatMap Pattern.freeFvarNames) :
      ∃ freeType, free name = some freeType := by
    cases typed with
    | nil => simp at membership
    | cons representation parameterType argumentTyped argumentsTyped =>
        simp only [isObjectPatternList, Bool.and_eq_true] at objects
        simp only [List.flatMap_cons, List.mem_append] at membership
        rcases membership with headMembership | tailMembership
        · exact argumentTyped.freeType_of_mem_freeFvarNames_of_isObjectPattern
            objects.1 headMembership
        · exact argumentsTyped.freeType_of_mem_freeFvarNames_of_isObjectPatternList
            objects.2 tailMembership

  /-- Collection-element companion to free-variable support of object
  terms. -/
  theorem ElementsHaveType.freeType_of_mem_freeFvarNames_of_isObjectPatternList
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (typed : ElementsHaveType language free bound elements elementType)
      (objects : isObjectPatternList elements = true)
      {name : String}
      (membership : name ∈ elements.flatMap Pattern.freeFvarNames) :
      ∃ freeType, free name = some freeType := by
    cases typed with
    | nil => simp at membership
    | cons elementTyped elementsTyped =>
        simp only [isObjectPatternList, Bool.and_eq_true] at objects
        simp only [List.flatMap_cons, List.mem_append] at membership
        rcases membership with headMembership | tailMembership
        · exact elementTyped.freeType_of_mem_freeFvarNames_of_isObjectPattern
            objects.1 headMembership
        · exact elementsTyped.freeType_of_mem_freeFvarNames_of_isObjectPatternList
            objects.2 tailMembership
end

/-- Reindex an open object term into another free context that agrees on
every free-variable lookup actually used by the term.  Unused context entries
carry no syntax or typing authority. -/
def OpenTerm.recontextualizeFree
    {language : LanguageDef} {source target : FreeTypeContext}
    {bound : List TypeExpr} {sort : LangSort language}
    (term : OpenTerm language source bound sort)
    (preserves : ∀ {name freeType},
      name ∈ term.1.freeFvarNames →
      source name = some freeType → target name = some freeType) :
    OpenTerm language target bound sort :=
  ⟨term.1, term.2.1.recontextualizeFree preserves,
    term.2.2.1, term.2.2.2.1, term.2.2.2.2⟩

@[simp]
theorem OpenTerm.recontextualizeFree_pattern
    {language : LanguageDef} {source target : FreeTypeContext}
    {bound : List TypeExpr} {sort : LangSort language}
    (term : OpenTerm language source bound sort)
    (preserves : ∀ {name freeType},
      name ∈ term.1.freeFvarNames →
      source name = some freeType → target name = some freeType) :
    (term.recontextualizeFree preserves).1 = term.1 :=
  rfl

/-- Every open object term can be reindexed by the finite restriction of its
ambient free context to the names it actually contains. -/
def OpenTerm.restrictFreeContext
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {sort : LangSort language}
    (term : OpenTerm language free bound sort) :
    OpenTerm language (free.restrictTo term.1.freeFvarNames) bound sort :=
  ⟨term.1,
    term.2.1.recontextualizeFree (fun membership lookup => by
      simpa [FreeTypeContext.restrictTo, membership] using lookup),
    term.2.2.1, term.2.2.2.1, term.2.2.2.2⟩

@[simp]
theorem OpenTerm.restrictFreeContext_pattern
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {sort : LangSort language}
    (term : OpenTerm language free bound sort) :
    term.restrictFreeContext.1 = term.1 :=
  rfl

/-- The support bound specialized to the declaration-derived open carrier. -/
theorem OpenTerm.freeType_of_mem_freeFvarNames
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {sort : LangSort language}
    (term : OpenTerm language free bound sort)
    {name : String} (membership : name ∈ term.1.freeFvarNames) :
    ∃ freeType, free name = some freeType :=
  term.2.1.freeType_of_mem_freeFvarNames_of_isObjectPattern
    term.2.2.2.1 membership

/-- An open object term typed in a finitely restricted context can mention
only names retained by that restriction. -/
theorem OpenTerm.mem_of_restrictTo_freeFvarNames
    {language : LanguageDef} {free : FreeTypeContext}
    {names : List String} {bound : List TypeExpr}
    {sort : LangSort language}
    (term : OpenTerm language (free.restrictTo names) bound sort)
    {name : String} (membership : name ∈ term.1.freeFvarNames) :
    name ∈ names := by
  obtain ⟨type, lookup⟩ := term.freeType_of_mem_freeFvarNames membership
  exact FreeTypeContext.mem_of_restrictTo_eq_some lookup

/-- Two free contexts that agree on every name used by one open object have
the same finite restriction to that object's support.  This is the precise
context equality behind naturality in unused ambient entries: no global
extensional equality of the original contexts is required. -/
theorem OpenTerm.restrictTo_freeFvarNames_eq_of_preserves
    {language : LanguageDef} {source target : FreeTypeContext}
    {bound : List TypeExpr} {sort : LangSort language}
    (term : OpenTerm language source bound sort)
    (preserves : ∀ {name freeType},
      name ∈ term.1.freeFvarNames →
      source name = some freeType → target name = some freeType) :
    source.restrictTo term.1.freeFvarNames =
      target.restrictTo term.1.freeFvarNames := by
  funext name
  by_cases membership : name ∈ term.1.freeFvarNames
  · obtain ⟨freeType, sourceLookup⟩ :=
      term.freeType_of_mem_freeFvarNames membership
    rw [FreeTypeContext.restrictTo_apply_of_mem source
      term.1.freeFvarNames name membership]
    rw [FreeTypeContext.restrictTo_apply_of_mem target
      term.1.freeFvarNames name membership]
    exact sourceLookup.trans (preserves membership sourceLookup).symm
  · simp [FreeTypeContext.restrictTo, membership]

/-- A semantic term at an authored sort: it is sorted from the exact grammar,
contains no schema metavariables or open collection tails, and respects the
ordinary locally nameless binder discipline. -/
def ClosedTermWellSorted (language : LanguageDef) (sort : LangSort language)
    (pattern : Pattern) : Prop :=
  HasSort language FreeTypeContext.empty [] pattern sort.1 ∧
    pattern.isGround = true ∧
    pattern.hasCanonicalBinderMetadata = true ∧
    isObjectPattern pattern = true ∧
    ScopeSafe language pattern

/-- The closed, declaration-derived carrier at one authored sort. -/
abbrev ClosedTerm (language : LanguageDef) (sort : LangSort language) :=
  { pattern : Pattern // ClosedTermWellSorted language sort pattern }

/-! ## Ordinary scope derived from sorting -/

mutual
  /-- A typing derivation bounds every de Bruijn index by its bound-variable
  context.  Ordinary locally nameless scope is therefore derived data of a
  sorted term rather than another admission predicate. -/
  theorem HasType.isWellScopedAt
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType language free bound pattern type) :
      pattern.isWellScopedAt bound.length = true := by
    cases typed with
    | @bvar bound index type lookup =>
        have inBounds := (List.getElem?_eq_some_iff.mp lookup).1
        simp [Pattern.isWellScopedAt, inBounds]
    | @fvar bound name type lookup =>
        simp [Pattern.isWellScopedAt]
    | @constructor bound rule arguments membership notBare argumentsTyped =>
        simpa [Pattern.isWellScopedAt] using argumentsTyped.isWellScopedListAt
    | @lambda bound binder body domain codomain bodyTyped =>
        simpa [Pattern.isWellScopedAt, Nat.add_comm] using
          bodyTyped.isWellScopedAt
    | @multiLambda bound arity binders body domain codomain bodyTyped =>
        simpa [Pattern.isWellScopedAt, List.length_append,
          List.length_replicate, Nat.add_comm] using bodyTyped.isWellScopedAt
    | @subst bound body replacement domain codomain bodyTyped replacementTyped =>
        simp only [Pattern.isWellScopedAt, Bool.and_eq_true]
        constructor
        · simpa [Nat.add_comm] using bodyTyped.isWellScopedAt
        · exact replacementTyped.isWellScopedAt
    | @collection bound collectionType elements rest elementType elementsTyped =>
        simpa [Pattern.isWellScopedAt] using elementsTyped.isWellScopedListAt
    | @collectionConstructor bound rule parameterName collectionType elements rest
        elementType membership parameterShape elementsTyped =>
        simpa [Pattern.isWellScopedAt] using elementsTyped.isWellScopedListAt

  theorem ArgumentsHaveTypes.isWellScopedListAt
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free bound arguments parameters) :
      Pattern.isWellScopedListAt bound.length arguments = true := by
    cases typed with
    | nil => rfl
    | cons representation parameterType argumentTyped argumentsTyped =>
        simp [Pattern.isWellScopedListAt, argumentTyped.isWellScopedAt,
          argumentsTyped.isWellScopedListAt]

  theorem ElementsHaveType.isWellScopedListAt
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (typed : ElementsHaveType language free bound elements elementType) :
      Pattern.isWellScopedListAt bound.length elements = true := by
    cases typed with
    | nil => rfl
    | cons elementTyped elementsTyped =>
        simp [Pattern.isWellScopedListAt, elementTyped.isWellScopedAt,
          elementsTyped.isWellScopedListAt]
end

/-- Forget an exact authored sort declaration to the established name-indexed
sort used by the generic constructor-category API.  The membership proof is
derived from the selected declaration; no sort name is re-authored. -/
def authoredSortToLangSort (presentation : ValidatedLanguageDef)
    (sort : StructuralMorphism.AuthoredSort presentation) :
    LangSort presentation.language := by
  refine ⟨sort.1.name, ?_⟩
  change sort.1.name ∈ presentation.language.types.map (·.name)
  exact List.mem_map.mpr ⟨sort.1, sort.2, rfl⟩

@[simp]
theorem authoredSortToLangSort_name (presentation : ValidatedLanguageDef)
    (sort : StructuralMorphism.AuthoredSort presentation) :
    (authoredSortToLangSort presentation sort).1 = sort.1.name :=
  rfl

/-! ## Groundness derived from sorting and scope -/

mutual
  /-- A term typed under the empty schema-variable context is ground at the
  current binder depth whenever it is an object pattern and locally scoped.

  This makes `isGround` a theorem about the declaration-derived carrier, not
  an independent admission policy that could drift from sorting. -/
  theorem HasType.empty_isGroundAt
      {language : LanguageDef} {bound : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      (typed : HasType language FreeTypeContext.empty bound pattern type)
      (object : isObjectPattern pattern = true)
      (wellScoped : pattern.isWellScopedAt bound.length = true) :
      pattern.isGroundAt bound.length = true := by
    cases typed with
    | @bvar bound index type lookup =>
        simp only [Pattern.isGroundAt, decide_eq_true_eq]
        exact (List.getElem?_eq_some_iff.mp lookup).1
    | @fvar bound name type lookup =>
        simp [FreeTypeContext.empty] at lookup
    | @constructor bound rule arguments membership notBare argumentsTyped =>
        simp only [isObjectPattern, Pattern.isWellScopedAt] at object wellScoped
        simp only [Pattern.isGroundAt]
        exact argumentsTyped.empty_isGroundListAt object wellScoped
    | @lambda bound binder body domain codomain bodyTyped =>
        simp only [isObjectPattern, Pattern.isWellScopedAt] at object wellScoped
        simp only [Pattern.isGroundAt]
        simpa using bodyTyped.empty_isGroundAt object wellScoped
    | @multiLambda bound arity binders body domain codomain bodyTyped =>
        simp only [isObjectPattern, Pattern.isWellScopedAt] at object wellScoped
        simp only [Pattern.isGroundAt]
        have bodyScoped :
            body.isWellScopedAt
                (List.replicate arity domain ++ bound).length = true := by
          simpa [List.length_append, List.length_replicate, Nat.add_comm] using
            wellScoped
        have bodyGround := bodyTyped.empty_isGroundAt object bodyScoped
        simpa [List.length_append, List.length_replicate, Nat.add_comm] using
          bodyGround
    | @subst bound body replacement domain codomain bodyTyped replacementTyped =>
        simp [isObjectPattern] at object
    | @collection bound collectionType elements rest elementType elementsTyped =>
        simp only [isObjectPattern, Bool.and_eq_true] at object
        obtain ⟨restClosed, elementsObject⟩ := object
        cases rest with
        | none =>
            simp only [Pattern.isWellScopedAt] at wellScoped
            simp only [Pattern.isGroundAt, Option.isNone_none, Bool.and_true]
            exact elementsTyped.empty_isGroundListAt elementsObject wellScoped
        | some restName => simp at restClosed
    | @collectionConstructor bound rule parameterName collectionType elements rest
        elementType membership parameterShape elementsTyped =>
        simp only [isObjectPattern, Bool.and_eq_true] at object
        obtain ⟨restClosed, elementsObject⟩ := object
        cases rest with
        | none =>
            simp only [Pattern.isWellScopedAt] at wellScoped
            simp only [Pattern.isGroundAt, Option.isNone_none, Bool.and_true]
            exact elementsTyped.empty_isGroundListAt elementsObject wellScoped
        | some restName => simp at restClosed

  /-- Ordered constructor arguments inherit the groundness theorem
  pointwise. -/
  theorem ArgumentsHaveTypes.empty_isGroundListAt
      {language : LanguageDef} {bound : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language FreeTypeContext.empty bound
        arguments parameters)
      (object : isObjectPatternList arguments = true)
      (wellScoped : Pattern.isWellScopedListAt bound.length arguments = true) :
      Pattern.isGroundListAt bound.length arguments = true := by
    cases typed with
    | nil => rfl
    | cons representation parameterType argumentTyped argumentsTyped =>
        simp only [isObjectPatternList, Bool.and_eq_true] at object
        simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at wellScoped
        simp only [Pattern.isGroundListAt, Bool.and_eq_true]
        exact ⟨argumentTyped.empty_isGroundAt object.1 wellScoped.1,
          argumentsTyped.empty_isGroundListAt object.2 wellScoped.2⟩

  /-- Collection elements inherit the groundness theorem pointwise. -/
  theorem ElementsHaveType.empty_isGroundListAt
      {language : LanguageDef} {bound : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      (typed : ElementsHaveType language FreeTypeContext.empty bound
        elements elementType)
      (object : isObjectPatternList elements = true)
      (wellScoped : Pattern.isWellScopedListAt bound.length elements = true) :
      Pattern.isGroundListAt bound.length elements = true := by
    cases typed with
    | nil => rfl
    | cons elementTyped elementsTyped =>
        simp only [isObjectPatternList, Bool.and_eq_true] at object
        simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at wellScoped
        simp only [Pattern.isGroundListAt, Bool.and_eq_true]
        exact ⟨elementTyped.empty_isGroundAt object.1 wellScoped.1,
          elementsTyped.empty_isGroundListAt object.2 wellScoped.2⟩
end

/-- At top level, groundness follows from declaration typing, object shape,
and ordinary locally nameless scope. -/
theorem ground_of_closed_sorting
    {language : LanguageDef} {sort : LangSort language} {pattern : Pattern}
    (typed : HasSort language FreeTypeContext.empty [] pattern sort.1)
    (object : isObjectPattern pattern = true)
    (safe : ScopeSafe language pattern) :
    pattern.isGround = true := by
  simpa [Pattern.isGround] using
    typed.empty_isGroundAt object safe

/-! ## Structural transport -/

/-- Structural presentation maps carry every name-indexed authored sort to
the correspondingly renamed target sort.  This is the action needed by open
sorted fibers; it is derived from declaration preservation rather than from
an independent sort map. -/
def mapLangSort {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sort : LangSort source.language) : LangSort target.language := by
  refine ⟨morphism.symbols.sort sort.1, ?_⟩
  change morphism.symbols.sort sort.1 ∈
    target.language.types.map (fun declaration => declaration.name)
  have sourceMembership : sort.1 ∈
      source.language.types.map (fun declaration => declaration.name) := by
    exact sort.2
  obtain ⟨declaration, membership, name⟩ :=
    List.mem_map.mp sourceMembership
  apply List.mem_map.mpr
  refine ⟨mapTypeDecl morphism.symbols declaration,
    morphism.mapsTypes declaration membership, ?_⟩
  simp [mapTypeDecl, name]

@[simp]
theorem mapLangSort_name {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sort : LangSort source.language) :
    (mapLangSort morphism sort).1 = morphism.symbols.sort sort.1 :=
  rfl

@[simp]
theorem mapLangSort_id (presentation : ValidatedLanguageDef)
    (sort : LangSort presentation.language) :
    mapLangSort (StructuralMorphism.id presentation) sort = sort := by
  apply Subtype.ext
  rfl

@[simp]
theorem mapLangSort_comp {first second third : ValidatedLanguageDef}
    (left : StructuralMorphism first second)
    (right : StructuralMorphism second third)
    (sort : LangSort first.language) :
    mapLangSort (StructuralMorphism.comp left right) sort =
      mapLangSort right (mapLangSort left sort) := by
  apply Subtype.ext
  rfl

/-- Mapping the name-indexed view of an exact authored sort agrees with
mapping the authored declaration and then forgetting it to its name. -/
theorem mapLangSort_authoredSortToLangSort
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (sort : StructuralMorphism.AuthoredSort source) :
    mapLangSort morphism (authoredSortToLangSort source sort) =
      authoredSortToLangSort target (morphism.mapSort sort) := by
  apply Subtype.ext
  rfl

private theorem isObjectPatternList_map_eq
    (symbols : PresentationSymbols) (patterns : List Pattern)
    (pointwise : ∀ pattern ∈ patterns,
      isObjectPattern (mapPattern symbols pattern) =
        isObjectPattern pattern) :
    isObjectPatternList (patterns.map (mapPattern symbols)) =
      isObjectPatternList patterns := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp only [List.map, isObjectPatternList]
      rw [pointwise pattern (by simp)]
      rw [inductionHypothesis]
      intro member membership
      exact pointwise member (by simp [membership])

/-- Renaming presentation symbols preserves whether a raw pattern has
object-language shape.  In particular, it cannot turn a schema substitution
or open collection tail into an object term. -/
@[simp]
theorem isObjectPattern_mapPattern (symbols : PresentationSymbols)
    (pattern : Pattern) :
    isObjectPattern (mapPattern symbols pattern) =
      isObjectPattern pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [mapPattern, isObjectPattern]
  | hfvar name => simp [mapPattern, isObjectPattern]
  | happly constructor arguments inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map, isObjectPattern]
      exact isObjectPatternList_map_eq symbols arguments inductionHypothesis
  | hlambda binder body inductionHypothesis =>
      simpa [mapPattern, isObjectPattern] using inductionHypothesis
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa [mapPattern, isObjectPattern] using inductionHypothesis
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp [mapPattern, isObjectPattern]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map, isObjectPattern]
      rw [isObjectPatternList_map_eq symbols elements inductionHypothesis]

private theorem canonicalBinderMetadataList_map_eq
    (symbols : PresentationSymbols) (patterns : List Pattern)
    (pointwise : ∀ pattern ∈ patterns,
      (mapPattern symbols pattern).hasCanonicalBinderMetadata =
        pattern.hasCanonicalBinderMetadata) :
    Pattern.hasCanonicalBinderMetadataList
        (patterns.map (mapPattern symbols)) =
      Pattern.hasCanonicalBinderMetadataList patterns := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp only [List.map, Pattern.hasCanonicalBinderMetadataList]
      rw [pointwise pattern (by simp)]
      rw [inductionHypothesis]
      intro member membership
      exact pointwise member (by simp [membership])

/-- Symbol renaming leaves locally nameless binder metadata unchanged. -/
@[simp]
theorem hasCanonicalBinderMetadata_mapPattern
    (symbols : PresentationSymbols) (pattern : Pattern) :
    (mapPattern symbols pattern).hasCanonicalBinderMetadata =
      pattern.hasCanonicalBinderMetadata := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [mapPattern, Pattern.hasCanonicalBinderMetadata]
  | hfvar name => simp [mapPattern, Pattern.hasCanonicalBinderMetadata]
  | happly constructor arguments inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map,
        Pattern.hasCanonicalBinderMetadata]
      exact canonicalBinderMetadataList_map_eq symbols arguments
        inductionHypothesis
  | hlambda binder body inductionHypothesis =>
      simp only [mapPattern, Pattern.hasCanonicalBinderMetadata]
      rw [inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [mapPattern, Pattern.hasCanonicalBinderMetadata]
      rw [inductionHypothesis]
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp only [mapPattern, Pattern.hasCanonicalBinderMetadata]
      rw [bodyHypothesis, replacementHypothesis]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map,
        Pattern.hasCanonicalBinderMetadata]
      exact canonicalBinderMetadataList_map_eq symbols elements
        inductionHypothesis

private theorem binderSafeListAt_mapPattern_of_constructor_injective
    (symbols : PresentationSymbols)
    (quoteConstructor : String) (depth : Nat) (patterns : List Pattern)
    (pointwise : ∀ pattern ∈ patterns, ∀ localDepth,
      binderSafeAt (symbols.constructor quoteConstructor) localDepth
          (mapPattern symbols pattern) =
        binderSafeAt quoteConstructor localDepth pattern) :
    binderSafeListAt (symbols.constructor quoteConstructor) depth
        (patterns.map (mapPattern symbols)) =
      binderSafeListAt quoteConstructor depth patterns := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp only [List.map, binderSafeListAt]
      rw [pointwise pattern (by simp) depth]
      apply congrArg (binderSafeAt quoteConstructor depth pattern && ·)
      apply inductionHypothesis
      intro member membership localDepth
      exact pointwise member (by simp [membership]) localDepth

/-- An injective renaming of constructor symbols preserves quotation-aware
binder scope when the distinguished quotation constructor is renamed by the
same action. -/
theorem binderSafeAt_mapPattern_of_constructor_injective
    (symbols : PresentationSymbols)
    (constructorInjective : Function.Injective symbols.constructor)
    (quoteConstructor : String) (depth : Nat) (pattern : Pattern) :
    binderSafeAt (symbols.constructor quoteConstructor) depth
        (mapPattern symbols pattern) =
      binderSafeAt quoteConstructor depth pattern := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index => simp [mapPattern, binderSafeAt]
  | hfvar name => simp [mapPattern, binderSafeAt]
  | happly constructor arguments inductionHypothesis =>
      have listEquality : ∀ localDepth,
          binderSafeListAt (symbols.constructor quoteConstructor) localDepth
              (arguments.map (mapPattern symbols)) =
            binderSafeListAt quoteConstructor localDepth arguments := by
        intro localDepth
        exact binderSafeListAt_mapPattern_of_constructor_injective symbols
          quoteConstructor localDepth arguments inductionHypothesis
      cases arguments with
      | nil => simp [mapPattern, binderSafeAt, binderSafeListAt]
      | cons argument arguments =>
          cases arguments with
          | nil =>
              by_cases quoted : constructor = quoteConstructor
              · subst constructor
                simpa [mapPattern, binderSafeAt] using
                  inductionHypothesis argument (by simp) 0
              · have mappedNotQuoted :
                    symbols.constructor constructor ≠
                      symbols.constructor quoteConstructor := by
                  exact fun equality => quoted (constructorInjective equality)
                simpa [mapPattern, binderSafeAt, quoted, mappedNotQuoted] using
                  listEquality depth
          | cons second remainder =>
              simpa [mapPattern, binderSafeAt] using listEquality depth
  | hlambda binder body inductionHypothesis =>
      simpa [mapPattern, binderSafeAt] using inductionHypothesis (depth + 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa [mapPattern, binderSafeAt] using
        inductionHypothesis (depth + arity)
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp [mapPattern, binderSafeAt, bodyHypothesis, replacementHypothesis]
  | hcollection collectionType elements rest inductionHypothesis =>
      simpa [mapPattern, binderSafeAt] using
        binderSafeListAt_mapPattern_of_constructor_injective symbols
          quoteConstructor depth elements inductionHypothesis

private theorem binderSafeListAt_eq_isWellScopedListAt_mapPattern
    (symbols : PresentationSymbols) (quoteConstructor : String)
    (depth : Nat) (patterns : List Pattern)
    (pointwise : ∀ pattern ∈ patterns, ∀ localDepth,
      binderSafeAt quoteConstructor localDepth (mapPattern symbols pattern) =
        (mapPattern symbols pattern).isWellScopedAt localDepth) :
    binderSafeListAt quoteConstructor depth
        (patterns.map (mapPattern symbols)) =
      Pattern.isWellScopedListAt depth
        (patterns.map (mapPattern symbols)) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp only [List.map, binderSafeListAt, Pattern.isWellScopedListAt]
      rw [pointwise pattern (by simp) depth]
      apply congrArg ((mapPattern symbols pattern).isWellScopedAt depth && ·)
      apply inductionHypothesis
      intro member membership localDepth
      exact pointwise member (by simp [membership]) localDepth

/-- If a quotation label is disjoint from the image of a constructor action,
its reflective scope check on the mapped term is exactly ordinary locally
nameless scope.  This is the negative half needed for disjoint generated
syntax fibers. -/
theorem binderSafeAt_mapPattern_of_constructor_avoids
    (symbols : PresentationSymbols) (quoteConstructor : String)
    (avoids : ∀ constructor, symbols.constructor constructor ≠ quoteConstructor)
    (depth : Nat) (pattern : Pattern) :
    binderSafeAt quoteConstructor depth (mapPattern symbols pattern) =
      (mapPattern symbols pattern).isWellScopedAt depth := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index => simp [mapPattern, binderSafeAt, Pattern.isWellScopedAt]
  | hfvar name => simp [mapPattern, binderSafeAt, Pattern.isWellScopedAt]
  | happly constructor arguments inductionHypothesis =>
      have listEquality : ∀ localDepth,
          binderSafeListAt quoteConstructor localDepth
              (arguments.map (mapPattern symbols)) =
            Pattern.isWellScopedListAt localDepth
              (arguments.map (mapPattern symbols)) := by
        intro localDepth
        exact binderSafeListAt_eq_isWellScopedListAt_mapPattern symbols
          quoteConstructor localDepth arguments inductionHypothesis
      cases arguments with
      | nil => simp [mapPattern, binderSafeAt, Pattern.isWellScopedAt,
          binderSafeListAt, Pattern.isWellScopedListAt]
      | cons argument arguments =>
          cases arguments with
          | nil =>
              simpa [mapPattern, binderSafeAt, Pattern.isWellScopedAt,
                avoids constructor] using listEquality depth
          | cons second remainder =>
              simpa [mapPattern, binderSafeAt, Pattern.isWellScopedAt] using
                listEquality depth
  | hlambda binder body inductionHypothesis =>
      simpa [mapPattern, binderSafeAt, Pattern.isWellScopedAt] using
        inductionHypothesis (depth + 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa [mapPattern, binderSafeAt, Pattern.isWellScopedAt] using
        inductionHypothesis (depth + arity)
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp [mapPattern, binderSafeAt, Pattern.isWellScopedAt,
        bodyHypothesis, replacementHypothesis]
  | hcollection collectionType elements rest inductionHypothesis =>
      simpa [mapPattern, binderSafeAt, Pattern.isWellScopedAt] using
        binderSafeListAt_eq_isWellScopedListAt_mapPattern symbols
          quoteConstructor depth elements inductionHypothesis

@[simp]
theorem parameterType?_mapTermParam (symbols : PresentationSymbols)
    (parameter : TermParam) :
    parameterType? (mapTermParam symbols parameter) =
      (parameterType? parameter).map (mapTypeExpr symbols) := by
  cases parameter with
  | simple name type => simp [parameterType?, mapTermParam]
  | abstractionNamed binder body type =>
      cases type <;> simp [parameterType?, mapTermParam, mapTypeExpr]
  | multiAbstractionNamed binders body type =>
      cases type with
      | base sort => simp [parameterType?, mapTermParam, mapTypeExpr]
      | arrow domain codomain =>
          cases domain <;> simp [parameterType?, mapTermParam, mapTypeExpr]
      | multiBinder body => simp [parameterType?, mapTermParam, mapTypeExpr]
      | collection collectionType element =>
          simp [parameterType?, mapTermParam, mapTypeExpr]

@[simp]
theorem matchesParameterRepresentation_map_iff
    (symbols : PresentationSymbols) (parameter : TermParam)
    (argument : Pattern) :
    MatchesParameterRepresentation (mapTermParam symbols parameter)
        (mapPattern symbols argument) ↔
      MatchesParameterRepresentation parameter argument := by
  cases parameter with
  | simple name type =>
      simp [MatchesParameterRepresentation, mapTermParam]
  | abstractionNamed declaredBinder bodyName type =>
      cases argument with
      | bvar index =>
          simp [MatchesParameterRepresentation, mapTermParam, mapPattern]
      | fvar name =>
          simp [MatchesParameterRepresentation, mapTermParam, mapPattern]
      | apply name arguments =>
          simp [MatchesParameterRepresentation, mapTermParam, mapPattern]
      | lambda actualBinder body =>
          cases actualBinder <;>
            simp [MatchesParameterRepresentation, mapTermParam, mapPattern]
      | multiLambda arity binders body =>
          simp [MatchesParameterRepresentation, mapTermParam, mapPattern]
      | subst body replacement =>
          simp [MatchesParameterRepresentation, mapTermParam, mapPattern]
      | collection collectionType elements rest =>
          simp [MatchesParameterRepresentation, mapTermParam, mapPattern]
  | multiAbstractionNamed declaredBinders bodyName type =>
      cases argument with
      | bvar index =>
          simp [MatchesParameterRepresentation, mapTermParam, mapPattern]
      | fvar name =>
          simp [MatchesParameterRepresentation, mapTermParam, mapPattern]
      | apply name arguments =>
          simp [MatchesParameterRepresentation, mapTermParam, mapPattern]
      | lambda binder body =>
          simp [MatchesParameterRepresentation, mapTermParam, mapPattern]
      | multiLambda arity actualBinders body =>
          cases actualBinders with
          | nil =>
              simp [MatchesParameterRepresentation, mapTermParam, mapPattern]
          | cons binder binders =>
              simp [MatchesParameterRepresentation, mapTermParam, mapPattern]
      | subst body replacement =>
          simp [MatchesParameterRepresentation, mapTermParam, mapPattern]
      | collection collectionType elements rest =>
          simp [MatchesParameterRepresentation, mapTermParam, mapPattern]

mutual
  /-- Typed-profile maps preserve every term-typing derivation. -/
  theorem HasType.mapTyping
      {source target : ValidatedLanguageDef}
      (morphism : TypingMorphism source target)
      {free : FreeTypeContext} {bound : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      (typed : HasType source.language free bound pattern type) :
      HasType target.language (free.map morphism.symbols)
        (bound.map (mapTypeExpr morphism.symbols))
        (mapPattern morphism.symbols pattern)
        (mapTypeExpr morphism.symbols type) := by
    cases typed with
    | @bvar bound index type lookup =>
        have mappedLookup :
            (bound.map (mapTypeExpr morphism.symbols))[index]?
              = some (mapTypeExpr morphism.symbols type) := by
          simpa using congrArg
            (Option.map (mapTypeExpr morphism.symbols)) lookup
        simpa [mapPattern] using
          (HasType.bvar (free := free.map morphism.symbols) mappedLookup)
    | @fvar bound name type lookup =>
        have mappedLookup :
            (free.map morphism.symbols) name =
              some (mapTypeExpr morphism.symbols type) := by
          simp [FreeTypeContext.map, lookup]
        simpa [mapPattern] using
          (HasType.fvar (bound := bound.map (mapTypeExpr morphism.symbols))
            mappedLookup)
    | @constructor bound rule arguments membership notBareCollection argumentsTyped =>
        obtain ⟨targetRule, targetMembership, targetLabel, targetCategory,
          targetParameters⟩ := morphism.mapsTerms rule membership
        have mappedArguments := argumentsTyped.mapTyping morphism
        have mappedNotBareCollection :
            ¬ UsesBareCollection (mapGrammarRule morphism.symbols rule) :=
          fun mappedBare => notBareCollection
            ((usesBareCollection_mapGrammarRule_iff morphism.symbols rule).mp
              mappedBare)
        have targetArguments :
            ArgumentsHaveTypes target.language
              (free.map morphism.symbols)
              (bound.map (mapTypeExpr morphism.symbols))
              (arguments.map (mapPattern morphism.symbols))
              targetRule.params := by
          simpa [targetParameters] using mappedArguments
        simpa [mapPattern, targetLabel, targetCategory, mapTypeExpr] using
          (HasType.constructor
            targetMembership (by
              simpa [UsesBareCollection, targetParameters, mapGrammarRule] using
                mappedNotBareCollection)
            targetArguments)
    | @lambda bound binder body domain codomain bodyTyped =>
        have mappedBody := bodyTyped.mapTyping morphism
        simpa [mapPattern, mapTypeExpr] using HasType.lambda mappedBody
    | @multiLambda bound arity binders body domain codomain bodyTyped =>
        have mappedBody := bodyTyped.mapTyping morphism
        have mappedBody' :
            HasType target.language (free.map morphism.symbols)
              (List.replicate arity (mapTypeExpr morphism.symbols domain) ++
                bound.map (mapTypeExpr morphism.symbols))
              (mapPattern morphism.symbols body)
              (mapTypeExpr morphism.symbols codomain) := by
          simpa [List.map_append, List.map_replicate] using mappedBody
        simpa [mapPattern, mapTypeExpr] using
          HasType.multiLambda mappedBody'
    | @subst bound body replacement domain codomain bodyTyped replacementTyped =>
        have mappedBody := bodyTyped.mapTyping morphism
        have mappedReplacement := replacementTyped.mapTyping morphism
        simpa [mapPattern] using HasType.subst mappedBody mappedReplacement
    | @collection bound collectionType elements rest elementType elementsTyped =>
        have mappedElements := elementsTyped.mapTyping morphism
        simpa [mapPattern, mapTypeExpr] using
          (HasType.collection (rest := rest) mappedElements)
    | @collectionConstructor bound rule parameterName collectionType elements rest
        elementType membership parameterShape elementsTyped =>
        obtain ⟨targetRule, targetMembership, targetLabel, targetCategory,
          targetParameters⟩ := morphism.mapsTerms rule membership
        have mappedElements := elementsTyped.mapTyping morphism
        have mappedParameterShape :
            targetRule.params =
              [.simple parameterName
                (.collection collectionType
                  (mapTypeExpr morphism.symbols elementType))] := by
          simp [targetParameters, parameterShape, mapTermParam, mapTypeExpr]
        simpa [mapPattern, targetLabel, targetCategory, mapTypeExpr] using
          (HasType.collectionConstructor
            targetMembership mappedParameterShape
            mappedElements)

  /-- Typed-profile maps preserve ordered constructor-argument
  derivations. -/
  theorem ArgumentsHaveTypes.mapTyping
      {source target : ValidatedLanguageDef}
      (morphism : TypingMorphism source target)
      {free : FreeTypeContext} {bound : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes source.language free bound
        arguments parameters) :
      ArgumentsHaveTypes target.language (free.map morphism.symbols)
        (bound.map (mapTypeExpr morphism.symbols))
        (arguments.map (mapPattern morphism.symbols))
        (parameters.map (mapTermParam morphism.symbols)) := by
    cases typed with
    | nil => exact .nil
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped =>
        have mappedParameterType :
            parameterType? (mapTermParam morphism.symbols parameter) =
              some (mapTypeExpr morphism.symbols expected) := by
          rw [parameterType?_mapTermParam, parameterType]
          rfl
        apply ArgumentsHaveTypes.cons
        · exact (matchesParameterRepresentation_map_iff
            morphism.symbols parameter argument).2 representation
        · exact mappedParameterType
        · exact argumentTyped.mapTyping morphism
        · exact argumentsTyped.mapTyping morphism

  /-- Typed-profile maps preserve collection-element derivations. -/
  theorem ElementsHaveType.mapTyping
      {source target : ValidatedLanguageDef}
      (morphism : TypingMorphism source target)
      {free : FreeTypeContext} {bound : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      (typed : ElementsHaveType source.language free bound
        elements elementType) :
      ElementsHaveType target.language (free.map morphism.symbols)
        (bound.map (mapTypeExpr morphism.symbols))
        (elements.map (mapPattern morphism.symbols))
        (mapTypeExpr morphism.symbols elementType) := by
    cases typed with
    | nil => exact .nil _ _
    | cons elementTyped elementsTyped =>
        exact .cons (elementTyped.mapTyping morphism)
          (elementsTyped.mapTyping morphism)
end

/-- Full signature maps transport typing through their underlying profile
action. -/
theorem HasType.mapSignature
    {source target : ValidatedLanguageDef}
    (morphism : SignatureMorphism source target)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    (typed : HasType source.language free bound pattern type) :
    HasType target.language (free.map morphism.symbols)
      (bound.map (mapTypeExpr morphism.symbols))
      (mapPattern morphism.symbols pattern)
      (mapTypeExpr morphism.symbols type) :=
  typed.mapTyping morphism.toTyping

/-- Full signature maps transport constructor-argument typing. -/
theorem ArgumentsHaveTypes.mapSignature
    {source target : ValidatedLanguageDef}
    (morphism : SignatureMorphism source target)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {arguments : List Pattern} {parameters : List TermParam}
    (typed : ArgumentsHaveTypes source.language free bound
      arguments parameters) :
    ArgumentsHaveTypes target.language (free.map morphism.symbols)
      (bound.map (mapTypeExpr morphism.symbols))
      (arguments.map (mapPattern morphism.symbols))
      (parameters.map (mapTermParam morphism.symbols)) :=
  typed.mapTyping morphism.toTyping

/-- Full signature maps transport collection-element typing. -/
theorem ElementsHaveType.mapSignature
    {source target : ValidatedLanguageDef}
    (morphism : SignatureMorphism source target)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern} {elementType : TypeExpr}
    (typed : ElementsHaveType source.language free bound
      elements elementType) :
    ElementsHaveType target.language (free.map morphism.symbols)
      (bound.map (mapTypeExpr morphism.symbols))
      (elements.map (mapPattern morphism.symbols))
      (mapTypeExpr morphism.symbols elementType) :=
  typed.mapTyping morphism.toTyping

/-- Full structural maps transport typing through their underlying typed
signature map. -/
theorem HasType.map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    (typed : HasType source.language free bound pattern type) :
    HasType target.language (free.map morphism.symbols)
      (bound.map (mapTypeExpr morphism.symbols))
      (mapPattern morphism.symbols pattern)
      (mapTypeExpr morphism.symbols type) :=
  typed.mapTyping morphism.toTyping

/-- Full structural maps transport constructor-argument typing through their
underlying typed signature map. -/
theorem ArgumentsHaveTypes.map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {arguments : List Pattern} {parameters : List TermParam}
    (typed : ArgumentsHaveTypes source.language free bound
      arguments parameters) :
    ArgumentsHaveTypes target.language (free.map morphism.symbols)
      (bound.map (mapTypeExpr morphism.symbols))
      (arguments.map (mapPattern morphism.symbols))
      (parameters.map (mapTermParam morphism.symbols)) :=
  typed.mapTyping morphism.toTyping

/-- Full structural maps transport collection-element typing through their
underlying typed signature map. -/
theorem ElementsHaveType.map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern} {elementType : TypeExpr}
    (typed : ElementsHaveType source.language free bound
      elements elementType) :
    ElementsHaveType target.language (free.map morphism.symbols)
      (bound.map (mapTypeExpr morphism.symbols))
      (elements.map (mapPattern morphism.symbols))
      (mapTypeExpr morphism.symbols elementType) :=
  typed.mapTyping morphism.toTyping

/-- Transport an open sorted term along a structural presentation map.
Typing, object shape, binder metadata, and ordinary scope are all forced by
the authored declaration map. -/
def OpenTerm.map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.language}
    (term : OpenTerm source.language free bound sort) :
    OpenTerm target.language
      (free.map morphism.symbols)
      (bound.map (mapTypeExpr morphism.symbols))
      (mapLangSort morphism sort) := by
  have mappedTyped := term.2.1.map morphism
  refine ⟨mapPattern morphism.symbols term.1, ?_, ?_, ?_, ?_⟩
  · simpa [mapTypeExpr] using mappedTyped
  · simpa using term.2.2.1
  · simpa using term.2.2.2.1
  · simpa [ScopeSafeAt] using mappedTyped.isWellScopedAt

@[simp]
theorem OpenTerm.map_pattern {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.language}
    (term : OpenTerm source.language free bound sort) :
    (term.map morphism).1 =
      mapPattern morphism.symbols term.1 :=
  rfl

/-- Structural presentation maps preserve the closed core carrier. -/
theorem ClosedTermWellSorted.map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    {sourceSort : StructuralMorphism.AuthoredSort source}
    {targetSort : StructuralMorphism.AuthoredSort target}
    (mapsSort : morphism.mapSort sourceSort = targetSort)
    {pattern : Pattern}
    (closed : ClosedTermWellSorted source.language
      (authoredSortToLangSort source sourceSort) pattern) :
    ClosedTermWellSorted target.language
      (authoredSortToLangSort target targetSort)
      (mapPattern morphism.symbols pattern) := by
  have sortName :
      morphism.symbols.sort sourceSort.1.name = targetSort.1.name := by
    have mappedName := congrArg
      (fun sort : StructuralMorphism.AuthoredSort target => sort.1.name)
      mapsSort
    simpa [StructuralMorphism.mapSort, mapTypeDecl] using mappedName
  have typed := closed.1.map morphism
  have mappedEmpty :
      FreeTypeContext.map morphism.symbols FreeTypeContext.empty =
        FreeTypeContext.empty := by
    funext name
    rfl
  have mappedTyped :
      HasSort target.language FreeTypeContext.empty []
        (mapPattern morphism.symbols pattern) targetSort.1.name := by
    change HasType target.language FreeTypeContext.empty []
      (mapPattern morphism.symbols pattern) (.base targetSort.1.name)
    change HasType target.language
      (FreeTypeContext.map morphism.symbols FreeTypeContext.empty) []
      (mapPattern morphism.symbols pattern)
      (.base (morphism.symbols.sort sourceSort.1.name)) at typed
    rw [mappedEmpty, sortName] at typed
    exact typed
  have canonical :
      (mapPattern morphism.symbols pattern).hasCanonicalBinderMetadata = true := by
    simpa using closed.2.2.1
  have object :
      isObjectPattern (mapPattern morphism.symbols pattern) = true := by
    simpa using closed.2.2.2.1
  have scopeSafe : ScopeSafe target.language
      (mapPattern morphism.symbols pattern) := by
    simpa [ScopeSafe, ScopeSafeAt] using mappedTyped.isWellScopedAt
  exact ⟨mappedTyped,
    ground_of_closed_sorting
      (sort := authoredSortToLangSort target targetSort)
      mappedTyped object scopeSafe,
    canonical, object, scopeSafe⟩

/-! ## Generic boundary facts -/

/-- A constructor application can be sorted only through an authored grammar
rule with that label and result sort. -/
theorem declared_constructor_of_hasType_apply
    {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {constructor : String} {arguments : List Pattern} {type : TypeExpr}
    (typed : HasType language free bound (.apply constructor arguments) type) :
    ∃ rule ∈ language.terms,
      rule.label = constructor ∧ type = .base rule.category := by
  cases typed with
  | constructor membership notBareCollection argumentsTyped =>
      exact ⟨_, membership, rfl, rfl⟩

/-- In a validated presentation, an application node has a unique result
type.  Constructor labels are unique, so two typing derivations for the same
raw application necessarily select the same authored declaration. -/
theorem HasType.apply_type_unique_of_validate_eq_nil
    {language : LanguageDef} (valid : language.validate = [])
    {free : FreeTypeContext} {bound : List TypeExpr}
    {constructor : String} {arguments : List Pattern}
    {firstType secondType : TypeExpr}
    (first : HasType language free bound
      (.apply constructor arguments) firstType)
    (second : HasType language free bound
      (.apply constructor arguments) secondType) :
    firstType = secondType := by
  rcases declared_constructor_of_hasType_apply first with
    ⟨firstRule, firstMembership, firstLabel, firstTypeEquation⟩
  rcases declared_constructor_of_hasType_apply second with
    ⟨secondRule, secondMembership, secondLabel, secondTypeEquation⟩
  have ruleEquality : firstRule = secondRule :=
    List.inj_on_of_nodup_map
      (LanguageDef.constructorLabels_nodup_of_validate_eq_nil language valid)
      firstMembership secondMembership
      (firstLabel.trans secondLabel.symm)
  calc
    firstType = .base firstRule.category := firstTypeEquation
    _ = .base secondRule.category := congrArg
      (fun rule : GrammarRule => TypeExpr.base rule.category) ruleEquality
    _ = secondType := secondTypeEquation.symm

/-- A bare collection can inhabit a base sort only through an authored
single-collection constructor of exactly that collection kind. -/
theorem declared_collection_constructor_of_hasSort
    {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {collectionType : CollType} {elements : List Pattern} {rest : Option String}
    {sort : String}
    (typed : HasSort language free bound
      (.collection collectionType elements rest) sort) :
    ∃ rule ∈ language.terms, rule.category = sort ∧
      ∃ parameterName elementType,
        rule.params =
          [.simple parameterName (.collection collectionType elementType)] := by
  cases typed with
  | collectionConstructor membership parameterShape elementsTyped =>
      exact ⟨_, membership, rfl, _, _, parameterShape⟩

/-- Negative control: no bound variable is sorted in the empty bound context. -/
theorem bvar_not_typed_in_empty
    {language : LanguageDef} {free : FreeTypeContext}
    {index : Nat} {type : TypeExpr} :
    ¬ HasType language free [] (.bvar index) type := by
  intro typed
  cases typed with
  | bvar lookup => simp at lookup

/-- Negative control: no free variable is sorted by the empty free context. -/
theorem fvar_not_typed_in_empty
    {language : LanguageDef} {bound : List TypeExpr}
    {name : String} {type : TypeExpr} :
    ¬ HasType language FreeTypeContext.empty bound (.fvar name) type := by
  intro typed
  cases typed with
  | fvar lookup => simp [FreeTypeContext.empty] at lookup

/-- Negative: an explicit substitution may be well-typed as a rule schema,
but it is never itself a closed object-language term. -/
theorem explicit_substitution_not_object
    (body replacement : Pattern) :
    isObjectPattern (.subst body replacement) = false :=
  rfl

/-- Negative: an arrow-typed variable is not a representation of an authored
abstraction parameter.  Binder shape is data, not an inference from type. -/
theorem abstraction_parameter_rejects_variable
    (binderName : Option String) (bodyName : String) (type : TypeExpr)
    (variableName : String) :
    ¬ MatchesParameterRepresentation
      (.abstractionNamed binderName bodyName type) (.fvar variableName) := by
  simp [MatchesParameterRepresentation]

/-- Negative: an open collection tail belongs to a rewrite schema, not to the
object-language carrier derived from the presentation. -/
theorem open_collection_tail_not_object
    (collectionType : CollType) (elements : List Pattern) (rest : String) :
    isObjectPattern (.collection collectionType elements (some rest)) = false := by
  simp [isObjectPattern]

/-! ## Rho controls derived from the canonical root -/

/-- Positive: the nullary process constructor is sorted in every binder
context by the declaration already present in `rhoCalc`. -/
theorem rho_zero_hasSort (free : FreeTypeContext) (bound : List TypeExpr) :
    HasSort rhoCalc free bound
      (.apply "PZero" []) "Proc" := by
  apply HasType.constructor
    (rule :=
      { label := "PZero"
        category := "Proc"
        params := []
        syntaxPattern := [.terminal "0"] })
  · simp [rhoCalc]
  · simp [UsesBareCollection]
  · exact .nil

/-- The canonical quotation declaration transports a sorted process to the
name sort. -/
theorem rho_quote_hasSort
    {free : FreeTypeContext} {bound : List TypeExpr} {process : Pattern}
    (typed : HasSort rhoCalc free bound process "Proc") :
    HasSort rhoCalc free bound (.apply "NQuote" [process]) "Name" := by
  apply HasType.constructor
    (rule :=
      { label := "NQuote"
        category := "Name"
        params := [.simple "p" TypeExpr.proc]
        syntaxPattern :=
          [.terminal "@", .terminal "(", .nonTerminal "p", .terminal ")"] })
  · simp [rhoCalc]
  · simp [UsesBareCollection, TypeExpr.proc, TypeExpr.baseType]
  · exact .cons trivial rfl typed .nil

/-- The canonical drop declaration transports a sorted name to the process
sort without asserting that it reduces. -/
theorem rho_drop_hasSort
    {free : FreeTypeContext} {bound : List TypeExpr} {name : Pattern}
    (typed : HasSort rhoCalc free bound name "Name") :
    HasSort rhoCalc free bound (.apply "PDrop" [name]) "Proc" := by
  apply HasType.constructor
    (rule :=
      { label := "PDrop"
        category := "Proc"
        params := [.simple "n" TypeExpr.name]
        syntaxPattern :=
          [.terminal "*", .terminal "(", .nonTerminal "n", .terminal ")"] })
  · simp [rhoCalc]
  · simp [UsesBareCollection, TypeExpr.name, TypeExpr.baseType]
  · exact .cons trivial rfl typed .nil

/-- The canonical output declaration preserves the process sort. -/
theorem rho_output_hasSort
    {free : FreeTypeContext} {bound : List TypeExpr}
    {channel payload : Pattern}
    (channelTyped : HasSort rhoCalc free bound channel "Name")
    (payloadTyped : HasSort rhoCalc free bound payload "Proc") :
    HasSort rhoCalc free bound
      (.apply "POutput" [channel, payload]) "Proc" := by
  apply HasType.constructor
    (rule :=
      { label := "POutput"
        category := "Proc"
        params :=
          [.simple "n" TypeExpr.name, .simple "q" TypeExpr.proc]
        syntaxPattern :=
          [.nonTerminal "n", .terminal "!", .terminal "(",
            .nonTerminal "q", .terminal ")"] })
  · simp [rhoCalc]
  · simp [UsesBareCollection, TypeExpr.name, TypeExpr.proc,
      TypeExpr.baseType]
  · exact .cons trivial rfl channelTyped
      (.cons trivial rfl payloadTyped .nil)

/-- The canonical input declaration accepts a body under one bound name. -/
theorem rho_input_hasSort
    {free : FreeTypeContext} {bound : List TypeExpr}
    {channel body : Pattern}
    (channelTyped : HasSort rhoCalc free bound channel "Name")
    (bodyTyped : HasSort rhoCalc free (TypeExpr.name :: bound) body "Proc") :
    HasSort rhoCalc free bound
      (.apply "PInput" [channel, .lambda none body]) "Proc" := by
  apply HasType.constructor
    (rule :=
      { label := "PInput"
        category := "Proc"
        params :=
          [.simple "n" TypeExpr.name,
            .abstraction "p" (TypeExpr.funType TypeExpr.name TypeExpr.proc)]
        syntaxPattern :=
          [.nonTerminal "n", .terminal "?", .terminal ".", .terminal "{",
            .nonTerminal "p", .terminal "}"] })
  · simp [rhoCalc]
  · simp [UsesBareCollection, TypeExpr.name, TypeExpr.proc,
      TypeExpr.funType, TypeExpr.baseType]
  · exact .cons trivial rfl channelTyped
      (.cons trivial rfl (HasType.lambda bodyTyped) .nil)

/-- The canonical parallel declaration assigns the process sort to a bag of
sorted processes. -/
theorem rho_parallel_hasSort
    {free : FreeTypeContext} {bound : List TypeExpr}
    {processes : List Pattern}
    (typed : ElementsHaveType rhoCalc free bound processes TypeExpr.proc) :
    HasSort rhoCalc free bound (.collection .hashBag processes none) "Proc" := by
  apply HasType.collectionConstructor
    (rule :=
      { label := "PPar"
        category := "Proc"
        params := [.simple "ps" (TypeExpr.bag TypeExpr.proc)]
        syntaxPattern :=
          [.terminal "{", .nonTerminal "ps", .separator "|", .terminal "}"] })
    (parameterName := "ps")
  · simp [rhoCalc]
  · rfl
  · exact typed

/-- Positive: quotation crosses from the declared process sort to the
declared name sort. -/
theorem rho_quote_zero_hasSort (free : FreeTypeContext)
    (bound : List TypeExpr) :
    HasSort rhoCalc free bound
      (.apply "NQuote" [.apply "PZero" []]) "Name" := by
  exact rho_quote_hasSort (rho_zero_hasSort free bound)

/-- Positive: the input binder is accepted from the arrow-shaped parameter
of the canonical rho declaration. -/
theorem rho_input_zero_hasSort (free : FreeTypeContext)
    (bound : List TypeExpr) :
    HasSort rhoCalc free bound
      (.apply "PInput"
        [.apply "NQuote" [.apply "PZero" []],
          .lambda none (.apply "PZero" [])]) "Proc" := by
  exact rho_input_hasSort (rho_quote_zero_hasSort free bound)
    (rho_zero_hasSort free (TypeExpr.name :: bound))

/-- Positive: the representation-level bag becomes a process only because
the canonical rho root authors the corresponding collection constructor. -/
theorem rho_parallel_zero_hasSort (free : FreeTypeContext)
    (bound : List TypeExpr) :
    HasSort rhoCalc free bound
      (.collection .hashBag [.apply "PZero" []] none) "Proc" := by
  exact rho_parallel_hasSort
    (.cons (rho_zero_hasSort free bound) (.nil bound TypeExpr.proc))

/-- Negative: pure rho's authored collection constructor does not turn a set
representation into a process. -/
theorem rho_set_zero_not_hasSort (bound : List TypeExpr) :
    ¬ HasSort rhoCalc FreeTypeContext.empty bound
      (.collection .hashSet [.apply "PZero" []] none) "Proc" := by
  intro typed
  obtain ⟨rule, membership, category, parameterName, elementType,
    parameterShape⟩ := declared_collection_constructor_of_hasSort typed
  simp [rhoCalc] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [TypeExpr.name, TypeExpr.proc, TypeExpr.bag,
      TypeExpr.baseType]

end Mettapedia.GSLT.LanguageDef.WellSorted
