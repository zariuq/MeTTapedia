import Mettapedia.GSLT.LanguageDef.CostInteractive
import Mettapedia.GSLT.LanguageDef.CostStaticTyping
import Mettapedia.GSLT.LanguageDef.EquationSubstitution
import Mettapedia.OSLF.MeTTaIL.DerivedContexts
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.OSLF.MeTTaIL.PatternCode
import Std.Data.String.ToNat

/-!
# Canonical sections for generated Cost presentations

The static theory of `Cost(L)` contains two injectively tagged images of the
authored equations of `L`.  This file starts the constructive canonical lift
by making those images exactly decodable.  The decoder operates on the shared
`Pattern` carrier and introduces no second term language.

Decoding is deliberately partial.  A maximal region in one static namespace
stops when it meets Cost apparatus or the other namespace; subsequent layers
replace those already-canonical boundaries by rigid, content-keyed variables
before invoking the source open canonical section.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open StructuralMorphism

/-- Remove one exact reserved string prefix. -/
def decodeTaggedPayload (tag name : String) : Option String :=
  (dropListPrefix? tag.toList name.toList).map String.ofList

@[simp]
theorem decodeTaggedPayload_append (tag payload : String) :
    decodeTaggedPayload tag (tag ++ payload) = some payload := by
  simp [decodeTaggedPayload, String.toList_append]

/-- Successful prefix decoding reconstructs the original string exactly. -/
theorem decodeTaggedPayload_eq_some_iff (tag name payload : String) :
    decodeTaggedPayload tag name = some payload ↔
      name = tag ++ payload := by
  constructor
  · intro decoded
    unfold decodeTaggedPayload at decoded
    cases decodedPrefix : dropListPrefix? tag.toList name.toList with
    | none => simp [decodedPrefix] at decoded
    | some suffix =>
        simp only [decodedPrefix, Option.map_some, Option.some.injEq] at decoded
        have reconstructed : tag ++ String.ofList suffix = name := by
          apply String.toList_inj.mp
          simpa [String.toList_append] using
            append_eq_of_dropListPrefix?_eq_some decodedPrefix
        simpa [decoded] using reconstructed.symm
  · rintro rfl
    exact decodeTaggedPayload_append _ _

/-- Decode the constructor label of one selected static namespace. -/
def decodeCostStaticConstructor (color : CostStaticColor)
    (constructor : String) : Option String :=
  decodeTaggedPayload color.constructorTag constructor

@[simp]
theorem decodeCostStaticConstructor_append (color : CostStaticColor)
    (constructor : String) :
    decodeCostStaticConstructor color
        (color.constructorTag ++ constructor) =
      some constructor :=
  decodeTaggedPayload_append _ _

/-- A successful color decoder recovers exactly the corresponding tagged
constructor name. -/
theorem decodeCostStaticConstructor_eq_some_iff
    (color : CostStaticColor) (constructor sourceConstructor : String) :
    decodeCostStaticConstructor color constructor = some sourceConstructor ↔
      constructor = color.constructorTag ++ sourceConstructor :=
  decodeTaggedPayload_eq_some_iff _ _ _

@[simp]
theorem decodeCostStaticConstructor_symbols (source : CIGSLT)
    (color : CostStaticColor) (constructor : String) :
    decodeCostStaticConstructor color
        ((color.symbols source).constructor constructor) =
      some constructor := by
  rw [CostStaticColor.symbols_constructor]
  exact decodeTaggedPayload_append _ _

/-! ## Decoding the typed static fibers -/

/-- Decode a sort name in the uniform base fiber. -/
def decodeCostBaseSortName (name : String) : Option String :=
  decodeTaggedPayload costBaseSortTag name

@[simp]
theorem decodeCostBaseSortName_encode (name : String) :
    decodeCostBaseSortName (costBaseSortName name) = some name := by
  exact decodeTaggedPayload_append _ _

/-- Decode the type action of one static Cost copy.  In the wrapped copy the
distinguished interacting sort is represented by the single wrapped carrier;
every other base sort remains in the tagged base fiber. -/
def decodeCostStaticTypeExpr (source : CIGSLT)
    (color : CostStaticColor) : TypeExpr → Option TypeExpr
  | .base sort =>
      match color with
      | .base => (decodeCostBaseSortName sort).map TypeExpr.base
      | .wrapped =>
          if sort = costWrappedSortName then
            some (.base source.theory.presentation.interactingSort.1.name)
          else do
            let sourceSort ← decodeCostBaseSortName sort
            if sourceSort =
                source.theory.presentation.interactingSort.1.name then
              none
            else
              some (.base sourceSort)
  | .arrow domain codomain => do
      let sourceDomain ← decodeCostStaticTypeExpr source color domain
      let sourceCodomain ← decodeCostStaticTypeExpr source color codomain
      pure (.arrow sourceDomain sourceCodomain)
  | .multiBinder body => do
      let sourceBody ← decodeCostStaticTypeExpr source color body
      pure (.multiBinder sourceBody)
  | .collection collectionType element => do
      let sourceElement ← decodeCostStaticTypeExpr source color element
      pure (.collection collectionType sourceElement)

/-- Decoding is a computable left inverse of either exact static type action.
The wrapped interacting sort is separated from every tagged base sort by the
reserved namespace theorem of the generated signature. -/
@[simp]
theorem decodeCostStaticTypeExpr_mapTypeExpr (source : CIGSLT)
    (color : CostStaticColor) (type : TypeExpr) :
    decodeCostStaticTypeExpr source color
        (mapTypeExpr (color.symbols source) type) = some type := by
  induction type with
  | base sort =>
      cases color with
      | base =>
          change decodeCostStaticTypeExpr source .base
              (mapTypeExpr costBaseStaticSymbols (.base sort)) = _
          rw [mapTypeExpr_costBaseStaticSymbols]
          simp [decodeCostStaticTypeExpr, costBaseTypeExpr,
            decodeCostBaseSortName_encode]
      | wrapped =>
          change decodeCostStaticTypeExpr source .wrapped
              (mapTypeExpr (costWrappedStaticSymbols source.theory)
                (.base sort)) = _
          rw [mapTypeExpr_costWrappedStaticSymbols]
          by_cases interacting :
              sort = source.theory.presentation.interactingSort.1.name
          · subst sort
            simp [decodeCostStaticTypeExpr, costWrappedTypeExpr]
          · simp [decodeCostStaticTypeExpr, costWrappedTypeExpr,
              interacting, costBaseSortName_ne_wrapped,
              decodeCostBaseSortName_encode]
  | arrow domain codomain domainHypothesis codomainHypothesis =>
      simp [decodeCostStaticTypeExpr, mapTypeExpr,
        domainHypothesis, codomainHypothesis]
  | multiBinder body inductionHypothesis =>
      simp [decodeCostStaticTypeExpr, mapTypeExpr, inductionHypothesis]
  | collection collectionType element inductionHypothesis =>
      simp [decodeCostStaticTypeExpr, mapTypeExpr, inductionHypothesis]

/-- A successfully decoded static type lies in the exact image of the
selected Cost fiber.  In the wrapped fiber the base-tagged interacting sort
is deliberately rejected: its only image is the distinguished wrapped sort.
Together with `decodeCostStaticTypeExpr_mapTypeExpr`, this makes decoding a
partial equivalence rather than a merely one-sided parser. -/
theorem mapTypeExpr_decodeCostStaticTypeExpr (source : CIGSLT)
    (color : CostStaticColor) {target sourceType : TypeExpr}
    (decoded : decodeCostStaticTypeExpr source color target =
      some sourceType) :
    mapTypeExpr (color.symbols source) sourceType = target := by
  induction target generalizing sourceType with
  | base sort =>
      cases color with
      | base =>
          cases decodedSort : decodeCostBaseSortName sort with
          | none =>
              simp [decodeCostStaticTypeExpr, decodedSort] at decoded
          | some sourceSort =>
              simp [decodeCostStaticTypeExpr, decodedSort] at decoded
              subst sourceType
              have sortEquality : sort = costBaseSortName sourceSort :=
                (decodeTaggedPayload_eq_some_iff
                  costBaseSortTag sort sourceSort).mp decodedSort
              subst sort
              simp [CostStaticColor.symbols, costBaseStaticSymbols,
                costBasePresentationSymbols, mapTypeExpr]
      | wrapped =>
          by_cases wrapped : sort = costWrappedSortName
          · subst sort
            simp [decodeCostStaticTypeExpr] at decoded
            subst sourceType
            simp [CostStaticColor.symbols, costWrappedStaticSymbols,
              mapTypeExpr]
          · cases decodedSort : decodeCostBaseSortName sort with
            | none =>
                simp [decodeCostStaticTypeExpr, wrapped, decodedSort] at decoded
            | some sourceSort =>
                by_cases interacting : sourceSort =
                    source.theory.presentation.interactingSort.1.name
                · simp [decodeCostStaticTypeExpr, wrapped, decodedSort,
                    interacting] at decoded
                · simp [decodeCostStaticTypeExpr, wrapped, decodedSort,
                    interacting] at decoded
                  subst sourceType
                  have sortEquality : sort = costBaseSortName sourceSort :=
                    (decodeTaggedPayload_eq_some_iff
                      costBaseSortTag sort sourceSort).mp decodedSort
                  subst sort
                  simp [CostStaticColor.symbols, costWrappedStaticSymbols,
                    mapTypeExpr, interacting]
  | arrow domain codomain domainHypothesis codomainHypothesis =>
      cases decodedDomain : decodeCostStaticTypeExpr source color domain with
      | none =>
          simp [decodeCostStaticTypeExpr, decodedDomain] at decoded
      | some sourceDomain =>
          cases decodedCodomain :
              decodeCostStaticTypeExpr source color codomain with
          | none =>
              simp [decodeCostStaticTypeExpr, decodedDomain,
                decodedCodomain] at decoded
          | some sourceCodomain =>
              simp [decodeCostStaticTypeExpr, decodedDomain,
                decodedCodomain] at decoded
              subst sourceType
              simp [mapTypeExpr,
                domainHypothesis decodedDomain,
                codomainHypothesis decodedCodomain]
  | multiBinder body inductionHypothesis =>
      cases decodedBody : decodeCostStaticTypeExpr source color body with
      | none =>
          simp [decodeCostStaticTypeExpr, decodedBody] at decoded
      | some sourceBody =>
          simp [decodeCostStaticTypeExpr, decodedBody] at decoded
          subst sourceType
          simp [mapTypeExpr, inductionHypothesis decodedBody]
  | collection collectionType element inductionHypothesis =>
      cases decodedElement : decodeCostStaticTypeExpr source color element with
      | none =>
          simp [decodeCostStaticTypeExpr, decodedElement] at decoded
      | some sourceElement =>
          simp [decodeCostStaticTypeExpr, decodedElement] at decoded
          subst sourceType
          simp [mapTypeExpr, inductionHypothesis decodedElement]

/-- Each static type action is injective. -/
theorem mapTypeExpr_costStatic_injective (source : CIGSLT)
    (color : CostStaticColor) :
    Function.Injective (mapTypeExpr (color.symbols source)) := by
  intro left right equality
  have decoded := congrArg (decodeCostStaticTypeExpr source color) equality
  simpa using decoded

mutual
  /-- Decode a pattern wholly contained in one generated static namespace.
  Binder, variable, substitution, and collection representation nodes are
  shared; every constructor application must carry the selected tag. -/
  def decodeCostStaticPattern (color : CostStaticColor) :
      Pattern → Option Pattern
    | .bvar index => some (.bvar index)
    | .fvar name => some (.fvar name)
    | .apply constructor arguments => do
        let sourceConstructor ← decodeCostStaticConstructor color constructor
        let sourceArguments ← decodeCostStaticPatternList color arguments
        pure (.apply sourceConstructor sourceArguments)
    | .lambda binderName body => do
        let sourceBody ← decodeCostStaticPattern color body
        pure (.lambda binderName sourceBody)
    | .multiLambda arity binderNames body => do
        let sourceBody ← decodeCostStaticPattern color body
        pure (.multiLambda arity binderNames sourceBody)
    | .subst body replacement => do
        let sourceBody ← decodeCostStaticPattern color body
        let sourceReplacement ← decodeCostStaticPattern color replacement
        pure (.subst sourceBody sourceReplacement)
    | .collection collectionType elements rest => do
        let sourceElements ← decodeCostStaticPatternList color elements
        pure (.collection collectionType sourceElements rest)

  /-- Pointwise decoder used by `decodeCostStaticPattern`. -/
  def decodeCostStaticPatternList (color : CostStaticColor) :
      List Pattern → Option (List Pattern)
    | [] => some []
    | pattern :: patterns => do
        let sourcePattern ← decodeCostStaticPattern color pattern
        let sourcePatterns ← decodeCostStaticPatternList color patterns
        pure (sourcePattern :: sourcePatterns)
end

/-- Encoding a source pattern into either generated static namespace and
decoding it again is the identity. -/
@[simp]
theorem decodeCostStaticPattern_mapPattern (source : CIGSLT)
    (color : CostStaticColor) (pattern : Pattern) :
    decodeCostStaticPattern color
        (mapPattern (color.symbols source) pattern) =
      some pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [mapPattern, decodeCostStaticPattern]
  | hfvar name => simp [mapPattern, decodeCostStaticPattern]
  | happly constructor arguments inductionHypothesis =>
      have decodeArguments :
          decodeCostStaticPatternList color
              (arguments.map (mapPattern (color.symbols source))) =
            some arguments := by
        induction arguments with
        | nil => rfl
        | cons argument arguments listInduction =>
            simp only [List.map_cons, decodeCostStaticPatternList]
            rw [inductionHypothesis argument (by simp)]
            rw [listInduction]
            · rfl
            · intro other membership
              exact inductionHypothesis other (by simp [membership])
      simp [mapPattern, decodeCostStaticPattern, decodeArguments,
        decodeCostStaticConstructor]
  | hlambda binderName body inductionHypothesis =>
      simp [mapPattern, decodeCostStaticPattern, inductionHypothesis]
  | hmultiLambda arity binderNames body inductionHypothesis =>
      simp [mapPattern, decodeCostStaticPattern, inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [mapPattern, decodeCostStaticPattern, bodyInduction,
        replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      have decodeElements :
          decodeCostStaticPatternList color
              (elements.map (mapPattern (color.symbols source))) =
            some elements := by
        induction elements with
        | nil => rfl
        | cons element elements listInduction =>
            simp only [List.map_cons, decodeCostStaticPatternList]
            rw [inductionHypothesis element (by simp)]
            rw [listInduction]
            · rfl
            · intro other membership
              exact inductionHypothesis other (by simp [membership])
      simp [mapPattern, decodeCostStaticPattern, decodeElements]

/-- Successful decoding followed by the selected static embedding reconstructs
the encoded pattern. -/
theorem mapPattern_decodeCostStaticPattern (source : CIGSLT)
    (color : CostStaticColor) (pattern decoded : Pattern)
    (success : decodeCostStaticPattern color pattern = some decoded) :
    mapPattern (color.symbols source) decoded = pattern := by
  induction pattern using Pattern.inductionOn generalizing decoded with
  | hbvar index =>
      simp [decodeCostStaticPattern] at success
      subst decoded
      simp [mapPattern]
  | hfvar name =>
      simp [decodeCostStaticPattern] at success
      subst decoded
      simp [mapPattern]
  | happly constructor arguments inductionHypothesis =>
      simp only [decodeCostStaticPattern] at success
      cases constructorResult :
          decodeCostStaticConstructor color constructor with
      | none => simp [constructorResult] at success
      | some sourceConstructor =>
          cases argumentsResult :
              decodeCostStaticPatternList color arguments with
          | none => simp [constructorResult, argumentsResult] at success
          | some sourceArguments =>
              simp [constructorResult, argumentsResult] at success
              subst decoded
              have constructorEquality :
                  (color.symbols source).constructor sourceConstructor =
                    constructor := by
                rw [CostStaticColor.symbols_constructor]
                exact (decodeCostStaticConstructor_eq_some_iff
                  color constructor sourceConstructor).mp constructorResult |>.symm
              have argumentsEquality :
                  sourceArguments.map (mapPattern (color.symbols source)) =
                    arguments := by
                induction arguments generalizing sourceArguments with
                | nil =>
                    simp [decodeCostStaticPatternList] at argumentsResult
                    subst sourceArguments
                    rfl
                | cons argument arguments listInduction =>
                    simp only [decodeCostStaticPatternList] at argumentsResult
                    cases headResult :
                        decodeCostStaticPattern color argument with
                    | none => simp [headResult] at argumentsResult
                    | some sourceArgument =>
                        cases tailResult :
                            decodeCostStaticPatternList color arguments with
                        | none =>
                            simp [headResult, tailResult] at argumentsResult
                        | some sourceArgumentsTail =>
                            simp [headResult, tailResult] at argumentsResult
                            subst sourceArguments
                            simp only [List.map_cons, List.cons.injEq]
                            constructor
                            · exact inductionHypothesis argument (by simp)
                                sourceArgument headResult
                            · exact listInduction
                                (fun other membership =>
                                  inductionHypothesis other (by simp [membership]))
                                sourceArgumentsTail tailResult
              simp only [mapPattern, mapPatternList_eq_map]
              rw [constructorEquality, argumentsEquality]
  | hlambda binderName body inductionHypothesis =>
      simp only [decodeCostStaticPattern] at success
      cases bodyResult : decodeCostStaticPattern color body with
      | none => simp [bodyResult] at success
      | some sourceBody =>
          simp [bodyResult] at success
          subst decoded
          simp [mapPattern, inductionHypothesis sourceBody bodyResult]
  | hmultiLambda arity binderNames body inductionHypothesis =>
      simp only [decodeCostStaticPattern] at success
      cases bodyResult : decodeCostStaticPattern color body with
      | none => simp [bodyResult] at success
      | some sourceBody =>
          simp [bodyResult] at success
          subst decoded
          simp [mapPattern, inductionHypothesis sourceBody bodyResult]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [decodeCostStaticPattern] at success
      cases bodyResult : decodeCostStaticPattern color body with
      | none => simp [bodyResult] at success
      | some sourceBody =>
          cases replacementResult :
              decodeCostStaticPattern color replacement with
          | none => simp [bodyResult, replacementResult] at success
          | some sourceReplacement =>
              simp [bodyResult, replacementResult] at success
              subst decoded
              simp [mapPattern, bodyInduction sourceBody bodyResult,
                replacementInduction sourceReplacement replacementResult]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [decodeCostStaticPattern] at success
      cases elementsResult : decodeCostStaticPatternList color elements with
      | none => simp [elementsResult] at success
      | some sourceElements =>
          simp [elementsResult] at success
          subst decoded
          have elementsEquality :
              sourceElements.map (mapPattern (color.symbols source)) =
                elements := by
            induction elements generalizing sourceElements with
            | nil =>
                simp [decodeCostStaticPatternList] at elementsResult
                subst sourceElements
                rfl
            | cons element elements listInduction =>
                simp only [decodeCostStaticPatternList] at elementsResult
                cases headResult : decodeCostStaticPattern color element with
                | none => simp [headResult] at elementsResult
                | some sourceElement =>
                    cases tailResult :
                        decodeCostStaticPatternList color elements with
                    | none => simp [headResult, tailResult] at elementsResult
                    | some sourceElementsTail =>
                        simp [headResult, tailResult] at elementsResult
                        subst sourceElements
                        simp only [List.map_cons, List.cons.injEq]
                        constructor
                        · exact inductionHypothesis element (by simp)
                            sourceElement headResult
                        · exact listInduction
                            (fun other membership =>
                              inductionHypothesis other (by simp [membership]))
                            sourceElementsTail tailResult
          simp [mapPattern, elementsEquality]

/-- The uniform embedding into either generated static namespace is
injective on raw patterns.  This follows from the executable left inverse,
not from an assumed property of reserved names. -/
theorem mapPattern_costStatic_injective (source : CIGSLT)
    (color : CostStaticColor) :
    Function.Injective (mapPattern (color.symbols source)) := by
  intro left right equality
  have decoded := congrArg (decodeCostStaticPattern color) equality
  simpa using decoded

/-! ## Transport of non-left-linear matches -/

/-- Transport a source matcher environment into the collision-free schema
namespace of one generated static copy.  Values undergo only the structural
constructor translation; their free names remain concrete data. -/
def mapCostStaticBindings (source : CIGSLT) (color : CostStaticColor) :
    Mettapedia.OSLF.MeTTaIL.Match.Bindings →
      Mettapedia.OSLF.MeTTaIL.Match.Bindings :=
  List.map fun entry =>
    (costSourceSchemaName entry.1,
      mapPattern (color.symbols source) entry.2)

@[simp]
theorem mapCostStaticBindings_nil (source : CIGSLT)
    (color : CostStaticColor) :
    mapCostStaticBindings source color [] = [] :=
  rfl

@[simp]
theorem mapCostStaticBindings_cons (source : CIGSLT)
    (color : CostStaticColor) (name : String) (value : Pattern)
    (bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings) :
    mapCostStaticBindings source color ((name, value) :: bindings) =
      (costSourceSchemaName name,
        mapPattern (color.symbols source) value) ::
          mapCostStaticBindings source color bindings :=
  rfl

/-- Looking up a renamed key in the transported environment is exactly
source lookup followed by constructor translation. -/
theorem find?_mapCostStaticBindings (source : CIGSLT)
    (color : CostStaticColor)
    (bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings) (name : String) :
    (mapCostStaticBindings source color bindings).find?
        (fun entry => entry.1 == costSourceSchemaName name) =
      (bindings.find? (fun entry => entry.1 == name)).map
        (fun entry =>
          (costSourceSchemaName entry.1,
            mapPattern (color.symbols source) entry.2)) := by
  induction bindings with
  | nil => rfl
  | cons entry bindings inductionHypothesis =>
      rcases entry with ⟨entryName, entryValue⟩
      by_cases equality : entryName = name
      · subst entryName
        simp [mapCostStaticBindings]
      · have mappedInequality :
            costSourceSchemaName entryName ≠ costSourceSchemaName name :=
          fun mappedEquality =>
            equality (costSourceSchemaName_injective mappedEquality)
        simpa [mapCostStaticBindings, equality, mappedInequality] using
          inductionHypothesis

/-- One step of binding merge commutes with the static Cost encoding.  The
injectivity argument in the repeated-variable branch is the reason this is
stated separately from the fold theorem below. -/
theorem mergeBindingStep_mapCostStaticBindings (source : CIGSLT)
    (color : CostStaticColor)
    (left : Mettapedia.OSLF.MeTTaIL.Match.Bindings)
    (name : String) (value : Pattern) :
    (Mettapedia.OSLF.MeTTaIL.Match.mergeBindings left [(name, value)]).map
        (mapCostStaticBindings source color) =
      Mettapedia.OSLF.MeTTaIL.Match.mergeBindings
        (mapCostStaticBindings source color left)
        [(costSourceSchemaName name,
          mapPattern (color.symbols source) value)] := by
  unfold Mettapedia.OSLF.MeTTaIL.Match.mergeBindings
  simp only [List.foldlM_cons, List.foldlM_nil, Option.bind_eq_bind]
  have lookup := find?_mapCostStaticBindings source color left name
  cases found : left.find? (fun entry => entry.1 == name) with
  | none =>
      rw [found] at lookup
      simp only [Option.map_none] at lookup
      rw [lookup]
      simp [mapCostStaticBindings]
  | some existingEntry =>
      rcases existingEntry with ⟨existingName, existingValue⟩
      rw [found] at lookup
      simp only [Option.map_some] at lookup
      rw [lookup]
      by_cases equality : existingValue = value
      · subst existingValue
        simp
      · have mappedInequality :
            mapPattern (color.symbols source) existingValue ≠
              mapPattern (color.symbols source) value :=
          fun mappedEquality =>
            equality (mapPattern_costStatic_injective source color
              mappedEquality)
        simp [equality, mappedInequality]

/-- Binding merge commutes with the injective schema and constructor maps.
This is the load-bearing non-left-linear case: repeated metavariables are
compared after transport without gaining or losing a match. -/
theorem mergeBindings_mapCostStaticBindings (source : CIGSLT)
    (color : CostStaticColor)
    (left right : Mettapedia.OSLF.MeTTaIL.Match.Bindings) :
    (Mettapedia.OSLF.MeTTaIL.Match.mergeBindings left right).map
        (mapCostStaticBindings source color) =
      Mettapedia.OSLF.MeTTaIL.Match.mergeBindings
        (mapCostStaticBindings source color left)
        (mapCostStaticBindings source color right) := by
  induction right generalizing left with
  | nil => simp [Mettapedia.OSLF.MeTTaIL.Match.mergeBindings]
  | cons entry right inductionHypothesis =>
      rcases entry with ⟨name, value⟩
      unfold Mettapedia.OSLF.MeTTaIL.Match.mergeBindings
      rw [mapCostStaticBindings_cons, List.foldlM_cons, List.foldlM_cons]
      have lookup := find?_mapCostStaticBindings source color left name
      cases found : left.find? (fun entry => entry.1 == name) with
      | none =>
          rw [found] at lookup
          simp only [Option.map_none] at lookup
          simp only [found, lookup]
          simpa [Mettapedia.OSLF.MeTTaIL.Match.mergeBindings] using
            inductionHypothesis ((name, value) :: left)
      | some existingEntry =>
          rcases existingEntry with ⟨existingName, existingValue⟩
          rw [found] at lookup
          simp only [Option.map_some] at lookup
          by_cases equality : existingValue = value
          · subst existingValue
            simp only [found, lookup, beq_self_eq_true, if_true]
            simpa [Mettapedia.OSLF.MeTTaIL.Match.mergeBindings] using
              inductionHypothesis left
          · have mappedInequality :
                mapPattern (color.symbols source) existingValue ≠
                  mapPattern (color.symbols source) value :=
              fun mappedEquality =>
                equality (mapPattern_costStatic_injective source color
                  mappedEquality)
            simp [found, lookup, equality, mappedInequality]

/-- Translate an authored matcher pattern into one static Cost copy.  Schema
variables and constructor symbols occupy independent injective namespaces. -/
def mapCostStaticSchemaPattern (source : CIGSLT)
    (color : CostStaticColor) (pattern : Pattern) : Pattern :=
  mapPatternSchemaNames costSourceSchemaName
    (mapPattern (color.symbols source) pattern)

/-- The authored equation declaration selected by one generated static
fiber. -/
def costStaticEquationDecl (source : CIGSLT) (color : CostStaticColor)
    (equation : Equation) : Equation :=
  match color with
  | .base => costBaseEquationDecl equation
  | .wrapped => costWrappedEquationDecl source.theory equation

@[simp]
theorem costStaticEquationDecl_left (source : CIGSLT)
    (color : CostStaticColor) (equation : Equation) :
    (costStaticEquationDecl source color equation).left =
      mapCostStaticSchemaPattern source color equation.left := by
  cases color <;>
    rfl

@[simp]
theorem costStaticEquationDecl_right (source : CIGSLT)
    (color : CostStaticColor) (equation : Equation) :
    (costStaticEquationDecl source color equation).right =
      mapCostStaticSchemaPattern source color equation.right := by
  cases color <;>
    rfl

@[simp]
theorem costStaticEquationDecl_premises (source : CIGSLT)
    (color : CostStaticColor) (equation : Equation)
    (premiseFree : equation.premises = []) :
    (costStaticEquationDecl source color equation).premises = [] := by
  cases color <;>
    simp [costStaticEquationDecl, costBaseEquationDecl,
      costWrappedEquationDecl, costBaseEquation, costWrappedEquation,
      mapEquationSchemaNames, mapEquation, premiseFree]

/-- Either color image of an authored source equation belongs to the exact
generated static equation list. -/
theorem costStaticEquationDecl_mem (source : CIGSLT)
    (color : CostStaticColor) (equation : Equation)
    (membership : equation ∈
      source.theory.presentation.presentation.language.equations) :
    costStaticEquationDecl source color equation ∈
      source.costStaticEquations := by
  cases color with
  | base =>
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨equation, membership, rfl⟩
  | wrapped =>
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨equation, membership, rfl⟩

/-- Every equation declaration in the generated Cost theory comes from one
authored source equation in exactly one of the two static embeddings.  This
is the declaration-level colour-homogeneity boundary; a mixed-colour equation
cannot enter through a third generator family. -/
theorem mem_costStaticEquations_iff_exists_source
    (source : CIGSLT) {target : Equation} :
    target ∈ source.costStaticEquations ↔
      ∃ color sourceEquation,
        sourceEquation ∈
            source.theory.presentation.presentation.language.equations ∧
          target = costStaticEquationDecl source color sourceEquation := by
  rw [CIGSLT.costStaticEquations, List.mem_append]
  constructor
  · rintro (baseMembership | wrappedMembership)
    · obtain ⟨sourceEquation, membership, equality⟩ :=
        List.mem_map.mp baseMembership
      exact ⟨.base, sourceEquation, membership, by
        simpa [costStaticEquationDecl] using equality.symm⟩
    · obtain ⟨sourceEquation, membership, equality⟩ :=
        List.mem_map.mp wrappedMembership
      exact ⟨.wrapped, sourceEquation, membership, by
        simpa [costStaticEquationDecl] using equality.symm⟩
  · rintro ⟨color, sourceEquation, membership, rfl⟩
    cases color with
    | base =>
        exact Or.inl (List.mem_map.mpr
          ⟨sourceEquation, membership, rfl⟩)
    | wrapped =>
        exact Or.inr (List.mem_map.mpr
          ⟨sourceEquation, membership, rfl⟩)

/-- The authored reflective declaration selected by one generated static
fiber.  This is the same structural image already present in the generated
`LanguageDef`; it introduces no second reflective theory. -/
def costStaticReflectivePresentationDecl (source : CIGSLT)
    (color : CostStaticColor)
    (declaration : ReflectivePresentationDecl) : ReflectivePresentationDecl :=
  match color with
  | .base => costBaseReflectivePresentationDecl declaration
  | .wrapped =>
      costWrappedReflectivePresentationDecl source.theory declaration

@[simp]
theorem costStaticReflectivePresentationDecl_eq_map
    (source : CIGSLT) (color : CostStaticColor)
    (declaration : ReflectivePresentationDecl) :
    costStaticReflectivePresentationDecl source color declaration =
      mapReflectivePresentation (color.symbols source) declaration := by
  cases color <;> rfl

/-- Either color image of an authored reflective declaration belongs to the
exact generated static presentation list. -/
theorem costStaticReflectivePresentationDecl_mem (source : CIGSLT)
    (color : CostStaticColor)
    (declaration : ReflectivePresentationDecl)
    (membership : declaration ∈
      source.theory.presentation.presentation.language.reflectivePresentations) :
    costStaticReflectivePresentationDecl source color declaration ∈
      source.costStaticReflectivePresentations := by
  cases color with
  | base =>
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨declaration, membership, rfl⟩
  | wrapped =>
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨declaration, membership, rfl⟩

/-- Every generated reflective presentation is likewise one exact coloured
image of an authored declaration.  Together with the equation inversion
above, this exhausts the two generator forms used by static normalization. -/
theorem mem_costStaticReflectivePresentations_iff_exists_source
    (source : CIGSLT) {target : ReflectivePresentationDecl} :
    target ∈ source.costStaticReflectivePresentations ↔
      ∃ color sourceDeclaration,
        sourceDeclaration ∈ source.theory.presentation.presentation.language.reflectivePresentations ∧
          target = costStaticReflectivePresentationDecl source color
            sourceDeclaration := by
  rw [CIGSLT.costStaticReflectivePresentations, List.mem_append]
  constructor
  · rintro (baseMembership | wrappedMembership)
    · obtain ⟨sourceDeclaration, membership, equality⟩ :=
        List.mem_map.mp baseMembership
      exact ⟨.base, sourceDeclaration, membership, by
        simpa [costStaticReflectivePresentationDecl] using equality.symm⟩
    · obtain ⟨sourceDeclaration, membership, equality⟩ :=
        List.mem_map.mp wrappedMembership
      exact ⟨.wrapped, sourceDeclaration, membership, by
        simpa [costStaticReflectivePresentationDecl] using equality.symm⟩
  · rintro ⟨color, sourceDeclaration, membership, rfl⟩
    cases color with
    | base =>
        exact Or.inl (List.mem_map.mpr
          ⟨sourceDeclaration, membership, rfl⟩)
    | wrapped =>
        exact Or.inr (List.mem_map.mpr
          ⟨sourceDeclaration, membership, rfl⟩)

@[simp]
theorem mapCostStaticSchemaPattern_bvar (source : CIGSLT)
    (color : CostStaticColor) (index : Nat) :
    mapCostStaticSchemaPattern source color (.bvar index) = .bvar index :=
  by simp [mapCostStaticSchemaPattern, mapPatternSchemaNames, mapPattern]

@[simp]
theorem mapCostStaticSchemaPattern_fvar (source : CIGSLT)
    (color : CostStaticColor) (name : String) :
    mapCostStaticSchemaPattern source color (.fvar name) =
      .fvar (costSourceSchemaName name) :=
  by simp [mapCostStaticSchemaPattern, mapPatternSchemaNames, mapPattern]

@[simp]
theorem mapCostStaticSchemaPattern_apply (source : CIGSLT)
    (color : CostStaticColor) (constructor : String)
    (arguments : List Pattern) :
    mapCostStaticSchemaPattern source color (.apply constructor arguments) =
      .apply ((color.symbols source).constructor constructor)
        (arguments.map (mapCostStaticSchemaPattern source color)) := by
  simp [mapCostStaticSchemaPattern, mapPattern, mapPatternSchemaNames,
    mapPatternListSchemaNames_eq_map, Function.comp_def, List.map_map]

@[simp]
theorem mapCostStaticSchemaPattern_lambda (source : CIGSLT)
    (color : CostStaticColor) (binder : Option String) (body : Pattern) :
    mapCostStaticSchemaPattern source color (.lambda binder body) =
      .lambda (binder.map costSourceSchemaName)
        (mapCostStaticSchemaPattern source color body) :=
  by simp [mapCostStaticSchemaPattern, mapPatternSchemaNames, mapPattern]

@[simp]
theorem mapCostStaticSchemaPattern_multiLambda (source : CIGSLT)
    (color : CostStaticColor) (arity : Nat) (binders : List String)
    (body : Pattern) :
    mapCostStaticSchemaPattern source color
        (.multiLambda arity binders body) =
      .multiLambda arity (binders.map costSourceSchemaName)
        (mapCostStaticSchemaPattern source color body) :=
  by simp [mapCostStaticSchemaPattern, mapPatternSchemaNames, mapPattern]

@[simp]
theorem mapCostStaticSchemaPattern_subst (source : CIGSLT)
    (color : CostStaticColor) (body replacement : Pattern) :
    mapCostStaticSchemaPattern source color (.subst body replacement) =
      .subst (mapCostStaticSchemaPattern source color body)
        (mapCostStaticSchemaPattern source color replacement) :=
  by simp [mapCostStaticSchemaPattern, mapPatternSchemaNames, mapPattern]

@[simp]
theorem mapCostStaticSchemaPattern_collection (source : CIGSLT)
    (color : CostStaticColor) (collectionType : CollType)
    (elements : List Pattern) (rest : Option String) :
    mapCostStaticSchemaPattern source color
        (.collection collectionType elements rest) =
      .collection collectionType
        (elements.map (mapCostStaticSchemaPattern source color))
        (rest.map costSourceSchemaName) := by
  simp [mapCostStaticSchemaPattern, mapPattern, mapPatternSchemaNames,
    mapPatternListSchemaNames_eq_map, Function.comp_def, List.map_map]

mutual
  /-- Structural measure shared by the mutually recursive matcher proofs. -/
  private def matchPatternMeasure : Pattern → Nat
    | .bvar _ | .fvar _ => 1
    | .apply _ arguments => 1 + matchPatternListMeasure arguments
    | .lambda _ body | .multiLambda _ _ body => 1 + matchPatternMeasure body
    | .subst body replacement =>
        1 + matchPatternMeasure body + matchPatternMeasure replacement
    | .collection _ elements _ => 1 + matchPatternListMeasure elements

  /-- List companion to `matchPatternMeasure`. -/
  private def matchPatternListMeasure : List Pattern → Nat
    | [] => 0
    | pattern :: patterns =>
        1 + matchPatternMeasure pattern + matchPatternListMeasure patterns
end

mutual
  /-- Relational matching is preserved by the static Cost embedding,
  including the equality-sensitive repeated-variable cases. -/
  theorem matchRel_mapCostStatic (source : CIGSLT)
      (color : CostStaticColor) {pattern term : Pattern}
      {bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings}
      (derivation : Mettapedia.OSLF.MeTTaIL.MatchSpec.MatchRel
        pattern term bindings) :
      Mettapedia.OSLF.MeTTaIL.MatchSpec.MatchRel
        (mapCostStaticSchemaPattern source color pattern)
        (mapPattern (color.symbols source) term)
        (mapCostStaticBindings source color bindings) := by
    cases derivation with
    | fvar =>
        simp only [mapCostStaticSchemaPattern_fvar, mapCostStaticBindings]
        exact .fvar
    | bvar =>
        simp only [mapCostStaticSchemaPattern_bvar, mapPattern,
          mapCostStaticBindings]
        exact .bvar
    | apply arguments lengthEquality =>
        simp only [mapCostStaticSchemaPattern_apply, mapPattern,
          mapPatternList_eq_map]
        exact Mettapedia.OSLF.MeTTaIL.MatchSpec.MatchRel.apply
          (matchArgsRel_mapCostStatic source color arguments)
          (by simpa using lengthEquality)
    | lambda body =>
        simp only [mapCostStaticSchemaPattern_lambda, mapPattern]
        exact .lambda (matchRel_mapCostStatic source color body)
    | multiLambda body =>
        simp only [mapCostStaticSchemaPattern_multiLambda, mapPattern]
        exact .multiLambda (matchRel_mapCostStatic source color body)
    | collection bag =>
        simp only [mapCostStaticSchemaPattern_collection, mapPattern,
          mapPatternList_eq_map]
        exact .collection (matchBagRel_mapCostStatic source color bag)
    | subst body replacement mergeEquality =>
        simp only [mapCostStaticSchemaPattern_subst, mapPattern]
        have mappedMerge := congrArg
          (Option.map (mapCostStaticBindings source color)) mergeEquality
        rw [mergeBindings_mapCostStaticBindings] at mappedMerge
        apply Mettapedia.OSLF.MeTTaIL.MatchSpec.MatchRel.subst
          (matchRel_mapCostStatic source color body)
          (matchRel_mapCostStatic source color replacement)
        simpa using mappedMerge
  termination_by 3 * matchPatternMeasure pattern + 2
  decreasing_by
    all_goals
      (subst_vars
       simp [matchPatternMeasure] <;> omega)

  /-- Pairwise argument matching is preserved by the static Cost embedding. -/
  theorem matchArgsRel_mapCostStatic (source : CIGSLT)
      (color : CostStaticColor) {patterns terms : List Pattern}
      {bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings}
      (derivation : Mettapedia.OSLF.MeTTaIL.MatchSpec.MatchArgsRel
        patterns terms bindings) :
      Mettapedia.OSLF.MeTTaIL.MatchSpec.MatchArgsRel
        (patterns.map (mapCostStaticSchemaPattern source color))
        (terms.map (mapPattern (color.symbols source)))
        (mapCostStaticBindings source color bindings) := by
    cases derivation with
    | nil => exact .nil
    | cons head tail mergeEquality =>
        have mappedMerge := congrArg
          (Option.map (mapCostStaticBindings source color)) mergeEquality
        rw [mergeBindings_mapCostStaticBindings] at mappedMerge
        apply Mettapedia.OSLF.MeTTaIL.MatchSpec.MatchArgsRel.cons
          (matchRel_mapCostStatic source color head)
          (matchArgsRel_mapCostStatic source color tail)
        simpa using mappedMerge
  termination_by 3 * matchPatternListMeasure patterns + 1
  decreasing_by
    all_goals
      (subst_vars
       simp [matchPatternListMeasure] <;> omega)

  /-- Collection matching is preserved without changing its nondeterministic
  choice of an occurrence. -/
  theorem matchBagRel_mapCostStatic (source : CIGSLT)
      (color : CostStaticColor) {patterns : List Pattern}
      {rest : Option String} {collectionType : CollType}
      {terms : List Pattern}
      {bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings}
      (derivation : Mettapedia.OSLF.MeTTaIL.MatchSpec.MatchBagRel
        patterns rest collectionType terms bindings) :
      Mettapedia.OSLF.MeTTaIL.MatchSpec.MatchBagRel
        (patterns.map (mapCostStaticSchemaPattern source color))
        (rest.map costSourceSchemaName) collectionType
        (terms.map (mapPattern (color.symbols source)))
        (mapCostStaticBindings source color bindings) := by
    cases derivation with
    | nilNoRest => exact .nilNoRest
    | nilRest =>
        simp only [List.map_nil, Option.map_some, mapCostStaticBindings,
          List.map_cons, mapPattern, mapPatternList_eq_map]
        exact .nilRest
    | cons index indexBound head tail mergeEquality =>
        have mappedMerge := congrArg
          (Option.map (mapCostStaticBindings source color)) mergeEquality
        rw [mergeBindings_mapCostStaticBindings] at mappedMerge
        exact Mettapedia.OSLF.MeTTaIL.MatchSpec.MatchBagRel.cons index
          (by simpa using indexBound)
          (by simpa using matchRel_mapCostStatic source color head)
          (by simpa only [List.eraseIdx_map] using
            matchBagRel_mapCostStatic source color tail)
          (by simpa using mappedMerge)
  termination_by 3 * matchPatternListMeasure patterns
  decreasing_by
    all_goals
      (subst_vars
       simp [matchPatternListMeasure] <;> omega)
end

/-! ## Match coverage of schema metavariables -/

/-- A matcher environment assigns every free schema metavariable occurring
in one pattern.  The exact `find?` result is retained because subsequent
binding merges preserve that result definitionally. -/
def BindingsCoverPattern
    (bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings)
    (pattern : Pattern) : Prop :=
  ∀ name ∈ pattern.freeFvarNames,
    ∃ value, bindings.find? (fun entry => entry.1 == name) =
      some (name, value)

/-- List companion to `BindingsCoverPattern`, stated over the flattened
free-variable occurrence list used by the authored validator. -/
def BindingsCoverPatterns
    (bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings)
    (patterns : List Pattern) : Prop :=
  ∀ name ∈ patterns.flatMap Pattern.freeFvarNames,
    ∃ value, bindings.find? (fun entry => entry.1 == name) =
      some (name, value)

mutual
  /-- Every relational match binds every free metavariable of its pattern
  side, including repeated variables whose equal values survive merging. -/
  theorem matchRel_coversPattern {pattern term : Pattern}
      {bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings}
      (derivation : Mettapedia.OSLF.MeTTaIL.MatchSpec.MatchRel
        pattern term bindings) :
      BindingsCoverPattern bindings pattern := by
    intro name membership
    cases derivation with
    | fvar =>
        simp only [Pattern.freeFvarNames, List.mem_singleton] at membership
        subst name
        exact ⟨term, by simp⟩
    | bvar => simp [Pattern.freeFvarNames] at membership
    | apply arguments _ =>
        exact matchArgsRel_coversPatterns arguments name
          (by simpa [Pattern.freeFvarNames] using membership)
    | lambda body =>
        exact matchRel_coversPattern body name
          (by simpa [Pattern.freeFvarNames] using membership)
    | multiLambda body =>
        exact matchRel_coversPattern body name
          (by simpa [Pattern.freeFvarNames] using membership)
    | collection bag =>
        exact matchBagRel_coversPatterns bag name
          (by simpa [Pattern.freeFvarNames] using membership)
    | subst body replacement mergeEquality =>
        simp only [Pattern.freeFvarNames, List.mem_append] at membership
        rcases membership with bodyMembership | replacementMembership
        · rcases matchRel_coversPattern body name bodyMembership with
            ⟨value, found⟩
          exact ⟨value,
            Mettapedia.OSLF.MeTTaIL.MatchSpec.mergeBindings_subsumed_left
              mergeEquality found⟩
        · rcases matchRel_coversPattern replacement name
            replacementMembership with ⟨value, found⟩
          exact ⟨value,
            Mettapedia.OSLF.MeTTaIL.MatchSpec.mergeBindings_subsumed_right
              mergeEquality found⟩
  termination_by 3 * matchPatternMeasure pattern + 2
  decreasing_by
    all_goals
      (subst_vars
       simp [matchPatternMeasure] <;> omega)

  /-- Argument matching covers the flattened free-variable occurrences in
  every pattern argument. -/
  theorem matchArgsRel_coversPatterns {patterns terms : List Pattern}
      {bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings}
      (derivation : Mettapedia.OSLF.MeTTaIL.MatchSpec.MatchArgsRel
        patterns terms bindings) :
      BindingsCoverPatterns bindings patterns := by
    intro name membership
    cases derivation with
    | nil => simp at membership
    | cons head tail mergeEquality =>
        simp only [List.flatMap_cons, List.mem_append] at membership
        rcases membership with headMembership | tailMembership
        · rcases matchRel_coversPattern head name headMembership with
            ⟨value, found⟩
          exact ⟨value,
            Mettapedia.OSLF.MeTTaIL.MatchSpec.mergeBindings_subsumed_left
              mergeEquality found⟩
        · rcases matchArgsRel_coversPatterns tail name tailMembership with
            ⟨value, found⟩
          exact ⟨value,
            Mettapedia.OSLF.MeTTaIL.MatchSpec.mergeBindings_subsumed_right
              mergeEquality found⟩
  termination_by 3 * matchPatternListMeasure patterns + 1
  decreasing_by
    all_goals
      (subst_vars
       simp [matchPatternListMeasure] <;> omega)

  /-- Bag matching covers both its explicitly matched elements and its open
  tail.  The tail constructor records the unmatched occurrence multiset as
  a collection binding of the exact authored kind. -/
  theorem matchBagRel_coversPatterns {patterns : List Pattern}
      {rest : Option String} {collectionType : CollType}
      {terms : List Pattern}
      {bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings}
      (derivation : Mettapedia.OSLF.MeTTaIL.MatchSpec.MatchBagRel
        patterns rest collectionType terms bindings) :
      ∀ name ∈ patterns.flatMap Pattern.freeFvarNames ++ rest.toList,
        ∃ value, bindings.find? (fun entry => entry.1 == name) =
          some (name, value) := by
    intro name membership
    cases derivation with
    | nilNoRest => simp at membership
    | nilRest =>
        simp only [List.flatMap_nil, List.nil_append, Option.toList_some,
          List.mem_singleton] at membership
        subst name
        exact ⟨.collection collectionType terms none, by simp⟩
    | cons index indexBound head tail mergeEquality =>
        simp only [List.flatMap_cons, List.append_assoc,
          List.mem_append] at membership
        rcases membership with headMembership | tailMembership
        · rcases matchRel_coversPattern head name headMembership with
            ⟨value, found⟩
          exact ⟨value,
            Mettapedia.OSLF.MeTTaIL.MatchSpec.mergeBindings_subsumed_left
              mergeEquality found⟩
        · rcases matchBagRel_coversPatterns tail name
            (by simpa [List.mem_append] using tailMembership) with
            ⟨value, found⟩
          exact ⟨value,
            Mettapedia.OSLF.MeTTaIL.MatchSpec.mergeBindings_subsumed_right
              mergeEquality found⟩
  termination_by 3 * matchPatternListMeasure patterns
  decreasing_by
    all_goals
      (subst_vars
       simp [matchPatternListMeasure] <;> omega)
end

/-! ## Instantiation naturality of the stable schema fragment -/

/-- Constructor translation commutes with de Bruijn lifting.  This is the
binder-sensitive ingredient of explicit-substitution transport. -/
theorem mapPattern_liftBVars (symbols : PresentationSymbols)
    (cutoff shift : Nat) (pattern : Pattern) :
    mapPattern symbols (liftBVars cutoff shift pattern) =
      liftBVars cutoff shift (mapPattern symbols pattern) := by
  induction pattern using Pattern.inductionOn generalizing cutoff with
  | hbvar index =>
      by_cases shifted : index ≥ cutoff <;>
        simp [liftBVars, mapPattern, shifted]
  | hfvar name => simp [mapPattern, liftBVars]
  | happly constructor arguments inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map, liftBVars, List.map_map]
      congr 1
      apply List.map_congr_left
      intro argument membership
      exact inductionHypothesis argument membership cutoff
  | hlambda binder body inductionHypothesis =>
      simp [mapPattern, liftBVars, inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [mapPattern, liftBVars, inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [mapPattern, liftBVars, bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map, liftBVars, List.map_map]
      congr 1
      apply List.map_congr_left
      intro element membership
      exact inductionHypothesis element membership cutoff

/-- Constructor translation commutes with elimination of one locally
nameless binder, including the lift performed beneath nested binders. -/
theorem mapPattern_instantiateBVarAt (symbols : PresentationSymbols)
    (depth : Nat) (replacement body : Pattern) :
    mapPattern symbols (instantiateBVarAt depth replacement body) =
      instantiateBVarAt depth (mapPattern symbols replacement)
        (mapPattern symbols body) := by
  induction body using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      by_cases below : index < depth
      · simp [instantiateBVarAt, mapPattern, below]
      · by_cases equal : index = depth
        · subst index
          simp [instantiateBVarAt, mapPattern, mapPattern_liftBVars]
        · simp [instantiateBVarAt, mapPattern, below, equal]
  | hfvar name => simp [instantiateBVarAt, mapPattern]
  | happly constructor arguments inductionHypothesis =>
      simp only [instantiateBVarAt, mapPattern, mapPatternList_eq_map,
        List.map_map]
      congr 1
      apply List.map_congr_left
      intro argument membership
      exact inductionHypothesis argument membership depth
  | hlambda binder body inductionHypothesis =>
      simp [instantiateBVarAt, mapPattern, inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [instantiateBVarAt, mapPattern, inductionHypothesis]
  | hsubst body nestedReplacement bodyInduction replacementInduction =>
      simp [instantiateBVarAt, mapPattern, bodyInduction,
        replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [instantiateBVarAt, mapPattern, mapPatternList_eq_map,
        List.map_map]
      congr 1
      apply List.map_congr_left
      intro element membership
      exact inductionHypothesis element membership depth

@[simp]
theorem mapPattern_instantiateBVar (symbols : PresentationSymbols)
    (replacement body : Pattern) :
    mapPattern symbols (instantiateBVar replacement body) =
      instantiateBVar (mapPattern symbols replacement)
        (mapPattern symbols body) := by
  exact mapPattern_instantiateBVarAt symbols 0 replacement body

/-- On stable, fully covered schemas, gradual binding application commutes
exactly with the generated Cost namespace.  This theorem exposes both
otherwise-hidden failure modes: uncovered metavariables and open collection
tails. -/
theorem applyBindings_mapCostStatic (source : CIGSLT)
    (color : CostStaticColor) (bindings : Bindings) (pattern : Pattern)
    (stable : schemaInstantiationStable pattern = true)
    (covered : BindingsCoverPattern bindings pattern) :
    applyBindings (mapCostStaticBindings source color bindings)
        (mapCostStaticSchemaPattern source color pattern) =
      mapPattern (color.symbols source) (applyBindings bindings pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [applyBindings, mapPattern]
  | hfvar name =>
      rcases covered name (by simp [Pattern.freeFvarNames]) with
        ⟨value, found⟩
      have mappedFound := find?_mapCostStaticBindings source color bindings name
      rw [found] at mappedFound
      simp only [Option.map_some] at mappedFound
      simp [applyBindings, found, mappedFound]
  | happly constructor arguments inductionHypothesis =>
      have argumentsStable : schemaListInstantiationStable arguments = true := by
        simpa [schemaInstantiationStable, schemaListInstantiationStable,
          Pattern.hasCanonicalBinderMetadata, schemaHasNoCollectionRest]
          using stable
      simp only [mapCostStaticSchemaPattern_apply, applyBindings, mapPattern,
        mapPatternList_eq_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro argument membership
      apply inductionHypothesis argument membership
      · exact schemaInstantiationStable_of_mem argumentsStable membership
      · intro name nameMembership
        apply covered name
        simp only [Pattern.freeFvarNames, List.mem_flatMap]
        exact ⟨argument, membership, nameMembership⟩
  | hlambda binder body inductionHypothesis =>
      cases binder with
      | none =>
          have bodyStable : schemaInstantiationStable body = true := by
            simpa [schemaInstantiationStable, Pattern.hasCanonicalBinderMetadata,
              schemaHasNoCollectionRest] using stable
          simp only [mapCostStaticSchemaPattern_lambda, Option.map_none,
            applyBindings, mapPattern]
          congr 1
          exact inductionHypothesis bodyStable
            (by simpa [BindingsCoverPattern, Pattern.freeFvarNames] using covered)
      | some binderName =>
          simp [schemaInstantiationStable, Pattern.hasCanonicalBinderMetadata]
            at stable
  | hmultiLambda arity binders body inductionHypothesis =>
      cases binders with
      | nil =>
          have bodyStable : schemaInstantiationStable body = true := by
            simpa [schemaInstantiationStable, Pattern.hasCanonicalBinderMetadata,
              schemaHasNoCollectionRest] using stable
          simp only [mapCostStaticSchemaPattern_multiLambda, List.map_nil,
            applyBindings, mapPattern]
          congr 1
          exact inductionHypothesis bodyStable
            (by simpa [BindingsCoverPattern, Pattern.freeFvarNames] using covered)
      | cons binderName binders =>
          simp [schemaInstantiationStable, Pattern.hasCanonicalBinderMetadata]
            at stable
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [schemaInstantiationStable, Pattern.hasCanonicalBinderMetadata,
        schemaHasNoCollectionRest, Bool.and_eq_true] at stable
      have bodyStable : schemaInstantiationStable body = true := by
        simp only [schemaInstantiationStable, Bool.and_eq_true]
        exact ⟨stable.1.1, stable.2.1⟩
      have replacementStable : schemaInstantiationStable replacement = true := by
        simp only [schemaInstantiationStable, Bool.and_eq_true]
        exact ⟨stable.1.2, stable.2.2⟩
      have bodyCovered : BindingsCoverPattern bindings body := by
        intro name membership
        apply covered name
        simp [Pattern.freeFvarNames, membership]
      have replacementCovered : BindingsCoverPattern bindings replacement := by
        intro name membership
        apply covered name
        simp [Pattern.freeFvarNames, membership]
      simp only [mapCostStaticSchemaPattern_subst, applyBindings]
      rw [bodyInduction bodyStable bodyCovered,
        replacementInduction replacementStable replacementCovered,
        mapPattern_instantiateBVar]
  | hcollection collectionType elements rest inductionHypothesis =>
      cases rest with
      | none =>
          have elementsStable :
              schemaListInstantiationStable elements = true := by
            simpa [schemaInstantiationStable, schemaListInstantiationStable,
              Pattern.hasCanonicalBinderMetadata,
              schemaHasNoCollectionRest] using stable
          simp only [mapCostStaticSchemaPattern_collection, Option.map_none,
            applyBindings, mapPattern, mapPatternList_eq_map, List.map_map,
            List.append_nil]
          congr 1
          apply List.map_congr_left
          intro element membership
          apply inductionHypothesis element membership
          · exact schemaInstantiationStable_of_mem elementsStable membership
          · intro name nameMembership
            apply covered name
            simp only [Pattern.freeFvarNames, Option.toList_none,
              List.append_nil, List.mem_flatMap]
            exact ⟨element, membership, nameMembership⟩
      | some restName =>
          simp [schemaInstantiationStable, schemaHasNoCollectionRest] at stable

/-- One premise-free source equation instance transports to either generated
static Cost fiber.  Matching, repeated-variable equality, schema coverage,
and binder-eliminating substitution are all transported by the preceding
independent lemmas; no generated equation is validated against itself. -/
theorem equationInstanceAt_mapCostStatic (source : CIGSLT)
    (color : CostStaticColor) {fuel : Nat} {input output : Pattern}
    (derivation : EquationSemantics.EquationInstanceAt defaultBasePremises
      source.theory.presentation.presentation.language fuel input output) :
    EquationSemantics.EquationInstanceAt defaultBasePremises
      source.costWholeLanguage fuel
      (mapPattern (color.symbols source) input)
      (mapPattern (color.symbols source) output) := by
  cases derivation with
  | @forward equation _ _ initialBindings finalBindings equationMembership
      matchMembership premises application =>
      have retypable :=
        source.equationsRetypable equation equationMembership
      rw [retypable.premiseFree] at premises
      cases premises with
      | nil =>
          have sourceMatch :=
            Mettapedia.OSLF.MeTTaIL.MatchSpec.matchPattern_sound
              matchMembership
          have mappedMatch := matchRel_mapCostStatic source color sourceMatch
          have mappedMatchMembership :=
            Mettapedia.OSLF.MeTTaIL.MatchSpec.matchRel_complete mappedMatch
          have leftCovered := matchRel_coversPattern sourceMatch
          have rightCovered :
              BindingsCoverPattern initialBindings equation.right := by
            intro name rightMembership
            apply leftCovered name
            simpa [LanguageDef.patternFvarNames_nil] using
              rightFvar_mem_left_of_validatedEquation_noPremises
                source.theory.presentation.presentation.language
                source.theory.presentation.presentation.valid equation
                equationMembership retypable.premiseFree name
                (by simpa [LanguageDef.patternFvarNames_nil] using
                  rightMembership)
          apply EquationSemantics.EquationInstanceAt.forward
              (equation := costStaticEquationDecl source color equation)
              (initialBindings :=
                mapCostStaticBindings source color initialBindings)
              (finalBindings :=
                mapCostStaticBindings source color initialBindings)
          · change costStaticEquationDecl source color equation ∈
              source.costStaticEquations
            exact costStaticEquationDecl_mem source color equation
              equationMembership
          · simpa only [costStaticEquationDecl_left] using
              mappedMatchMembership
          · rw [costStaticEquationDecl_premises _ _ _
              retypable.premiseFree]
            exact .nil _
          · rw [costStaticEquationDecl_right]
            calc
              applyBindings
                    (mapCostStaticBindings source color initialBindings)
                    (mapCostStaticSchemaPattern source color equation.right) =
                  mapPattern (color.symbols source)
                    (applyBindings initialBindings equation.right) :=
                applyBindings_mapCostStatic source color initialBindings
                  equation.right retypable.rightInstantiationStable
                  rightCovered
              _ = mapPattern (color.symbols source) output :=
                congrArg (mapPattern (color.symbols source)) application

  | @reverse equation _ _ initialBindings finalBindings equationMembership
      matchMembership premises application =>
      have retypable :=
        source.equationsRetypable equation equationMembership
      rw [retypable.premiseFree] at premises
      cases premises with
      | nil =>
          have sourceMatch :=
            Mettapedia.OSLF.MeTTaIL.MatchSpec.matchPattern_sound
              matchMembership
          have mappedMatch := matchRel_mapCostStatic source color sourceMatch
          have mappedMatchMembership :=
            Mettapedia.OSLF.MeTTaIL.MatchSpec.matchRel_complete mappedMatch
          have rightCovered := matchRel_coversPattern sourceMatch
          have leftCovered :
              BindingsCoverPattern initialBindings equation.left := by
            intro name leftMembership
            apply rightCovered name
            exact LanguageDef.equation_leftFvar_mem_right_of_executionFlowErrors_eq_nil
              source.theory.presentation.presentation.language
              source.theory.executionProfile.relationModes
              source.sourceExecutionFlowErrors_eq_nil equation
              equationMembership retypable.premiseFree name leftMembership
          apply EquationSemantics.EquationInstanceAt.reverse
              (equation := costStaticEquationDecl source color equation)
              (initialBindings :=
                mapCostStaticBindings source color initialBindings)
              (finalBindings :=
                mapCostStaticBindings source color initialBindings)
          · change costStaticEquationDecl source color equation ∈
              source.costStaticEquations
            exact costStaticEquationDecl_mem source color equation
              equationMembership
          · simpa only [costStaticEquationDecl_right] using
              mappedMatchMembership
          · rw [costStaticEquationDecl_premises _ _ _
              retypable.premiseFree]
            exact .nil _
          · rw [costStaticEquationDecl_left]
            calc
              applyBindings
                    (mapCostStaticBindings source color initialBindings)
                    (mapCostStaticSchemaPattern source color equation.left) =
                  mapPattern (color.symbols source)
                    (applyBindings initialBindings equation.left) :=
                applyBindings_mapCostStatic source color initialBindings
                  equation.left retypable.leftInstantiationStable leftCovered
              _ = mapPattern (color.symbols source) output :=
                congrArg (mapPattern (color.symbols source)) application

/-- Existential premise depth is preserved by either generated static
embedding. -/
theorem equationInstance_mapCostStatic (source : CIGSLT)
    (color : CostStaticColor) {input output : Pattern}
    (derivation : EquationSemantics.EquationInstance defaultBasePremises
      source.theory.presentation.presentation.language input output) :
    EquationSemantics.EquationInstance defaultBasePremises
      source.costWholeLanguage
      (mapPattern (color.symbols source) input)
      (mapPattern (color.symbols source) output) := by
  rcases derivation with ⟨fuel, derivation⟩
  exact ⟨fuel, equationInstanceAt_mapCostStatic source color derivation⟩

private theorem mapPattern_filter_ne_parallelUnit_costStatic
    (source : CIGSLT) (color : CostStaticColor)
    (declaration : ReflectivePresentationDecl) : ∀ patterns : List Pattern,
    (patterns.filter fun pattern =>
        pattern ≠ .apply declaration.parallelUnitConstructor []).map
        (mapPattern (color.symbols source)) =
      (patterns.map (mapPattern (color.symbols source))).filter fun pattern =>
        pattern ≠ .apply
          ((color.symbols source).constructor
            declaration.parallelUnitConstructor) []
  | [] => rfl
  | pattern :: patterns => by
      have mappedUnit :
          mapPattern (color.symbols source)
              (.apply declaration.parallelUnitConstructor []) =
              .apply
              ((color.symbols source).constructor
                declaration.parallelUnitConstructor) [] := by
        simp [mapPattern]
      by_cases isUnit :
          pattern = .apply declaration.parallelUnitConstructor []
      · subst pattern
        have sourceDecision :
            decide
                (Pattern.apply declaration.parallelUnitConstructor [] ≠
                  Pattern.apply declaration.parallelUnitConstructor []) = false := by
          simp
        have targetDecision :
            decide
                (mapPattern (color.symbols source)
                    (.apply declaration.parallelUnitConstructor []) ≠
                  .apply ((color.symbols source).constructor
                    declaration.parallelUnitConstructor) []) = false := by
          rw [mappedUnit]
          simp
        simp only [List.filter_cons, List.map_cons]
        rw [sourceDecision, targetDecision]
        simpa using
          (mapPattern_filter_ne_parallelUnit_costStatic source color
            declaration patterns)
      · have mappedNotUnit :
            mapPattern (color.symbols source) pattern ≠
              .apply
                ((color.symbols source).constructor
                  declaration.parallelUnitConstructor) [] := by
          rw [← mappedUnit]
          exact (mapPattern_costStatic_injective source color).ne isUnit
        have sourceDecision :
            decide
                (pattern ≠
                  .apply declaration.parallelUnitConstructor []) = true := by
          simp [isUnit]
        have targetDecision :
            decide
                (mapPattern (color.symbols source) pattern ≠
                  .apply ((color.symbols source).constructor
                    declaration.parallelUnitConstructor) []) = true := by
          simpa using mappedNotUnit
        simp only [List.filter_cons, List.map_cons]
        rw [sourceDecision, targetDecision]
        exact congrArg (List.cons (mapPattern (color.symbols source) pattern))
          (mapPattern_filter_ne_parallelUnit_costStatic source color
            declaration patterns)

private theorem mapPattern_parallelSplice_costStatic
    (source : CIGSLT) (color : CostStaticColor)
    (declaration : ReflectivePresentationDecl) (pattern : Pattern) :
    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice
        declaration pattern).map (mapPattern (color.symbols source)) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice
        (costStaticReflectivePresentationDecl source color declaration)
        (mapPattern (color.symbols source) pattern) := by
  cases pattern <;> try simp [
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice, mapPattern]
  case collection collectionType elements rest =>
    cases rest with
    | some restName =>
        simp [mapPattern]
    | none =>
        by_cases isParallel :
            collectionType = declaration.parallelCollection
        · subst collectionType
          simp [mapReflectivePresentation]
        · simp [mapPattern, isParallel, mapReflectivePresentation]

private theorem mapPattern_parallelContents_costStatic
    (source : CIGSLT) (color : CostStaticColor)
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern) :
    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents
        declaration patterns).map (mapPattern (color.symbols source)) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents
        (costStaticReflectivePresentationDecl source color declaration)
        (patterns.map (mapPattern (color.symbols source))) := by
  unfold Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents
  simp only [costStaticReflectivePresentationDecl_eq_map,
    mapReflectivePresentation]
  rw [mapPattern_filter_ne_parallelUnit_costStatic]
  rw [List.map_flatMap, List.flatMap_map]
  apply congrArg
  apply List.flatMap_congr
  intro pattern membership
  simpa [costStaticReflectivePresentationDecl_eq_map,
    mapReflectivePresentation] using
      (mapPattern_parallelSplice_costStatic source color declaration pattern)

private theorem normalizeParallelElements_costStatic_perm
    (source : CIGSLT) (color : CostStaticColor)
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern) :
    List.Perm
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements
        (costStaticReflectivePresentationDecl source color declaration)
        (patterns.map (mapPattern (color.symbols source))))
      ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements
        declaration patterns).map (mapPattern (color.symbols source))) := by
  rw [normalizeParallelElements_eq_sort_parallelContents,
    normalizeParallelElements_eq_sort_parallelContents]
  let targetContents :=
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents
      (costStaticReflectivePresentationDecl source color declaration)
      (patterns.map (mapPattern (color.symbols source)))
  let sourceContents :=
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents
      declaration patterns
  have contentsEquality :
      targetContents =
        sourceContents.map (mapPattern (color.symbols source)) :=
    (mapPattern_parallelContents_costStatic source color declaration
      patterns).symm
  exact
    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.sortPatterns_perm
      targetContents).trans
      ((List.Perm.of_eq contentsEquality).trans
        ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.sortPatterns_perm
          sourceContents |>.map
            (mapPattern (color.symbols source))).symm))

private theorem mapPattern_collapseParallel_costStatic
    (source : CIGSLT) (color : CostStaticColor)
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern) :
    mapPattern (color.symbols source)
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
          declaration patterns) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
        (costStaticReflectivePresentationDecl source color declaration)
        (patterns.map (mapPattern (color.symbols source))) := by
  cases patterns with
  | nil =>
      simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel,
        mapPattern, costStaticReflectivePresentationDecl_eq_map,
        mapReflectivePresentation]
  | cons first remaining =>
      cases remaining with
      | nil => rfl
      | cons second tail =>
          simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel,
            mapPattern, costStaticReflectivePresentationDecl_eq_map,
            mapReflectivePresentation]

/-- Mapping into one static Cost fiber does not change the reflective
canonical equivalence class.  The target canonicalizer may choose a different
deterministic order after constructor tagging, so the statement deliberately
re-canonicalizes the mapped source representative instead of claiming that
sorting commutes syntactically with the symbol map. -/
theorem canonicalize_costStatic_factor (source : CIGSLT)
    (color : CostStaticColor)
    (declaration : ReflectivePresentationDecl)
    (membership : declaration ∈
      source.theory.presentation.presentation.language.reflectivePresentations)
    (pattern : Pattern) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        (costStaticReflectivePresentationDecl source color declaration)
        (mapPattern (color.symbols source) pattern) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        (costStaticReflectivePresentationDecl source color declaration)
        (mapPattern (color.symbols source)
          (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
            declaration pattern)) := by
  have declarationValid :=
    LanguageDef.reflectivePresentation_validate_of_validate_eq_nil
      source.theory.presentation.presentation.language
      source.theory.presentation.presentation.valid declaration membership
  have quote_ne_drop :=
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.quoteConstructor_ne_dropConstructor_of_validate
      source.theory.presentation.presentation.language declaration declarationValid
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly constructor arguments inductionHypothesis =>
      have listFactor :
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
              (costStaticReflectivePresentationDecl source color declaration)
              (arguments.map (mapPattern (color.symbols source))) =
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
              (costStaticReflectivePresentationDecl source color declaration)
              ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                declaration arguments).map
                  (mapPattern (color.symbols source))) := by
        induction arguments with
        | nil => rfl
        | cons argument arguments listInduction =>
            simp only [List.map_cons,
              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList]
            rw [inductionHypothesis argument (by simp)]
            apply congrArg₂ List.cons rfl
            apply listInduction
            intro other membership
            exact inductionHypothesis other (by simp [membership])
      simp only [mapPattern, mapPatternList_eq_map,
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
      rw [listFactor]
      by_cases isQuote : constructor = declaration.quoteConstructor
      · subst constructor
        generalize normalizedEquality :
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
              declaration arguments = normalizedArguments at *
        by_cases collapses : ∃ name,
            normalizedArguments =
              [.apply declaration.dropConstructor [name]]
        · obtain ⟨name, normalizedArgumentsEquality⟩ := collapses
          subst normalizedArguments
          rw [normalizedArgumentsEquality]
          have mappedQuoteNeDrop :
              color.constructorTag ++ declaration.quoteConstructor ≠
                color.constructorTag ++ declaration.dropConstructor := by
            intro equality
            exact quote_ne_drop
              ((String.append_right_inj color.constructorTag).mp equality)
          have mappedDropNeQuote :
              color.constructorTag ++ declaration.dropConstructor ≠
                color.constructorTag ++ declaration.quoteConstructor :=
            Ne.symm mappedQuoteNeDrop
          simp only [costStaticReflectivePresentationDecl_eq_map,
            mapReflectivePresentation]
          simp [mapPattern,
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
            Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
            CostStaticColor.symbols_constructor, mappedDropNeQuote]
        · have sourceDoesNotCollapse :
              Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
                  declaration declaration.quoteConstructor normalizedArguments =
                .apply declaration.quoteConstructor normalizedArguments := by
            unfold Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
            simp only [beq_self_eq_true, if_true]
            cases normalizedArguments with
            | nil => rfl
            | cons first remaining =>
                cases remaining with
                | nil =>
                    cases first with
                    | apply nestedConstructor nestedArguments =>
                        cases nestedArguments with
                        | nil => rfl
                        | cons name tail =>
                            cases tail with
                            | nil =>
                                by_cases isDrop :
                                    nestedConstructor = declaration.dropConstructor
                                · subst nestedConstructor
                                  exact False.elim
                                    (collapses ⟨name, rfl⟩)
                                · simp [isDrop]
                            | cons second tail => rfl
                    | bvar index => rfl
                    | fvar name => rfl
                    | lambda binder body => rfl
                    | multiLambda arity binders body => rfl
                    | subst body replacement => rfl
                    | collection collectionType elements rest => rfl
                | cons second tail => simp
          change _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
            _ (mapPattern _
              (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
                declaration declaration.quoteConstructor normalizedArguments))
          rw [sourceDoesNotCollapse]
          simp only [mapPattern, mapPatternList_eq_map,
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
      · have mappedNotQuote :
            (color.symbols source).constructor constructor ≠
              (color.symbols source).constructor
                declaration.quoteConstructor := by
          intro equality
          apply isQuote
          simpa [CostStaticColor.symbols_constructor] using equality
        simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
          isQuote, mapPattern,
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
  | hlambda binder body inductionHypothesis =>
      simp only [mapPattern,
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
      exact congrArg (Pattern.lambda binder) inductionHypothesis
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [mapPattern,
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
      exact congrArg (Pattern.multiLambda arity binders) inductionHypothesis
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [mapPattern,
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
      exact congrArg₂ Pattern.subst bodyInduction replacementInduction
  | hcollection collectionType elements rest inductionHypothesis =>
      have listFactor :
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
              (costStaticReflectivePresentationDecl source color declaration)
              (elements.map (mapPattern (color.symbols source))) =
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
              (costStaticReflectivePresentationDecl source color declaration)
              ((Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                declaration elements).map
                  (mapPattern (color.symbols source))) := by
        induction elements with
        | nil => rfl
        | cons element elements listInduction =>
            simp only [List.map_cons,
              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList]
            rw [inductionHypothesis element (by simp)]
            apply congrArg₂ List.cons rfl
            apply listInduction
            intro other membership
            exact inductionHypothesis other (by simp [membership])
      cases rest with
      | some restName =>
          simp only [mapPattern, mapPatternList_eq_map,
            Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
          exact congrArg
            (fun normalized =>
              Pattern.collection collectionType normalized (some restName))
            listFactor
      | none =>
          by_cases isParallel :
              collectionType = declaration.parallelCollection
          · subst collectionType
            simp only [mapPattern, mapPatternList_eq_map,
              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
              beq_self_eq_true, if_true]
            rw [listFactor]
            simp only [costStaticReflectivePresentationDecl_eq_map,
              mapReflectivePresentation]
            simp only [beq_self_eq_true, if_true]
            let target :=
              mapReflectivePresentation (color.symbols source) declaration
            let sourceCanonical :=
              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList
                declaration elements
            let sourceNormalized :=
              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements
                declaration sourceCanonical
            calc
              _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize target
                    (.collection target.parallelCollection
                      (sourceCanonical.map
                        (mapPattern (color.symbols source))) none) := by
                  dsimp [target, sourceCanonical]
                  unfold mapReflectivePresentation
                  simp only [
                    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
                    beq_self_eq_true, if_true]
              _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize target
                    (.collection target.parallelCollection
                      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements
                        target
                        (sourceCanonical.map
                          (mapPattern (color.symbols source)))) none) :=
                  Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize_parallel_normalize_input
                    target _
              _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize target
                    (.collection target.parallelCollection
                      (sourceNormalized.map
                        (mapPattern (color.symbols source))) none) :=
                  Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize_parallel_permutation
                    target
                      (by
                        simpa [target,
                          costStaticReflectivePresentationDecl_eq_map] using
                            (normalizeParallelElements_costStatic_perm source color
                              declaration sourceCanonical))
              _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize target
                    (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
                      target
                      (sourceNormalized.map
                        (mapPattern (color.symbols source)))) :=
                  Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize_parallel_collapse
                    target _
              _ = Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize target
                    (mapPattern (color.symbols source)
                      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
                        declaration sourceNormalized)) := by
                  simpa [target,
                    costStaticReflectivePresentationDecl_eq_map] using
                      congrArg
                        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
                          target)
                        (mapPattern_collapseParallel_costStatic source color
                          declaration sourceNormalized).symm
          · have targetNotParallel :
                collectionType ≠
                  (costStaticReflectivePresentationDecl source color declaration).parallelCollection := by
              simpa [costStaticReflectivePresentationDecl_eq_map,
                mapReflectivePresentation] using isParallel
            simp only [mapPattern, mapPatternList_eq_map,
              Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize]
            rw [listFactor]
            simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
              mapPattern, isParallel,
              costStaticReflectivePresentationDecl_eq_map,
              mapReflectivePresentation]

/-- Equality of source reflective representatives survives either generated
static embedding.  The proof factors through target re-canonicalization, so
it remains valid when constructor tagging changes the target's deterministic
parallel order. -/
theorem canonicalize_eq_mapCostStatic (source : CIGSLT)
    (color : CostStaticColor)
    (declaration : ReflectivePresentationDecl)
    (membership : declaration ∈
      source.theory.presentation.presentation.language.reflectivePresentations)
    {left right : Pattern}
    (representatives :
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration left =
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration right) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        (costStaticReflectivePresentationDecl source color declaration)
        (mapPattern (color.symbols source) left) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        (costStaticReflectivePresentationDecl source color declaration)
        (mapPattern (color.symbols source) right) := by
  rw [canonicalize_costStatic_factor source color declaration membership left,
    canonicalize_costStatic_factor source color declaration membership right,
    representatives]

/-- Every source contextual equation generator maps to the corresponding
generator of the one authored Cost presentation. -/
theorem equationContextStep_mapCostStatic (source : CIGSLT)
    (color : CostStaticColor) {input output : Pattern}
    (derivation : EquationSemantics.EquationContextStep defaultBasePremises
      source.theory.presentation.presentation.language input output) :
    EquationSemantics.EquationContextStep defaultBasePremises
      source.costWholeLanguage
      (mapPattern (color.symbols source) input)
      (mapPattern (color.symbols source) output) := by
  cases derivation with
  | inContext context equationWitness =>
      rw [← CIGSLT.mapOneHoleContext_fill,
        ← CIGSLT.mapOneHoleContext_fill]
      exact EquationSemantics.EquationContextStep.inContext
        (CIGSLT.mapOneHoleContext (color.symbols source) context)
        (equationInstance_mapCostStatic source color equationWitness)
  | reflectiveInContext context membership representatives =>
      rw [← CIGSLT.mapOneHoleContext_fill,
        ← CIGSLT.mapOneHoleContext_fill]
      apply EquationSemantics.EquationContextStep.reflectiveInContext
        (CIGSLT.mapOneHoleContext (color.symbols source) context)
      · rw [CIGSLT.costWholeLanguage_reflectivePresentations]
        exact costStaticReflectivePresentationDecl_mem source color _ membership
      · exact canonicalize_eq_mapCostStatic source color _ membership
          representatives

/-- The entire least contextual equivalence generated by the source static
theory maps into the generated Cost equivalence. -/
theorem equationEquiv_mapCostStatic (source : CIGSLT)
    (color : CostStaticColor) {input output : Pattern}
    (derivation : EquationSemantics.EquationEquiv defaultBasePremises
      source.theory.presentation.presentation.language input output) :
    EquationSemantics.EquationEquiv defaultBasePremises
      source.costWholeLanguage
      (mapPattern (color.symbols source) input)
      (mapPattern (color.symbols source) output) := by
  exact EquationSemantics.equationEquiv_map_of_contextStep
    (mapPattern (color.symbols source))
    (fun step => Relation.EqvGen.rel _ _
      (equationContextStep_mapCostStatic source color step))
    derivation

/-! The authored canonicalization step itself transports through the Cost
symbol map.  This is intentionally weaker than substitution naturality: it
relates the two mapped terms in the generated Cost equation relation, while
leaving binder-sensitive reflective substitution for the typed M1 theorem. -/
theorem canonicalize_mapCostStatic_equationEquiv
    (source : CIGSLT) (color : CostStaticColor)
    {declaration : ReflectivePresentationDecl}
    (membership : List.Mem declaration
      source.theory.presentation.presentation.language.reflectivePresentations)
    (pattern : Pattern) :
    EquationSemantics.EquationEquiv defaultBasePremises
      source.costWholeLanguage
      (mapPattern (color.symbols source)
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          declaration pattern))
      (mapPattern (color.symbols source) pattern) := by
  exact equationEquiv_mapCostStatic source color
    (EquationSemantics.canonicalize_equationEquiv_self membership pattern)

/-! The target Cost canonicalizer also has its ordinary representative
equivalence on mapped terms.  Keeping this separate from the factorization
lemma above makes the two directions explicit for the later canonical-section
proof. -/
theorem costStatic_canonicalize_mapped_equationEquiv
    (source : CIGSLT) (color : CostStaticColor)
    {declaration : ReflectivePresentationDecl}
    (membership : List.Mem declaration
      source.theory.presentation.presentation.language.reflectivePresentations)
    (pattern : Pattern) :
    EquationSemantics.EquationEquiv defaultBasePremises
      source.costWholeLanguage
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        (costStaticReflectivePresentationDecl source color declaration)
        (mapPattern (color.symbols source) pattern))
      (mapPattern (color.symbols source) pattern) := by
  exact EquationSemantics.canonicalize_equationEquiv_self
    (costStaticReflectivePresentationDecl_mem source color _ membership) _

/-! The same transport is available for the typed open-fiber relation used
by the source canonical section.  This is the bridge needed by the unary Cost
normalization theorem; it does not erase the source typing proof or introduce
a second equation relation. -/

theorem openEquationSetoid_mapCostStatic (source : CIGSLT)
    (color : CostStaticColor)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    {left right : OpenTerm source.theory free bound sort}
    (derivation : (openEquationSetoid source.theory free bound sort).r left right) :
    EquationSemantics.EquationEquiv defaultBasePremises
      source.costWholeLanguage
      (mapPattern (color.symbols source) left.1)
      (mapPattern (color.symbols source) right.1) := by
  induction derivation with
  | rel left right step =>
      exact Relation.EqvGen.rel _ _
        (equationContextStep_mapCostStatic source color step)
  | refl term =>
      exact Relation.EqvGen.refl _
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

/-! ## Stable keys for opaque region boundaries -/

/-- A boundary is identified by its canonical content together with the
authored result type and the reflective binder support at which it may be
filled.  Content alone is insufficient: the same raw pattern at two sorts or
across two quotation supports is not one typed structural parameter. -/
structure CostRegionBoundary where
  /-- Type of the rigid placeholder presented to the source canonicalizer. -/
  type : TypeExpr
  /-- Binder support of that placeholder in the source open fiber. -/
  support : List TypeExpr
  /-- Exact type of the restored content in the generated Cost fiber.  This
  need not be the uniform static image of `type`: a boundary at a selected
  continuation is retyped by the authored interaction cut. -/
  targetType : TypeExpr
  /-- Exact binder support of the restored content in the Cost fiber. -/
  targetSupport : List TypeExpr
  content : Pattern
deriving Repr, DecidableEq

/-- A boundary together with the typing evidence needed to restore its
content in the selected Cost fiber.  The raw record remains the stable,
serializable key; this dependent layer certifies that its source type and
support are transported to the exact type and binder context inhabited by
the Cost term. -/
structure TypedCostRegionBoundary (source : CIGSLT)
    (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext) where
  boundary : CostRegionBoundary
  contentTyped : WellSorted.HasType source.costWholeLanguage targetFree
    boundary.targetSupport boundary.content boundary.targetType
  contentCanonicalBinderMetadata :
    boundary.content.hasCanonicalBinderMetadata = true
  contentObjectPattern :
    WellSorted.isObjectPattern boundary.content = true
  contentReflectiveScopeSafe :
    WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
      boundary.targetSupport.length boundary.content

/-- One occurrence of a maximal foreign region in a Cost static stratum.
`context` is traversal evidence only: filling it with `content` reconstructs
the surrounding root for occurrences emitted by the certified collector
below.  It is deliberately absent from `CostRegionBoundary`, whose semantic
identity remains type, reflective support, and canonical content. -/
structure CostRegionOccurrence where
  context : OneHoleContext
  content : Pattern
deriving Repr, DecidableEq

/-- Occurrence-sensitive assignment of semantic boundary data.  Different
occurrences may share a semantic boundary, but an assignment can no longer
conflate two equal raw patterns before inspecting their binder contexts. -/
abbrev CostRegionBoundaryAssignment :=
  CostRegionOccurrence → CostRegionBoundary

/-- Occurrence-sensitive typed boundaries for one normalization stratum. -/
abbrev TypedCostRegionBoundaryAssignment (source : CIGSLT)
    (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext) :=
  CostRegionOccurrence → TypedCostRegionBoundary source color targetFree

/-- Forget only the proof layer when feeding the existing occurrence-aware
collector and collision-free boundary codec. -/
def TypedCostRegionBoundaryAssignment.raw {source : CIGSLT}
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (boundary : TypedCostRegionBoundaryAssignment source color targetFree) :
    CostRegionBoundaryAssignment :=
  fun occurrence => (boundary occurrence).boundary

/-- Collision-free structural code for a typed, support-indexed boundary. -/
def CostRegionBoundary.code (boundary : CostRegionBoundary) : Nat :=
  Nat.pair (typeExprCode boundary.type)
    (Nat.pair (typeExprListCode boundary.support)
      (Nat.pair (typeExprCode boundary.targetType)
        (Nat.pair (typeExprListCode boundary.targetSupport)
          (patternCode boundary.content))))

/-- The boundary code retains type, support, and canonical content. -/
theorem CostRegionBoundary.code_injective :
    Function.Injective CostRegionBoundary.code := by
  intro left right equality
  simp only [CostRegionBoundary.code, Nat.pair_eq_pair] at equality
  cases left with
  | mk leftType leftSupport leftTargetType leftTargetSupport leftContent =>
      cases right with
      | mk rightType rightSupport rightTargetType rightTargetSupport
          rightContent =>
          simp only at equality
          have typeEquality : leftType = rightType :=
            typeExprCode_injective equality.1
          have supportEquality : leftSupport = rightSupport :=
            typeExprListCode_injective equality.2.1
          have targetTypeEquality : leftTargetType = rightTargetType :=
            typeExprCode_injective equality.2.2.1
          have targetSupportEquality :
              leftTargetSupport = rightTargetSupport :=
            typeExprListCode_injective equality.2.2.2.1
          have contentEquality : leftContent = rightContent :=
            patternCode_injective equality.2.2.2.2
          cases typeEquality
          cases supportEquality
          cases targetTypeEquality
          cases targetSupportEquality
          cases contentEquality
          rfl

/-- Original source parameters and generated boundary parameters occupy
disjoint namespaces before the source canonicalizer sees a region. -/
def costRegionSourceVariableTag : String := "$cost:region-source:"

def costRegionBoundaryVariableTag : String := "$cost:region-boundary:"

def costRegionSourceVariableName (name : String) : String :=
  costRegionSourceVariableTag ++ name

def costRegionBoundaryVariableName (boundary : CostRegionBoundary) : String :=
  costRegionBoundaryVariableTag ++ boundary.code.repr

theorem costRegionSourceVariableName_injective :
    Function.Injective costRegionSourceVariableName := by
  intro left right equality
  exact (String.append_right_inj costRegionSourceVariableTag).mp equality

theorem costRegionBoundaryVariableName_injective :
    Function.Injective costRegionBoundaryVariableName := by
  intro left right equality
  apply CostRegionBoundary.code_injective
  apply Nat.repr_injective
  exact (String.append_right_inj costRegionBoundaryVariableTag).mp equality

/-- A retagged source parameter can never be mistaken for an opaque
content-keyed boundary. -/
theorem costRegionSourceVariableName_ne_boundary
    (sourceName : String) (boundary : CostRegionBoundary) :
    costRegionSourceVariableName sourceName ≠
      costRegionBoundaryVariableName boundary := by
  intro equality
  have characterEquality := congrArg String.toList equality
  simp [costRegionSourceVariableName, costRegionSourceVariableTag,
    costRegionBoundaryVariableName, costRegionBoundaryVariableTag,
    String.toList_append] at characterEquality

/-- Recover one original free-variable name from the reserved region
namespace. -/
def decodeCostRegionSourceVariableName (name : String) : Option String :=
  decodeTaggedPayload costRegionSourceVariableTag name

@[simp]
theorem decodeCostRegionSourceVariableName_encode (name : String) :
    decodeCostRegionSourceVariableName (costRegionSourceVariableName name) =
      some name := by
  exact decodeTaggedPayload_append _ _

mutual
  /-- Retag only genuine free-variable positions before opaque boundary
  variables are added.  Locally nameless binder display metadata is retained;
  collection rests are free-variable positions and are therefore retagged. -/
  def retagCostRegionFreeVariables : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar (costRegionSourceVariableName name)
    | .apply constructor arguments =>
        .apply constructor (retagCostRegionFreeVariableList arguments)
    | .lambda binderName body =>
        .lambda binderName (retagCostRegionFreeVariables body)
    | .multiLambda arity binderNames body =>
        .multiLambda arity binderNames (retagCostRegionFreeVariables body)
    | .subst body replacement =>
        .subst (retagCostRegionFreeVariables body)
          (retagCostRegionFreeVariables replacement)
    | .collection collectionType elements rest =>
        .collection collectionType
          (retagCostRegionFreeVariableList elements)
          (rest.map costRegionSourceVariableName)

  def retagCostRegionFreeVariableList : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns =>
          retagCostRegionFreeVariables pattern ::
          retagCostRegionFreeVariableList patterns
end

/-- Retagging free variables preserves the representation form selected by
every authored parameter: ordinary, single-binder, and multi-binder nodes
retain their outer constructor exactly. -/
theorem matchesParameterRepresentation_retagCostRegionFreeVariables
    (parameter : TermParam) (pattern : Pattern) :
    WellSorted.MatchesParameterRepresentation parameter
        (retagCostRegionFreeVariables pattern) ↔
      WellSorted.MatchesParameterRepresentation parameter pattern := by
  cases parameter with
  | simple name type =>
      simp [WellSorted.MatchesParameterRepresentation]
  | abstractionNamed declaredBinder bodyName type =>
      cases pattern with
      | bvar index =>
          simp [WellSorted.MatchesParameterRepresentation,
            retagCostRegionFreeVariables]
      | fvar name =>
          simp [WellSorted.MatchesParameterRepresentation,
            retagCostRegionFreeVariables]
      | apply name arguments =>
          simp [WellSorted.MatchesParameterRepresentation,
            retagCostRegionFreeVariables]
      | lambda actualBinder body =>
          cases actualBinder <;>
            simp [WellSorted.MatchesParameterRepresentation,
              retagCostRegionFreeVariables]
      | multiLambda arity binders body =>
          simp [WellSorted.MatchesParameterRepresentation,
            retagCostRegionFreeVariables]
      | subst body replacement =>
          simp [WellSorted.MatchesParameterRepresentation,
            retagCostRegionFreeVariables]
      | collection collectionType elements rest =>
          simp [WellSorted.MatchesParameterRepresentation,
            retagCostRegionFreeVariables]
  | multiAbstractionNamed declaredBinders bodyName type =>
      cases pattern with
      | bvar index =>
          simp [WellSorted.MatchesParameterRepresentation,
            retagCostRegionFreeVariables]
      | fvar name =>
          simp [WellSorted.MatchesParameterRepresentation,
            retagCostRegionFreeVariables]
      | apply name arguments =>
          simp [WellSorted.MatchesParameterRepresentation,
            retagCostRegionFreeVariables]
      | lambda binder body =>
          simp [WellSorted.MatchesParameterRepresentation,
            retagCostRegionFreeVariables]
      | subst body replacement =>
          simp [WellSorted.MatchesParameterRepresentation,
            retagCostRegionFreeVariables]
      | collection collectionType elements rest =>
          simp [WellSorted.MatchesParameterRepresentation,
            retagCostRegionFreeVariables]
      | multiLambda arity actualBinders body =>
          cases actualBinders with
          | nil =>
              simp [WellSorted.MatchesParameterRepresentation,
                retagCostRegionFreeVariables]
          | cons binder binders =>
              simp [WellSorted.MatchesParameterRepresentation,
                retagCostRegionFreeVariables]

mutual
  /-- Injective source-name retagging preserves an existing typing derivation
whenever the target context provides the same type at every renamed lookup.
Constructor declarations and binder contexts are untouched. -/
  theorem WellSorted.HasType.retagCostRegionFreeVariables
      {language : LanguageDef}
      {sourceFree targetFree : WellSorted.FreeTypeContext}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : WellSorted.HasType language sourceFree bound pattern type)
      (mapsLookup : ∀ {name freeType},
        sourceFree name = some freeType →
          targetFree (costRegionSourceVariableName name) = some freeType) :
      WellSorted.HasType language targetFree bound
        (retagCostRegionFreeVariables pattern) type := by
    cases typed with
    | bvar lookup => exact .bvar lookup
    | fvar lookup => exact .fvar (mapsLookup lookup)
    | constructor membership notBare argumentsTyped =>
        exact .constructor membership notBare
          (argumentsTyped.retagCostRegionFreeVariables mapsLookup)
    | lambda bodyTyped =>
        exact .lambda (bodyTyped.retagCostRegionFreeVariables mapsLookup)
    | multiLambda bodyTyped =>
        exact .multiLambda
          (bodyTyped.retagCostRegionFreeVariables mapsLookup)
    | subst bodyTyped replacementTyped =>
        exact .subst
          (bodyTyped.retagCostRegionFreeVariables mapsLookup)
          (replacementTyped.retagCostRegionFreeVariables mapsLookup)
    | collection elementsTyped =>
        exact .collection
          (elementsTyped.retagCostRegionFreeVariables mapsLookup)
    | collectionConstructor membership parameterShape elementsTyped =>
        exact .collectionConstructor membership parameterShape
          (elementsTyped.retagCostRegionFreeVariables mapsLookup)

  /-- Ordered constructor-argument companion to free-name retagging. -/
  theorem WellSorted.ArgumentsHaveTypes.retagCostRegionFreeVariables
      {language : LanguageDef}
      {sourceFree targetFree : WellSorted.FreeTypeContext}
      {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (typed : WellSorted.ArgumentsHaveTypes language sourceFree bound
        arguments parameters)
      (mapsLookup : ∀ {name freeType},
        sourceFree name = some freeType →
          targetFree (costRegionSourceVariableName name) = some freeType) :
      WellSorted.ArgumentsHaveTypes language targetFree bound
        (retagCostRegionFreeVariableList arguments) parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation parameterType argumentTyped argumentsTyped =>
        exact .cons
          ((matchesParameterRepresentation_retagCostRegionFreeVariables
            _ _).2 representation) parameterType
          (argumentTyped.retagCostRegionFreeVariables mapsLookup)
          (argumentsTyped.retagCostRegionFreeVariables mapsLookup)

  /-- Collection-element companion to free-name retagging. -/
  theorem WellSorted.ElementsHaveType.retagCostRegionFreeVariables
      {language : LanguageDef}
      {sourceFree targetFree : WellSorted.FreeTypeContext}
      {bound : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (typed : WellSorted.ElementsHaveType language sourceFree bound
        elements elementType)
      (mapsLookup : ∀ {name freeType},
        sourceFree name = some freeType →
          targetFree (costRegionSourceVariableName name) = some freeType) :
      WellSorted.ElementsHaveType language targetFree bound
        (retagCostRegionFreeVariableList elements) elementType := by
    cases typed with
    | nil => exact .nil _ _
    | cons elementTyped elementsTyped =>
        exact .cons
          (elementTyped.retagCostRegionFreeVariables mapsLookup)
          (elementsTyped.retagCostRegionFreeVariables mapsLookup)
end

mutual
  /-- Declaration-aware constructor support is invariant under the hygienic
  free-name retagging used to isolate one Cost normalization stratum.  In
  particular, a bare collection keeps the authored constructor that typed it. -/
  theorem WellSorted.HasTypeWithConstructors.retagCostRegionFreeVariables
      {language : LanguageDef} {allowed : String → Prop}
      {sourceFree targetFree : WellSorted.FreeTypeContext}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : WellSorted.HasTypeWithConstructors language allowed sourceFree
        bound pattern type)
      (mapsLookup : ∀ {name freeType},
        sourceFree name = some freeType →
          targetFree (costRegionSourceVariableName name) = some freeType) :
      WellSorted.HasTypeWithConstructors language allowed targetFree bound
        (retagCostRegionFreeVariables pattern) type := by
    cases typed with
    | bvar lookup => exact .bvar lookup
    | fvar lookup => exact .fvar (mapsLookup lookup)
    | constructor allowedLabel membership notBare argumentsTyped =>
        exact .constructor allowedLabel membership notBare
          (argumentsTyped.retagCostRegionFreeVariables mapsLookup)
    | lambda bodyTyped =>
        exact .lambda (bodyTyped.retagCostRegionFreeVariables mapsLookup)
    | multiLambda bodyTyped =>
        exact .multiLambda
          (bodyTyped.retagCostRegionFreeVariables mapsLookup)
    | subst bodyTyped replacementTyped =>
        exact .subst
          (bodyTyped.retagCostRegionFreeVariables mapsLookup)
          (replacementTyped.retagCostRegionFreeVariables mapsLookup)
    | collection elementsTyped =>
        exact .collection
          (elementsTyped.retagCostRegionFreeVariables mapsLookup)
    | collectionConstructor allowedLabel membership parameterShape
        elementsTyped =>
        exact .collectionConstructor allowedLabel membership parameterShape
          (elementsTyped.retagCostRegionFreeVariables mapsLookup)

  /-- Ordered constructor-argument companion to typed free-name retagging. -/
  theorem WellSorted.ArgumentsHaveTypesWithConstructors.retagCostRegionFreeVariables
      {language : LanguageDef} {allowed : String → Prop}
      {sourceFree targetFree : WellSorted.FreeTypeContext}
      {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (typed : WellSorted.ArgumentsHaveTypesWithConstructors language allowed
        sourceFree bound arguments parameters)
      (mapsLookup : ∀ {name freeType},
        sourceFree name = some freeType →
          targetFree (costRegionSourceVariableName name) = some freeType) :
      WellSorted.ArgumentsHaveTypesWithConstructors language allowed targetFree
        bound (retagCostRegionFreeVariableList arguments) parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation parameterType argumentTyped argumentsTyped =>
        exact .cons
          ((matchesParameterRepresentation_retagCostRegionFreeVariables
            _ _).2 representation) parameterType
          (argumentTyped.retagCostRegionFreeVariables mapsLookup)
          (argumentsTyped.retagCostRegionFreeVariables mapsLookup)

  /-- Collection-element companion to typed free-name retagging. -/
  theorem WellSorted.ElementsHaveTypeWithConstructors.retagCostRegionFreeVariables
      {language : LanguageDef} {allowed : String → Prop}
      {sourceFree targetFree : WellSorted.FreeTypeContext}
      {bound : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (typed : WellSorted.ElementsHaveTypeWithConstructors language allowed
        sourceFree bound elements elementType)
      (mapsLookup : ∀ {name freeType},
        sourceFree name = some freeType →
          targetFree (costRegionSourceVariableName name) = some freeType) :
      WellSorted.ElementsHaveTypeWithConstructors language allowed targetFree
        bound (retagCostRegionFreeVariableList elements) elementType := by
    cases typed with
    | nil => exact .nil _ _
    | cons elementTyped elementsTyped =>
        exact .cons
          (elementTyped.retagCostRegionFreeVariables mapsLookup)
          (elementsTyped.retagCostRegionFreeVariables mapsLookup)
end

theorem retagCostRegionFreeVariableList_eq_map (patterns : List Pattern) :
    retagCostRegionFreeVariableList patterns =
      patterns.map retagCostRegionFreeVariables := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp [retagCostRegionFreeVariableList, inductionHypothesis]

/-- Hygienic free-variable retagging changes no constructor occurrence. -/
theorem constructorsWithin_retagCostRegionFreeVariables_iff
    (allowed : String → Prop) (pattern : Pattern) :
    ConstructorsWithin allowed (retagCostRegionFreeVariables pattern) ↔
      ConstructorsWithin allowed pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [retagCostRegionFreeVariables]
  | hfvar name => simp [retagCostRegionFreeVariables]
  | happly constructor arguments inductionHypothesis =>
      simp only [retagCostRegionFreeVariables, constructorsWithin_apply]
      constructor
      · rintro ⟨constructorAllowed, argumentsSupported⟩
        refine ⟨constructorAllowed, ?_⟩
        rw [constructorListWithin_iff_forall] at argumentsSupported ⊢
        intro argument membership
        exact (inductionHypothesis argument membership).mp
          (argumentsSupported
            (retagCostRegionFreeVariables argument) (by
              rw [retagCostRegionFreeVariableList_eq_map]
              exact List.mem_map.mpr ⟨argument, membership, rfl⟩))
      · rintro ⟨constructorAllowed, argumentsSupported⟩
        refine ⟨constructorAllowed, ?_⟩
        rw [constructorListWithin_iff_forall] at argumentsSupported ⊢
        intro retagged membership
        rw [retagCostRegionFreeVariableList_eq_map] at membership
        rcases List.mem_map.mp membership with ⟨argument, sourceMembership, rfl⟩
        exact (inductionHypothesis argument sourceMembership).mpr
          (argumentsSupported argument sourceMembership)
  | hlambda binder body inductionHypothesis =>
      simpa [retagCostRegionFreeVariables] using inductionHypothesis
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa [retagCostRegionFreeVariables] using inductionHypothesis
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp [retagCostRegionFreeVariables, bodyHypothesis,
        replacementHypothesis]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [retagCostRegionFreeVariables, constructorsWithin_collection]
      rw [constructorListWithin_iff_forall,
        constructorListWithin_iff_forall]
      constructor
      · intro supported element membership
        exact (inductionHypothesis element membership).mp
          (supported (retagCostRegionFreeVariables element) (by
            rw [retagCostRegionFreeVariableList_eq_map]
            exact List.mem_map.mpr ⟨element, membership, rfl⟩))
      · intro supported retagged membership
        rw [retagCostRegionFreeVariableList_eq_map] at membership
        rcases List.mem_map.mp membership with ⟨element, sourceMembership, rfl⟩
        exact (inductionHypothesis element sourceMembership).mpr
          (supported element sourceMembership)

/-- Retagging source metavariables changes no locally nameless binder
metadata. -/
@[simp]
theorem hasCanonicalBinderMetadata_retagCostRegionFreeVariables
    (pattern : Pattern) :
    (retagCostRegionFreeVariables pattern).hasCanonicalBinderMetadata =
      pattern.hasCanonicalBinderMetadata := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly constructor arguments inductionHypothesis =>
      simp only [retagCostRegionFreeVariables,
        Pattern.hasCanonicalBinderMetadata,
        retagCostRegionFreeVariableList_eq_map]
      induction arguments with
      | nil => rfl
      | cons argument arguments listInduction =>
          simp only [List.map_cons,
            Pattern.hasCanonicalBinderMetadataList]
          rw [inductionHypothesis argument (by simp)]
          apply congrArg (argument.hasCanonicalBinderMetadata && ·)
          apply listInduction
          intro other membership
          exact inductionHypothesis other (by simp [membership])
  | hlambda binder body inductionHypothesis =>
      simp [retagCostRegionFreeVariables, Pattern.hasCanonicalBinderMetadata,
        inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [retagCostRegionFreeVariables, Pattern.hasCanonicalBinderMetadata,
        inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [retagCostRegionFreeVariables, Pattern.hasCanonicalBinderMetadata,
        bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [retagCostRegionFreeVariables,
        Pattern.hasCanonicalBinderMetadata,
        retagCostRegionFreeVariableList_eq_map]
      induction elements with
      | nil => rfl
      | cons element elements listInduction =>
          simp only [List.map_cons,
            Pattern.hasCanonicalBinderMetadataList]
          rw [inductionHypothesis element (by simp)]
          apply congrArg (element.hasCanonicalBinderMetadata && ·)
          apply listInduction
          intro other membership
          exact inductionHypothesis other (by simp [membership])

/-- Retagging source metavariables neither introduces an explicit
substitution nor opens a collection tail. -/
@[simp]
theorem isObjectPattern_retagCostRegionFreeVariables (pattern : Pattern) :
    WellSorted.isObjectPattern (retagCostRegionFreeVariables pattern) =
      WellSorted.isObjectPattern pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly constructor arguments inductionHypothesis =>
      simp only [retagCostRegionFreeVariables, WellSorted.isObjectPattern,
        retagCostRegionFreeVariableList_eq_map]
      induction arguments with
      | nil => rfl
      | cons argument arguments listInduction =>
          simp only [List.map_cons, WellSorted.isObjectPatternList]
          rw [inductionHypothesis argument (by simp)]
          apply congrArg (WellSorted.isObjectPattern argument && ·)
          apply listInduction
          intro other membership
          exact inductionHypothesis other (by simp [membership])
  | hlambda binder body inductionHypothesis =>
      simpa [retagCostRegionFreeVariables, WellSorted.isObjectPattern]
        using inductionHypothesis
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa [retagCostRegionFreeVariables, WellSorted.isObjectPattern]
        using inductionHypothesis
  | hsubst body replacement bodyInduction replacementInduction =>
      rfl
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [retagCostRegionFreeVariables, WellSorted.isObjectPattern,
        Option.isNone_map, retagCostRegionFreeVariableList_eq_map]
      have listEquality :
          WellSorted.isObjectPatternList
              (elements.map retagCostRegionFreeVariables) =
            WellSorted.isObjectPatternList elements := by
        induction elements with
        | nil => rfl
        | cons element elements listInduction =>
            simp only [List.map_cons, WellSorted.isObjectPatternList]
            rw [inductionHypothesis element (by simp)]
            apply congrArg (WellSorted.isObjectPattern element && ·)
            apply listInduction
            intro other membership
            exact inductionHypothesis other (by simp [membership])
      rw [listEquality]

/-- Free-name retagging does not affect ordinary de Bruijn scope. -/
@[simp]
theorem isWellScopedAt_retagCostRegionFreeVariables
    (depth : Nat) (pattern : Pattern) :
    (retagCostRegionFreeVariables pattern).isWellScopedAt depth =
      pattern.isWellScopedAt depth := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly constructor arguments inductionHypothesis =>
      simp only [retagCostRegionFreeVariables, Pattern.isWellScopedAt,
        retagCostRegionFreeVariableList_eq_map]
      induction arguments with
      | nil => rfl
      | cons argument arguments listInduction =>
          simp only [List.map_cons, Pattern.isWellScopedListAt]
          rw [inductionHypothesis argument (by simp)]
          apply congrArg (argument.isWellScopedAt depth && ·)
          apply listInduction
          intro other membership otherDepth
          exact inductionHypothesis other (by simp [membership]) otherDepth
  | hlambda binder body inductionHypothesis =>
      simpa [retagCostRegionFreeVariables, Pattern.isWellScopedAt]
        using inductionHypothesis (depth + 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa [retagCostRegionFreeVariables, Pattern.isWellScopedAt]
        using inductionHypothesis (depth + arity)
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [retagCostRegionFreeVariables, Pattern.isWellScopedAt,
        bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [retagCostRegionFreeVariables, Pattern.isWellScopedAt,
        retagCostRegionFreeVariableList_eq_map]
      induction elements with
      | nil => rfl
      | cons element elements listInduction =>
          simp only [List.map_cons, Pattern.isWellScopedListAt]
          rw [inductionHypothesis element (by simp)]
          apply congrArg (element.isWellScopedAt depth && ·)
          apply listInduction
          intro other membership otherDepth
          exact inductionHypothesis other (by simp [membership]) otherDepth

/-- Free-name retagging also preserves every reflective quotation boundary;
quotation resets and binder increments depend only on term shape. -/
@[simp]
theorem binderSafeAt_retagCostRegionFreeVariables
    (quoteConstructor : String) (depth : Nat) (pattern : Pattern) :
    binderSafeAt quoteConstructor depth
        (retagCostRegionFreeVariables pattern) =
      binderSafeAt quoteConstructor depth pattern := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly constructor arguments inductionHypothesis =>
      have listEquality : ∀ localDepth,
          binderSafeListAt quoteConstructor localDepth
              (arguments.map retagCostRegionFreeVariables) =
            binderSafeListAt quoteConstructor localDepth arguments := by
        intro localDepth
        induction arguments with
        | nil => rfl
        | cons argument arguments listInduction =>
            simp only [List.map_cons, binderSafeListAt]
            rw [inductionHypothesis argument (by simp)]
            apply congrArg
              (binderSafeAt quoteConstructor localDepth argument && ·)
            apply listInduction
            intro other membership otherDepth
            exact inductionHypothesis other (by simp [membership]) otherDepth
      cases arguments with
      | nil => simp [retagCostRegionFreeVariables, binderSafeAt,
          retagCostRegionFreeVariableList_eq_map]
      | cons argument arguments =>
          cases arguments with
          | nil =>
              simp only [retagCostRegionFreeVariables,
                retagCostRegionFreeVariableList_eq_map, List.map_cons,
                List.map_nil, binderSafeAt]
              split
              · exact inductionHypothesis argument (by simp) 0
              · exact listEquality depth
          | cons second arguments =>
              simpa [retagCostRegionFreeVariables, binderSafeAt,
                retagCostRegionFreeVariableList_eq_map]
                using listEquality depth
  | hlambda binder body inductionHypothesis =>
      simpa [retagCostRegionFreeVariables, binderSafeAt]
        using inductionHypothesis (depth + 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      simpa [retagCostRegionFreeVariables, binderSafeAt]
        using inductionHypothesis (depth + arity)
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [retagCostRegionFreeVariables, binderSafeAt,
        bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [retagCostRegionFreeVariables, binderSafeAt,
        retagCostRegionFreeVariableList_eq_map]
      induction elements with
      | nil => rfl
      | cons element elements listInduction =>
          simp only [List.map_cons, binderSafeListAt]
          rw [inductionHypothesis element (by simp)]
          apply congrArg
            (binderSafeAt quoteConstructor depth element && ·)
          apply listInduction
          intro other membership otherDepth
          exact inductionHypothesis other (by simp [membership]) otherDepth

/-- The free typing fiber obtained by injectively retagging every source
metavariable.  Names outside the reserved source namespace are absent. -/
def retagCostRegionFreeContext
    (sourceFree : WellSorted.FreeTypeContext) :
    WellSorted.FreeTypeContext :=
  fun name =>
    (decodeCostRegionSourceVariableName name).bind sourceFree

@[simp]
theorem retagCostRegionFreeContext_source
    (sourceFree : WellSorted.FreeTypeContext) (name : String) :
    retagCostRegionFreeContext sourceFree
        (costRegionSourceVariableName name) = sourceFree name := by
  simp [retagCostRegionFreeContext]

/-- Transport a reflective binder-support assignment through the injective
source-variable namespace.  Names outside that namespace receive empty
support; typed normalized source regions cannot contain such names. -/
def retagCostRegionSupport (support : ContextSupport.Support) :
    ContextSupport.Support :=
  fun name =>
    (decodeCostRegionSourceVariableName name).map support |>.getD []

@[simp]
theorem retagCostRegionSupport_source
    (support : ContextSupport.Support) (name : String) :
    retagCostRegionSupport support (costRegionSourceVariableName name) =
      support name := by
  simp [retagCostRegionSupport]

/-- The generated three-motive recursor keeps the binder-image index shared
across a term, its argument spines, and its collection spines while free
variable names are retagged. -/
private theorem retagCostRegionFreeVariablesSupportAux
    {language : LanguageDef}
    {sourceFree targetFree : WellSorted.FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {typed : WellSorted.HasType language sourceFree bound pattern type}
    {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    (mapsLookup : ∀ {name freeType},
      sourceFree name = some freeType →
        targetFree (costRegionSourceVariableName name) = some freeType)
    (safe : typed.ReflectiveSupportSafeAt support available binderImage) :
    (typed.retagCostRegionFreeVariables mapsLookup).ReflectiveSupportSafeAt
      (retagCostRegionSupport support) available binderImage := by
  exact WellSorted.HasType.ReflectiveSupportSafeAt.rec
    (motive_1 := fun {bound pattern type} typed available currentImage _ =>
      (typed.retagCostRegionFreeVariables mapsLookup).ReflectiveSupportSafeAt
        (retagCostRegionSupport support) available currentImage)
    (motive_2 := fun {bound arguments parameters} typed available
        currentImage _ =>
      (typed.retagCostRegionFreeVariables mapsLookup).ReflectiveSupportSafeAt
        (retagCostRegionSupport support) available currentImage)
    (motive_3 := fun {bound elements elementType} typed available
        currentImage _ =>
      (typed.retagCostRegionFreeVariables mapsLookup).ReflectiveSupportSafeAt
        (retagCostRegionSupport support) available currentImage)
    (by
      intro bound index type lookup available currentImage
      exact .bvar lookup available)
    (by
      intro bound name type lookup available currentImage shape
      exact .fvar (mapsLookup lookup) available (by simpa using shape))
    (by
      intro bound rule arguments membership notBare argumentsTyped available
        currentImage quoted argumentsSafe argumentsIH
      exact .constructorQuote (membership := membership) (notBare := notBare)
        quoted argumentsIH)
    (by
      intro bound rule arguments membership notBare argumentsTyped available
        currentImage ordinary argumentsSafe argumentsIH
      exact .constructorOrdinary (membership := membership)
        (notBare := notBare) ordinary argumentsIH)
    (by
      intro bound binder body domain codomain bodyTyped available currentImage
        bodySafe bodyIH
      exact .lambda bodyIH)
    (by
      intro bound arity binders body domain codomain bodyTyped available
        currentImage bodySafe bodyIH
      exact .multiLambda bodyIH)
    (by
      intro bound body replacement domain codomain bodyTyped replacementTyped
        available currentImage bodySafe replacementSafe bodyIH replacementIH
      exact .subst bodyIH replacementIH)
    (by
      intro bound collectionType elements rest elementType elementsTyped
        available currentImage elementsSafe elementsIH
      exact .collection elementsIH)
    (by
      intro bound rule parameterName collectionType elements rest elementType
        membership parameterShape elementsTyped available currentImage
        elementsSafe elementsIH
      exact .collectionConstructor (parameterName := parameterName)
        (membership := membership) (parameterShape := parameterShape)
        elementsIH)
    (by
      intro bound available currentImage
      exact .nil bound available)
    (by
      intro bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped available
        currentImage argumentSafe argumentsSafe argumentIH argumentsIH
      exact .cons
        (representation :=
          (matchesParameterRepresentation_retagCostRegionFreeVariables
            parameter argument).2 representation)
        (parameterType := parameterType) argumentIH argumentsIH)
    (by
      intro bound elementType available currentImage
      exact .nil bound elementType available)
    (by
      intro bound element elements elementType elementTyped elementsTyped
        available currentImage elementSafe elementsSafe elementIH elementsIH
      exact .cons elementIH elementsIH)
    safe

/-- Free-name retagging preserves the reflective support discipline of a
typed source term.  Binder availability and quotation resets are unchanged;
only the support-map key is transported. -/
theorem WellSorted.HasType.ReflectiveSupportSafeAt.retagCostRegionFreeVariables
      {language : LanguageDef}
      {sourceFree targetFree : WellSorted.FreeTypeContext}
      {support : ContextSupport.Support}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      {typed : WellSorted.HasType language sourceFree bound pattern type}
      {available : List TypeExpr} (binderImage : TypeExpr → TypeExpr)
      (safe : typed.ReflectiveSupportSafeAt support available binderImage)
      (mapsLookup : ∀ {name freeType},
        sourceFree name = some freeType →
          targetFree (costRegionSourceVariableName name) = some freeType) :
      (typed.retagCostRegionFreeVariables mapsLookup).ReflectiveSupportSafeAt
        (retagCostRegionSupport support) available binderImage := by
  exact retagCostRegionFreeVariablesSupportAux mapsLookup safe

/-- A typed open source term remains in the same sort and binder fiber after
the hygienic source-name retagging used by a Cost normalization stratum. -/
def WellSorted.OpenTerm.retagCostRegionFreeVariables
    {language : LanguageDef} {sourceFree : WellSorted.FreeTypeContext}
    {bound : List TypeExpr} {sort : LangSort language}
  (term : WellSorted.OpenTerm language sourceFree bound sort) :
    WellSorted.OpenTerm language (retagCostRegionFreeContext sourceFree)
      bound sort :=
  ⟨Mettapedia.GSLT.LanguageDef.retagCostRegionFreeVariables term.1,
    term.2.1.retagCostRegionFreeVariables
      (targetFree := retagCostRegionFreeContext sourceFree)
      (fun {name freeType} lookup => by
      rw [retagCostRegionFreeContext_source]
      exact lookup),
    by simpa using term.2.2.1,
    by simpa using term.2.2.2.1,
    by
      intro presentation membership
      simpa [WellSorted.ReflectiveScopeSafeAt] using
        term.2.2.2.2 presentation membership⟩

@[simp]
theorem WellSorted.OpenTerm.retagCostRegionFreeVariables_pattern
    {language : LanguageDef} {sourceFree : WellSorted.FreeTypeContext}
    {bound : List TypeExpr} {sort : LangSort language}
    (term : WellSorted.OpenTerm language sourceFree bound sort) :
    term.retagCostRegionFreeVariables.1 =
      Mettapedia.GSLT.LanguageDef.retagCostRegionFreeVariables term.1 :=
  rfl

/-- The typed open-term retagging transports an existing reflective support
certificate to the retagged namespace. -/
theorem WellSorted.OpenTerm.retagCostRegionFreeVariables_reflectiveSupportSafeAt
    {language : LanguageDef} {sourceFree : WellSorted.FreeTypeContext}
    {bound : List TypeExpr} {sort : LangSort language}
    (term : WellSorted.OpenTerm language sourceFree bound sort)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr)
    (safe : term.2.1.ReflectiveSupportSafeAt support available binderImage) :
    term.retagCostRegionFreeVariables.2.1.ReflectiveSupportSafeAt
      (retagCostRegionSupport support) available binderImage := by
  exact safe.retagCostRegionFreeVariables
    (targetFree := retagCostRegionFreeContext sourceFree)
    binderImage
    (fun {name freeType} lookup => by
      rw [retagCostRegionFreeContext_source]
      exact lookup)

/-- Run the sole source open canonical section on a hygienically retagged
typed region.  This is the typed operation underlying the raw stratum
formula below; it stays in exactly the same sort and binder fiber. -/
def CIGSLT.normalizeRetaggedOpenTerm (source : CIGSLT)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (term : WellSorted.OpenTerm
      source.theory.presentation.presentation.language free bound sort) :
    WellSorted.OpenTerm source.theory.presentation.presentation.language
      (retagCostRegionFreeContext free) bound sort :=
  source.openCanonical.normalize term.retagCostRegionFreeVariables

/-- The sole source canonicalizer preserves the transported reflective
binder support of a retagged region. -/
theorem CIGSLT.normalizeRetaggedOpenTerm_preservesReflectiveSupport
    (source : CIGSLT)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (term : WellSorted.OpenTerm
      source.theory.presentation.presentation.language free bound sort)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr)
    (safe : term.2.1.ReflectiveSupportSafeAt support available binderImage) :
    (source.normalizeRetaggedOpenTerm term).2.1.ReflectiveSupportSafeAt
      (retagCostRegionSupport support) available binderImage := by
  exact source.openCanonical.preservesReflectiveSupport
    term.retagCostRegionFreeVariables (retagCostRegionSupport support)
    available binderImage
    (term.retagCostRegionFreeVariables_reflectiveSupportSafeAt support
      available binderImage safe)

/-- Typed source normalization preserves the exact declaration-derived
non-principal constructor fragment after hygienic free-variable retagging,
including the label of a constructor represented by a bare collection. -/
theorem CIGSLT.normalizeRetaggedOpenTerm_preservesWrappedConstructorTyping
    (source : CIGSLT)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (term : WellSorted.OpenTerm
      source.theory.presentation.presentation.language free bound sort)
    (supported : WellSorted.HasTypeWithConstructors
      source.theory.presentation.presentation.language
      (· ∈ source.continuationRetyping.wrappedLabels)
      free bound term.1 (.base sort.1)) :
    WellSorted.HasTypeWithConstructors
      source.theory.presentation.presentation.language
      (· ∈ source.continuationRetyping.wrappedLabels)
      (retagCostRegionFreeContext free) bound
      (source.normalizeRetaggedOpenTerm term).1 (.base sort.1) := by
  apply source.openCanonicalPreservesWrappedConstructorTyping
  exact supported.retagCostRegionFreeVariables
    (targetFree := retagCostRegionFreeContext free)
    (fun {name freeType} lookup => by
      rw [retagCostRegionFreeContext_source]
      exact lookup)

/-- Every free name surviving the typed monochromatic normalization still
belongs to the injective source namespace.  In particular, the restoration
fallback is unreachable even if equations delete some original variables. -/
theorem CIGSLT.normalizeRetaggedOpenTerm_name_decodes (source : CIGSLT)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (term : WellSorted.OpenTerm
      source.theory.presentation.presentation.language free bound sort)
    {name : String}
    (membership : name ∈
      (source.normalizeRetaggedOpenTerm term).1.freeFvarNames) :
    ∃ sourceName,
      decodeCostRegionSourceVariableName name = some sourceName := by
  obtain ⟨type, lookup⟩ :=
    (source.normalizeRetaggedOpenTerm term).freeType_of_mem_freeFvarNames
      membership
  cases decoded : decodeCostRegionSourceVariableName name with
  | none =>
      simp [retagCostRegionFreeContext, decoded] at lookup
  | some sourceName => exact ⟨sourceName, rfl⟩

mutual
  /-- Remove the source-variable namespace from a region skeleton.  The
  operation is partial so a generated boundary variable can never be
  mistaken for an original source variable. -/
  def restoreCostRegionFreeVariables : Pattern → Option Pattern
    | .bvar index => some (.bvar index)
    | .fvar name => do
        let sourceName ← decodeCostRegionSourceVariableName name
        pure (.fvar sourceName)
    | .apply constructor arguments => do
        let sourceArguments ← restoreCostRegionFreeVariableList arguments
        pure (.apply constructor sourceArguments)
    | .lambda binderName body => do
        let sourceBody ← restoreCostRegionFreeVariables body
        pure (.lambda binderName sourceBody)
    | .multiLambda arity binderNames body => do
        let sourceBody ← restoreCostRegionFreeVariables body
        pure (.multiLambda arity binderNames sourceBody)
    | .subst body replacement => do
        let sourceBody ← restoreCostRegionFreeVariables body
        let sourceReplacement ← restoreCostRegionFreeVariables replacement
        pure (.subst sourceBody sourceReplacement)
    | .collection collectionType elements rest => do
        let sourceElements ← restoreCostRegionFreeVariableList elements
        let sourceRest ← match rest with
          | none => some none
          | some name =>
              (decodeCostRegionSourceVariableName name).map some
        pure (.collection collectionType sourceElements sourceRest)

  def restoreCostRegionFreeVariableList :
      List Pattern → Option (List Pattern)
    | [] => some []
    | pattern :: patterns => do
        let sourcePattern ← restoreCostRegionFreeVariables pattern
        let sourcePatterns ← restoreCostRegionFreeVariableList patterns
        pure (sourcePattern :: sourcePatterns)
end

/-- Successful hygienic restoration changes free-variable names only; it
preserves the representation class required by every authored parameter. -/
theorem matchesParameterRepresentation_restoreCostRegionFreeVariables
    (parameter : TermParam) (pattern sourcePattern : Pattern)
    (restored : restoreCostRegionFreeVariables pattern = some sourcePattern) :
    WellSorted.MatchesParameterRepresentation parameter pattern →
      WellSorted.MatchesParameterRepresentation parameter sourcePattern := by
  intro representation
  cases parameter with
  | simple name type => trivial
  | abstractionNamed binder body type =>
      cases pattern with
      | bvar index =>
          simp [WellSorted.MatchesParameterRepresentation] at representation
      | fvar name =>
          simp [WellSorted.MatchesParameterRepresentation] at representation
      | apply constructor arguments =>
          simp [WellSorted.MatchesParameterRepresentation] at representation
      | lambda binderName patternBody =>
          cases binderName with
          | some binderName =>
              simp [WellSorted.MatchesParameterRepresentation] at representation
          | none =>
              cases bodyResult : restoreCostRegionFreeVariables patternBody with
              | none =>
                  simp [restoreCostRegionFreeVariables, bodyResult] at restored
              | some sourceBody =>
                  simp [restoreCostRegionFreeVariables, bodyResult] at restored
                  subst sourcePattern
                  trivial
      | multiLambda arity binders patternBody =>
          simp [WellSorted.MatchesParameterRepresentation] at representation
      | subst body replacement =>
          simp [WellSorted.MatchesParameterRepresentation] at representation
      | collection collectionType elements rest =>
          simp [WellSorted.MatchesParameterRepresentation] at representation
  | multiAbstractionNamed binders body type =>
      cases pattern with
      | bvar index =>
          simp [WellSorted.MatchesParameterRepresentation] at representation
      | fvar name =>
          simp [WellSorted.MatchesParameterRepresentation] at representation
      | apply constructor arguments =>
          simp [WellSorted.MatchesParameterRepresentation] at representation
      | lambda binderName patternBody =>
          simp [WellSorted.MatchesParameterRepresentation] at representation
      | multiLambda arity binderNames patternBody =>
          cases binderNames with
          | cons binderName binderNames =>
              simp [WellSorted.MatchesParameterRepresentation] at representation
          | nil =>
              cases bodyResult : restoreCostRegionFreeVariables patternBody with
              | none =>
                  simp [restoreCostRegionFreeVariables, bodyResult] at restored
              | some sourceBody =>
                  simp [restoreCostRegionFreeVariables, bodyResult] at restored
                  subst sourcePattern
                  trivial
      | subst body replacement =>
          simp [WellSorted.MatchesParameterRepresentation] at representation
      | collection collectionType elements rest =>
          simp [WellSorted.MatchesParameterRepresentation] at representation

mutual
  /-- Invert hygienic source-name restoration on a typed pattern.  A
  successful restoration returns a term in the original free-variable fiber
  with exactly the same authored type. -/
  theorem WellSorted.HasType.restoreCostRegionFreeVariables
      {language : LanguageDef} {sourceFree : WellSorted.FreeTypeContext}
      {bound : List TypeExpr} {pattern sourcePattern : Pattern}
      {type : TypeExpr}
      (typed : WellSorted.HasType language
        (retagCostRegionFreeContext sourceFree) bound pattern type)
      (restored : Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables
        pattern = some sourcePattern) :
      WellSorted.HasType language sourceFree bound sourcePattern type := by
    cases typed with
    | bvar lookup =>
        simp [Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables]
          at restored
        subst sourcePattern
        exact .bvar lookup
    | @fvar bound name type lookup =>
        cases decoded : decodeCostRegionSourceVariableName name with
        | none =>
            simp [Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables,
              decoded] at restored
        | some sourceName =>
            simp [Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables,
              decoded] at restored
            subst sourcePattern
            have sourceLookup : sourceFree sourceName = some type := by
              simpa [retagCostRegionFreeContext, decoded] using lookup
            exact .fvar sourceLookup
    | @constructor bound rule arguments membership notBare argumentsTyped =>
        cases argumentsResult : restoreCostRegionFreeVariableList arguments with
        | none =>
            simp [Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables,
              argumentsResult] at restored
        | some sourceArguments =>
            simp [Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables,
              argumentsResult] at restored
            subst sourcePattern
            exact .constructor membership notBare
              (argumentsTyped.restoreCostRegionFreeVariables argumentsResult)
    | @lambda bound binder body domain codomain bodyTyped =>
        cases bodyResult :
            Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables body with
        | none =>
            simp [Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables,
              bodyResult] at restored
        | some sourceBody =>
            simp [Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables,
              bodyResult] at restored
            subst sourcePattern
            exact .lambda
              (bodyTyped.restoreCostRegionFreeVariables bodyResult)
    | @multiLambda bound arity binders body domain codomain bodyTyped =>
        cases bodyResult :
            Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables body with
        | none =>
            simp [Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables,
              bodyResult] at restored
        | some sourceBody =>
            simp [Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables,
              bodyResult] at restored
            subst sourcePattern
            exact .multiLambda
              (bodyTyped.restoreCostRegionFreeVariables bodyResult)
    | @subst bound body replacement domain codomain bodyTyped replacementTyped =>
        cases bodyResult :
            Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables body with
        | none =>
            simp [Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables,
              bodyResult] at restored
        | some sourceBody =>
            cases replacementResult :
                Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables
                  replacement with
            | none =>
                simp [Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables,
                  bodyResult, replacementResult] at restored
            | some sourceReplacement =>
                simp [Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables,
                  bodyResult, replacementResult] at restored
                subst sourcePattern
                exact .subst
                  (bodyTyped.restoreCostRegionFreeVariables bodyResult)
                  (replacementTyped.restoreCostRegionFreeVariables
                    replacementResult)
    | @collection bound collectionType elements rest elementType elementsTyped =>
        cases elementsResult : restoreCostRegionFreeVariableList elements with
        | none =>
            simp [Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables,
              elementsResult] at restored
        | some sourceElements =>
            have sourceElementsTyped :=
              elementsTyped.restoreCostRegionFreeVariables elementsResult
            cases rest with
            | none =>
                simp [Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables,
                  elementsResult] at restored
                subst sourcePattern
                exact .collection sourceElementsTyped
            | some restName =>
                cases restResult : decodeCostRegionSourceVariableName restName with
                | none =>
                    simp [Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables,
                      elementsResult, restResult] at restored
                | some sourceRest =>
                    simp [Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables,
                      elementsResult, restResult] at restored
                    subst sourcePattern
                    exact .collection sourceElementsTyped
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType membership parameterShape elementsTyped =>
        cases elementsResult : restoreCostRegionFreeVariableList elements with
        | none =>
            simp [Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables,
              elementsResult] at restored
        | some sourceElements =>
            have sourceElementsTyped :=
              elementsTyped.restoreCostRegionFreeVariables elementsResult
            cases rest with
            | none =>
                simp [Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables,
                  elementsResult] at restored
                subst sourcePattern
                exact .collectionConstructor membership parameterShape
                  sourceElementsTyped
            | some restName =>
                cases restResult : decodeCostRegionSourceVariableName restName with
                | none =>
                    simp [Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables,
                      elementsResult, restResult] at restored
                | some sourceRest =>
                    simp [Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables,
                      elementsResult, restResult] at restored
                    subst sourcePattern
                    exact .collectionConstructor membership parameterShape
                      sourceElementsTyped

  /-- Ordered constructor arguments inherit typing through a successful
  hygienic restoration. -/
  theorem WellSorted.ArgumentsHaveTypes.restoreCostRegionFreeVariables
      {language : LanguageDef} {sourceFree : WellSorted.FreeTypeContext}
      {bound : List TypeExpr} {arguments sourceArguments : List Pattern}
      {parameters : List TermParam}
      (typed : WellSorted.ArgumentsHaveTypes language
        (retagCostRegionFreeContext sourceFree) bound arguments parameters)
      (restored : restoreCostRegionFreeVariableList arguments =
        some sourceArguments) :
      WellSorted.ArgumentsHaveTypes language sourceFree bound sourceArguments
        parameters := by
    cases typed with
    | nil =>
        simp [restoreCostRegionFreeVariableList] at restored
        subst sourceArguments
        exact .nil
    | @cons bound argument arguments parameter parameters expected representation
        parameterType argumentTyped argumentsTyped =>
        cases argumentResult :
            Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables argument with
        | none =>
            simp [restoreCostRegionFreeVariableList, argumentResult] at restored
        | some sourceArgument =>
            cases argumentsResult : restoreCostRegionFreeVariableList arguments with
            | none =>
                simp [restoreCostRegionFreeVariableList, argumentResult,
                  argumentsResult] at restored
            | some sourceArgumentsTail =>
                simp [restoreCostRegionFreeVariableList, argumentResult,
                  argumentsResult] at restored
                subst sourceArguments
                exact .cons
                  (matchesParameterRepresentation_restoreCostRegionFreeVariables
                    parameter argument sourceArgument argumentResult representation)
                  parameterType
                  (argumentTyped.restoreCostRegionFreeVariables argumentResult)
                  (argumentsTyped.restoreCostRegionFreeVariables
                    argumentsResult)

  /-- Collection elements inherit their common authored type through a
  successful hygienic restoration. -/
  theorem WellSorted.ElementsHaveType.restoreCostRegionFreeVariables
      {language : LanguageDef} {sourceFree : WellSorted.FreeTypeContext}
      {bound : List TypeExpr} {elements sourceElements : List Pattern}
      {elementType : TypeExpr}
      (typed : WellSorted.ElementsHaveType language
        (retagCostRegionFreeContext sourceFree) bound elements elementType)
      (restored : restoreCostRegionFreeVariableList elements =
        some sourceElements) :
      WellSorted.ElementsHaveType language sourceFree bound sourceElements
        elementType := by
    cases typed with
    | nil =>
        simp [restoreCostRegionFreeVariableList] at restored
        subst sourceElements
        exact .nil _ _
    | @cons bound element elements elementType elementTyped elementsTyped =>
        cases elementResult :
            Mettapedia.GSLT.LanguageDef.restoreCostRegionFreeVariables element with
        | none =>
            simp [restoreCostRegionFreeVariableList, elementResult] at restored
        | some sourceElement =>
            cases elementsResult : restoreCostRegionFreeVariableList elements with
            | none =>
                simp [restoreCostRegionFreeVariableList, elementResult,
                  elementsResult] at restored
            | some sourceElementsTail =>
                simp [restoreCostRegionFreeVariableList, elementResult,
                  elementsResult] at restored
                subst sourceElements
                exact .cons
                  (elementTyped.restoreCostRegionFreeVariables elementResult)
                  (elementsTyped.restoreCostRegionFreeVariables elementsResult)
end

/-- Restoration succeeds on every pattern whose free-variable occurrences
belong to the injective source namespace.  The statement is intentionally
existential: source normalization may delete variables or change the
representative, but it cannot manufacture an undecodable source name. -/
theorem restoreCostRegionFreeVariables_exists_of_all_decodable
    (pattern : Pattern)
    (decodes : ∀ name, name ∈ pattern.freeFvarNames →
      ∃ sourceName,
        decodeCostRegionSourceVariableName name = some sourceName) :
    ∃ sourcePattern,
      restoreCostRegionFreeVariables pattern = some sourcePattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      exact ⟨.bvar index, rfl⟩
  | hfvar name =>
      rcases decodes name (by simp [Pattern.freeFvarNames]) with
        ⟨sourceName, decoded⟩
      exact ⟨.fvar sourceName, by
        simp [restoreCostRegionFreeVariables, decoded]⟩
  | happly constructor arguments inductionHypothesis =>
      have argumentsResult :
          ∃ sourceArguments,
            restoreCostRegionFreeVariableList arguments =
              some sourceArguments := by
        induction arguments with
        | nil => exact ⟨[], rfl⟩
        | cons argument arguments listInduction =>
            have argumentDecodes : ∀ name,
                name ∈ argument.freeFvarNames →
                  ∃ sourceName,
                    decodeCostRegionSourceVariableName name =
                      some sourceName := by
              intro name membership
              apply decodes name
              simp only [Pattern.freeFvarNames, List.mem_flatMap]
              exact ⟨argument, by simp, membership⟩
            rcases inductionHypothesis argument (by simp) argumentDecodes with
              ⟨sourceArgument, argumentResult⟩
            have tailDecodes : ∀ name,
                name ∈ (Pattern.apply constructor arguments).freeFvarNames →
                  ∃ sourceName,
                    decodeCostRegionSourceVariableName name =
                      some sourceName := by
              intro name membership
              apply decodes name
              simp only [Pattern.freeFvarNames, List.mem_flatMap] at membership ⊢
              rcases membership with ⟨other, otherMembership, nameMembership⟩
              exact ⟨other, by simp [otherMembership], nameMembership⟩
            rcases listInduction
                (fun other membership =>
                  inductionHypothesis other (by simp [membership]))
                tailDecodes with
              ⟨sourceArguments, argumentsResult⟩
            exact ⟨sourceArgument :: sourceArguments, by
              simp [restoreCostRegionFreeVariableList, argumentResult,
                argumentsResult]⟩
      rcases argumentsResult with ⟨sourceArguments, argumentsResult⟩
      exact ⟨.apply constructor sourceArguments, by
        simp [restoreCostRegionFreeVariables, argumentsResult]⟩
  | hlambda binderName body inductionHypothesis =>
      have bodyDecodes : ∀ name, name ∈ body.freeFvarNames →
          ∃ sourceName,
            decodeCostRegionSourceVariableName name = some sourceName := by
        intro name membership
        apply decodes name
        simpa [Pattern.freeFvarNames] using membership
      rcases inductionHypothesis bodyDecodes with ⟨sourceBody, bodyResult⟩
      exact ⟨.lambda binderName sourceBody, by
        simp [restoreCostRegionFreeVariables, bodyResult]⟩
  | hmultiLambda arity binderNames body inductionHypothesis =>
      have bodyDecodes : ∀ name, name ∈ body.freeFvarNames →
          ∃ sourceName,
            decodeCostRegionSourceVariableName name = some sourceName := by
        intro name membership
        apply decodes name
        simpa [Pattern.freeFvarNames] using membership
      rcases inductionHypothesis bodyDecodes with ⟨sourceBody, bodyResult⟩
      exact ⟨.multiLambda arity binderNames sourceBody, by
        simp [restoreCostRegionFreeVariables, bodyResult]⟩
  | hsubst body replacement bodyInduction replacementInduction =>
      have bodyDecodes : ∀ name, name ∈ body.freeFvarNames →
          ∃ sourceName,
            decodeCostRegionSourceVariableName name = some sourceName := by
        intro name membership
        apply decodes name
        simp [Pattern.freeFvarNames, membership]
      have replacementDecodes : ∀ name,
          name ∈ replacement.freeFvarNames →
            ∃ sourceName,
              decodeCostRegionSourceVariableName name = some sourceName := by
        intro name membership
        apply decodes name
        simp [Pattern.freeFvarNames, membership]
      rcases bodyInduction bodyDecodes with ⟨sourceBody, bodyResult⟩
      rcases replacementInduction replacementDecodes with
        ⟨sourceReplacement, replacementResult⟩
      exact ⟨.subst sourceBody sourceReplacement, by
        simp [restoreCostRegionFreeVariables, bodyResult,
          replacementResult]⟩
  | hcollection collectionType elements rest inductionHypothesis =>
      have elementsResult :
          ∃ sourceElements,
            restoreCostRegionFreeVariableList elements = some sourceElements := by
        induction elements with
        | nil => exact ⟨[], rfl⟩
        | cons element elements listInduction =>
            have elementDecodes : ∀ name,
                name ∈ element.freeFvarNames →
                  ∃ sourceName,
                    decodeCostRegionSourceVariableName name =
                      some sourceName := by
              intro name membership
              apply decodes name
              simp only [Pattern.freeFvarNames, List.mem_append,
                List.mem_flatMap]
              exact Or.inl ⟨element, by simp, membership⟩
            rcases inductionHypothesis element (by simp) elementDecodes with
              ⟨sourceElement, elementResult⟩
            have tailDecodes : ∀ name,
                name ∈ (Pattern.collection collectionType elements rest).freeFvarNames →
                  ∃ sourceName,
                    decodeCostRegionSourceVariableName name =
                      some sourceName := by
              intro name membership
              apply decodes name
              simp only [Pattern.freeFvarNames, List.mem_append,
                List.mem_flatMap] at membership ⊢
              rcases membership with tailMembership | restMembership
              · left
                rcases tailMembership with
                  ⟨other, otherMembership, nameMembership⟩
                exact ⟨other, by simp [otherMembership], nameMembership⟩
              · exact Or.inr restMembership
            rcases listInduction
                (fun other membership =>
                  inductionHypothesis other (by simp [membership]))
                tailDecodes with
              ⟨sourceElements, elementsResult⟩
            exact ⟨sourceElement :: sourceElements, by
              simp [restoreCostRegionFreeVariableList, elementResult,
                elementsResult]⟩
      rcases elementsResult with ⟨sourceElements, elementsResult⟩
      cases rest with
      | none =>
          exact ⟨.collection collectionType sourceElements none, by
            simp [restoreCostRegionFreeVariables, elementsResult]⟩
      | some restName =>
          rcases decodes restName (by simp [Pattern.freeFvarNames]) with
            ⟨sourceRest, restResult⟩
          exact ⟨.collection collectionType sourceElements (some sourceRest), by
            simp [restoreCostRegionFreeVariables, elementsResult, restResult]⟩

/-- Typed normalization after source-name retagging always has an exact
source-name restoration.  This closes the finite partiality seam without
asserting that normalization preserves the original representative. -/
theorem CIGSLT.normalizeRetaggedOpenTerm_restorable (source : CIGSLT)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (term : WellSorted.OpenTerm
      source.theory.presentation.presentation.language free bound sort) :
    ∃ sourcePattern,
      restoreCostRegionFreeVariables
          (source.normalizeRetaggedOpenTerm term).1 =
        some sourcePattern := by
  apply restoreCostRegionFreeVariables_exists_of_all_decodable
  intro name membership
  exact source.normalizeRetaggedOpenTerm_name_decodes term membership

/-- The restoration option for a typed normalized source region is
computably inhabited. -/
theorem CIGSLT.normalizeRetaggedOpenTerm_restore_isSome (source : CIGSLT)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (term : WellSorted.OpenTerm
      source.theory.presentation.presentation.language free bound sort) :
    (restoreCostRegionFreeVariables
      (source.normalizeRetaggedOpenTerm term).1).isSome = true := by
  rcases source.normalizeRetaggedOpenTerm_restorable term with
    ⟨sourcePattern, restored⟩
  simp [restored]

/-- The source representative obtained by typed normalization in the
hygienic namespace followed by its certified inverse. -/
def CIGSLT.normalizedSourcePattern (source : CIGSLT)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (term : WellSorted.OpenTerm
      source.theory.presentation.presentation.language free bound sort) :
    Pattern :=
  (restoreCostRegionFreeVariables
    (source.normalizeRetaggedOpenTerm term).1).get
      (source.normalizeRetaggedOpenTerm_restore_isSome term)

/-- `normalizedSourcePattern` is exactly the successful result of the
partial hygienic inverse, rather than a fallback representative. -/
@[simp]
theorem CIGSLT.restore_normalizeRetaggedOpenTerm (source : CIGSLT)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (term : WellSorted.OpenTerm
      source.theory.presentation.presentation.language free bound sort) :
    restoreCostRegionFreeVariables
        (source.normalizeRetaggedOpenTerm term).1 =
      some (source.normalizedSourcePattern term) := by
  exact (Option.some_get
    (source.normalizeRetaggedOpenTerm_restore_isSome term)).symm

/-- The restored normalized representative inhabits the original authored
typing fiber.  This is a typing theorem about the independently computed
inverse, not a definitional self-comparison. -/
theorem CIGSLT.normalizedSourcePattern_hasType (source : CIGSLT)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (term : WellSorted.OpenTerm
      source.theory.presentation.presentation.language free bound sort) :
    WellSorted.HasType source.theory.presentation.presentation.language free
      bound (source.normalizedSourcePattern term) (.base sort.1) := by
  exact (source.normalizeRetaggedOpenTerm term).2.1
    |>.restoreCostRegionFreeVariables
      (source.restore_normalizeRetaggedOpenTerm term)

/-- Retagging source free variables is exactly reversible. -/
@[simp]
theorem restoreCostRegionFreeVariables_retag
    (pattern : Pattern) :
    restoreCostRegionFreeVariables (retagCostRegionFreeVariables pattern) =
      some pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => simp [retagCostRegionFreeVariables,
      restoreCostRegionFreeVariables]
  | happly constructor arguments inductionHypothesis =>
      have argumentsResult :
          restoreCostRegionFreeVariableList
              (retagCostRegionFreeVariableList arguments) = some arguments := by
        induction arguments with
        | nil => rfl
        | cons argument arguments listInduction =>
            simp only [retagCostRegionFreeVariableList,
              restoreCostRegionFreeVariableList]
            rw [inductionHypothesis argument (by simp)]
            rw [listInduction]
            · rfl
            · intro other membership
              exact inductionHypothesis other (by simp [membership])
      simp [retagCostRegionFreeVariables,
        restoreCostRegionFreeVariables, argumentsResult]
  | hlambda binderName body inductionHypothesis =>
      simp [retagCostRegionFreeVariables,
        restoreCostRegionFreeVariables, inductionHypothesis]
  | hmultiLambda arity binderNames body inductionHypothesis =>
      simp [retagCostRegionFreeVariables,
        restoreCostRegionFreeVariables, inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [retagCostRegionFreeVariables,
        restoreCostRegionFreeVariables, bodyInduction,
        replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      have elementsResult :
          restoreCostRegionFreeVariableList
              (retagCostRegionFreeVariableList elements) = some elements := by
        induction elements with
        | nil => rfl
        | cons element elements listInduction =>
            simp only [retagCostRegionFreeVariableList,
              restoreCostRegionFreeVariableList]
            rw [inductionHypothesis element (by simp)]
            rw [listInduction]
            · rfl
            · intro other membership
              exact inductionHypothesis other (by simp [membership])
      cases rest <;>
        simp [retagCostRegionFreeVariables,
          restoreCostRegionFreeVariables, elementsResult]

/-! ## Restoring opaque boundaries after one source normalization -/

mutual
  /-- Enumerate exactly the maximal foreign applications abstracted from one
  selected-color skeleton.  Shared binder, substitution, and collection
  representation nodes are traversed; an application from another namespace
  is one opaque boundary and its interior is not traversed at this stratum. -/
  def collectCostStaticBoundaries (color : CostStaticColor) :
      Pattern → List Pattern
    | .bvar _ | .fvar _ => []
    | pattern@(.apply constructor arguments) =>
        match decodeCostStaticConstructor color constructor with
        | some _ => collectCostStaticBoundaryList color arguments
        | none => [pattern]
    | .lambda _ body => collectCostStaticBoundaries color body
    | .multiLambda _ _ body => collectCostStaticBoundaries color body
    | .subst body replacement =>
        collectCostStaticBoundaries color body ++
          collectCostStaticBoundaries color replacement
    | .collection _ elements _ =>
        collectCostStaticBoundaryList color elements

  def collectCostStaticBoundaryList (color : CostStaticColor) :
      List Pattern → List Pattern
    | [] => []
    | pattern :: patterns =>
        collectCostStaticBoundaries color pattern ++
          collectCostStaticBoundaryList color patterns
end

mutual
  /-- Enumerate maximal foreign applications together with their exact
  structural occurrence.  `outer` is the context from the root to the
  current pattern; it is extended at every recursive descent, including
  binder and substitution frames. -/
  def collectCostStaticBoundaryOccurrencesAt (color : CostStaticColor)
      (outer : OneHoleContext) : Pattern → List CostRegionOccurrence
    | .bvar _ | .fvar _ => []
    | pattern@(.apply constructor arguments) =>
        match decodeCostStaticConstructor color constructor with
        | some _ =>
            collectCostStaticApplyBoundaryOccurrences color outer constructor
              [] arguments
        | none => [{ context := outer, content := pattern }]
    | .lambda binderName body =>
        collectCostStaticBoundaryOccurrencesAt color
          (outer.comp (.lambda binderName .hole)) body
    | .multiLambda arity binderNames body =>
        collectCostStaticBoundaryOccurrencesAt color
          (outer.comp (.multiLambda arity binderNames .hole)) body
    | .subst body replacement =>
        collectCostStaticBoundaryOccurrencesAt color
            (outer.comp (.substBody .hole replacement)) body ++
          collectCostStaticBoundaryOccurrencesAt color
            (outer.comp (.substReplacement body .hole)) replacement
    | .collection collectionType elements rest =>
        collectCostStaticCollectionBoundaryOccurrences color outer
          collectionType [] elements rest

  /-- Occurrence-preserving traversal of application arguments.  `before`
  records the already traversed siblings, while the recursive list supplies
  the siblings after the current argument. -/
  def collectCostStaticApplyBoundaryOccurrences (color : CostStaticColor)
      (outer : OneHoleContext) (constructor : String) (before : List Pattern) :
      List Pattern → List CostRegionOccurrence
    | [] => []
    | argument :: after =>
        collectCostStaticBoundaryOccurrencesAt color
            (outer.comp (.apply constructor before .hole after)) argument ++
          collectCostStaticApplyBoundaryOccurrences color outer constructor
            (before ++ [argument]) after

  /-- Occurrence-preserving traversal of collection elements.  Collection
  shape is traversed structurally but grants no reduction authority. -/
  def collectCostStaticCollectionBoundaryOccurrences
      (color : CostStaticColor) (outer : OneHoleContext)
      (collectionType : CollType) (before : List Pattern) :
      List Pattern → Option String → List CostRegionOccurrence
    | [], _ => []
    | element :: after, rest =>
        collectCostStaticBoundaryOccurrencesAt color
            (outer.comp
              (.collection collectionType before .hole after rest)) element ++
          collectCostStaticCollectionBoundaryOccurrences color outer
            collectionType (before ++ [element]) after rest
end

/-- Occurrence-sensitive maximal foreign regions of one complete stratum. -/
def collectCostStaticBoundaryOccurrences (color : CostStaticColor)
    (pattern : Pattern) : List CostRegionOccurrence :=
  collectCostStaticBoundaryOccurrencesAt color .hole pattern

mutual
  /-- Every occurrence emitted below `outer` reconstructs the same complete
  root as the current pattern.  Thus occurrence identity is structural
  evidence, not an unchecked numeric address. -/
  theorem collectCostStaticBoundaryOccurrencesAt_reconstructs
      (color : CostStaticColor) (outer : OneHoleContext)
      (pattern : Pattern) (occurrence : CostRegionOccurrence)
      (membership : occurrence ∈
        collectCostStaticBoundaryOccurrencesAt color outer pattern) :
      occurrence.context.fill occurrence.content = outer.fill pattern := by
    cases pattern with
    | bvar index => cases membership
    | fvar name => cases membership
    | apply constructor arguments =>
        cases decoded : decodeCostStaticConstructor color constructor with
        | none =>
            simp [collectCostStaticBoundaryOccurrencesAt, decoded] at membership
            subst occurrence
            rfl
        | some sourceConstructor =>
            exact collectCostStaticApplyBoundaryOccurrences_reconstructs
              color outer constructor [] arguments occurrence
              (by simpa [collectCostStaticBoundaryOccurrencesAt, decoded]
                using membership)
    | lambda binderName body =>
        have reconstructed :=
          collectCostStaticBoundaryOccurrencesAt_reconstructs color
            (outer.comp (.lambda binderName .hole)) body occurrence
            (by simpa [collectCostStaticBoundaryOccurrencesAt] using membership)
        simpa [OneHoleContext.fill] using reconstructed
    | multiLambda arity binderNames body =>
        have reconstructed :=
          collectCostStaticBoundaryOccurrencesAt_reconstructs color
            (outer.comp (.multiLambda arity binderNames .hole)) body occurrence
            (by simpa [collectCostStaticBoundaryOccurrencesAt] using membership)
        simpa [OneHoleContext.fill] using reconstructed
    | subst body replacement =>
        simp only [collectCostStaticBoundaryOccurrencesAt,
          List.mem_append] at membership
        rcases membership with bodyMembership | replacementMembership
        · have reconstructed :=
            collectCostStaticBoundaryOccurrencesAt_reconstructs color
              (outer.comp (.substBody .hole replacement)) body occurrence
              bodyMembership
          simpa [OneHoleContext.fill] using reconstructed
        · have reconstructed :=
            collectCostStaticBoundaryOccurrencesAt_reconstructs color
              (outer.comp (.substReplacement body .hole)) replacement occurrence
              replacementMembership
          simpa [OneHoleContext.fill] using reconstructed
    | collection collectionType elements rest =>
        exact collectCostStaticCollectionBoundaryOccurrences_reconstructs
          color outer collectionType [] elements rest occurrence
          (by simpa [collectCostStaticBoundaryOccurrencesAt] using membership)

  theorem collectCostStaticApplyBoundaryOccurrences_reconstructs
      (color : CostStaticColor) (outer : OneHoleContext)
      (constructor : String) (before arguments : List Pattern)
      (occurrence : CostRegionOccurrence)
      (membership : occurrence ∈
        collectCostStaticApplyBoundaryOccurrences color outer constructor
          before arguments) :
      occurrence.context.fill occurrence.content =
        outer.fill (.apply constructor (before ++ arguments)) := by
    cases arguments with
    | nil => cases membership
    | cons argument after =>
        simp only [collectCostStaticApplyBoundaryOccurrences,
          List.mem_append] at membership
        rcases membership with argumentMembership | afterMembership
        · have reconstructed :=
            collectCostStaticBoundaryOccurrencesAt_reconstructs color
              (outer.comp (.apply constructor before .hole after)) argument
              occurrence argumentMembership
          simpa [OneHoleContext.fill] using reconstructed
        · have reconstructed :=
            collectCostStaticApplyBoundaryOccurrences_reconstructs color outer
              constructor (before ++ [argument]) after occurrence
              afterMembership
          simpa [List.append_assoc] using reconstructed

  theorem collectCostStaticCollectionBoundaryOccurrences_reconstructs
      (color : CostStaticColor) (outer : OneHoleContext)
      (collectionType : CollType) (before elements : List Pattern)
      (rest : Option String) (occurrence : CostRegionOccurrence)
      (membership : occurrence ∈
        collectCostStaticCollectionBoundaryOccurrences color outer
          collectionType before elements rest) :
      occurrence.context.fill occurrence.content =
        outer.fill (.collection collectionType (before ++ elements) rest) := by
    cases elements with
    | nil => cases membership
    | cons element after =>
        simp only [collectCostStaticCollectionBoundaryOccurrences,
          List.mem_append] at membership
        rcases membership with elementMembership | afterMembership
        · have reconstructed :=
            collectCostStaticBoundaryOccurrencesAt_reconstructs color
              (outer.comp
                (.collection collectionType before .hole after rest)) element
              occurrence elementMembership
          simpa [OneHoleContext.fill] using reconstructed
        · have reconstructed :=
            collectCostStaticCollectionBoundaryOccurrences_reconstructs color
              outer collectionType (before ++ [element]) after rest occurrence
              afterMembership
          simpa [List.append_assoc] using reconstructed
end

/-- Every emitted maximal foreign-region occurrence really selects its
content in the complete input pattern. -/
theorem collectCostStaticBoundaryOccurrences_reconstructs
    (color : CostStaticColor) (pattern : Pattern)
    (occurrence : CostRegionOccurrence)
    (membership : occurrence ∈
      collectCostStaticBoundaryOccurrences color pattern) :
    occurrence.context.fill occurrence.content = pattern := by
  simpa [collectCostStaticBoundaryOccurrences] using
    collectCostStaticBoundaryOccurrencesAt_reconstructs color .hole pattern
      occurrence membership

/-- The executable collector agrees with the established relational zipper
specification: every reported boundary is an actual occurrence in the input,
not merely a pattern with the same content. -/
theorem collectCostStaticBoundaryOccurrences_selects
    (color : CostStaticColor) (pattern : Pattern)
    (occurrence : CostRegionOccurrence)
    (membership : occurrence ∈
      collectCostStaticBoundaryOccurrences color pattern) :
    Selects occurrence.content occurrence.context pattern := by
  have selected := Selects.of_fill occurrence.context occurrence.content
  rw [collectCostStaticBoundaryOccurrences_reconstructs color pattern
    occurrence membership] at selected
  exact selected

mutual
  /-- Forgetting locations from the occurrence-sensitive traversal recovers
  exactly the earlier maximal-region content traversal. -/
  theorem collectCostStaticBoundaryOccurrencesAt_contents
      (color : CostStaticColor) (outer : OneHoleContext)
      (pattern : Pattern) :
      (collectCostStaticBoundaryOccurrencesAt color outer pattern).map
          CostRegionOccurrence.content =
        collectCostStaticBoundaries color pattern := by
    cases pattern with
    | bvar index => rfl
    | fvar name => rfl
    | apply constructor arguments =>
        cases decoded : decodeCostStaticConstructor color constructor with
        | none =>
            simp [collectCostStaticBoundaryOccurrencesAt,
              collectCostStaticBoundaries, decoded]
        | some sourceConstructor =>
            simpa [collectCostStaticBoundaryOccurrencesAt,
              collectCostStaticBoundaries, decoded] using
              collectCostStaticApplyBoundaryOccurrences_contents color outer
                constructor [] arguments
    | lambda binderName body =>
        simpa [collectCostStaticBoundaryOccurrencesAt,
          collectCostStaticBoundaries] using
          collectCostStaticBoundaryOccurrencesAt_contents color
            (outer.comp (.lambda binderName .hole)) body
    | multiLambda arity binderNames body =>
        simpa [collectCostStaticBoundaryOccurrencesAt,
          collectCostStaticBoundaries] using
          collectCostStaticBoundaryOccurrencesAt_contents color
            (outer.comp (.multiLambda arity binderNames .hole)) body
    | subst body replacement =>
        simp [collectCostStaticBoundaryOccurrencesAt,
          collectCostStaticBoundaries,
          collectCostStaticBoundaryOccurrencesAt_contents]
    | collection collectionType elements rest =>
        simpa [collectCostStaticBoundaryOccurrencesAt,
          collectCostStaticBoundaries] using
          collectCostStaticCollectionBoundaryOccurrences_contents color outer
            collectionType [] elements rest

  theorem collectCostStaticApplyBoundaryOccurrences_contents
      (color : CostStaticColor) (outer : OneHoleContext)
      (constructor : String) (before arguments : List Pattern) :
      (collectCostStaticApplyBoundaryOccurrences color outer constructor
          before arguments).map CostRegionOccurrence.content =
        collectCostStaticBoundaryList color arguments := by
    cases arguments with
    | nil => rfl
    | cons argument after =>
        simp [collectCostStaticApplyBoundaryOccurrences,
          collectCostStaticBoundaryList,
          collectCostStaticBoundaryOccurrencesAt_contents,
          collectCostStaticApplyBoundaryOccurrences_contents]

  theorem collectCostStaticCollectionBoundaryOccurrences_contents
      (color : CostStaticColor) (outer : OneHoleContext)
      (collectionType : CollType) (before elements : List Pattern)
      (rest : Option String) :
      (collectCostStaticCollectionBoundaryOccurrences color outer
          collectionType before elements rest).map
            CostRegionOccurrence.content =
        collectCostStaticBoundaryList color elements := by
    cases elements with
    | nil => rfl
    | cons element after =>
        simp [collectCostStaticCollectionBoundaryOccurrences,
          collectCostStaticBoundaryList,
          collectCostStaticBoundaryOccurrencesAt_contents,
          collectCostStaticCollectionBoundaryOccurrences_contents]
end

/-- The public occurrence collector changes only the information retained
about each maximal region; it neither loses nor invents boundary contents. -/
theorem collectCostStaticBoundaryOccurrences_contents
    (color : CostStaticColor) (pattern : Pattern) :
    (collectCostStaticBoundaryOccurrences color pattern).map
        CostRegionOccurrence.content =
      collectCostStaticBoundaries color pattern := by
  exact collectCostStaticBoundaryOccurrencesAt_contents color .hole pattern

mutual
  /-- Every maximal foreign region emitted by the content collector is an
  application.  Shared variables, binders, substitutions, and collection
  representation nodes are traversed; none of them is itself promoted to a
  region boundary. -/
  theorem exists_apply_of_mem_collectCostStaticBoundaries
      (color : CostStaticColor) (pattern boundary : Pattern)
      (membership : boundary ∈ collectCostStaticBoundaries color pattern) :
      ∃ constructor arguments,
        boundary = .apply constructor arguments ∧
        decodeCostStaticConstructor color constructor = none := by
    cases pattern with
    | bvar index => cases membership
    | fvar name => cases membership
    | apply constructor arguments =>
        cases decoded : decodeCostStaticConstructor color constructor with
        | none =>
            simp [collectCostStaticBoundaries, decoded] at membership
            subst boundary
            exact ⟨constructor, arguments, rfl, decoded⟩
        | some sourceConstructor =>
            exact exists_apply_of_mem_collectCostStaticBoundaryList color
              arguments boundary
              (by simpa [collectCostStaticBoundaries, decoded] using membership)
    | lambda binderName body =>
        exact exists_apply_of_mem_collectCostStaticBoundaries color body
          boundary (by simpa [collectCostStaticBoundaries] using membership)
    | multiLambda arity binderNames body =>
        exact exists_apply_of_mem_collectCostStaticBoundaries color body
          boundary (by simpa [collectCostStaticBoundaries] using membership)
    | subst body replacement =>
        simp only [collectCostStaticBoundaries, List.mem_append] at membership
        rcases membership with bodyMembership | replacementMembership
        · exact exists_apply_of_mem_collectCostStaticBoundaries color body
            boundary bodyMembership
        · exact exists_apply_of_mem_collectCostStaticBoundaries color replacement
            boundary replacementMembership
    | collection collectionType elements rest =>
        exact exists_apply_of_mem_collectCostStaticBoundaryList color elements
          boundary
          (by simpa [collectCostStaticBoundaries] using membership)

  /-- The list traversal inherits the application-only boundary invariant. -/
  theorem exists_apply_of_mem_collectCostStaticBoundaryList
      (color : CostStaticColor) (patterns : List Pattern) (boundary : Pattern)
      (membership : boundary ∈ collectCostStaticBoundaryList color patterns) :
      ∃ constructor arguments,
        boundary = .apply constructor arguments ∧
        decodeCostStaticConstructor color constructor = none := by
    cases patterns with
    | nil => cases membership
    | cons pattern patterns =>
        simp only [collectCostStaticBoundaryList, List.mem_append] at membership
        rcases membership with headMembership | tailMembership
        · exact exists_apply_of_mem_collectCostStaticBoundaries color pattern
            boundary headMembership
        · exact exists_apply_of_mem_collectCostStaticBoundaryList color patterns
            boundary tailMembership
end

/-- Occurrence-sensitive collection has the same application-only invariant
as its content projection.  This is the inversion fact needed to recover the
authored result sort from a boundary's typing derivation. -/
theorem exists_apply_of_mem_collectCostStaticBoundaryOccurrences
    (color : CostStaticColor) (pattern : Pattern)
    (occurrence : CostRegionOccurrence)
    (membership : occurrence ∈
      collectCostStaticBoundaryOccurrences color pattern) :
    ∃ constructor arguments,
      occurrence.content = .apply constructor arguments ∧
      decodeCostStaticConstructor color constructor = none := by
  apply exists_apply_of_mem_collectCostStaticBoundaries color pattern
  rw [← collectCostStaticBoundaryOccurrences_contents color pattern]
  exact List.mem_map_of_mem membership

mutual
  /-- Free source variables exposed by the selected-color skeleton.  A
  foreign application is opaque at this stratum, so names in its interior
  belong to the boundary content rather than to the source normalizer's
  ambient context. -/
  def collectCostStaticSourceNames (color : CostStaticColor) :
      Pattern → List String
    | .bvar _ => []
    | .fvar name => [name]
    | .apply constructor arguments =>
        match decodeCostStaticConstructor color constructor with
        | some _ => collectCostStaticSourceNameList color arguments
        | none => []
    | .lambda _ body => collectCostStaticSourceNames color body
    | .multiLambda _ _ body => collectCostStaticSourceNames color body
    | .subst body replacement =>
        collectCostStaticSourceNames color body ++
          collectCostStaticSourceNames color replacement
    | .collection _ elements rest =>
        collectCostStaticSourceNameList color elements ++ rest.toList

  def collectCostStaticSourceNameList (color : CostStaticColor) :
      List Pattern → List String
    | [] => []
    | pattern :: patterns =>
        collectCostStaticSourceNames color pattern ++
          collectCostStaticSourceNameList color patterns
end

/-- A finite executable lookup table for the complete boundary records of one
concrete stratum.  Equal stable keys necessarily carry equal typed,
support-indexed content, so the first matching entry is canonical even when a
boundary occurs more than once. -/
def resolveCostRegionBoundaryData (boundary : CostRegionBoundaryAssignment) :
    List CostRegionOccurrence → String → Option CostRegionBoundary
  | [], _ => none
  | occurrence :: occurrences, name =>
      if name = costRegionBoundaryVariableName (boundary occurrence) then
        some (boundary occurrence)
      else
        resolveCostRegionBoundaryData boundary occurrences name

/-- Typed boundary lookup follows the same finite, occurrence-sensitive
table as the raw codec while retaining the proof that the selected content
inhabits its transported type and support. -/
def resolveTypedCostRegionBoundaryData {source : CIGSLT}
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (boundary : TypedCostRegionBoundaryAssignment source color targetFree) :
    List CostRegionOccurrence → String →
      Option (TypedCostRegionBoundary source color targetFree)
  | [], _ => none
  | occurrence :: occurrences, name =>
      if name = costRegionBoundaryVariableName
          (boundary occurrence).boundary then
        some (boundary occurrence)
      else
        resolveTypedCostRegionBoundaryData boundary occurrences name

/-- Typed boundaries are determined by their proof-relevant raw key; the
typing field is proposition-valued and therefore carries no second identity. -/
@[ext]
theorem TypedCostRegionBoundary.ext {source : CIGSLT}
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {left right : TypedCostRegionBoundary source color targetFree}
    (boundary : left.boundary = right.boundary) : left = right := by
  cases left
  cases right
  cases boundary
  rfl

/-- Every enumerated typed boundary is recovered from its stable raw key. -/
theorem resolveTypedCostRegionBoundaryData_of_mem {source : CIGSLT}
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (boundary : TypedCostRegionBoundaryAssignment source color targetFree)
    (regions : List CostRegionOccurrence) (occurrence : CostRegionOccurrence)
    (membership : occurrence ∈ regions) :
    resolveTypedCostRegionBoundaryData boundary regions
        (costRegionBoundaryVariableName (boundary occurrence).boundary) =
      some (boundary occurrence) := by
  induction regions with
  | nil => cases membership
  | cons head regions inductionHypothesis =>
      rcases List.mem_cons.mp membership with equality | membership
      · subst occurrence
        simp [resolveTypedCostRegionBoundaryData]
      · by_cases keyEquality :
          costRegionBoundaryVariableName (boundary occurrence).boundary =
            costRegionBoundaryVariableName (boundary head).boundary
        · have rawEquality :
              (boundary occurrence).boundary = (boundary head).boundary :=
            costRegionBoundaryVariableName_injective keyEquality
          have typedEquality : boundary occurrence = boundary head :=
            TypedCostRegionBoundary.ext rawEquality
          rw [typedEquality]
          simp [resolveTypedCostRegionBoundaryData]
        · simp [resolveTypedCostRegionBoundaryData, keyEquality,
            inductionHypothesis membership]

/-- Every enumerated complete boundary record is recovered by the finite
resolver. -/
theorem resolveCostRegionBoundaryData_of_mem
    (boundary : CostRegionBoundaryAssignment)
    (regions : List CostRegionOccurrence) (occurrence : CostRegionOccurrence)
    (membership : occurrence ∈ regions) :
    resolveCostRegionBoundaryData boundary regions
        (costRegionBoundaryVariableName (boundary occurrence)) =
      some (boundary occurrence) := by
  induction regions with
  | nil => cases membership
  | cons head regions inductionHypothesis =>
      rcases List.mem_cons.mp membership with equality | membership
      · subst occurrence
        simp [resolveCostRegionBoundaryData]
      · by_cases keyEquality :
          costRegionBoundaryVariableName (boundary occurrence) =
            costRegionBoundaryVariableName (boundary head)
        · have boundaryEquality : boundary occurrence = boundary head :=
            costRegionBoundaryVariableName_injective keyEquality
          rw [boundaryEquality]
          simp [resolveCostRegionBoundaryData]
        · simp [resolveCostRegionBoundaryData, keyEquality,
            inductionHypothesis membership]

/-- Content restoration is the content projection of the one complete
boundary lookup. -/
def resolveCostRegionBoundaries (boundary : CostRegionBoundaryAssignment)
    (regions : List CostRegionOccurrence) (name : String) : Option Pattern :=
  (resolveCostRegionBoundaryData boundary regions name).map (·.content)

/-- Every enumerated boundary content is recovered by the projected finite
resolver. -/
theorem resolveCostRegionBoundaries_of_mem
    (boundary : CostRegionBoundaryAssignment)
    (regions : List CostRegionOccurrence) (occurrence : CostRegionOccurrence)
    (membership : occurrence ∈ regions) :
    resolveCostRegionBoundaries boundary regions
        (costRegionBoundaryVariableName (boundary occurrence)) =
      some (boundary occurrence).content := by
  simp [resolveCostRegionBoundaries,
    resolveCostRegionBoundaryData_of_mem boundary regions occurrence membership]

/-- Decode the free typing context seen by one source normalization stratum.
Genuine source variables obtain their type by inverting the selected static
sort action; opaque variables obtain the authored source type stored in their
complete boundary record. -/
def costStaticAbstractionFreeContext (source : CIGSLT)
    (color : CostStaticColor) (targetFree : WellSorted.FreeTypeContext)
    (boundary : CostRegionBoundaryAssignment)
    (regions : List CostRegionOccurrence) :
    WellSorted.FreeTypeContext :=
  fun name =>
    match decodeCostRegionSourceVariableName name with
    | some sourceName =>
        (targetFree sourceName).bind (decodeCostStaticTypeExpr source color)
    | none =>
        (resolveCostRegionBoundaryData boundary regions name).map (·.type)

@[simp]
theorem costStaticAbstractionFreeContext_source
    (source : CIGSLT) (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext)
    (boundary : CostRegionBoundaryAssignment)
    (regions : List CostRegionOccurrence)
    (sourceName : String) :
    costStaticAbstractionFreeContext source color targetFree boundary regions
        (costRegionSourceVariableName sourceName) =
      (targetFree sourceName).bind (decodeCostStaticTypeExpr source color) := by
  simp [costStaticAbstractionFreeContext]

/-- Boundary-variable names are outside the namespace used to preserve
genuine source free variables. -/
theorem decodeCostRegionSourceVariableName_boundary
    (boundary : CostRegionBoundary) :
    decodeCostRegionSourceVariableName
        (costRegionBoundaryVariableName boundary) = none := by
  cases decoded : decodeCostRegionSourceVariableName
      (costRegionBoundaryVariableName boundary) with
  | none => rfl
  | some sourceName =>
      have reconstructed :
          costRegionBoundaryVariableName boundary =
            costRegionSourceVariableName sourceName := by
        exact (decodeTaggedPayload_eq_some_iff
          costRegionSourceVariableTag
          (costRegionBoundaryVariableName boundary) sourceName).mp decoded
      exact False.elim
        (costRegionSourceVariableName_ne_boundary sourceName boundary
          reconstructed.symm)

@[simp]
theorem costStaticAbstractionFreeContext_boundary
    (source : CIGSLT) (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext)
    (boundary : CostRegionBoundaryAssignment)
    (regions : List CostRegionOccurrence)
    (occurrence : CostRegionOccurrence)
    (membership : occurrence ∈ regions) :
    costStaticAbstractionFreeContext source color targetFree boundary regions
        (costRegionBoundaryVariableName (boundary occurrence)) =
      some (boundary occurrence).type := by
  simp [costStaticAbstractionFreeContext,
    decodeCostRegionSourceVariableName_boundary,
    resolveCostRegionBoundaryData_of_mem boundary regions occurrence membership]

/-! ## Typed, support-safe boundary restoration -/

/-- Source-side abstraction context recovered from a typed boundary table.
Source variables are decoded from the selected static type fiber; boundary
variables retain the source type stored in their stable key. -/
def typedCostStaticAbstractionFreeContext (source : CIGSLT)
    (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext)
    (boundary : TypedCostRegionBoundaryAssignment source color targetFree)
    (regions : List CostRegionOccurrence) :
    WellSorted.FreeTypeContext :=
  fun name =>
    match decodeCostRegionSourceVariableName name with
    | some sourceName =>
        (targetFree sourceName).bind (decodeCostStaticTypeExpr source color)
    | none =>
        (resolveTypedCostRegionBoundaryData boundary regions name).map
          (fun typedBoundary => typedBoundary.boundary.type)

/-- The free context of the Cost skeleton obtained after transporting the
typed source abstraction back into the selected static fiber.  Genuine
source variables use the exact partial static type equivalence.  Boundary
variables use their independently certified target type, because selected
continuation positions are retyped by the interaction cut rather than by the
uniform static action. -/
def mappedCostStaticAbstractionFreeContext (source : CIGSLT)
    (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext)
    (boundary : TypedCostRegionBoundaryAssignment source color targetFree)
    (regions : List CostRegionOccurrence) :
    WellSorted.FreeTypeContext :=
  fun name =>
    match decodeCostRegionSourceVariableName name with
    | some sourceName =>
        ((targetFree sourceName).bind
          (decodeCostStaticTypeExpr source color)).map
            (mapTypeExpr (color.symbols source))
    | none =>
        (resolveTypedCostRegionBoundaryData boundary regions name).map
          (fun typedBoundary => typedBoundary.boundary.targetType)

/-- Binder support for restoration in the generated Cost language.  Genuine
source variables are support-free structural parameters; a boundary uses
the exact target support certified by its typed key. -/
def costStaticRestorationSupport (source : CIGSLT)
    (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext)
    (boundary : TypedCostRegionBoundaryAssignment source color targetFree)
    (regions : List CostRegionOccurrence) : ContextSupport.Support :=
  fun name =>
    match decodeCostRegionSourceVariableName name with
    | some _ => []
    | none =>
        match resolveTypedCostRegionBoundaryData boundary regions name with
        | some typedBoundary =>
            typedBoundary.boundary.targetSupport
        | none => []

/-- Exact agreement between one typed source abstraction fiber and the
boundary table used to restore its Cost image.  Static regions transport
types and reflective supports uniformly; interaction-principal boundaries
may instead use cut-specific retyping and therefore cannot inhabit this
contract accidentally. -/
structure CostStaticBoundaryTransport (source : CIGSLT)
    (color : CostStaticColor)
    (targetFree sourceFree : WellSorted.FreeTypeContext)
    (sourceSupport : ContextSupport.Support)
    (boundary : TypedCostRegionBoundaryAssignment source color targetFree)
    (regions : List CostRegionOccurrence) : Prop where
  freeContext : sourceFree.map (color.symbols source) =
    mappedCostStaticAbstractionFreeContext source color targetFree boundary
      regions
  reflectiveSupport : mapCostStaticSupport source color sourceSupport =
    costStaticRestorationSupport source color targetFree boundary regions

/-- Structural assignment used by supported restoration.  Source variables
lose only their hygienic tag; boundaries are replaced by their typed Cost
content.  The fallback is unreachable for a variable in the mapped
abstraction context, but keeps the operation total on raw syntax. -/
def costStaticRestorationAssignment (source : CIGSLT)
    (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext)
    (boundary : TypedCostRegionBoundaryAssignment source color targetFree)
    (regions : List CostRegionOccurrence) : ContextSupport.Assignment :=
  fun name =>
    match decodeCostRegionSourceVariableName name with
    | some sourceName => .fvar sourceName
    | none =>
        match resolveTypedCostRegionBoundaryData boundary regions name with
        | some typedBoundary => typedBoundary.boundary.content
        | none => .fvar name

/-- The complete restoration table is a `SupportedAssignment` in the exact
generated Cost language.  This is the load-bearing bridge from stable raw
boundary keys to proof-carrying substitution; no typing fact is recovered
from the key's serialization. -/
def costStaticSupportedAssignment (source : CIGSLT)
    (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext)
    (boundary : TypedCostRegionBoundaryAssignment source color targetFree)
    (regions : List CostRegionOccurrence) :
    WellSorted.SupportedAssignment source.costWholeLanguage
      (mappedCostStaticAbstractionFreeContext source color targetFree boundary
        regions)
      targetFree
      (costStaticRestorationSupport source color targetFree boundary
        regions) where
  assignment :=
    costStaticRestorationAssignment source color targetFree boundary regions
  typed := by
    intro name type lookup
    cases decodedName : decodeCostRegionSourceVariableName name with
    | some sourceName =>
        cases targetLookup : targetFree sourceName with
        | none =>
            simp [mappedCostStaticAbstractionFreeContext,
              decodedName, targetLookup]
              at lookup
        | some targetType =>
            cases decodedType :
                decodeCostStaticTypeExpr source color targetType with
            | none =>
                simp [mappedCostStaticAbstractionFreeContext,
                  decodedName, targetLookup, decodedType] at lookup
            | some sourceType =>
                have encodedType :
                    mapTypeExpr (color.symbols source) sourceType =
                      targetType :=
                  mapTypeExpr_decodeCostStaticTypeExpr source color decodedType
                have mappedType :
                    mapTypeExpr (color.symbols source) sourceType = type := by
                  simpa [mappedCostStaticAbstractionFreeContext,
                    typedCostStaticAbstractionFreeContext,
                    WellSorted.FreeTypeContext.map, decodedName, targetLookup,
                    decodedType] using lookup
                have targetTypeEquality : targetType = type :=
                  encodedType.symm.trans mappedType
                have targetLookup' : targetFree sourceName = some type := by
                  simpa [targetTypeEquality] using targetLookup
                simpa [costStaticRestorationSupport,
                  costStaticRestorationAssignment, decodedName] using
                    (WellSorted.HasType.fvar (bound := []) targetLookup')
    | none =>
        cases resolved :
            resolveTypedCostRegionBoundaryData boundary regions name with
        | none =>
            simp [mappedCostStaticAbstractionFreeContext,
              decodedName, resolved] at lookup
        | some typedBoundary =>
            have targetType : typedBoundary.boundary.targetType = type := by
              simpa [mappedCostStaticAbstractionFreeContext, decodedName,
                resolved] using lookup
            simpa [costStaticRestorationSupport,
              costStaticRestorationAssignment, decodedName, resolved,
              targetType] using typedBoundary.contentTyped

/-- The restoration table consists of genuine open object terms.  Original
source variables map to themselves; generated boundary variables map to the
proof-carrying contents selected by the finite typed table. -/
def costStaticSupportedOpenAssignment (source : CIGSLT)
    (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext)
    (boundary : TypedCostRegionBoundaryAssignment source color targetFree)
    (regions : List CostRegionOccurrence) :
    WellSorted.SupportedOpenAssignment source.costWholeLanguage
      (mappedCostStaticAbstractionFreeContext source color targetFree boundary
        regions)
      targetFree
      (costStaticRestorationSupport source color targetFree boundary
        regions) where
  toSupportedAssignment :=
    costStaticSupportedAssignment source color targetFree boundary regions
  canonicalBinderMetadata := by
    intro name type lookup
    change
      (costStaticRestorationAssignment source color targetFree boundary regions
        name).hasCanonicalBinderMetadata = true
    cases decodedName : decodeCostRegionSourceVariableName name with
    | some sourceName =>
        simp only [costStaticRestorationAssignment, decodedName]
        rfl
    | none =>
        cases resolved :
            resolveTypedCostRegionBoundaryData boundary regions name with
        | none =>
            simp [mappedCostStaticAbstractionFreeContext,
              decodedName, resolved] at lookup
        | some typedBoundary =>
            simpa [costStaticRestorationAssignment, decodedName, resolved]
              using typedBoundary.contentCanonicalBinderMetadata
  objectPattern := by
    intro name type lookup
    change WellSorted.isObjectPattern
      (costStaticRestorationAssignment source color targetFree boundary regions
        name) = true
    cases decodedName : decodeCostRegionSourceVariableName name with
    | some sourceName =>
        simp only [costStaticRestorationAssignment, decodedName]
        rfl
    | none =>
        cases resolved :
            resolveTypedCostRegionBoundaryData boundary regions name with
        | none =>
            simp [mappedCostStaticAbstractionFreeContext,
              decodedName, resolved] at lookup
        | some typedBoundary =>
            simpa [costStaticRestorationAssignment, decodedName, resolved]
              using typedBoundary.contentObjectPattern
  reflectiveScopeSafe := by
    intro name type lookup
    change WellSorted.ReflectiveScopeSafeAt source.costWholeLanguage
      (costStaticRestorationSupport source color targetFree boundary regions
        name).length
      (costStaticRestorationAssignment source color targetFree boundary regions
        name)
    cases decodedName : decodeCostRegionSourceVariableName name with
    | some sourceName =>
        intro presentation membership
        simp only [costStaticRestorationSupport,
          costStaticRestorationAssignment, decodedName, List.length_nil]
        rfl
    | none =>
        cases resolved :
            resolveTypedCostRegionBoundaryData boundary regions name with
        | none =>
            simp [mappedCostStaticAbstractionFreeContext,
              decodedName, resolved] at lookup
        | some typedBoundary =>
            simpa [costStaticRestorationSupport,
              costStaticRestorationAssignment, decodedName, resolved]
              using typedBoundary.contentReflectiveScopeSafe

/-- Reflective supported restoration of one already transported Cost
skeleton.  Unlike raw replacement, this operation weakens each boundary
through precisely the additional binders at its occurrence and resets
available support at authored quotation constructors. -/
def restoreSupportedCostStaticSkeleton (source : CIGSLT)
    (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext)
    (boundary : TypedCostRegionBoundaryAssignment source color targetFree)
    (regions : List CostRegionOccurrence) (bound : List TypeExpr)
    (pattern : Pattern) : Pattern :=
  ReflectiveContextSupport.substitute source.costWholeLanguage
    (costStaticRestorationSupport source color targetFree boundary regions)
    (costStaticRestorationAssignment source color targetFree boundary regions)
    bound pattern

/-- Supported restoration preserves the exact Cost typing judgment.  The
support premise is intentionally explicit: canonicalization may move or
duplicate a boundary only where its original support remains admissible. -/
theorem restoreSupportedCostStaticSkeleton_typed (source : CIGSLT)
    (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext)
    (boundary : TypedCostRegionBoundaryAssignment source color targetFree)
    (regions : List CostRegionOccurrence) {bound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    (typed : WellSorted.HasType source.costWholeLanguage
      (mappedCostStaticAbstractionFreeContext source color targetFree boundary
        regions) bound pattern type)
    (supported : typed.ReflectiveSupportSafeAt
      (costStaticRestorationSupport source color targetFree boundary
        regions) bound) :
    WellSorted.HasType source.costWholeLanguage targetFree bound
      (restoreSupportedCostStaticSkeleton source color targetFree boundary
        regions bound pattern) type := by
  exact supported.substituteRoot
    (costStaticSupportedAssignment source color targetFree boundary regions)

/-- Supported restoration preserves the complete open object-term carrier,
not only its typing projection.  Thus a rigid region cannot re-enter the Cost
syntax with malformed binder metadata, a pending schema substitution, an open
collection tail, or a violation of an authored quotation boundary. -/
theorem restoreSupportedCostStaticSkeleton_openTermWellSorted
    (source : CIGSLT) (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext)
    (boundary : TypedCostRegionBoundaryAssignment source color targetFree)
    (regions : List CostRegionOccurrence) {bound : List TypeExpr}
    {sort : LangSort source.costWholeLanguage}
    (skeleton : WellSorted.OpenTerm source.costWholeLanguage
      (mappedCostStaticAbstractionFreeContext source color targetFree boundary
        regions) bound sort)
    (supported : skeleton.2.1.ReflectiveSupportSafeAt
      (costStaticRestorationSupport source color targetFree boundary regions)
      bound) :
    WellSorted.OpenTermWellSorted source.costWholeLanguage targetFree bound sort
      (restoreSupportedCostStaticSkeleton source color targetFree boundary
        regions bound skeleton.1) := by
  simpa only [restoreSupportedCostStaticSkeleton,
    costStaticSupportedOpenAssignment, costStaticSupportedAssignment] using
    supported.substituteOpenTermWellSorted
      (costStaticSupportedOpenAssignment source color targetFree boundary regions)
      skeleton.2.2.1 skeleton.2.2.2.1 skeleton.2.2.2.2

mutual
  /-- Re-embed a normalized source skeleton into one Cost static namespace.
Retagged genuine source variables are decoded, while rigid boundary variables
are replaced by their already-canonical target contents.  An unrelated free
variable is retained, making the function total; the section proof later
shows that normalized skeletons contain only the two reserved namespaces. -/
  def restoreCostStaticSkeleton (color : CostStaticColor)
      (resolveBoundary : String → Option Pattern) : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name =>
        match decodeCostRegionSourceVariableName name with
        | some sourceName => .fvar sourceName
        | none => (resolveBoundary name).getD (.fvar name)
    | .apply constructor arguments =>
        .apply (color.constructorTag ++ constructor)
          (restoreCostStaticSkeletonList color resolveBoundary arguments)
    | .lambda binderName body =>
        .lambda binderName
          (restoreCostStaticSkeleton color resolveBoundary body)
    | .multiLambda arity binderNames body =>
        .multiLambda arity binderNames
          (restoreCostStaticSkeleton color resolveBoundary body)
    | .subst body replacement =>
        .subst (restoreCostStaticSkeleton color resolveBoundary body)
          (restoreCostStaticSkeleton color resolveBoundary replacement)
    | .collection collectionType elements rest =>
        .collection collectionType
          (restoreCostStaticSkeletonList color resolveBoundary elements)
          (rest.map fun name =>
            (decodeCostRegionSourceVariableName name).getD name)

  def restoreCostStaticSkeletonList (color : CostStaticColor)
      (resolveBoundary : String → Option Pattern) :
      List Pattern → List Pattern
    | [] => []
    | pattern :: patterns =>
        restoreCostStaticSkeleton color resolveBoundary pattern ::
          restoreCostStaticSkeletonList color resolveBoundary patterns
end

/-- Re-embedding after the hygienic source-variable renaming is exactly the
uniform static Cost embedding.  No boundary resolver is consulted in a
monochromatic source image. -/
@[simp]
theorem restoreCostStaticSkeleton_retag
    (source : CIGSLT) (color : CostStaticColor)
    (resolveBoundary : String → Option Pattern) (pattern : Pattern) :
    restoreCostStaticSkeleton color resolveBoundary
        (retagCostRegionFreeVariables pattern) =
      mapPattern (color.symbols source) pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      simp [restoreCostStaticSkeleton, retagCostRegionFreeVariables,
        mapPattern]
  | hfvar name =>
      simp [restoreCostStaticSkeleton, retagCostRegionFreeVariables,
        mapPattern]
  | happly constructor arguments inductionHypothesis =>
      simp only [restoreCostStaticSkeleton, retagCostRegionFreeVariables,
        mapPattern, CostStaticColor.symbols_constructor,
        Pattern.apply.injEq, true_and]
      induction arguments with
      | nil => rfl
      | cons argument arguments listInduction =>
          simp only [retagCostRegionFreeVariableList,
            restoreCostStaticSkeletonList, mapPatternList,
            List.cons.injEq]
          constructor
          · exact inductionHypothesis argument (by simp)
          · apply listInduction
            intro other membership
            exact inductionHypothesis other (by simp [membership])
  | hlambda binderName body inductionHypothesis =>
      simp [restoreCostStaticSkeleton, retagCostRegionFreeVariables,
        mapPattern, inductionHypothesis]
  | hmultiLambda arity binderNames body inductionHypothesis =>
      simp [restoreCostStaticSkeleton, retagCostRegionFreeVariables,
        mapPattern, inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [restoreCostStaticSkeleton, retagCostRegionFreeVariables,
        mapPattern, bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [restoreCostStaticSkeleton, retagCostRegionFreeVariables,
        mapPattern, Pattern.collection.injEq, true_and]
      constructor
      · induction elements with
        | nil => rfl
        | cons element elements listInduction =>
            simp only [retagCostRegionFreeVariableList,
              restoreCostStaticSkeletonList, mapPatternList,
              List.cons.injEq]
            constructor
            · exact inductionHypothesis element (by simp)
            · apply listInduction
              intro other membership
              exact inductionHypothesis other (by simp [membership])
      · cases rest <;>
          simp [decodeCostRegionSourceVariableName_encode]

/-- A certified resolver restores every abstracted boundary to its canonical
target content. -/
@[simp]
theorem restoreCostStaticSkeleton_boundary
    (color : CostStaticColor) (boundary : CostRegionBoundaryAssignment)
    (regions : List CostRegionOccurrence)
    (occurrence : CostRegionOccurrence)
    (membership : occurrence ∈ regions) :
    restoreCostStaticSkeleton color
        (resolveCostRegionBoundaries boundary regions)
        (.fvar (costRegionBoundaryVariableName (boundary occurrence))) =
      (boundary occurrence).content := by
  simp [restoreCostStaticSkeleton,
    decodeCostRegionSourceVariableName_boundary,
    resolveCostRegionBoundaries_of_mem boundary regions occurrence membership]

mutual
  /-- Decode one maximal region of the selected color into a source skeleton.
  Every constructor outside that color becomes one rigid, content-keyed
  variable.  `outer` records the exact occurrence at which the caller's
  typed boundary assignment is consulted. -/
  def abstractCostStaticRegionAt (color : CostStaticColor)
      (boundary : CostRegionBoundaryAssignment) (outer : OneHoleContext) :
      Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar (costRegionSourceVariableName name)
    | pattern@(.apply constructor arguments) =>
        match decodeCostStaticConstructor color constructor with
        | some sourceConstructor =>
            .apply sourceConstructor
              (abstractCostStaticApplyRegionListAt color boundary outer
                constructor [] arguments)
        | none =>
            let occurrence : CostRegionOccurrence :=
              { context := outer, content := pattern }
            .fvar (costRegionBoundaryVariableName (boundary occurrence))
    | .lambda binderName body =>
        .lambda binderName
          (abstractCostStaticRegionAt color boundary
            (outer.comp (.lambda binderName .hole)) body)
    | .multiLambda arity binderNames body =>
        .multiLambda arity binderNames
          (abstractCostStaticRegionAt color boundary
            (outer.comp (.multiLambda arity binderNames .hole)) body)
    | .subst body replacement =>
        .subst
          (abstractCostStaticRegionAt color boundary
            (outer.comp (.substBody .hole replacement)) body)
          (abstractCostStaticRegionAt color boundary
            (outer.comp (.substReplacement body .hole)) replacement)
    | .collection collectionType elements rest =>
        .collection collectionType
          (abstractCostStaticCollectionRegionListAt color boundary outer
            collectionType [] elements rest)
          (rest.map costRegionSourceVariableName)

  def abstractCostStaticApplyRegionListAt (color : CostStaticColor)
      (boundary : CostRegionBoundaryAssignment) (outer : OneHoleContext)
      (constructor : String) (before : List Pattern) :
      List Pattern → List Pattern
    | [] => []
    | argument :: after =>
        abstractCostStaticRegionAt color boundary
            (outer.comp (.apply constructor before .hole after)) argument ::
          abstractCostStaticApplyRegionListAt color boundary outer constructor
            (before ++ [argument]) after

  def abstractCostStaticCollectionRegionListAt (color : CostStaticColor)
      (boundary : CostRegionBoundaryAssignment) (outer : OneHoleContext)
      (collectionType : CollType) (before : List Pattern) :
      List Pattern → Option String → List Pattern
    | [], _ => []
    | element :: after, rest =>
        abstractCostStaticRegionAt color boundary
            (outer.comp
              (.collection collectionType before .hole after rest)) element ::
          abstractCostStaticCollectionRegionListAt color boundary outer
            collectionType (before ++ [element]) after rest
end

/-- Public occurrence-sensitive abstraction of one complete stratum. -/
def abstractCostStaticRegion (color : CostStaticColor)
    (boundary : CostRegionBoundaryAssignment) (pattern : Pattern) : Pattern :=
  abstractCostStaticRegionAt color boundary .hole pattern

/-- Free names presented to the source canonicalizer by one abstraction
stratum.  The first summand is the injectively retagged source support; the
second is the finite family of rigid variables naming maximal foreign
regions. -/
def costStaticAbstractionNames (color : CostStaticColor)
    (boundary : CostRegionBoundaryAssignment) (pattern : Pattern) :
    List String :=
  (collectCostStaticSourceNames color pattern).map
      costRegionSourceVariableName ++
    (collectCostStaticBoundaryOccurrences color pattern).map
      (fun occurrence =>
        costRegionBoundaryVariableName (boundary occurrence))

/-- The complete finite namespace exposed below an arbitrary root context. -/
def costStaticAbstractionNamesAt (color : CostStaticColor)
    (boundary : CostRegionBoundaryAssignment) (outer : OneHoleContext)
    (pattern : Pattern) : List String :=
  (collectCostStaticSourceNames color pattern).map
      costRegionSourceVariableName ++
    (collectCostStaticBoundaryOccurrencesAt color outer pattern).map
      (fun occurrence =>
        costRegionBoundaryVariableName (boundary occurrence))

mutual
  /-- Abstraction below any root context introduces exactly retagged source
  names and occurrence-sensitive foreign-boundary names. -/
  theorem mem_freeFvarNames_abstractCostStaticRegionAt_iff
      (color : CostStaticColor) (boundary : CostRegionBoundaryAssignment)
      (outer : OneHoleContext) (pattern : Pattern) (name : String) :
      name ∈ (abstractCostStaticRegionAt color boundary outer pattern).freeFvarNames ↔
        name ∈ costStaticAbstractionNamesAt color boundary outer pattern := by
    cases pattern with
    | bvar index =>
        simp [abstractCostStaticRegionAt, costStaticAbstractionNamesAt,
          collectCostStaticBoundaryOccurrencesAt,
          collectCostStaticSourceNames, Pattern.freeFvarNames]
    | fvar sourceName =>
        simp [abstractCostStaticRegionAt, costStaticAbstractionNamesAt,
          collectCostStaticBoundaryOccurrencesAt,
          collectCostStaticSourceNames, Pattern.freeFvarNames]
    | apply constructor arguments =>
        cases decoded : decodeCostStaticConstructor color constructor with
        | none =>
            simp [abstractCostStaticRegionAt, costStaticAbstractionNamesAt,
              collectCostStaticBoundaryOccurrencesAt,
              collectCostStaticSourceNames, Pattern.freeFvarNames, decoded]
        | some sourceConstructor =>
            simpa [abstractCostStaticRegionAt, costStaticAbstractionNamesAt,
              collectCostStaticBoundaryOccurrencesAt,
              collectCostStaticSourceNames, Pattern.freeFvarNames, decoded]
              using mem_freeFvarNames_abstractCostStaticApplyRegionListAt_iff
                color boundary outer constructor [] arguments name
    | lambda binderName body =>
        simpa [abstractCostStaticRegionAt, costStaticAbstractionNamesAt,
          collectCostStaticBoundaryOccurrencesAt,
          collectCostStaticSourceNames, Pattern.freeFvarNames]
          using mem_freeFvarNames_abstractCostStaticRegionAt_iff color boundary
            (outer.comp (.lambda binderName .hole)) body name
    | multiLambda arity binderNames body =>
        simpa [abstractCostStaticRegionAt, costStaticAbstractionNamesAt,
          collectCostStaticBoundaryOccurrencesAt,
          collectCostStaticSourceNames, Pattern.freeFvarNames]
          using mem_freeFvarNames_abstractCostStaticRegionAt_iff color boundary
            (outer.comp (.multiLambda arity binderNames .hole)) body name
    | subst body replacement =>
        simp only [abstractCostStaticRegionAt, Pattern.freeFvarNames,
          List.mem_append, costStaticAbstractionNamesAt,
          collectCostStaticBoundaryOccurrencesAt,
          collectCostStaticSourceNames, List.map_append]
        rw [mem_freeFvarNames_abstractCostStaticRegionAt_iff color boundary
            (outer.comp (.substBody .hole replacement)) body name,
          mem_freeFvarNames_abstractCostStaticRegionAt_iff color boundary
            (outer.comp (.substReplacement body .hole)) replacement name]
        simp [costStaticAbstractionNamesAt, or_assoc, or_left_comm]
    | collection collectionType elements rest =>
        have elementsClaim :=
          mem_freeFvarNames_abstractCostStaticCollectionRegionListAt_iff
            color boundary outer collectionType [] elements rest name
        cases rest with
        | none =>
            simpa [abstractCostStaticRegionAt, costStaticAbstractionNamesAt,
              collectCostStaticBoundaryOccurrencesAt,
              collectCostStaticSourceNames, Pattern.freeFvarNames,
              List.mem_append, or_assoc, or_left_comm] using elementsClaim
        | some restName =>
            have withRest :
                (name ∈ (abstractCostStaticCollectionRegionListAt color
                      boundary outer collectionType [] elements
                      (some restName)).flatMap Pattern.freeFvarNames ∨
                    name = costRegionSourceVariableName restName) ↔
                  (name ∈
                      (collectCostStaticSourceNameList color elements).map
                            costRegionSourceVariableName ++
                        (collectCostStaticCollectionBoundaryOccurrences color
                          outer collectionType [] elements
                          (some restName)).map
                            (fun occurrence =>
                              costRegionBoundaryVariableName
                                (boundary occurrence)) ∨
                    name = costRegionSourceVariableName restName) :=
              or_congr elementsClaim Iff.rfl
            simpa [abstractCostStaticRegionAt,
              costStaticAbstractionNamesAt,
              collectCostStaticBoundaryOccurrencesAt,
              collectCostStaticSourceNames, Pattern.freeFvarNames,
              List.mem_append, or_assoc, or_left_comm, or_comm] using withRest

  theorem mem_freeFvarNames_abstractCostStaticApplyRegionListAt_iff
      (color : CostStaticColor) (boundary : CostRegionBoundaryAssignment)
      (outer : OneHoleContext) (constructor : String)
      (before arguments : List Pattern) (name : String) :
      name ∈ (abstractCostStaticApplyRegionListAt color boundary outer
          constructor before arguments).flatMap Pattern.freeFvarNames ↔
        name ∈
          (collectCostStaticSourceNameList color arguments).map
              costRegionSourceVariableName ++
            (collectCostStaticApplyBoundaryOccurrences color outer constructor
              before arguments).map
                (fun occurrence =>
                  costRegionBoundaryVariableName (boundary occurrence)) := by
    cases arguments with
    | nil =>
        simp [abstractCostStaticApplyRegionListAt,
          collectCostStaticSourceNameList,
          collectCostStaticApplyBoundaryOccurrences]
    | cons argument after =>
        simp only [abstractCostStaticApplyRegionListAt, List.flatMap_cons,
          collectCostStaticSourceNameList,
          collectCostStaticApplyBoundaryOccurrences, List.map_append,
          List.mem_append]
        rw [mem_freeFvarNames_abstractCostStaticRegionAt_iff color boundary
            (outer.comp (.apply constructor before .hole after)) argument name,
          mem_freeFvarNames_abstractCostStaticApplyRegionListAt_iff color
            boundary outer constructor (before ++ [argument]) after name]
        simp [costStaticAbstractionNamesAt, or_assoc, or_left_comm, or_comm]

  theorem mem_freeFvarNames_abstractCostStaticCollectionRegionListAt_iff
      (color : CostStaticColor) (boundary : CostRegionBoundaryAssignment)
      (outer : OneHoleContext) (collectionType : CollType)
      (before elements : List Pattern) (rest : Option String) (name : String) :
      name ∈ (abstractCostStaticCollectionRegionListAt color boundary outer
          collectionType before elements rest).flatMap Pattern.freeFvarNames ↔
        name ∈
          (collectCostStaticSourceNameList color elements).map
              costRegionSourceVariableName ++
            (collectCostStaticCollectionBoundaryOccurrences color outer
              collectionType before elements rest).map
                (fun occurrence =>
                  costRegionBoundaryVariableName (boundary occurrence)) := by
    cases elements with
    | nil =>
        simp [abstractCostStaticCollectionRegionListAt,
          collectCostStaticSourceNameList,
          collectCostStaticCollectionBoundaryOccurrences]
    | cons element after =>
        simp only [abstractCostStaticCollectionRegionListAt, List.flatMap_cons,
          collectCostStaticSourceNameList,
          collectCostStaticCollectionBoundaryOccurrences, List.map_append,
          List.mem_append]
        rw [mem_freeFvarNames_abstractCostStaticRegionAt_iff color boundary
            (outer.comp
              (.collection collectionType before .hole after rest)) element name,
          mem_freeFvarNames_abstractCostStaticCollectionRegionListAt_iff color
            boundary outer collectionType (before ++ [element]) after rest name]
        simp [costStaticAbstractionNamesAt, or_assoc, or_left_comm, or_comm]
end

/-- Abstraction introduces exactly the two reserved classes of free names:
retagged source variables and the finite, occurrence-sensitive foreign
boundaries collected from this stratum. -/
theorem mem_freeFvarNames_abstractCostStaticRegion_iff
    (color : CostStaticColor) (boundary : CostRegionBoundaryAssignment)
    (pattern : Pattern) (name : String) :
    name ∈ (abstractCostStaticRegion color boundary pattern).freeFvarNames ↔
      name ∈ costStaticAbstractionNames color boundary pattern := by
  simpa [abstractCostStaticRegion, costStaticAbstractionNames,
    costStaticAbstractionNamesAt,
    collectCostStaticBoundaryOccurrences] using
    mem_freeFvarNames_abstractCostStaticRegionAt_iff color boundary .hole
      pattern name

/-- Once an abstracted skeleton has been sorted in a source open fiber, its
normal form cannot mention any name outside the finite namespace assembled
by that abstraction.  This is the exact bridge from typed contextual support
to the executable restoration table. -/
theorem mem_costStaticAbstractionNames_of_mem_normalize
    (source : CIGSLT) (color : CostStaticColor)
    (boundary : CostRegionBoundaryAssignment) (pattern : Pattern)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (skeleton : OpenTerm source.theory free bound sort)
    (skeletonPattern : skeleton.1 =
      abstractCostStaticRegion color boundary pattern)
    {name : String}
    (membership : name ∈
      (source.openCanonical.normalize skeleton).1.freeFvarNames) :
    name ∈ costStaticAbstractionNames color boundary pattern := by
  have sourceMembership :=
    source.openCanonical.normalize_freeFvarNames_subset skeleton membership
  rw [skeletonPattern] at sourceMembership
  exact (mem_freeFvarNames_abstractCostStaticRegion_iff
    color boundary pattern name).mp sourceMembership

/-- Every free name surviving typed source normalization is actionable by
restoration: it either decodes to a genuine source variable or names one of
the finitely collected foreign regions.  Thus the total fallback branch of
`restoreCostStaticSkeleton` is unreachable on a certified stratum. -/
theorem normalizedCostStaticName_decodes_or_resolves
    (source : CIGSLT) (color : CostStaticColor)
    (boundary : CostRegionBoundaryAssignment) (pattern : Pattern)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (skeleton : OpenTerm source.theory free bound sort)
    (skeletonPattern : skeleton.1 =
      abstractCostStaticRegion color boundary pattern)
    {name : String}
    (membership : name ∈
      (source.openCanonical.normalize skeleton).1.freeFvarNames) :
    (∃ sourceName,
        decodeCostRegionSourceVariableName name = some sourceName) ∨
      ∃ occurrence,
        occurrence ∈ collectCostStaticBoundaryOccurrences color pattern ∧
          name = costRegionBoundaryVariableName (boundary occurrence) := by
  have classified := mem_costStaticAbstractionNames_of_mem_normalize
    source color boundary pattern skeleton skeletonPattern membership
  simp only [costStaticAbstractionNames, List.mem_append,
    List.mem_map] at classified
  rcases classified with sourceMembership | boundaryMembership
  · rcases sourceMembership with ⟨sourceName, _membership, equality⟩
    left
    refine ⟨sourceName, ?_⟩
    rw [← equality]
    exact decodeCostRegionSourceVariableName_encode sourceName
  · rcases boundaryMembership with
      ⟨occurrence, occurrenceMembership, equality⟩
    exact Or.inr ⟨occurrence, occurrenceMembership, equality.symm⟩

mutual
  /-- The semantic effect of completing one abstraction stratum: selected
  constructor regions retain their exact target syntax, while each maximal
  foreign application is replaced atomically by the canonical content carried
  in its typed boundary key.  The assignment is consulted at the same exact
  occurrence used by abstraction. -/
  def replaceCostStaticBoundariesAt (color : CostStaticColor)
      (boundary : CostRegionBoundaryAssignment) (outer : OneHoleContext) :
      Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | pattern@(.apply constructor arguments) =>
        match decodeCostStaticConstructor color constructor with
        | some _ =>
            .apply constructor
              (replaceCostStaticApplyBoundaryListAt color boundary outer
                constructor [] arguments)
        | none =>
            boundary { context := outer, content := pattern } |>.content
    | .lambda binderName body =>
        .lambda binderName
          (replaceCostStaticBoundariesAt color boundary
            (outer.comp (.lambda binderName .hole)) body)
    | .multiLambda arity binderNames body =>
        .multiLambda arity binderNames
          (replaceCostStaticBoundariesAt color boundary
            (outer.comp (.multiLambda arity binderNames .hole)) body)
    | .subst body replacement =>
        .subst
          (replaceCostStaticBoundariesAt color boundary
            (outer.comp (.substBody .hole replacement)) body)
          (replaceCostStaticBoundariesAt color boundary
            (outer.comp (.substReplacement body .hole)) replacement)
    | .collection collectionType elements rest =>
        .collection collectionType
          (replaceCostStaticCollectionBoundaryListAt color boundary outer
            collectionType [] elements rest) rest

  def replaceCostStaticApplyBoundaryListAt (color : CostStaticColor)
      (boundary : CostRegionBoundaryAssignment) (outer : OneHoleContext)
      (constructor : String) (before : List Pattern) :
      List Pattern → List Pattern
    | [] => []
    | argument :: after =>
        replaceCostStaticBoundariesAt color boundary
            (outer.comp (.apply constructor before .hole after)) argument ::
          replaceCostStaticApplyBoundaryListAt color boundary outer constructor
            (before ++ [argument]) after

  def replaceCostStaticCollectionBoundaryListAt (color : CostStaticColor)
      (boundary : CostRegionBoundaryAssignment) (outer : OneHoleContext)
      (collectionType : CollType) (before : List Pattern) :
      List Pattern → Option String → List Pattern
    | [], _ => []
    | element :: after, rest =>
        replaceCostStaticBoundariesAt color boundary
            (outer.comp
              (.collection collectionType before .hole after rest)) element ::
          replaceCostStaticCollectionBoundaryListAt color boundary outer
            collectionType (before ++ [element]) after rest
end

/-- Public occurrence-sensitive boundary replacement for a full stratum. -/
def replaceCostStaticBoundaries (color : CostStaticColor)
    (boundary : CostRegionBoundaryAssignment) (pattern : Pattern) : Pattern :=
  replaceCostStaticBoundariesAt color boundary .hole pattern

mutual
  /-- Replacing every maximal foreign occurrence by its own recorded content
  is the identity below any outer context.  The hypothesis is
  occurrence-sensitive: two equal raw subterms at different binder supports
  remain distinct inputs to the boundary assignment. -/
  theorem replaceCostStaticBoundariesAt_eq_self_of_contents
      (color : CostStaticColor) (boundary : CostRegionBoundaryAssignment)
      (outer : OneHoleContext) (pattern : Pattern)
      (contents : ∀ occurrence,
        occurrence ∈ collectCostStaticBoundaryOccurrencesAt color outer pattern →
          (boundary occurrence).content = occurrence.content) :
      replaceCostStaticBoundariesAt color boundary outer pattern = pattern := by
    cases pattern with
    | bvar index => rfl
    | fvar name => rfl
    | apply constructor arguments =>
        cases decoded : decodeCostStaticConstructor color constructor with
        | none =>
            let occurrence : CostRegionOccurrence :=
              { context := outer, content := .apply constructor arguments }
            have contentEquality :
                (boundary occurrence).content =
                  Pattern.apply constructor arguments := by
              simpa [occurrence] using contents occurrence (by
                simp [occurrence, collectCostStaticBoundaryOccurrencesAt,
                  decoded])
            simpa [replaceCostStaticBoundariesAt, decoded, occurrence] using
              contentEquality
        | some sourceConstructor =>
            simp only [replaceCostStaticBoundariesAt, decoded,
              Pattern.apply.injEq, true_and]
            exact replaceCostStaticApplyBoundaryListAt_eq_self_of_contents
              color boundary outer constructor [] arguments
              (by
                intro occurrence membership
                apply contents occurrence
                simpa [collectCostStaticBoundaryOccurrencesAt, decoded] using
                  membership)
    | lambda binderName body =>
        simp only [replaceCostStaticBoundariesAt, Pattern.lambda.injEq]
        exact ⟨trivial,
          replaceCostStaticBoundariesAt_eq_self_of_contents color boundary
            (outer.comp (.lambda binderName .hole)) body
            (by simpa [collectCostStaticBoundaryOccurrencesAt] using contents)⟩
    | multiLambda arity binderNames body =>
        simp only [replaceCostStaticBoundariesAt,
          Pattern.multiLambda.injEq, true_and]
        exact replaceCostStaticBoundariesAt_eq_self_of_contents color boundary
          (outer.comp (.multiLambda arity binderNames .hole)) body
          (by simpa [collectCostStaticBoundaryOccurrencesAt] using contents)
    | subst body replacement =>
        simp only [replaceCostStaticBoundariesAt, Pattern.subst.injEq]
        exact ⟨
          replaceCostStaticBoundariesAt_eq_self_of_contents color boundary
            (outer.comp (.substBody .hole replacement)) body
            (by
              intro occurrence membership
              apply contents occurrence
              simp [collectCostStaticBoundaryOccurrencesAt, membership]),
          replaceCostStaticBoundariesAt_eq_self_of_contents color boundary
            (outer.comp (.substReplacement body .hole)) replacement
            (by
              intro occurrence membership
              apply contents occurrence
              simp [collectCostStaticBoundaryOccurrencesAt, membership])⟩
    | collection collectionType elements rest =>
        simp only [replaceCostStaticBoundariesAt,
          Pattern.collection.injEq, true_and]
        exact ⟨
          replaceCostStaticCollectionBoundaryListAt_eq_self_of_contents
            color boundary outer collectionType [] elements rest
            (by
              intro occurrence membership
              apply contents occurrence
              simpa [collectCostStaticBoundaryOccurrencesAt] using membership),
          trivial⟩

  /-- Ordered application-argument companion to occurrence-sensitive
  identity replacement. -/
  theorem replaceCostStaticApplyBoundaryListAt_eq_self_of_contents
      (color : CostStaticColor) (boundary : CostRegionBoundaryAssignment)
      (outer : OneHoleContext) (constructor : String)
      (before arguments : List Pattern)
      (contents : ∀ occurrence,
        occurrence ∈ collectCostStaticApplyBoundaryOccurrences color outer
            constructor before arguments →
          (boundary occurrence).content = occurrence.content) :
      replaceCostStaticApplyBoundaryListAt color boundary outer constructor
          before arguments = arguments := by
    cases arguments with
    | nil => rfl
    | cons argument after =>
        simp only [replaceCostStaticApplyBoundaryListAt, List.cons.injEq]
        exact ⟨
          replaceCostStaticBoundariesAt_eq_self_of_contents color boundary
            (outer.comp (.apply constructor before .hole after)) argument
            (by
              intro occurrence membership
              apply contents occurrence
              simp [collectCostStaticApplyBoundaryOccurrences, membership]),
          replaceCostStaticApplyBoundaryListAt_eq_self_of_contents color
            boundary outer constructor (before ++ [argument]) after
            (by
              intro occurrence membership
              apply contents occurrence
              simp [collectCostStaticApplyBoundaryOccurrences, membership])⟩

  /-- Ordered collection-element companion to occurrence-sensitive identity
  replacement. -/
  theorem replaceCostStaticCollectionBoundaryListAt_eq_self_of_contents
      (color : CostStaticColor) (boundary : CostRegionBoundaryAssignment)
      (outer : OneHoleContext) (collectionType : CollType)
      (before elements : List Pattern) (rest : Option String)
      (contents : ∀ occurrence,
        occurrence ∈ collectCostStaticCollectionBoundaryOccurrences color outer
            collectionType before elements rest →
          (boundary occurrence).content = occurrence.content) :
      replaceCostStaticCollectionBoundaryListAt color boundary outer
          collectionType before elements rest = elements := by
    cases elements with
    | nil => rfl
    | cons element after =>
        simp only [replaceCostStaticCollectionBoundaryListAt, List.cons.injEq]
        exact ⟨
          replaceCostStaticBoundariesAt_eq_self_of_contents color boundary
            (outer.comp
              (.collection collectionType before .hole after rest)) element
            (by
              intro occurrence membership
              apply contents occurrence
              simp [collectCostStaticCollectionBoundaryOccurrences,
                membership]),
          replaceCostStaticCollectionBoundaryListAt_eq_self_of_contents color
            boundary outer collectionType (before ++ [element]) after rest
            (by
              intro occurrence membership
              apply contents occurrence
              simp [collectCostStaticCollectionBoundaryOccurrences,
                membership])⟩
end

/-- Public identity law for a boundary assignment whose stored contents
agree with every occurrence selected from the complete stratum. -/
theorem replaceCostStaticBoundaries_eq_self_of_contents
    (color : CostStaticColor) (boundary : CostRegionBoundaryAssignment)
    (pattern : Pattern)
    (contents : ∀ occurrence,
      occurrence ∈ collectCostStaticBoundaryOccurrences color pattern →
        (boundary occurrence).content = occurrence.content) :
    replaceCostStaticBoundaries color boundary pattern = pattern := by
  exact replaceCostStaticBoundariesAt_eq_self_of_contents color boundary
    .hole pattern
    (by simpa [collectCostStaticBoundaryOccurrences] using contents)

mutual
  /-- Abstraction followed by restoration below any root context has exactly
  the atomic occurrence-sensitive boundary-replacement semantics. -/
  theorem restoreCostStaticSkeleton_abstractAt_of_resolves
      (color : CostStaticColor) (boundary : CostRegionBoundaryAssignment)
      (outer : OneHoleContext) (pattern : Pattern)
      (resolveBoundary : String → Option Pattern)
      (resolves : ∀ occurrence,
        occurrence ∈ collectCostStaticBoundaryOccurrencesAt color outer pattern →
          resolveBoundary
              (costRegionBoundaryVariableName (boundary occurrence)) =
            some (boundary occurrence).content) :
      restoreCostStaticSkeleton color resolveBoundary
          (abstractCostStaticRegionAt color boundary outer pattern) =
        replaceCostStaticBoundariesAt color boundary outer pattern := by
    cases pattern with
    | bvar index =>
        rfl
    | fvar name =>
        simp [abstractCostStaticRegionAt, restoreCostStaticSkeleton,
          replaceCostStaticBoundariesAt]
    | apply constructor arguments =>
        cases decoded : decodeCostStaticConstructor color constructor with
        | none =>
            let occurrence : CostRegionOccurrence :=
              { context := outer, content := .apply constructor arguments }
            have resolved :
                resolveBoundary
                    (costRegionBoundaryVariableName (boundary occurrence)) =
                  some (boundary occurrence).content := by
              apply resolves occurrence
              simp [occurrence, collectCostStaticBoundaryOccurrencesAt,
                decoded]
            simp [abstractCostStaticRegionAt, replaceCostStaticBoundariesAt,
              decoded, occurrence, restoreCostStaticSkeleton,
              decodeCostRegionSourceVariableName_boundary, resolved]
        | some sourceConstructor =>
            have constructorEquality :
                color.constructorTag ++ sourceConstructor = constructor :=
              (decodeCostStaticConstructor_eq_some_iff color constructor
                sourceConstructor).mp decoded |>.symm
            simp only [abstractCostStaticRegionAt,
              replaceCostStaticBoundariesAt, decoded,
              restoreCostStaticSkeleton, Pattern.apply.injEq,
              constructorEquality, true_and]
            exact restoreCostStaticSkeleton_abstractApplyListAt_of_resolves
              color boundary outer constructor [] arguments resolveBoundary
              (by
                intro occurrence membership
                apply resolves occurrence
                simpa [collectCostStaticBoundaryOccurrencesAt, decoded] using
                  membership)
    | lambda binderName body =>
        simp only [abstractCostStaticRegionAt, restoreCostStaticSkeleton,
          replaceCostStaticBoundariesAt, Pattern.lambda.injEq]
        constructor
        · trivial
        · exact restoreCostStaticSkeleton_abstractAt_of_resolves color boundary
            (outer.comp (.lambda binderName .hole)) body resolveBoundary
            (by simpa [collectCostStaticBoundaryOccurrencesAt] using resolves)
    | multiLambda arity binderNames body =>
        simp only [abstractCostStaticRegionAt, restoreCostStaticSkeleton,
          replaceCostStaticBoundariesAt, Pattern.multiLambda.injEq, true_and]
        exact restoreCostStaticSkeleton_abstractAt_of_resolves color boundary
          (outer.comp (.multiLambda arity binderNames .hole)) body
          resolveBoundary
          (by simpa [collectCostStaticBoundaryOccurrencesAt] using resolves)
    | subst body replacement =>
        simp only [abstractCostStaticRegionAt, restoreCostStaticSkeleton,
          replaceCostStaticBoundariesAt, Pattern.subst.injEq]
        constructor
        · exact restoreCostStaticSkeleton_abstractAt_of_resolves color boundary
            (outer.comp (.substBody .hole replacement)) body resolveBoundary
            (by
              intro occurrence membership
              apply resolves occurrence
              simp [collectCostStaticBoundaryOccurrencesAt, membership])
        · exact restoreCostStaticSkeleton_abstractAt_of_resolves color boundary
            (outer.comp (.substReplacement body .hole)) replacement
            resolveBoundary
            (by
              intro occurrence membership
              apply resolves occurrence
              simp [collectCostStaticBoundaryOccurrencesAt, membership])
    | collection collectionType elements rest =>
        simp only [abstractCostStaticRegionAt, restoreCostStaticSkeleton,
          replaceCostStaticBoundariesAt, Pattern.collection.injEq, true_and]
        constructor
        · exact
            restoreCostStaticSkeleton_abstractCollectionListAt_of_resolves
              color boundary outer collectionType [] elements rest
              resolveBoundary
              (by
                intro occurrence membership
                apply resolves occurrence
                simpa [collectCostStaticBoundaryOccurrencesAt] using membership)
        · cases rest <;>
            simp [decodeCostRegionSourceVariableName_encode]

  theorem restoreCostStaticSkeleton_abstractApplyListAt_of_resolves
      (color : CostStaticColor) (boundary : CostRegionBoundaryAssignment)
      (outer : OneHoleContext) (constructor : String)
      (before arguments : List Pattern)
      (resolveBoundary : String → Option Pattern)
      (resolves : ∀ occurrence,
        occurrence ∈ collectCostStaticApplyBoundaryOccurrences color outer
            constructor before arguments →
          resolveBoundary
              (costRegionBoundaryVariableName (boundary occurrence)) =
            some (boundary occurrence).content) :
      restoreCostStaticSkeletonList color resolveBoundary
          (abstractCostStaticApplyRegionListAt color boundary outer constructor
            before arguments) =
        replaceCostStaticApplyBoundaryListAt color boundary outer constructor
          before arguments := by
    cases arguments with
    | nil => rfl
    | cons argument after =>
        simp only [abstractCostStaticApplyRegionListAt,
          restoreCostStaticSkeletonList,
          replaceCostStaticApplyBoundaryListAt, List.cons.injEq]
        constructor
        · exact restoreCostStaticSkeleton_abstractAt_of_resolves color boundary
            (outer.comp (.apply constructor before .hole after)) argument
            resolveBoundary
            (by
              intro occurrence membership
              apply resolves occurrence
              simp [collectCostStaticApplyBoundaryOccurrences, membership])
        · exact restoreCostStaticSkeleton_abstractApplyListAt_of_resolves color
            boundary outer constructor (before ++ [argument]) after
            resolveBoundary
            (by
              intro occurrence membership
              apply resolves occurrence
              simp [collectCostStaticApplyBoundaryOccurrences, membership])

  theorem restoreCostStaticSkeleton_abstractCollectionListAt_of_resolves
      (color : CostStaticColor) (boundary : CostRegionBoundaryAssignment)
      (outer : OneHoleContext) (collectionType : CollType)
      (before elements : List Pattern) (rest : Option String)
      (resolveBoundary : String → Option Pattern)
      (resolves : ∀ occurrence,
        occurrence ∈ collectCostStaticCollectionBoundaryOccurrences color outer
            collectionType before elements rest →
          resolveBoundary
              (costRegionBoundaryVariableName (boundary occurrence)) =
            some (boundary occurrence).content) :
      restoreCostStaticSkeletonList color resolveBoundary
          (abstractCostStaticCollectionRegionListAt color boundary outer
            collectionType before elements rest) =
        replaceCostStaticCollectionBoundaryListAt color boundary outer
          collectionType before elements rest := by
    cases elements with
    | nil => rfl
    | cons element after =>
        simp only [abstractCostStaticCollectionRegionListAt,
          restoreCostStaticSkeletonList,
          replaceCostStaticCollectionBoundaryListAt, List.cons.injEq]
        constructor
        · exact restoreCostStaticSkeleton_abstractAt_of_resolves color boundary
            (outer.comp
              (.collection collectionType before .hole after rest)) element
            resolveBoundary
            (by
              intro occurrence membership
              apply resolves occurrence
              simp [collectCostStaticCollectionBoundaryOccurrences, membership])
        · exact
            restoreCostStaticSkeleton_abstractCollectionListAt_of_resolves
              color boundary outer collectionType (before ++ [element]) after
              rest resolveBoundary
              (by
                intro occurrence membership
                apply resolves occurrence
                simp [collectCostStaticCollectionBoundaryOccurrences, membership])
end

/-- Abstraction followed by restoration has exactly the atomic
boundary-replacement semantics whenever the resolver covers the complete
occurrence-sensitive boundary list. -/
theorem restoreCostStaticSkeleton_abstract_of_resolves
    (color : CostStaticColor) (boundary : CostRegionBoundaryAssignment)
    (pattern : Pattern) (resolveBoundary : String → Option Pattern)
    (resolves : ∀ occurrence,
      occurrence ∈ collectCostStaticBoundaryOccurrences color pattern →
        resolveBoundary
            (costRegionBoundaryVariableName (boundary occurrence)) =
          some (boundary occurrence).content) :
    restoreCostStaticSkeleton color resolveBoundary
        (abstractCostStaticRegion color boundary pattern) =
      replaceCostStaticBoundaries color boundary pattern := by
  exact restoreCostStaticSkeleton_abstractAt_of_resolves color boundary .hole
    pattern resolveBoundary
    (by simpa [collectCostStaticBoundaryOccurrences] using resolves)

/-- The concrete table collected from a stratum covers every boundary that
its abstraction can introduce. -/
theorem restoreCostStaticSkeleton_abstract
    (color : CostStaticColor) (boundary : CostRegionBoundaryAssignment)
    (pattern : Pattern) :
    restoreCostStaticSkeleton color
        (resolveCostRegionBoundaries boundary
          (collectCostStaticBoundaryOccurrences color pattern))
        (abstractCostStaticRegion color boundary pattern) =
      replaceCostStaticBoundaries color boundary pattern := by
  apply restoreCostStaticSkeleton_abstract_of_resolves
  intro occurrence membership
  exact resolveCostRegionBoundaries_of_mem boundary _ occurrence membership

/-- Decomposition followed by finite-table recomposition is exactly the
original stratum when every typed key records the content of the occurrence
from which it was extracted.  This is the first RegionTree round-trip law;
it uses no canonicalization and therefore cannot hide movement or scope
obligations. -/
theorem restoreCostStaticSkeleton_abstract_eq_self_of_contents
    (color : CostStaticColor) (boundary : CostRegionBoundaryAssignment)
    (pattern : Pattern)
    (contents : ∀ occurrence,
      occurrence ∈ collectCostStaticBoundaryOccurrences color pattern →
        (boundary occurrence).content = occurrence.content) :
    restoreCostStaticSkeleton color
        (resolveCostRegionBoundaries boundary
          (collectCostStaticBoundaryOccurrences color pattern))
        (abstractCostStaticRegion color boundary pattern) = pattern := by
  rw [restoreCostStaticSkeleton_abstract]
  exact replaceCostStaticBoundaries_eq_self_of_contents color boundary pattern
    contents

mutual
  /-- A wholly monochromatic embedded source term introduces no opaque
  boundary below any outer context: abstraction is exactly constructor
  decoding plus hygienic free-variable retagging. -/
  theorem abstractCostStaticRegionAt_mapPattern
      (source : CIGSLT) (color : CostStaticColor)
      (boundary : CostRegionBoundaryAssignment) (outer : OneHoleContext)
      (pattern : Pattern) :
      abstractCostStaticRegionAt color boundary outer
          (mapPattern (color.symbols source) pattern) =
        retagCostRegionFreeVariables pattern := by
    cases pattern with
    | bvar index =>
        simp [mapPattern, abstractCostStaticRegionAt,
          retagCostRegionFreeVariables]
    | fvar name =>
        simp [mapPattern, abstractCostStaticRegionAt,
          retagCostRegionFreeVariables]
    | apply constructor arguments =>
        simp only [mapPattern, mapPatternList_eq_map,
          abstractCostStaticRegionAt,
          decodeCostStaticConstructor_symbols,
          retagCostRegionFreeVariables, Pattern.apply.injEq, true_and]
        exact abstractCostStaticApplyRegionListAt_mapPattern source color
          boundary outer constructor [] arguments
    | lambda binderName body =>
        simp only [mapPattern, abstractCostStaticRegionAt,
          retagCostRegionFreeVariables, Pattern.lambda.injEq, true_and]
        exact abstractCostStaticRegionAt_mapPattern source color boundary
          (outer.comp (.lambda binderName .hole)) body
    | multiLambda arity binderNames body =>
        simp only [mapPattern, abstractCostStaticRegionAt,
          retagCostRegionFreeVariables, Pattern.multiLambda.injEq, true_and]
        exact abstractCostStaticRegionAt_mapPattern source color boundary
          (outer.comp (.multiLambda arity binderNames .hole)) body
    | subst body replacement =>
        simp only [mapPattern, abstractCostStaticRegionAt,
          retagCostRegionFreeVariables, Pattern.subst.injEq]
        exact ⟨
          abstractCostStaticRegionAt_mapPattern source color boundary
            (outer.comp
              (.substBody .hole (mapPattern (color.symbols source) replacement)))
            body,
          abstractCostStaticRegionAt_mapPattern source color boundary
            (outer.comp
              (.substReplacement
                (mapPattern (color.symbols source) body) .hole)) replacement⟩
    | collection collectionType elements rest =>
        simp only [mapPattern, mapPatternList_eq_map,
          abstractCostStaticRegionAt,
          retagCostRegionFreeVariables, Pattern.collection.injEq, true_and]
        constructor
        · exact abstractCostStaticCollectionRegionListAt_mapPattern source color
            boundary outer collectionType [] elements rest
        · trivial

  theorem abstractCostStaticApplyRegionListAt_mapPattern
      (source : CIGSLT) (color : CostStaticColor)
      (boundary : CostRegionBoundaryAssignment) (outer : OneHoleContext)
      (constructor : String) (before arguments : List Pattern) :
      abstractCostStaticApplyRegionListAt color boundary outer
          ((color.symbols source).constructor constructor) before
          (arguments.map (mapPattern (color.symbols source))) =
        retagCostRegionFreeVariableList arguments := by
    cases arguments with
    | nil => rfl
    | cons argument after =>
        simp only [List.map_cons, abstractCostStaticApplyRegionListAt,
          retagCostRegionFreeVariableList, List.cons.injEq]
        constructor
        · exact abstractCostStaticRegionAt_mapPattern source color boundary
            (outer.comp
              (.apply ((color.symbols source).constructor constructor) before
                .hole (after.map (mapPattern (color.symbols source))))) argument
        · exact abstractCostStaticApplyRegionListAt_mapPattern source color
            boundary outer constructor
            (before ++ [mapPattern (color.symbols source) argument]) after

  theorem abstractCostStaticCollectionRegionListAt_mapPattern
      (source : CIGSLT) (color : CostStaticColor)
      (boundary : CostRegionBoundaryAssignment) (outer : OneHoleContext)
      (collectionType : CollType) (before elements : List Pattern)
      (rest : Option String) :
      abstractCostStaticCollectionRegionListAt color boundary outer
          collectionType before
          (elements.map (mapPattern (color.symbols source))) rest =
        retagCostRegionFreeVariableList elements := by
    cases elements with
    | nil => rfl
    | cons element after =>
        simp only [List.map_cons,
          abstractCostStaticCollectionRegionListAt,
          retagCostRegionFreeVariableList, List.cons.injEq]
        constructor
        · exact abstractCostStaticRegionAt_mapPattern source color boundary
            (outer.comp
              (.collection collectionType before .hole
                (after.map (mapPattern (color.symbols source))) rest)) element
        · exact abstractCostStaticCollectionRegionListAt_mapPattern source color
            boundary outer collectionType
            (before ++ [mapPattern (color.symbols source) element]) after rest
end

/-- Public monochromatic specialization of the occurrence-sensitive
abstraction theorem. -/
theorem abstractCostStaticRegion_mapPattern
    (source : CIGSLT) (color : CostStaticColor)
    (boundary : CostRegionBoundaryAssignment) (pattern : Pattern) :
    abstractCostStaticRegion color boundary
        (mapPattern (color.symbols source) pattern) =
      retagCostRegionFreeVariables pattern := by
  exact abstractCostStaticRegionAt_mapPattern source color boundary .hole pattern

/-- Execute one innermost-first normalization stratum on a certified source
skeleton.  The caller must first prove that abstraction, including every
opaque opposite-color boundary, inhabits this exact open source fiber.  Thus
the sole source open section receives all sort and binder indices rather than
reconstructing them from an untyped raw pattern. -/
def normalizeCostStaticStratum (source : CIGSLT)
    (color : CostStaticColor)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (skeleton : OpenTerm source.theory free bound sort) : Pattern :=
  mapPattern (color.symbols source)
    (source.openCanonical.normalize skeleton).1

/-- Exact source-section completeness survives either static Cost embedding.
This is the stratum-local equality engine used by the alternating-region
normalizer: it invokes only the source's authored open canonical section and
then applies the generated symbol map as an ordinary function. -/
theorem normalizeCostStaticStratum_eq_of_openEquationSetoid
    (source : CIGSLT) (color : CostStaticColor)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    {left right : OpenTerm source.theory free bound sort}
    (equivalent :
      (openEquationSetoid source.theory free bound sort).r left right) :
    normalizeCostStaticStratum source color left =
      normalizeCostStaticStratum source color right := by
  exact congrArg
    (fun term => mapPattern (color.symbols source) term.1)
    (source.openCanonical.complete equivalent)

/-- In particular, one authored typed source generator is collapsed exactly
inside either static Cost colour.  The least-equivalence closure is introduced
only to feed the already-authored source section. -/
theorem normalizeCostStaticStratum_eq_of_openEquationGenerator
    (source : CIGSLT) (color : CostStaticColor)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    {left right : OpenTerm source.theory free bound sort}
    (generator : openEquationGenerator source.theory free bound sort
      left right) :
    normalizeCostStaticStratum source color left =
      normalizeCostStaticStratum source color right :=
  normalizeCostStaticStratum_eq_of_openEquationSetoid source color
    (Relation.EqvGen.rel left right generator)

theorem normalizeCostStaticStratum_equationEquiv
    (source : CIGSLT) (color : CostStaticColor)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (skeleton : OpenTerm source.theory free bound sort) :
    EquationSemantics.EquationEquiv defaultBasePremises
      source.costWholeLanguage
      (normalizeCostStaticStratum source color skeleton)
      (mapPattern (color.symbols source) skeleton.1) := by
  exact openEquationSetoid_mapCostStatic source color
    (source.openCanonical.equivalent skeleton)

/-- On a certified monochromatic source term, the stratum is exactly the
typed source normalization after hygienic free-variable retagging. -/
@[simp]
theorem normalizeCostStaticStratum_retagged
    (source : CIGSLT) (color : CostStaticColor)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (term : WellSorted.OpenTerm
      source.theory.presentation.presentation.language free bound sort) :
    normalizeCostStaticStratum source color
        term.retagCostRegionFreeVariables =
      mapPattern (color.symbols source)
        (source.normalizeRetaggedOpenTerm term).1 :=
  rfl

/-- One source normalization stratum transports both its declaration-aware
typing derivation and its reflective binder-support certificate into the
selected Cost static fiber.  This is the typed boundary of the region
algorithm: normalization remains the sole source `LanguageDef` section, and
the Cost mapper merely relabels the certified result. -/
theorem normalizeCostStaticStratum_typedReflectiveSupport
    (source : CIGSLT) (color : CostStaticColor)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (skeleton : WellSorted.OpenTerm
      source.theory.presentation.presentation.language free bound sort)
    (support : ContextSupport.Support)
    (supported : WellSorted.HasTypeWithConstructors
      source.theory.presentation.presentation.language
      (· ∈ source.continuationRetyping.wrappedLabels)
      free bound skeleton.1 (.base sort.1))
    (safe : skeleton.2.1.ReflectiveSupportSafeAt support bound) :
    ∃ targetTyped : WellSorted.HasType source.costWholeLanguage
        (free.map (color.symbols source))
        (bound.map (mapTypeExpr (color.symbols source)))
        (normalizeCostStaticStratum source color skeleton)
        (mapTypeExpr (color.symbols source) (.base sort.1)),
      targetTyped.ReflectiveSupportSafeAt
        (mapCostStaticSupport source color support)
        (bound.map (mapTypeExpr (color.symbols source))) := by
  have normalizedSupported :=
    source.openCanonicalPreservesWrappedConstructorTyping skeleton supported
  have normalizedSafeRaw :=
    source.openCanonical.preservesReflectiveSupport skeleton support bound id
      safe
  have normalizedSafe :
      normalizedSupported.toHasType.ReflectiveSupportSafeAt support bound :=
    normalizedSafeRaw.castTyping
  have normalizedTargetSafe :=
    normalizedSafe.mapCostStaticSupport source color
  simpa [normalizeCostStaticStratum] using
    normalizedTargetSafe.mapCostStatic source color
      normalizedSupported.constructorsWithin

/-- One source normalization stratum preserves reflective support that is
already interpreted in the selected Cost binder codomain.  This is the
mixed-context companion to `normalizeCostStaticStratum_typedReflectiveSupport`:
source binders are acted on by the static type map, while foreign target
binders remain visible without being decoded into a source typing context. -/
theorem normalizeCostStaticStratum_typedTargetReflectiveSupport
    (source : CIGSLT) (color : CostStaticColor)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (skeleton : WellSorted.OpenTerm
      source.theory.presentation.presentation.language free bound sort)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (supported : WellSorted.HasTypeWithConstructors
      source.theory.presentation.presentation.language
      (· ∈ source.continuationRetyping.wrappedLabels)
      free bound skeleton.1 (.base sort.1))
    (safe : skeleton.2.1.ReflectiveSupportSafeAt support available
      (mapTypeExpr (color.symbols source))) :
    ∃ targetTyped : WellSorted.HasType source.costWholeLanguage
        (free.map (color.symbols source))
        (bound.map (mapTypeExpr (color.symbols source)))
        (normalizeCostStaticStratum source color skeleton)
        (mapTypeExpr (color.symbols source) (.base sort.1)),
      targetTyped.ReflectiveSupportSafeAt support available := by
  have normalizedSupported :=
    source.openCanonicalPreservesWrappedConstructorTyping skeleton supported
  have normalizedSafeRaw :=
    source.openCanonical.preservesReflectiveSupport skeleton support available
      (mapTypeExpr (color.symbols source)) safe
  have normalizedSafe :
      normalizedSupported.toHasType.ReflectiveSupportSafeAt support available
        (mapTypeExpr (color.symbols source)) :=
    normalizedSafeRaw.castTyping
  simpa [normalizeCostStaticStratum] using
    normalizedSafe.mapCostStatic source color
      normalizedSupported.constructorsWithin

/-- One normalized static stratum inhabits the complete open Cost carrier.
Besides transported sorting, the theorem preserves canonical binder metadata,
object-pattern shape, and all reflective scope boundaries across both disjoint
Cost colors. -/
theorem normalizeCostStaticStratum_openTermWellSorted
    (source : CIGSLT) (color : CostStaticColor)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (skeleton : WellSorted.OpenTerm
      source.theory.presentation.presentation.language free bound sort)
    (support : ContextSupport.Support)
    (supported : WellSorted.HasTypeWithConstructors
      source.theory.presentation.presentation.language
      (· ∈ source.continuationRetyping.wrappedLabels)
      free bound skeleton.1 (.base sort.1))
    (safe : skeleton.2.1.ReflectiveSupportSafeAt support bound) :
    WellSorted.OpenTermWellSorted source.costWholeLanguage
      (free.map (color.symbols source))
      (bound.map (mapTypeExpr (color.symbols source)))
      (color.mapLangSort source sort)
      (normalizeCostStaticStratum source color skeleton) := by
  obtain ⟨mappedTyped, _mappedSupportSafe⟩ :=
    normalizeCostStaticStratum_typedReflectiveSupport source color skeleton
      support supported safe
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [mapTypeExpr] using mappedTyped
  · simpa [normalizeCostStaticStratum] using
      (source.openCanonical.normalize skeleton).2.2.1
  · simpa [normalizeCostStaticStratum] using
      (source.openCanonical.normalize skeleton).2.2.2.1
  · have mappedOrdinaryScope :
      (mapPattern (color.symbols source)
            (source.openCanonical.normalize skeleton).1).isWellScopedAt
            bound.length = true := by
      simpa only [normalizeCostStaticStratum, List.length_map] using
        mappedTyped.isWellScopedAt
    have mappedReflectiveScope := reflectiveScopeSafeAt_mapCostStatic
      source color (source.openCanonical.normalize skeleton).2.2.2.2
      mappedOrdinaryScope
    simpa only [normalizeCostStaticStratum, List.length_map] using
      mappedReflectiveScope

/-- Complete carrier preservation for a source stratum whose reflective
support already lives in the selected Cost binder codomain.  This is the
carrier-level form needed by finite region tables with mixed-color ambient
binders. -/
theorem normalizeCostStaticStratum_openTermWellSorted_targetSupport
    (source : CIGSLT) (color : CostStaticColor)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (skeleton : WellSorted.OpenTerm
      source.theory.presentation.presentation.language free bound sort)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (supported : WellSorted.HasTypeWithConstructors
      source.theory.presentation.presentation.language
      (· ∈ source.continuationRetyping.wrappedLabels)
      free bound skeleton.1 (.base sort.1))
    (safe : skeleton.2.1.ReflectiveSupportSafeAt support available
      (mapTypeExpr (color.symbols source))) :
    WellSorted.OpenTermWellSorted source.costWholeLanguage
      (free.map (color.symbols source))
      (bound.map (mapTypeExpr (color.symbols source)))
      (color.mapLangSort source sort)
      (normalizeCostStaticStratum source color skeleton) := by
  obtain ⟨mappedTyped, _mappedSupportSafe⟩ :=
    normalizeCostStaticStratum_typedTargetReflectiveSupport source color
      skeleton support available supported safe
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [mapTypeExpr] using mappedTyped
  · simpa [normalizeCostStaticStratum] using
      (source.openCanonical.normalize skeleton).2.2.1
  · simpa [normalizeCostStaticStratum] using
      (source.openCanonical.normalize skeleton).2.2.2.1
  · have mappedOrdinaryScope :
      (mapPattern (color.symbols source)
            (source.openCanonical.normalize skeleton).1).isWellScopedAt
            bound.length = true := by
      simpa only [normalizeCostStaticStratum, List.length_map] using
        mappedTyped.isWellScopedAt
    have mappedReflectiveScope := reflectiveScopeSafeAt_mapCostStatic
      source color (source.openCanonical.normalize skeleton).2.2.2.2
      mappedOrdinaryScope
    simpa only [normalizeCostStaticStratum, List.length_map] using
      mappedReflectiveScope

/-- Restore a normalized static stratum through the proof-carrying boundary
table.  Unlike the raw resolver below, this operation performs the same
reflective supported substitution used by the typing theorem, so boundaries
are weakened through precisely their certified binder contexts. -/
def restoreSupportedNormalizedCostStaticStratum (source : CIGSLT)
    (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext)
    (boundary : TypedCostRegionBoundaryAssignment source color targetFree)
    (regions : List CostRegionOccurrence)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (skeleton : WellSorted.OpenTerm
      source.theory.presentation.presentation.language free bound sort) :
    Pattern :=
  restoreSupportedCostStaticSkeleton source color targetFree boundary regions
    (bound.map (mapTypeExpr (color.symbols source)))
    (normalizeCostStaticStratum source color skeleton)

/-- A normalized static stratum restores to the exact generated Cost typing
fiber whenever its source abstraction context and support agree with the
typed boundary table.  No fact is reconstructed from serialized boundary
keys: all target typing evidence comes from `TypedCostRegionBoundary`. -/
theorem restoreSupportedNormalizedCostStaticStratum_typed
    (source : CIGSLT) (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext)
    (boundary : TypedCostRegionBoundaryAssignment source color targetFree)
    (regions : List CostRegionOccurrence)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (skeleton : WellSorted.OpenTerm
      source.theory.presentation.presentation.language free bound sort)
    (support : ContextSupport.Support)
    (supported : WellSorted.HasTypeWithConstructors
      source.theory.presentation.presentation.language
      (· ∈ source.continuationRetyping.wrappedLabels)
      free bound skeleton.1 (.base sort.1))
    (safe : skeleton.2.1.ReflectiveSupportSafeAt support bound)
    (transport : CostStaticBoundaryTransport source color targetFree free
      support boundary regions) :
    WellSorted.HasType source.costWholeLanguage targetFree
      (bound.map (mapTypeExpr (color.symbols source)))
      (restoreSupportedNormalizedCostStaticStratum source color targetFree
        boundary regions skeleton)
      (mapTypeExpr (color.symbols source) (.base sort.1)) := by
  have mappedPair :=
    normalizeCostStaticStratum_typedReflectiveSupport source color skeleton
      support supported safe
  rw [transport.freeContext, transport.reflectiveSupport] at mappedPair
  obtain ⟨mappedTyped, mappedSafe⟩ := mappedPair
  exact restoreSupportedCostStaticSkeleton_typed source color targetFree
    boundary regions mappedTyped mappedSafe

/-- The complete normalized-and-restored stratum inhabits the target open
Cost carrier.  This strengthens the typing projection above with canonical
binder metadata, object-pattern admissibility, and all generated reflective
scope boundaries. -/
theorem restoreSupportedNormalizedCostStaticStratum_openTermWellSorted
    (source : CIGSLT) (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext)
    (boundary : TypedCostRegionBoundaryAssignment source color targetFree)
    (regions : List CostRegionOccurrence)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (skeleton : WellSorted.OpenTerm
      source.theory.presentation.presentation.language free bound sort)
    (support : ContextSupport.Support)
    (supported : WellSorted.HasTypeWithConstructors
      source.theory.presentation.presentation.language
      (· ∈ source.continuationRetyping.wrappedLabels)
      free bound skeleton.1 (.base sort.1))
    (safe : skeleton.2.1.ReflectiveSupportSafeAt support bound)
    (transport : CostStaticBoundaryTransport source color targetFree free
      support boundary regions) :
    WellSorted.OpenTermWellSorted source.costWholeLanguage targetFree
      (bound.map (mapTypeExpr (color.symbols source)))
      (color.mapLangSort source sort)
      (restoreSupportedNormalizedCostStaticStratum source color targetFree
        boundary regions skeleton) := by
  have mappedWellSorted := normalizeCostStaticStratum_openTermWellSorted
    source color skeleton support supported safe
  rw [transport.freeContext] at mappedWellSorted
  let mappedSkeleton : WellSorted.OpenTerm source.costWholeLanguage
      (mappedCostStaticAbstractionFreeContext source color targetFree boundary
        regions)
      (bound.map (mapTypeExpr (color.symbols source)))
      (color.mapLangSort source sort) :=
    ⟨normalizeCostStaticStratum source color skeleton, mappedWellSorted⟩
  have mappedPair := normalizeCostStaticStratum_typedReflectiveSupport
    source color skeleton support supported safe
  rw [transport.freeContext, transport.reflectiveSupport] at mappedPair
  obtain ⟨_mappedTyped, mappedSafe⟩ := mappedPair
  have mappedSkeletonSafe : mappedSkeleton.2.1.ReflectiveSupportSafeAt
      (costStaticRestorationSupport source color targetFree boundary regions)
      (bound.map (mapTypeExpr (color.symbols source))) :=
    mappedSafe.castTyping
  simpa only [restoreSupportedNormalizedCostStaticStratum, mappedSkeleton] using
    restoreSupportedCostStaticSkeleton_openTermWellSorted source color
      targetFree boundary regions mappedSkeleton mappedSkeletonSafe

/-- Complete one normalization stratum by replacing the rigid variables in
the normalized source skeleton with the canonical target regions they name.
The normalizer remains the source's sole contextual section; the resolver is
only the inverse of the preceding abstraction step. -/
def restoreNormalizedCostStaticStratum (source : CIGSLT)
    (color : CostStaticColor) (boundary : CostRegionBoundaryAssignment)
    (pattern : Pattern)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.theory.presentation.presentation.language}
    (skeleton : OpenTerm source.theory free bound sort) : Pattern :=
  restoreCostStaticSkeleton color
    (resolveCostRegionBoundaries boundary
      (collectCostStaticBoundaryOccurrences color pattern))
    (source.openCanonical.normalize skeleton).1

end Mettapedia.GSLT.LanguageDef
