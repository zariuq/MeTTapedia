import Mettapedia.GSLT.LanguageDef.CostConstruction

/-!
# Functorial action of the declaration-derived Cost construction

The Cost construction uses reserved, injective tags to distinguish source
sorts and constructors from its added apparatus.  This module first defines
the total symbol action induced by a structural map.  Tagged source symbols
are translated inside their tag; apparatus symbols and unrelated strings are
fixed.  The action is total because `PresentationSymbols` is total, while its
identity and composition laws hold on every string, not only on declarations.
-/

namespace Mettapedia.GSLT.LanguageDef

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open StructuralMorphism

/-! ## Total, compositional maps inside reserved tags -/

/-- Remove an exact list prefix, returning the remaining suffix. -/
def dropListPrefix? {α : Type*} [DecidableEq α] :
    List α → List α → Option (List α)
  | [], value => some value
  | _ :: _, [] => none
  | expected :: initial, actual :: value =>
      if expected = actual then dropListPrefix? initial value else none

@[simp]
theorem dropListPrefix?_append {α : Type*} [DecidableEq α]
    (initial suffix : List α) :
    dropListPrefix? initial (initial ++ suffix) = some suffix := by
  induction initial with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [dropListPrefix?, inductionHypothesis]

theorem append_eq_of_dropListPrefix?_eq_some
    {α : Type*} [DecidableEq α]
    {initial value suffix : List α}
    (equality : dropListPrefix? initial value = some suffix) :
    initial ++ suffix = value := by
  induction initial generalizing value with
  | nil =>
      simp [dropListPrefix?] at equality
      exact equality.symm
  | cons expected initial inductionHypothesis =>
      cases value with
      | nil => simp [dropListPrefix?] at equality
      | cons actual value =>
          by_cases headEquality : expected = actual
          · subst actual
            have tailEquality :
                dropListPrefix? initial value = some suffix := by
              simpa [dropListPrefix?] using equality
            simp [inductionHypothesis tailEquality]
          · simp [dropListPrefix?, headEquality] at equality

/-- Apply `mapPayload` only to the payload of one exact reserved tag.
Names outside the tag are fixed. -/
def mapTaggedName (tag : String) (mapPayload : String → String)
    (name : String) : String :=
  match dropListPrefix? tag.toList name.toList with
  | some suffix => tag ++ mapPayload (String.ofList suffix)
  | none => name

@[simp]
theorem mapTaggedName_tagged (tag : String) (mapPayload : String → String)
    (payload : String) :
    mapTaggedName tag mapPayload (tag ++ payload) =
      tag ++ mapPayload payload := by
  simp [mapTaggedName, String.toList_append]

@[simp]
theorem mapTaggedName_id (tag name : String) :
    mapTaggedName tag id name = name := by
  unfold mapTaggedName
  split
  next suffix equality =>
    apply String.toList_inj.mp
    simp only [String.toList_append, id_eq, String.toList_ofList]
    exact append_eq_of_dropListPrefix?_eq_some equality
  next => rfl

theorem mapTaggedName_comp (tag : String) (first second : String → String)
    (name : String) :
    mapTaggedName tag (second ∘ first) name =
      mapTaggedName tag second (mapTaggedName tag first name) := by
  unfold mapTaggedName
  split
  next suffix equality =>
    simp only [String.toList_append, dropListPrefix?_append,
      String.ofList_toList, Function.comp_apply]
  next equality =>
    rw [equality]

@[simp]
theorem dropListPrefix?_baseConstructor_wrappedConstructor
    (payload : String) :
    dropListPrefix? costBaseConstructorTag.toList
      (costWrappedConstructorTag ++ payload).toList = none := by
  simp [costBaseConstructorTag, costWrappedConstructorTag,
    String.toList_append, dropListPrefix?]

/-- Translate payloads in either source-derived constructor namespace while
fixing the Cost apparatus and unrelated strings. -/
def mapCostConstructorName (mapPayload : String → String)
    (name : String) : String :=
  match dropListPrefix? costBaseConstructorTag.toList name.toList with
  | some suffix =>
      costBaseConstructorTag ++ mapPayload (String.ofList suffix)
  | none =>
      match dropListPrefix? costWrappedConstructorTag.toList name.toList with
      | some suffix =>
          costWrappedConstructorTag ++ mapPayload (String.ofList suffix)
      | none => name

@[simp]
theorem mapCostConstructorName_base (mapPayload : String → String)
    (payload : String) :
    mapCostConstructorName mapPayload (costBaseConstructorTag ++ payload) =
      costBaseConstructorTag ++ mapPayload payload := by
  simp [mapCostConstructorName, String.toList_append]

@[simp]
theorem mapCostConstructorName_wrapped (mapPayload : String → String)
    (payload : String) :
    mapCostConstructorName mapPayload
        (costWrappedConstructorTag ++ payload) =
      costWrappedConstructorTag ++ mapPayload payload := by
  unfold mapCostConstructorName
  rw [dropListPrefix?_baseConstructor_wrappedConstructor payload]
  simp [String.toList_append]

@[simp]
theorem mapCostConstructorName_id (name : String) :
    mapCostConstructorName id name = name := by
  unfold mapCostConstructorName
  split
  next suffix equality =>
    apply String.toList_inj.mp
    simp only [String.toList_append, id_eq, String.toList_ofList]
    exact append_eq_of_dropListPrefix?_eq_some equality
  next =>
    split
    next suffix equality =>
      apply String.toList_inj.mp
      simp only [String.toList_append, id_eq, String.toList_ofList]
      exact append_eq_of_dropListPrefix?_eq_some equality
    next => rfl

theorem mapCostConstructorName_comp (first second : String → String)
    (name : String) :
    mapCostConstructorName (second ∘ first) name =
      mapCostConstructorName second (mapCostConstructorName first name) := by
  unfold mapCostConstructorName
  split
  next suffix equality =>
    change costBaseConstructorTag ++
        (second ∘ first) (String.ofList suffix) =
      mapCostConstructorName second
        (costBaseConstructorTag ++ first (String.ofList suffix))
    rw [mapCostConstructorName_base]
    rfl
  next baseEquality =>
    split
    next suffix equality =>
      change costWrappedConstructorTag ++
          (second ∘ first) (String.ofList suffix) =
        mapCostConstructorName second
          (costWrappedConstructorTag ++ first (String.ofList suffix))
      rw [mapCostConstructorName_wrapped]
      rfl
    next wrappedEquality =>
      rw [baseEquality, wrappedEquality]

/-- Translate the source payload of either generated static-equation
namespace while fixing apparatus and unrelated equation names. -/
def mapCostEquationName (mapPayload : String → String)
    (name : String) : String :=
  match dropListPrefix? costBaseEquationTag.toList name.toList with
  | some suffix =>
      costBaseEquationTag ++ mapPayload (String.ofList suffix)
  | none =>
      match dropListPrefix? costWrappedEquationTag.toList name.toList with
      | some suffix =>
          costWrappedEquationTag ++ mapPayload (String.ofList suffix)
      | none => name

@[simp]
theorem mapCostEquationName_base (mapPayload : String → String)
    (payload : String) :
    mapCostEquationName mapPayload (costBaseEquationName payload) =
      costBaseEquationName (mapPayload payload) := by
  simp [mapCostEquationName, costBaseEquationName,
    String.toList_append]

@[simp]
theorem dropListPrefix?_baseEquation_wrappedEquation (payload : String) :
    dropListPrefix? costBaseEquationTag.toList
      (costWrappedEquationName payload).toList = none := by
  simp [costBaseEquationTag, costWrappedEquationTag,
    costWrappedEquationName, String.toList_append, dropListPrefix?]

@[simp]
theorem mapCostEquationName_wrapped (mapPayload : String → String)
    (payload : String) :
    mapCostEquationName mapPayload (costWrappedEquationName payload) =
      costWrappedEquationName (mapPayload payload) := by
  unfold mapCostEquationName
  rw [dropListPrefix?_baseEquation_wrappedEquation payload]
  simp [costWrappedEquationName, String.toList_append]

@[simp]
theorem mapCostEquationName_id (name : String) :
    mapCostEquationName id name = name := by
  unfold mapCostEquationName
  split
  next suffix equality =>
    apply String.toList_inj.mp
    simp only [String.toList_append, id_eq, String.toList_ofList]
    exact append_eq_of_dropListPrefix?_eq_some equality
  next =>
    split
    next suffix equality =>
      apply String.toList_inj.mp
      simp only [String.toList_append, id_eq, String.toList_ofList]
      exact append_eq_of_dropListPrefix?_eq_some equality
    next => rfl

theorem mapCostEquationName_comp (first second : String → String)
    (name : String) :
    mapCostEquationName (second ∘ first) name =
      mapCostEquationName second (mapCostEquationName first name) := by
  unfold mapCostEquationName
  split
  next suffix equality =>
    change costBaseEquationTag ++
        (second ∘ first) (String.ofList suffix) =
      mapCostEquationName second
        (costBaseEquationTag ++ first (String.ofList suffix))
    simpa [costBaseEquationName] using
      (mapCostEquationName_base second (first (String.ofList suffix))).symm
  next baseEquality =>
    split
    next suffix equality =>
      change costWrappedEquationTag ++
          (second ∘ first) (String.ofList suffix) =
        mapCostEquationName second
          (costWrappedEquationTag ++ first (String.ofList suffix))
      simpa [costWrappedEquationName] using
        (mapCostEquationName_wrapped second
          (first (String.ofList suffix))).symm
    next wrappedEquality =>
      rw [baseEquality, wrappedEquality]

/-- Translate source payloads in either generated reflective-presentation
namespace while fixing unrelated declarations. -/
def mapCostReflectiveName (mapPayload : String → String)
    (name : String) : String :=
  match dropListPrefix? costBaseReflectiveTag.toList name.toList with
  | some suffix =>
      costBaseReflectiveTag ++ mapPayload (String.ofList suffix)
  | none =>
      match dropListPrefix? costWrappedReflectiveTag.toList name.toList with
      | some suffix =>
          costWrappedReflectiveTag ++ mapPayload (String.ofList suffix)
      | none => name

@[simp]
theorem mapCostReflectiveName_base (mapPayload : String → String)
    (payload : String) :
    mapCostReflectiveName mapPayload (costBaseReflectiveName payload) =
      costBaseReflectiveName (mapPayload payload) := by
  simp [mapCostReflectiveName, costBaseReflectiveName,
    String.toList_append]

@[simp]
theorem dropListPrefix?_baseReflective_wrappedReflective
    (payload : String) :
    dropListPrefix? costBaseReflectiveTag.toList
      (costWrappedReflectiveName payload).toList = none := by
  simp [costBaseReflectiveTag, costWrappedReflectiveTag,
    costWrappedReflectiveName, String.toList_append, dropListPrefix?]

@[simp]
theorem mapCostReflectiveName_wrapped (mapPayload : String → String)
    (payload : String) :
    mapCostReflectiveName mapPayload (costWrappedReflectiveName payload) =
      costWrappedReflectiveName (mapPayload payload) := by
  unfold mapCostReflectiveName
  rw [dropListPrefix?_baseReflective_wrappedReflective payload]
  simp [costWrappedReflectiveName, String.toList_append]

@[simp]
theorem mapCostReflectiveName_id (name : String) :
    mapCostReflectiveName id name = name := by
  unfold mapCostReflectiveName
  split
  next suffix equality =>
    apply String.toList_inj.mp
    simp only [String.toList_append, id_eq, String.toList_ofList]
    exact append_eq_of_dropListPrefix?_eq_some equality
  next =>
    split
    next suffix equality =>
      apply String.toList_inj.mp
      simp only [String.toList_append, id_eq, String.toList_ofList]
      exact append_eq_of_dropListPrefix?_eq_some equality
    next => rfl

theorem mapCostReflectiveName_comp (first second : String → String)
    (name : String) :
    mapCostReflectiveName (second ∘ first) name =
      mapCostReflectiveName second (mapCostReflectiveName first name) := by
  unfold mapCostReflectiveName
  split
  next suffix equality =>
    change costBaseReflectiveTag ++
        (second ∘ first) (String.ofList suffix) =
      mapCostReflectiveName second
        (costBaseReflectiveTag ++ first (String.ofList suffix))
    simpa [costBaseReflectiveName] using
      (mapCostReflectiveName_base second (first (String.ofList suffix))).symm
  next baseEquality =>
    split
    next suffix equality =>
      change costWrappedReflectiveTag ++
          (second ∘ first) (String.ofList suffix) =
        mapCostReflectiveName second
          (costWrappedReflectiveTag ++ first (String.ofList suffix))
      simpa [costWrappedReflectiveName] using
        (mapCostReflectiveName_wrapped second
          (first (String.ofList suffix))).symm
    next wrappedEquality =>
      rw [baseEquality, wrappedEquality]

/-- Translate source payloads in either generated reflective-rule namespace
while fixing the generated Cost rewrite and unrelated rule names. -/
def mapCostReflectiveRuleName (mapPayload : String → String)
    (name : String) : String :=
  match dropListPrefix? costBaseReflectiveRuleTag.toList name.toList with
  | some suffix =>
      costBaseReflectiveRuleTag ++ mapPayload (String.ofList suffix)
  | none =>
      match dropListPrefix? costWrappedReflectiveRuleTag.toList name.toList with
      | some suffix =>
          costWrappedReflectiveRuleTag ++ mapPayload (String.ofList suffix)
      | none => name

@[simp]
theorem mapCostReflectiveRuleName_base (mapPayload : String → String)
    (payload : String) :
    mapCostReflectiveRuleName mapPayload
        (costBaseReflectiveRuleName payload) =
      costBaseReflectiveRuleName (mapPayload payload) := by
  simp [mapCostReflectiveRuleName, costBaseReflectiveRuleName,
    String.toList_append]

@[simp]
theorem dropListPrefix?_baseReflectiveRule_wrappedReflectiveRule
    (payload : String) :
    dropListPrefix? costBaseReflectiveRuleTag.toList
      (costWrappedReflectiveRuleName payload).toList = none := by
  simp [costBaseReflectiveRuleTag, costWrappedReflectiveRuleTag,
    costWrappedReflectiveRuleName, String.toList_append, dropListPrefix?]

@[simp]
theorem mapCostReflectiveRuleName_wrapped (mapPayload : String → String)
    (payload : String) :
    mapCostReflectiveRuleName mapPayload
        (costWrappedReflectiveRuleName payload) =
      costWrappedReflectiveRuleName (mapPayload payload) := by
  unfold mapCostReflectiveRuleName
  rw [dropListPrefix?_baseReflectiveRule_wrappedReflectiveRule payload]
  simp [costWrappedReflectiveRuleName, String.toList_append]

@[simp]
theorem mapCostReflectiveRuleName_id (name : String) :
    mapCostReflectiveRuleName id name = name := by
  unfold mapCostReflectiveRuleName
  split
  next suffix equality =>
    apply String.toList_inj.mp
    simp only [String.toList_append, id_eq, String.toList_ofList]
    exact append_eq_of_dropListPrefix?_eq_some equality
  next =>
    split
    next suffix equality =>
      apply String.toList_inj.mp
      simp only [String.toList_append, id_eq, String.toList_ofList]
      exact append_eq_of_dropListPrefix?_eq_some equality
    next => rfl

theorem mapCostReflectiveRuleName_comp (first second : String → String)
    (name : String) :
    mapCostReflectiveRuleName (second ∘ first) name =
      mapCostReflectiveRuleName second
        (mapCostReflectiveRuleName first name) := by
  unfold mapCostReflectiveRuleName
  split
  next suffix equality =>
    change costBaseReflectiveRuleTag ++
        (second ∘ first) (String.ofList suffix) =
      mapCostReflectiveRuleName second
        (costBaseReflectiveRuleTag ++ first (String.ofList suffix))
    simpa [costBaseReflectiveRuleName] using
      (mapCostReflectiveRuleName_base second
        (first (String.ofList suffix))).symm
  next baseEquality =>
    split
    next suffix equality =>
      change costWrappedReflectiveRuleTag ++
          (second ∘ first) (String.ofList suffix) =
        mapCostReflectiveRuleName second
          (costWrappedReflectiveRuleTag ++ first (String.ofList suffix))
      simpa [costWrappedReflectiveRuleName] using
        (mapCostReflectiveRuleName_wrapped second
          (first (String.ofList suffix))).symm
    next wrappedEquality =>
      rw [baseEquality, wrappedEquality]

/-! ## Symbol action of the Cost signature -/

/-- Extend a presentation symbol map to the declaration-derived Cost
signature.  Source-derived symbols move inside their reserved tags; all
new apparatus symbols are fixed. -/
def costPresentationSymbols (symbols : PresentationSymbols) :
    PresentationSymbols where
  sort := mapTaggedName costBaseSortTag symbols.sort
  constructor := mapCostConstructorName symbols.constructor
  relation := id
  equation := mapCostEquationName symbols.equation
  rewrite := id
  reflective := mapCostReflectiveName symbols.reflective
  reflectiveRule := mapCostReflectiveRuleName symbols.reflectiveRule

@[simp]
theorem costPresentationSymbols_sort_base
    (symbols : PresentationSymbols) (sort : String) :
    (costPresentationSymbols symbols).sort (costBaseSortName sort) =
      costBaseSortName (symbols.sort sort) := by
  simp [costPresentationSymbols, costBaseSortName, costBaseSortTag]

@[simp]
theorem costPresentationSymbols_constructor_base
    (symbols : PresentationSymbols) (constructor : String) :
    (costPresentationSymbols symbols).constructor
        (costBaseConstructorName constructor) =
      costBaseConstructorName (symbols.constructor constructor) := by
  change mapCostConstructorName symbols.constructor
      (costBaseConstructorTag ++ constructor) =
    costBaseConstructorTag ++ symbols.constructor constructor
  exact mapCostConstructorName_base symbols.constructor constructor

@[simp]
theorem costPresentationSymbols_constructor_wrapped
    (symbols : PresentationSymbols) (constructor : String) :
    (costPresentationSymbols symbols).constructor
        (costWrappedConstructorName constructor) =
      costWrappedConstructorName (symbols.constructor constructor) := by
  change mapCostConstructorName symbols.constructor
      (costWrappedConstructorTag ++ constructor) =
    costWrappedConstructorTag ++ symbols.constructor constructor
  exact mapCostConstructorName_wrapped symbols.constructor constructor

@[simp]
theorem costPresentationSymbols_equation_base
    (symbols : PresentationSymbols) (equation : String) :
    (costPresentationSymbols symbols).equation
        (costBaseEquationName equation) =
      costBaseEquationName (symbols.equation equation) := by
  exact mapCostEquationName_base symbols.equation equation

@[simp]
theorem costPresentationSymbols_equation_wrapped
    (symbols : PresentationSymbols) (equation : String) :
    (costPresentationSymbols symbols).equation
        (costWrappedEquationName equation) =
      costWrappedEquationName (symbols.equation equation) := by
  exact mapCostEquationName_wrapped symbols.equation equation

@[simp]
theorem costPresentationSymbols_reflective_base
    (symbols : PresentationSymbols) (presentation : String) :
    (costPresentationSymbols symbols).reflective
        (costBaseReflectiveName presentation) =
      costBaseReflectiveName (symbols.reflective presentation) := by
  exact mapCostReflectiveName_base symbols.reflective presentation

@[simp]
theorem costPresentationSymbols_reflective_wrapped
    (symbols : PresentationSymbols) (presentation : String) :
    (costPresentationSymbols symbols).reflective
        (costWrappedReflectiveName presentation) =
      costWrappedReflectiveName (symbols.reflective presentation) := by
  exact mapCostReflectiveName_wrapped symbols.reflective presentation

@[simp]
theorem costPresentationSymbols_reflectiveRule_base
    (symbols : PresentationSymbols) (declaration : String) :
    (costPresentationSymbols symbols).reflectiveRule
        (costBaseReflectiveRuleName declaration) =
      costBaseReflectiveRuleName (symbols.reflectiveRule declaration) := by
  exact mapCostReflectiveRuleName_base symbols.reflectiveRule declaration

@[simp]
theorem costPresentationSymbols_rewrite_fixed
    (symbols : PresentationSymbols) (rewrite : String) :
    (costPresentationSymbols symbols).rewrite rewrite = rewrite := rfl

@[simp]
theorem costPresentationSymbols_sort_wrapped
    (symbols : PresentationSymbols) :
    (costPresentationSymbols symbols).sort costWrappedSortName =
      costWrappedSortName := by
  simp [costPresentationSymbols, mapTaggedName, costBaseSortTag,
    costWrappedSortName, dropListPrefix?]

@[simp]
theorem costPresentationSymbols_sort_apparatus
    (symbols : PresentationSymbols) (sort : String) :
    (costPresentationSymbols symbols).sort (costApparatusSortName sort) =
      costApparatusSortName sort := by
  simp [costPresentationSymbols, mapTaggedName, costBaseSortTag,
    costApparatusSortName, dropListPrefix?]

@[simp]
theorem costPresentationSymbols_constructor_apparatus
    (symbols : PresentationSymbols) (constructor : String) :
    (costPresentationSymbols symbols).constructor
        (costApparatusConstructorName constructor) =
      costApparatusConstructorName constructor := by
  simp [costPresentationSymbols, mapCostConstructorName,
    costBaseConstructorTag, costWrappedConstructorTag,
    costApparatusConstructorName, dropListPrefix?]

@[simp]
theorem costPresentationSymbols_id :
    costPresentationSymbols PresentationSymbols.id =
      PresentationSymbols.id := by
  ext name <;>
    simp [costPresentationSymbols, PresentationSymbols.id,
      mapCostConstructorName_id, mapCostEquationName_id,
      mapCostReflectiveName_id, mapCostReflectiveRuleName_id]

theorem costPresentationSymbols_comp
    (first second : PresentationSymbols) :
    costPresentationSymbols (first.comp second) =
      (costPresentationSymbols first).comp
        (costPresentationSymbols second) := by
  ext name <;>
    simp [costPresentationSymbols, PresentationSymbols.comp,
      mapTaggedName_comp, mapCostConstructorName_comp,
      mapCostEquationName_comp, mapCostReflectiveName_comp,
      mapCostReflectiveRuleName_comp]

/-! ## Type-profile naturality -/

@[simp]
theorem mapTypeExpr_costBaseTypeExpr (symbols : PresentationSymbols)
    (type : TypeExpr) :
    mapTypeExpr (costPresentationSymbols symbols) (costBaseTypeExpr type) =
      costBaseTypeExpr (mapTypeExpr symbols type) := by
  induction type <;>
    simp_all [costBaseTypeExpr, mapTypeExpr]

/-- Wrapped retyping commutes with exactly those maps that reflect the
distinguished interacting-sort fiber. -/
theorem mapTypeExpr_costWrappedTypeExpr
    (symbols : PresentationSymbols)
    (sourceInteracting targetInteracting : String)
    (mapsInteracting :
      symbols.sort sourceInteracting = targetInteracting)
    (reflectsInteracting : ∀ sourceSort,
      symbols.sort sourceSort = targetInteracting →
        sourceSort = sourceInteracting)
    (type : TypeExpr) :
    mapTypeExpr (costPresentationSymbols symbols)
        (costWrappedTypeExpr sourceInteracting type) =
      costWrappedTypeExpr targetInteracting
        (mapTypeExpr symbols type) := by
  induction type with
  | base sort =>
      by_cases sourceEquality : sort = sourceInteracting
      · subst sort
        simp [costWrappedTypeExpr, mapTypeExpr, mapsInteracting]
      · have targetInequality :
            symbols.sort sort ≠ targetInteracting := by
          intro targetEquality
          exact sourceEquality (reflectsInteracting sort targetEquality)
        simp [costWrappedTypeExpr, mapTypeExpr, sourceEquality,
          targetInequality]
  | arrow domain codomain domainHypothesis codomainHypothesis =>
      simp [costWrappedTypeExpr, mapTypeExpr, domainHypothesis,
        codomainHypothesis]
  | multiBinder body inductionHypothesis =>
      simp [costWrappedTypeExpr, mapTypeExpr, inductionHypothesis]
  | collection collectionType body inductionHypothesis =>
      simp [costWrappedTypeExpr, mapTypeExpr, inductionHypothesis]

/-- Structural term translation commutes with formation of the base-fiber
copy.  Only constructor names occur in raw patterns; sort naturality is
handled separately by `mapTypeExpr_costBaseTypeExpr`. -/
theorem mapPattern_costBaseStatic_natural
    (symbols : PresentationSymbols) (pattern : Pattern) :
    mapPattern (costPresentationSymbols symbols)
        (mapPattern costBaseStaticSymbols pattern) =
      mapPattern costBaseStaticSymbols (mapPattern symbols pattern) := by
  induction pattern using Pattern.inductionOn <;>
    simp_all [mapPattern, costBaseStaticSymbols,
      costBasePresentationSymbols, List.map_inj_left]

@[simp]
theorem mapPattern_costBasePresentation_natural
    (symbols : PresentationSymbols) (pattern : Pattern) :
    mapPattern (costPresentationSymbols symbols)
        (mapPattern costBasePresentationSymbols pattern) =
      mapPattern costBasePresentationSymbols (mapPattern symbols pattern) := by
  simpa only [mapPattern_costBaseStaticSymbols] using
    mapPattern_costBaseStatic_natural symbols pattern

/-- Structural term translation likewise commutes with the hereditary
wrapped constructor copy. -/
@[simp]
theorem mapPattern_costWrappedStatic_natural
    (symbols : PresentationSymbols) (sourceTheory targetTheory : IGSLT)
    (pattern : Pattern) :
    mapPattern (costPresentationSymbols symbols)
        (mapPattern (costWrappedStaticSymbols sourceTheory) pattern) =
      mapPattern (costWrappedStaticSymbols targetTheory)
        (mapPattern symbols pattern) := by
  induction pattern using Pattern.inductionOn <;>
    simp_all [mapPattern, costWrappedStaticSymbols, List.map_inj_left]

/-- Type-context translation commutes with base-fiber formation. -/
theorem mapTypeContext_costBaseStatic_natural
    (symbols : PresentationSymbols)
    (context : List (String × TypeExpr)) :
    mapTypeContext (costPresentationSymbols symbols)
        (mapTypeContext costBaseStaticSymbols context) =
      mapTypeContext costBaseStaticSymbols
        (mapTypeContext symbols context) := by
  simp only [mapTypeContext, List.map_map]
  apply List.map_congr_left
  intro entry _membership
  rcases entry with ⟨name, type⟩
  simp [mapTypeExpr_costBaseStaticSymbols,
    mapTypeExpr_costBaseTypeExpr]

/-- Type-context translation commutes with hereditary wrapped formation
when the theory map preserves and reflects the interacting-sort fiber. -/
theorem mapTypeContext_costWrappedStatic_natural
    (symbols : PresentationSymbols) (sourceTheory targetTheory : IGSLT)
    (mapsInteracting :
      symbols.sort sourceTheory.presentation.interactingSort.1.name =
        targetTheory.presentation.interactingSort.1.name)
    (reflectsInteracting : ∀ sourceSort,
      symbols.sort sourceSort =
          targetTheory.presentation.interactingSort.1.name →
        sourceSort = sourceTheory.presentation.interactingSort.1.name)
    (context : List (String × TypeExpr)) :
    mapTypeContext (costPresentationSymbols symbols)
        (mapTypeContext (costWrappedStaticSymbols sourceTheory) context) =
      mapTypeContext (costWrappedStaticSymbols targetTheory)
        (mapTypeContext symbols context) := by
  simp only [mapTypeContext, List.map_map]
  apply List.map_congr_left
  intro entry _membership
  rcases entry with ⟨name, type⟩
  simp [mapTypeExpr_costWrappedStaticSymbols,
    mapTypeExpr_costWrappedTypeExpr symbols
      sourceTheory.presentation.interactingSort.1.name
      targetTheory.presentation.interactingSort.1.name mapsInteracting
      reflectsInteracting]

/-- Premise-free base equation transport is natural in presentation maps. -/
theorem mapEquation_costBase_natural
    (symbols : PresentationSymbols) (equation : Equation)
    (premisesEmpty : equation.premises = []) :
    mapEquation (costPresentationSymbols symbols) (costBaseEquation equation) =
      costBaseEquation (mapEquation symbols equation) := by
  rcases equation with ⟨name, context, premises, left, right⟩
  simp only at premisesEmpty
  subst premises
  simp only [costBaseEquation, mapEquation, List.map_nil]
  have sourceEquationName :
      costBaseStaticSymbols.equation name = costBaseEquationName name := rfl
  have targetEquationName :
      costBaseStaticSymbols.equation (symbols.equation name) =
        costBaseEquationName (symbols.equation name) := rfl
  rw [sourceEquationName, targetEquationName,
    costPresentationSymbols_equation_base,
    mapTypeContext_costBaseStatic_natural,
    mapPattern_costBaseStatic_natural,
    mapPattern_costBaseStatic_natural]

/-- Premise-free hereditary wrapped equation transport is natural when the
underlying map preserves and reflects the interacting-sort fiber. -/
theorem mapEquation_costWrapped_natural
    (symbols : PresentationSymbols) (sourceTheory targetTheory : IGSLT)
    (mapsInteracting :
      symbols.sort sourceTheory.presentation.interactingSort.1.name =
        targetTheory.presentation.interactingSort.1.name)
    (reflectsInteracting : ∀ sourceSort,
      symbols.sort sourceSort =
          targetTheory.presentation.interactingSort.1.name →
        sourceSort = sourceTheory.presentation.interactingSort.1.name)
    (equation : Equation) (premisesEmpty : equation.premises = []) :
    mapEquation (costPresentationSymbols symbols)
        (costWrappedEquation sourceTheory equation) =
      costWrappedEquation targetTheory (mapEquation symbols equation) := by
  rcases equation with ⟨name, context, premises, left, right⟩
  simp only at premisesEmpty
  subst premises
  simp only [costWrappedEquation, mapEquation, List.map_nil]
  have sourceEquationName :
      (costWrappedStaticSymbols sourceTheory).equation name =
        costWrappedEquationName name := rfl
  have targetEquationName :
      (costWrappedStaticSymbols targetTheory).equation
          (symbols.equation name) =
        costWrappedEquationName (symbols.equation name) := rfl
  rw [sourceEquationName, targetEquationName,
    costPresentationSymbols_equation_wrapped,
    mapTypeContext_costWrappedStatic_natural symbols sourceTheory targetTheory
      mapsInteracting reflectsInteracting,
    mapPattern_costWrappedStatic_natural symbols sourceTheory targetTheory left,
    mapPattern_costWrappedStatic_natural symbols sourceTheory targetTheory right]

@[simp]
theorem mapTermParam_costBase (symbols : PresentationSymbols)
    (parameter : TermParam) :
    mapTermParam (costPresentationSymbols symbols)
        (mapParameterType costBaseTypeExpr parameter) =
      mapParameterType costBaseTypeExpr (mapTermParam symbols parameter) := by
  cases parameter <;>
    simp [mapTermParam, mapParameterType, mapTypeExpr_costBaseTypeExpr]

theorem mapTermParam_costWrapped
    (symbols : PresentationSymbols)
    (sourceInteracting targetInteracting : String)
    (mapsInteracting :
      symbols.sort sourceInteracting = targetInteracting)
    (reflectsInteracting : ∀ sourceSort,
      symbols.sort sourceSort = targetInteracting →
        sourceSort = sourceInteracting)
    (parameter : TermParam) :
    mapTermParam (costPresentationSymbols symbols)
        (mapParameterType (costWrappedTypeExpr sourceInteracting) parameter) =
      mapParameterType (costWrappedTypeExpr targetInteracting)
        (mapTermParam symbols parameter) := by
  cases parameter <;>
    simp [mapTermParam, mapParameterType,
      mapTypeExpr_costWrappedTypeExpr symbols sourceInteracting
        targetInteracting mapsInteracting reflectsInteracting]

/-! ## Preservation and reflection of the selected continuation fibers -/

namespace CIGSLT.Morphism

theorem mapsInteractingSortName {source target : CIGSLT}
    (morphism : source.Morphism target) :
    morphism.underlying.structural.structural.symbols.sort
        source.theory.presentation.interactingSort.1.name =
      target.theory.presentation.interactingSort.1.name := by
  have equality := congrArg
    (fun sort => sort.1.name)
    morphism.underlying.structural.mapsInteractingSort
  exact equality

/-- The selected authored interaction rewrite is transported exactly, not
merely mapped to some target declaration. -/
theorem mapsInteractionRewriteValue {source target : CIGSLT}
    (morphism : source.Morphism target) :
    mapRewriteRule morphism.underlying.structural.structural.symbols
        source.theory.presentation.interactionRewrite.1 =
      target.theory.presentation.interactionRewrite.1 := by
  exact congrArg Subtype.val
    morphism.underlying.structural.mapsInteractionRewrite

theorem mapsInteractionRewriteTypeContext {source target : CIGSLT}
    (morphism : source.Morphism target) :
    mapTypeContext morphism.underlying.structural.structural.symbols
        source.theory.presentation.interactionRewrite.1.typeContext =
      target.theory.presentation.interactionRewrite.1.typeContext := by
  exact congrArg RewriteRule.typeContext morphism.mapsInteractionRewriteValue

theorem mapsInteractionRewriteLeft {source target : CIGSLT}
    (morphism : source.Morphism target) :
    mapPattern morphism.underlying.structural.structural.symbols
        source.theory.presentation.interactionRewrite.1.left =
      target.theory.presentation.interactionRewrite.1.left := by
  exact congrArg RewriteRule.left morphism.mapsInteractionRewriteValue

theorem mapsInteractionRewriteRight {source target : CIGSLT}
    (morphism : source.Morphism target) :
    mapPattern morphism.underlying.structural.structural.symbols
        source.theory.presentation.interactionRewrite.1.right =
      target.theory.presentation.interactionRewrite.1.right := by
  exact congrArg RewriteRule.right morphism.mapsInteractionRewriteValue

/-- Structural term maps preserve the schema-variable name selected by the
program continuation. -/
theorem mapsProgramContinuationVariableName {source target : CIGSLT}
    (morphism : source.Morphism target) :
    source.cut.program.continuationVariable.name =
      target.cut.program.continuationVariable.name := by
  have sourceName := ContinuationSchemaVariable.patternName?_mapPattern
    morphism.underlying.structural.structural.symbols
    source.cut.program.continuationVariable
  rw [morphism.mapsProgramContinuation] at sourceName
  rw [ContinuationSchemaVariable.patternName?_eq_name
    target.cut.program.continuationVariable] at sourceName
  exact Option.some.inj sourceName.symm

/-- Structural term maps preserve the schema-variable name selected by the
environment continuation. -/
theorem mapsEnvironmentContinuationVariableName {source target : CIGSLT}
    (morphism : source.Morphism target) :
    source.cut.environment.continuationVariable.name =
      target.cut.environment.continuationVariable.name := by
  have sourceName := ContinuationSchemaVariable.patternName?_mapPattern
    morphism.underlying.structural.structural.symbols
    source.cut.environment.continuationVariable
  rw [morphism.mapsEnvironmentContinuation] at sourceName
  rw [ContinuationSchemaVariable.patternName?_eq_name
    target.cut.environment.continuationVariable] at sourceName
  exact Option.some.inj sourceName.symm

theorem mapsProgramConstructorRule {source target : CIGSLT}
    (morphism : source.Morphism target) :
    mapGrammarRule morphism.underlying.structural.structural.symbols
        source.cut.program.constructor.1 =
      target.cut.program.constructor.1 := by
  have equality := congrArg
    (fun constructor => constructor.1)
    morphism.mapsProgramConstructor
  exact equality

theorem mapsEnvironmentConstructorRule {source target : CIGSLT}
    (morphism : source.Morphism target) :
    mapGrammarRule morphism.underlying.structural.structural.symbols
        source.cut.environment.constructor.1 =
      target.cut.environment.constructor.1 := by
  have equality := congrArg
    (fun constructor => constructor.1)
    morphism.mapsEnvironmentConstructor
  exact equality

theorem mapConstructor_eq_program_iff {source target : CIGSLT}
    (morphism : source.Morphism target) (constructor : GrammarRule) :
    mapGrammarRule morphism.underlying.structural.structural.symbols
          constructor = target.cut.program.constructor.1 ↔
      constructor = source.cut.program.constructor.1 := by
  constructor
  · exact morphism.reflectsProgramConstructor constructor
  · intro equality
    subst constructor
    exact morphism.mapsProgramConstructorRule

theorem mapConstructor_eq_environment_iff {source target : CIGSLT}
    (morphism : source.Morphism target) (constructor : GrammarRule) :
    mapGrammarRule morphism.underlying.structural.structural.symbols
          constructor = target.cut.environment.constructor.1 ↔
      constructor = source.cut.environment.constructor.1 := by
  constructor
  · exact morphism.reflectsEnvironmentConstructor constructor
  · intro equality
    subst constructor
    exact morphism.mapsEnvironmentConstructorRule

/-- The finite wrapped-constructor fiber is preserved and reflected on every
authored source constructor.  The label formulation is what the induced
contractum translation consumes; uniqueness of authored labels makes it
equivalent to the constructor-level morphism laws. -/
theorem mapConstructorLabel_mem_wrappedLabels_iff
    {source target : CIGSLT}
    (morphism : source.Morphism target)
    (constructor :
      AuthoredConstructor source.theory.presentation.presentation) :
    morphism.underlying.structural.structural.symbols.constructor
          constructor.1.label ∈
        target.continuationRetyping.wrappedLabels ↔
      constructor.1.label ∈
        source.continuationRetyping.wrappedLabels := by
  change
    (morphism.underlying.structural.structural.mapConstructor
        constructor).1.label ∈
          target.continuationRetyping.wrappedLabels ↔
      constructor.1.label ∈
        source.continuationRetyping.wrappedLabels
  rw [target.continuationRetyping.mem_wrappedLabels_iff,
    source.continuationRetyping.mem_wrappedLabels_iff]
  constructor
  · exact morphism.reflectsWrappedConstructors constructor
  · exact morphism.mapsWrappedConstructors constructor

/-- Continuation-retyped contracta are natural in continued theory maps.
The total wrapped-label fiber law is precisely what aligns the constructor
choice at every raw schema node; all remaining pattern structure is mapped
pointwise. -/
theorem mapContractum_natural {source target : CIGSLT}
    (morphism : source.Morphism target) (pattern : Pattern) :
    mapPattern
        (costPresentationSymbols
          morphism.underlying.structural.structural.symbols)
        (source.continuationRetyping.mapContractum pattern) =
      target.continuationRetyping.mapContractum
        (mapPattern morphism.underlying.structural.structural.symbols
          pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      simp [ContinuationRetypingPlan.mapContractum, mapPattern]
  | hfvar name =>
      simp [ContinuationRetypingPlan.mapContractum, mapPattern]
  | happly constructor arguments inductionHypothesis =>
      by_cases wrapped :
          constructor ∈ source.continuationRetyping.wrappedLabels
      · have targetWrapped :
            morphism.underlying.structural.structural.symbols.constructor
                constructor ∈
              target.continuationRetyping.wrappedLabels :=
          (morphism.mapsWrappedLabelMembership constructor).2 wrapped
        simp [ContinuationRetypingPlan.mapContractum,
          ContinuationRetypingPlan.mapContractumList_eq_map,
          mapPattern, List.map_map, wrapped, targetWrapped]
        exact inductionHypothesis
      · have targetNotWrapped :
            morphism.underlying.structural.structural.symbols.constructor
                constructor ∉
              target.continuationRetyping.wrappedLabels := by
          intro targetWrapped
          exact wrapped
            ((morphism.mapsWrappedLabelMembership constructor).1
              targetWrapped)
        simp [ContinuationRetypingPlan.mapContractum,
          ContinuationRetypingPlan.mapContractumList_eq_map,
          mapPattern, List.map_map, wrapped, targetNotWrapped]
        exact inductionHypothesis
  | hlambda binder body inductionHypothesis =>
      simp [ContinuationRetypingPlan.mapContractum, mapPattern,
        inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [ContinuationRetypingPlan.mapContractum, mapPattern,
        inductionHypothesis]
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp [ContinuationRetypingPlan.mapContractum, mapPattern,
        bodyHypothesis, replacementHypothesis]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp [ContinuationRetypingPlan.mapContractum,
        ContinuationRetypingPlan.mapContractumList_eq_map,
        mapPattern, List.map_map]
      exact inductionHypothesis

/-- Selected continuation positions are invariant under a continued theory
map.  The reflection fields are exactly what rules out newly selected fibers
created by a collapsing symbol translation. -/
theorem isSelectedContinuation_map {source target : CIGSLT}
    (morphism : source.Morphism target) (constructor : GrammarRule)
    (index : Nat) :
    isSelectedContinuation target.cut
        (mapGrammarRule
          morphism.underlying.structural.structural.symbols constructor)
        index =
      isSelectedContinuation source.cut constructor index := by
  apply Bool.eq_iff_iff.mpr
  simp only [isSelectedContinuation, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq]
  rw [morphism.mapConstructor_eq_program_iff,
    morphism.mapConstructor_eq_environment_iff,
    ← morphism.mapsProgramContinuationIndex,
    ← morphism.mapsEnvironmentContinuationIndex]

theorem mapTermParam_costBaseParameter {source target : CIGSLT}
    (morphism : source.Morphism target) (constructor : GrammarRule)
    (entry : TermParam × Nat) :
    mapTermParam
        (costPresentationSymbols
          morphism.underlying.structural.structural.symbols)
        (costBaseParameter source.cut constructor entry) =
      costBaseParameter target.cut
        (mapGrammarRule
          morphism.underlying.structural.structural.symbols constructor)
        (mapTermParam morphism.underlying.structural.structural.symbols
          entry.1, entry.2) := by
  unfold costBaseParameter
  rw [morphism.isSelectedContinuation_map constructor entry.2]
  split
  · exact mapTermParam_costWrapped
      morphism.underlying.structural.structural.symbols
      source.theory.presentation.interactingSort.1.name
      target.theory.presentation.interactingSort.1.name
      morphism.mapsInteractingSortName morphism.reflectsInteractingSort entry.1
  · exact mapTermParam_costBase
      morphism.underlying.structural.structural.symbols entry.1

theorem map_costBaseParameter_list {source target : CIGSLT}
    (morphism : source.Morphism target) (constructor : GrammarRule) :
    (constructor.params.zipIdx.map
        (costBaseParameter source.cut constructor)).map
        (mapTermParam (costPresentationSymbols
          morphism.underlying.structural.structural.symbols)) =
      (mapGrammarRule morphism.underlying.structural.structural.symbols
          constructor).params.zipIdx.map
        (costBaseParameter target.cut
          (mapGrammarRule
            morphism.underlying.structural.structural.symbols constructor)) := by
  simp only [mapGrammarRule]
  rw [List.zipIdx_map]
  simp only [List.map_map]
  apply List.map_congr_left
  intro entry _membership
  rcases entry with ⟨parameter, index⟩
  exact morphism.mapTermParam_costBaseParameter constructor
    (parameter, index)

/-- Base constructor retyping is natural in continued theory maps. -/
theorem mapGrammarRule_costBaseConstructor {source target : CIGSLT}
    (morphism : source.Morphism target) (constructor : GrammarRule) :
    mapGrammarRule
        (costPresentationSymbols
          morphism.underlying.structural.structural.symbols)
        (costBaseConstructor source.cut constructor) =
      costBaseConstructor target.cut
        (mapGrammarRule
          morphism.underlying.structural.structural.symbols constructor) := by
  have parameters := morphism.map_costBaseParameter_list constructor
  cases constructor
  simp only [costBaseConstructor, mapGrammarRule] at parameters ⊢
  congr <;> simp

theorem map_costWrappedParameter_list {source target : CIGSLT}
    (morphism : source.Morphism target) (parameters : List TermParam) :
    (parameters.map (mapParameterType
        (costWrappedTypeExpr
          source.theory.presentation.interactingSort.1.name))).map
        (mapTermParam (costPresentationSymbols
          morphism.underlying.structural.structural.symbols)) =
      (parameters.map
          (mapTermParam
            morphism.underlying.structural.structural.symbols)).map
        (mapParameterType (costWrappedTypeExpr
          target.theory.presentation.interactingSort.1.name)) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro parameter _membership
  exact mapTermParam_costWrapped
    morphism.underlying.structural.structural.symbols
    source.theory.presentation.interactingSort.1.name
    target.theory.presentation.interactingSort.1.name
    morphism.mapsInteractingSortName morphism.reflectsInteractingSort
    parameter

theorem map_costWrappedCategory {source target : CIGSLT}
    (morphism : source.Morphism target) (category : String) :
    (costPresentationSymbols
      morphism.underlying.structural.structural.symbols).sort
        (if category = source.theory.presentation.interactingSort.1.name then
          costWrappedSortName else costBaseSortName category) =
      if morphism.underlying.structural.structural.symbols.sort category =
          target.theory.presentation.interactingSort.1.name then
        costWrappedSortName
      else
        costBaseSortName
          (morphism.underlying.structural.structural.symbols.sort category) := by
  by_cases sourceEquality :
      category = source.theory.presentation.interactingSort.1.name
  · subst category
    simp [morphism.mapsInteractingSortName]
  · have targetInequality :
        morphism.underlying.structural.structural.symbols.sort category ≠
          target.theory.presentation.interactingSort.1.name := by
      intro targetEquality
      exact sourceEquality
        (morphism.reflectsInteractingSort category targetEquality)
    simp [sourceEquality, targetInequality]

/-- Wrapped residual constructors are natural in continued theory maps. -/
theorem mapGrammarRule_costWrappedConstructor {source target : CIGSLT}
    (morphism : source.Morphism target) (constructor : GrammarRule) :
    mapGrammarRule
        (costPresentationSymbols
          morphism.underlying.structural.structural.symbols)
        (costWrappedConstructor (theory := source.theory) constructor) =
      costWrappedConstructor (theory := target.theory)
        (mapGrammarRule
          morphism.underlying.structural.structural.symbols constructor) := by
  have parameters := morphism.map_costWrappedParameter_list constructor.params
  have categoryEquality := morphism.map_costWrappedCategory constructor.category
  cases constructor
  simp only [costWrappedConstructor, mapGrammarRule] at parameters categoryEquality ⊢
  congr 1
  simp

/-! ## Structural action on the generated continuation signature -/

@[simp]
theorem mapTypeDecl_costBase
    (symbols : PresentationSymbols) (declaration : TypeDecl) :
    mapTypeDecl (costPresentationSymbols symbols)
        { declaration with name := costBaseSortName declaration.name } =
      { mapTypeDecl symbols declaration with
        name := costBaseSortName (symbols.sort declaration.name) } := by
  cases declaration
  simp [mapTypeDecl, costPresentationSymbols, costBaseSortName,
    costBaseSortTag]

/-- Continued maps induce structural maps between the exact generated
continuation signatures.  This is the declaration-level action underlying
the Cost signature; it adds no equations or reductions. -/
def continuationRetypingStructural {source target : CIGSLT}
    (morphism : source.Morphism target) :
    StructuralMorphism
      source.continuationRetyping.generatedPresentation
      target.continuationRetyping.generatedPresentation where
  symbols := costPresentationSymbols
    morphism.underlying.structural.structural.symbols
  mapsTypes declaration membership := by
    change List.Mem declaration
      ((source.theory.presentation.presentation.language.types.map fun entry =>
          { entry with name := costBaseSortName entry.name }) ++
        [TypeDecl.plain costWrappedSortName]) at membership
    change List.Mem (mapTypeDecl
        (costPresentationSymbols
          morphism.underlying.structural.structural.symbols) declaration)
      ((target.theory.presentation.presentation.language.types.map fun entry =>
          { entry with name := costBaseSortName entry.name }) ++
        [TypeDecl.plain costWrappedSortName])
    rcases List.mem_append.mp membership with
      baseMembership | wrappedMembership
    · rcases List.mem_map.mp baseMembership with
        ⟨sourceDeclaration, sourceMembership, rfl⟩
      apply List.mem_append_left
      apply List.mem_map.mpr
      refine ⟨mapTypeDecl
          morphism.underlying.structural.structural.symbols
          sourceDeclaration,
        morphism.underlying.structural.structural.mapsTypes
          sourceDeclaration sourceMembership, ?_⟩
      exact (mapTypeDecl_costBase
        morphism.underlying.structural.structural.symbols
        sourceDeclaration).symm
    · have wrappedEquality : declaration = TypeDecl.plain costWrappedSortName :=
        List.mem_singleton.mp wrappedMembership
      subst declaration
      apply List.mem_append_right
      simp [mapTypeDecl, TypeDecl.plain]
  mapsTerms constructor membership := by
    change List.Mem constructor
      (source.theory.presentation.presentation.language.terms.map
          (costBaseConstructor source.cut) ++
        source.continuationRetyping.wrappedConstructors.map
          (fun entry => costWrappedConstructor (theory := source.theory) entry.1))
      at membership
    change List.Mem (mapGrammarRule
        (costPresentationSymbols
          morphism.underlying.structural.structural.symbols) constructor)
      (target.theory.presentation.presentation.language.terms.map
          (costBaseConstructor target.cut) ++
        target.continuationRetyping.wrappedConstructors.map
          (fun entry => costWrappedConstructor (theory := target.theory) entry.1))
    rcases List.mem_append.mp membership with
      baseMembership | wrappedMembership
    · rcases List.mem_map.mp baseMembership with
        ⟨sourceConstructor, sourceMembership, rfl⟩
      apply List.mem_append_left
      apply List.mem_map.mpr
      refine ⟨mapGrammarRule
          morphism.underlying.structural.structural.symbols
          sourceConstructor,
        morphism.underlying.structural.structural.mapsTerms
          sourceConstructor sourceMembership, ?_⟩
      exact (morphism.mapGrammarRule_costBaseConstructor
        sourceConstructor).symm
    · rcases List.mem_map.mp wrappedMembership with
        ⟨sourceConstructor, sourceMembership, rfl⟩
      apply List.mem_append_right
      apply List.mem_map.mpr
      refine ⟨morphism.underlying.structural.structural.mapConstructor
          sourceConstructor,
        morphism.mapsWrappedConstructors sourceConstructor sourceMembership,
        ?_⟩
      exact (morphism.mapGrammarRule_costWrappedConstructor
        sourceConstructor.1).symm
  mapsEquations equation membership := by
    change List.Mem equation [] at membership
    exact (List.not_mem_nil membership).elim
  mapsRewrites rewrite membership := by
    change List.Mem rewrite [] at membership
    exact (List.not_mem_nil membership).elim
  mapsReflectivePresentations declaration membership := by
    change List.Mem declaration [] at membership
    exact (List.not_mem_nil membership).elim
  mapsReflectiveRules declaration membership := by
    change List.Mem declaration [] at membership
    exact (List.not_mem_nil membership).elim

/-! ## Conservative extension by the fixed Cost apparatus -/

theorem map_costCoreTypes
    (symbols : PresentationSymbols) :
    costCoreTypes.map
        (mapTypeDecl (costPresentationSymbols symbols)) =
      costCoreTypes := by
  simp [costCoreTypes, costCoreSortSuffixes, mapTypeDecl, TypeDecl.plain]

theorem map_costCoreConstructors {source target : CIGSLT}
    (morphism : source.Morphism target) :
    (costCoreConstructors
        source.theory.presentation.interactingSort.1.name).map
        (mapGrammarRule (costPresentationSymbols
          morphism.underlying.structural.structural.symbols)) =
      costCoreConstructors
        target.theory.presentation.interactingSort.1.name := by
  simp [costCoreConstructors, costSignatureUnitConstructor,
    costSignatureProductConstructor, costSignedConstructor,
    costTokenStackEmptyConstructor, costTokenStackConsConstructor,
    costFundingConstructor, costContactConstructor,
    costSignatureSortName, costTokenStackSortName,
    costSignatureUnitConstructorName, costSignatureProductConstructorName,
    costSignedConstructorName, costTokenStackEmptyConstructorName,
    costTokenStackConsConstructorName, costFundingConstructorName,
    costContactConstructorName, mapGrammarRule, mapTermParam, mapTypeExpr,
    morphism.mapsInteractingSortName]

/-- The structural Cost-core action maps generated declarations through the
continued theory map and fixes the generic Cost apparatus. -/
def costCoreStructural {source target : CIGSLT}
    (morphism : source.Morphism target) :
    StructuralMorphism source.costCorePresentation target.costCorePresentation where
  symbols := costPresentationSymbols
    morphism.underlying.structural.structural.symbols
  mapsTypes declaration membership := by
    change List.Mem declaration
      (source.continuationRetyping.generatedLanguage.types ++ costCoreTypes)
      at membership
    change List.Mem (mapTypeDecl
        (costPresentationSymbols
          morphism.underlying.structural.structural.symbols) declaration)
      (target.continuationRetyping.generatedLanguage.types ++ costCoreTypes)
    rcases List.mem_append.mp membership with
      generatedMembership | apparatusMembership
    · exact List.mem_append_left _
        ((morphism.continuationRetypingStructural).mapsTypes
          declaration generatedMembership)
    · apply List.mem_append_right
      have mappedMembership : List.Mem
          (mapTypeDecl (costPresentationSymbols
            morphism.underlying.structural.structural.symbols) declaration)
          (costCoreTypes.map (mapTypeDecl (costPresentationSymbols
            morphism.underlying.structural.structural.symbols))) :=
        List.mem_map_of_mem apparatusMembership
      rw [map_costCoreTypes] at mappedMembership
      exact mappedMembership
  mapsTerms constructor membership := by
    change List.Mem constructor
      (source.continuationRetyping.generatedLanguage.terms ++
        costCoreConstructors
          source.theory.presentation.interactingSort.1.name) at membership
    change List.Mem (mapGrammarRule
        (costPresentationSymbols
          morphism.underlying.structural.structural.symbols) constructor)
      (target.continuationRetyping.generatedLanguage.terms ++
        costCoreConstructors
          target.theory.presentation.interactingSort.1.name)
    rcases List.mem_append.mp membership with
      generatedMembership | apparatusMembership
    · exact List.mem_append_left _
        ((morphism.continuationRetypingStructural).mapsTerms
          constructor generatedMembership)
    · apply List.mem_append_right
      have mappedMembership : List.Mem
          (mapGrammarRule (costPresentationSymbols
            morphism.underlying.structural.structural.symbols) constructor)
          ((costCoreConstructors
            source.theory.presentation.interactingSort.1.name).map
              (mapGrammarRule (costPresentationSymbols
                morphism.underlying.structural.structural.symbols))) :=
        List.mem_map_of_mem apparatusMembership
      rw [morphism.map_costCoreConstructors] at mappedMembership
      exact mappedMembership
  mapsEquations equation membership := by
    change List.Mem equation [] at membership
    exact (List.not_mem_nil membership).elim
  mapsRewrites rewrite membership := by
    change List.Mem rewrite [] at membership
    exact (List.not_mem_nil membership).elim
  mapsReflectivePresentations declaration membership := by
    change List.Mem declaration [] at membership
    exact (List.not_mem_nil membership).elim
  mapsReflectiveRules declaration membership := by
    change List.Mem declaration [] at membership
    exact (List.not_mem_nil membership).elim

end CIGSLT.Morphism

/-! ## Mathlib functor -/

namespace CIGSLT

/-- The declaration-derived Cost core is functorial from continued
interactive theories to exact validated language definitions. -/
def costCoreFunctor : CategoryTheory.Functor CIGSLT ValidatedLanguageDef where
  obj source := source.costCorePresentation
  map morphism := CIGSLT.Morphism.costCoreStructural morphism
  map_id source := by
    apply StructuralMorphism.ext
    exact costPresentationSymbols_id
  map_comp first second := by
    apply StructuralMorphism.ext
    exact costPresentationSymbols_comp
      first.underlying.structural.structural.symbols
      second.underlying.structural.structural.symbols

end CIGSLT

end Mettapedia.GSLT.LanguageDef
