import Mettapedia.GSLT.LanguageDef.ConstructorSupport
import Mettapedia.GSLT.LanguageDef.ConstructorFragmentSupport
import Mettapedia.GSLT.LanguageDef.ContextSupport
import Mettapedia.GSLT.LanguageDef.Cost.FiniteReflection

/-!
# Typed transport of declaration-derived Cost static fragments

The two static Cost namespaces are not independently authored languages.
They are derived from one exact continued-interaction presentation.  This
file proves that every typed source term confined to the cut-derived
non-principal constructor fragment transports into either generated static
fiber.

The restriction is load-bearing for the base fiber: the two interaction
principals have position-sensitive continuation types and are therefore
opaque region boundaries, not uniformly mapped static constructors.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.Reflection
open StructuralMorphism
open ReflectionExtension

namespace CostStaticColor

/-- Uniform static symbol action determined solely by the authored theory.
This is the non-circular form used while constructing the next continued
Cost object. -/
def symbolsOf (theory : IGSLT) : CostStaticColor → LanguageDefSymbolMap
  | .base => costBaseStaticSymbols
  | .wrapped => costWrappedStaticSymbols theory

/-- Uniform presentation action that embeds one static copy of a continued
theory: the action determined by its underlying theory. -/
abbrev symbols (source : WrappableIGSLT) (color : CostStaticColor) : LanguageDefSymbolMap :=
  color.symbolsOf source.theory

/-- The exact hereditary constructor image of one static Cost colour.  The
source witness belongs to the cut-derived non-principal fragment; recording
that witness also distinguishes the otherwise syntax-invisible declaration
used to type a bare collection. -/
def hereditaryConstructorImage (source : CIGSLT)
    (color : CostStaticColor) (targetConstructor : String) : Prop :=
  ∃ sourceConstructor,
    sourceConstructor ∈ source.continuationRetyping.wrappedLabels ∧
      targetConstructor = (color.symbols source).constructor sourceConstructor

/-- The corresponding action on the independently authored reflection
fibre.  Its core projection is exactly `symbols`; the additional component
renames presentation and reflective-rule identifiers. -/
def reflectiveSymbols (source : CIGSLT) : CostStaticColor → ReflectiveSymbols
  | .base => costBaseStaticReflectiveSymbols
  | .wrapped => costWrappedStaticReflectiveSymbols source.theory

@[simp]
theorem reflectiveSymbols_toLanguageDefSymbolMap
    (source : CIGSLT) (color : CostStaticColor) :
    (color.reflectiveSymbols source).toLanguageDefSymbolMap =
      color.symbols source := by
  cases color <;> rfl

@[simp]
theorem reflectiveSymbols_sort (source : CIGSLT)
    (color : CostStaticColor) (name : String) :
    (color.reflectiveSymbols source).sort name =
      (color.symbols source).sort name := by
  cases color <;> rfl

@[simp]
theorem reflectiveSymbols_constructor (source : CIGSLT)
    (color : CostStaticColor) (name : String) :
    (color.reflectiveSymbols source).constructor name =
      (color.symbols source).constructor name := by
  cases color <;> rfl

@[simp]
theorem reflectiveSymbols_relation (source : CIGSLT)
    (color : CostStaticColor) (name : String) :
    (color.reflectiveSymbols source).relation name =
      (color.symbols source).relation name := by
  cases color <;> rfl

@[simp]
theorem reflectiveSymbols_equation (source : CIGSLT)
    (color : CostStaticColor) (name : String) :
    (color.reflectiveSymbols source).equation name =
      (color.symbols source).equation name := by
  cases color <;> rfl

@[simp]
theorem reflectiveSymbols_rewrite (source : CIGSLT)
    (color : CostStaticColor) (name : String) :
    (color.reflectiveSymbols source).rewrite name =
      (color.symbols source).rewrite name := by
  cases color <;> rfl

@[simp]
theorem symbolsOf_constructor (theory : IGSLT) (color : CostStaticColor)
    (constructor : String) :
    (color.symbolsOf theory).constructor constructor =
      color.constructorTag ++ constructor := by
  cases color <;>
    rfl

theorem symbols_constructor (source : CIGSLT) (color : CostStaticColor)
    (constructor : String) :
    (color.symbols source).constructor constructor =
      color.constructorTag ++ constructor :=
  symbolsOf_constructor source.theory color constructor

/-- The theory-indexed static constructor action is injective in either
generated namespace. -/
theorem symbolsOf_constructor_injective (theory : IGSLT)
    (color : CostStaticColor) :
    Function.Injective (color.symbolsOf theory).constructor := by
  cases color with
  | base => exact costBaseConstructorName_injective
  | wrapped => exact costWrappedConstructorName_injective

/-- Each static Cost color embeds the source constructor namespace
injectively. -/
theorem symbols_constructor_injective (source : CIGSLT)
    (color : CostStaticColor) :
    Function.Injective (color.symbols source).constructor :=
  symbolsOf_constructor_injective source.theory color

/-- Quotation-aware scope is transported exactly inside either injectively
tagged static Cost fiber. -/
@[simp]
theorem binderSafeAt_mapPattern_symbolsOf (theory : IGSLT)
    (color : CostStaticColor) (quoteConstructor : String)
    (depth : Nat) (pattern : Pattern) :
    binderSafeAt ((color.symbolsOf theory).constructor quoteConstructor) depth
        (mapPattern (color.symbolsOf theory) pattern) =
      binderSafeAt quoteConstructor depth pattern :=
  WellSorted.binderSafeAt_mapPattern_of_constructor_injective
    (color.symbolsOf theory) (color.symbolsOf_constructor_injective theory)
    quoteConstructor depth pattern

theorem binderSafeAt_mapPattern_symbols (source : CIGSLT)
    (color : CostStaticColor) (quoteConstructor : String)
    (depth : Nat) (pattern : Pattern) :
    binderSafeAt ((color.symbols source).constructor quoteConstructor) depth
        (mapPattern (color.symbols source) pattern) =
      binderSafeAt quoteConstructor depth pattern :=
  binderSafeAt_mapPattern_symbolsOf source.theory color quoteConstructor depth pattern

/-- The sort action of either static Cost fiber lands in the exact generated
Cost language.  The wrapped color sends only the distinguished interacting
sort to the wrapped carrier; every other source sort remains in the tagged
base fiber. -/
def mapLangSort (source : CIGSLT) (color : CostStaticColor)
    (sort : LangSort source.theory.presentation.presentation.language) :
    LangSort source.costWholeLanguage := by
  refine ⟨(color.symbols source).sort sort.1, ?_⟩
  cases color with
  | base =>
      change costBaseSortName sort.1 ∈ source.costWholeLanguage.typeNames
      exact source.costBaseSortName_mem_costWhole sort.1 sort.2
  | wrapped =>
      by_cases interacting :
          sort.1 = source.theory.presentation.interactingSort.1.name
      · simp only [CostStaticColor.symbols, CostStaticColor.symbolsOf, costWrappedStaticSymbols,
          interacting, if_pos]
        exact source.costWrappedSortName_mem_costWhole
      · simp only [CostStaticColor.symbols, CostStaticColor.symbolsOf, costWrappedStaticSymbols,
          interacting]
        exact source.costBaseSortName_mem_costWhole sort.1 sort.2

/-- Static sort transport into the declaration-derived continuation
signature, before any interaction apparatus is added. -/
def mapGeneratedLangSort {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) (color : CostStaticColor)
    (sort : LangSort theory.presentation.presentation.language) :
    LangSort plan.generatedLanguage := by
  refine ⟨(color.symbolsOf theory).sort sort.1, ?_⟩
  cases color with
  | base =>
      exact plan.costBaseSortName_mem_generated sort.1 sort.2
  | wrapped =>
      by_cases interacting :
          sort.1 = theory.presentation.interactingSort.1.name
      · simp only [symbolsOf, costWrappedStaticSymbols, interacting, if_pos]
        exact plan.costWrappedSortName_mem_generated
      · simp only [symbolsOf, costWrappedStaticSymbols, interacting]
        exact plan.costBaseSortName_mem_generated sort.1 sort.2

@[simp]
theorem mapGeneratedLangSort_name {theory : IGSLT}
    {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) (color : CostStaticColor)
    (sort : LangSort theory.presentation.presentation.language) :
    (color.mapGeneratedLangSort plan sort).1 =
      (color.symbolsOf theory).sort sort.1 :=
  rfl

@[simp]
theorem mapLangSort_name (source : CIGSLT) (color : CostStaticColor)
    (sort : LangSort source.theory.presentation.presentation.language) :
    (color.mapLangSort source sort).1 = (color.symbols source).sort sort.1 :=
  rfl

/-- The two static type actions overlap exactly on types that avoid the
authored interacting sort. -/
theorem mapTypeExpr_base_eq_wrapped_iff (source : CIGSLT)
    (type : TypeExpr) :
    mapTypeExpr (CostStaticColor.base.symbols source) type =
        mapTypeExpr (CostStaticColor.wrapped.symbols source) type ↔
      source.theory.presentation.interactingSort.1.name ∉ type.baseNames := by
  simp only [CostStaticColor.symbols, CostStaticColor.symbolsOf, mapTypeExpr_costBaseStaticSymbols,
    mapTypeExpr_costWrappedStaticSymbols]
  rw [eq_comm]
  exact costWrappedTypeExpr_eq_costBaseTypeExpr_iff _ _

/-- Cross-color equality identifies both source types, not merely their
generated images.  The common source type necessarily avoids the interacting
sort, which is exactly the label-free overlap fiber. -/
theorem mapTypeExpr_base_eq_wrapped_iff_eq (source : CIGSLT)
    (left right : TypeExpr) :
    mapTypeExpr (CostStaticColor.base.symbols source) left =
        mapTypeExpr (CostStaticColor.wrapped.symbols source) right ↔
      left = right ∧
        source.theory.presentation.interactingSort.1.name ∉
          right.baseNames := by
  constructor
  · intro equality
    let interactingSort :=
      source.theory.presentation.interactingSort.1.name
    have rawEquality :
        costBaseTypeExpr left =
          costWrappedTypeExpr interactingSort right := by
      simpa [CostStaticColor.symbols, CostStaticColor.symbolsOf,
        mapTypeExpr_costBaseStaticSymbols,
        mapTypeExpr_costWrappedStaticSymbols, interactingSort] using
          equality
    have avoids : interactingSort ∉ right.baseNames := by
      intro membership
      have wrappedMembership :
          costWrappedSortName ∈
            (costWrappedTypeExpr interactingSort right).baseNames := by
        rw [costWrappedTypeExpr_baseNames]
        exact List.mem_map.mpr
          ⟨interactingSort, membership, by simp⟩
      have baseMembership :
          costWrappedSortName ∈ (costBaseTypeExpr left).baseNames := by
        rw [rawEquality]
        exact wrappedMembership
      rw [costBaseTypeExpr_baseNames] at baseMembership
      rcases List.mem_map.mp baseMembership with
        ⟨sourceSort, _, encodedEquality⟩
      exact
        (costBaseSortName_ne_wrapped sourceSort encodedEquality).elim
    have wrappedBase :
        costWrappedTypeExpr interactingSort right =
          costBaseTypeExpr right :=
      (costWrappedTypeExpr_eq_costBaseTypeExpr_iff interactingSort right).2
        avoids
    have sourceEq := costBaseTypeExpr_injective
      (rawEquality.trans wrappedBase)
    exact ⟨sourceEq, avoids⟩
  · rintro ⟨sourceEq, avoids⟩
    subst left
    exact (mapTypeExpr_base_eq_wrapped_iff source right).2 avoids

/-- At the sort level, base and wrapped colors coincide precisely away from
the distinguished interacting sort.  A label-free collection in this
overlap may therefore carry two proof-relevant root colors. -/
theorem mapLangSort_base_eq_wrapped_iff (source : CIGSLT)
    (sort : LangSort source.theory.presentation.presentation.language) :
    CostStaticColor.base.mapLangSort source sort =
        CostStaticColor.wrapped.mapLangSort source sort ↔
      sort.1 ≠ source.theory.presentation.interactingSort.1.name := by
  constructor
  · intro same
    have typeEquality :
        mapTypeExpr (CostStaticColor.base.symbols source)
            (.base sort.1) =
          mapTypeExpr (CostStaticColor.wrapped.symbols source)
            (.base sort.1) := by
      exact congrArg TypeExpr.base (congrArg Subtype.val same)
    have avoids :=
      (mapTypeExpr_base_eq_wrapped_iff source (.base sort.1)).1 typeEquality
    intro equality
    exact avoids (by simpa [TypeExpr.baseNames] using equality.symm)
  · intro different
    apply Subtype.ext
    have avoids :
        source.theory.presentation.interactingSort.1.name ∉
          (TypeExpr.base sort.1).baseNames := by
      simpa [TypeExpr.baseNames] using
        (fun equality :
            source.theory.presentation.interactingSort.1.name = sort.1 =>
          different equality.symm)
    have typeEquality :=
      (mapTypeExpr_base_eq_wrapped_iff source (.base sort.1)).2 avoids
    exact TypeExpr.base.inj typeEquality

/-- Cross-color equality of generated sorts recovers one common authored
sort and proves that it is not the interacting sort. -/
theorem mapLangSort_base_eq_wrapped_iff_eq (source : CIGSLT)
    (left right :
      LangSort source.theory.presentation.presentation.language) :
    CostStaticColor.base.mapLangSort source left =
        CostStaticColor.wrapped.mapLangSort source right ↔
      left = right ∧
        right.1 ≠ source.theory.presentation.interactingSort.1.name := by
  constructor
  · intro same
    have typeEquality :
        mapTypeExpr (CostStaticColor.base.symbols source) (.base left.1) =
          mapTypeExpr (CostStaticColor.wrapped.symbols source)
            (.base right.1) := by
      exact congrArg TypeExpr.base (congrArg Subtype.val same)
    have inversion :=
      (mapTypeExpr_base_eq_wrapped_iff_eq source
        (.base left.1) (.base right.1)).1 typeEquality
    have sortEq : left = right := by
      apply Subtype.ext
      exact TypeExpr.base.inj inversion.1
    refine ⟨sortEq, ?_⟩
    intro equality
    exact inversion.2 (by
      simpa [TypeExpr.baseNames] using equality.symm)
  · rintro ⟨sortEq, avoids⟩
    subst left
    exact (mapLangSort_base_eq_wrapped_iff source right).2 avoids

/-- Each fixed static colour embeds authored sorts injectively.  In the
wrapped colour the distinguished interacting sort lands in the reserved
wrapped carrier, while every other sort remains in the injective base
namespace. -/
theorem mapLangSort_injective (source : CIGSLT) (color : CostStaticColor) :
    Function.Injective (color.mapLangSort source) := by
  intro first second equality
  apply Subtype.ext
  have nameEquality := congrArg Subtype.val equality
  cases color with
  | base =>
      exact costBaseSortName_injective nameEquality
  | wrapped =>
      by_cases firstInteracting :
          first.1 = source.theory.presentation.interactingSort.1.name
      · by_cases secondInteracting :
            second.1 = source.theory.presentation.interactingSort.1.name
        · exact firstInteracting.trans secondInteracting.symm
        · have impossible : costWrappedSortName = costBaseSortName second.1 := by
            simpa [CostStaticColor.symbols, CostStaticColor.symbolsOf, costWrappedStaticSymbols,
              firstInteracting, secondInteracting] using nameEquality
          exact (costBaseSortName_ne_wrapped second.1 impossible.symm).elim
      · by_cases secondInteracting :
            second.1 = source.theory.presentation.interactingSort.1.name
        · have impossible : costBaseSortName first.1 = costWrappedSortName := by
            simpa [CostStaticColor.symbols, CostStaticColor.symbolsOf, costWrappedStaticSymbols,
              firstInteracting, secondInteracting] using nameEquality
          exact (costBaseSortName_ne_wrapped first.1 impossible).elim
        · exact costBaseSortName_injective (by
            simpa [CostStaticColor.symbols, CostStaticColor.symbolsOf, costWrappedStaticSymbols,
              firstInteracting, secondInteracting] using nameEquality)

/-- On the distinguished interacting sort, the generated target sort also
determines the static colour: base and wrapped land in disjoint reserved
namespaces. -/
theorem color_eq_of_mapLangSort_eq_of_interacting (source : CIGSLT)
    (firstColor secondColor : CostStaticColor)
    (firstSort secondSort :
      LangSort source.theory.presentation.presentation.language)
    (firstInteracting :
      firstSort.1 = source.theory.presentation.interactingSort.1.name)
    (secondInteracting :
      secondSort.1 = source.theory.presentation.interactingSort.1.name)
    (mappedEquality : firstColor.mapLangSort source firstSort =
      secondColor.mapLangSort source secondSort) :
    firstColor = secondColor := by
  have nameEquality := congrArg Subtype.val mappedEquality
  cases firstColor <;> cases secondColor
  · rfl
  · have impossible :
        costBaseSortName
            source.theory.presentation.interactingSort.1.name =
          costWrappedSortName := by
      simpa [CostStaticColor.mapLangSort_name, CostStaticColor.symbols, CostStaticColor.symbolsOf,
        costBaseStaticSymbols, costBaseLanguageDefSymbolMap,
        costWrappedStaticSymbols, firstInteracting, secondInteracting] using
        nameEquality
    exact (costBaseSortName_ne_wrapped _ impossible).elim
  · have impossible :
        costWrappedSortName =
          costBaseSortName
            source.theory.presentation.interactingSort.1.name := by
      simpa [CostStaticColor.mapLangSort_name, CostStaticColor.symbols, CostStaticColor.symbolsOf,
        costBaseStaticSymbols, costBaseLanguageDefSymbolMap,
        costWrappedStaticSymbols, firstInteracting, secondInteracting] using
        nameEquality
    exact (costBaseSortName_ne_wrapped _ impossible.symm).elim
  · rfl

end CostStaticColor

namespace ContinuationDecorationProfile

open WellSorted

/-- Static Cost transport preserves every authored reflective scope boundary.
The selected color transports the corresponding source quotation exactly;
the opposite color is disjoint from every constructor in the mapped term and
therefore contributes only the ordinary locally nameless scope check. -/
theorem reflectiveScopeSafeAt_mapStatic
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (profile : ContinuationDecorationProfile cut)
    (reflection : ReflectionProfile) (color : CostStaticColor)
    {depth : Nat} {pattern : Pattern}
    (sourceSafe : ReflectiveWellSorted.ReflectiveScopeSafeAt
      reflection depth pattern)
    (mappedOrdinaryScope :
      (mapPattern (color.symbolsOf theory) pattern).isWellScopedAt depth = true) :
    ReflectiveWellSorted.ReflectiveScopeSafeAt
      (profile.costWholeReflectionProfile reflection) depth
      (mapPattern (color.symbolsOf theory) pattern) := by
  intro targetPresentation targetMembership
  rw [costWholeReflectionProfile,
    costStaticReflectivePresentations, List.mem_append]
    at targetMembership
  rcases targetMembership with baseMembership | wrappedMembership
  · rcases List.mem_map.mp baseMembership with
      ⟨sourcePresentation, sourceMembership, rfl⟩
    cases color with
    | base =>
        simpa [costBaseReflectivePresentationDecl,
          mapReflectivePresentation, CostStaticColor.symbolsOf,
          costBaseStaticSymbols, costBaseStaticReflectiveSymbols,
          costBaseLanguageDefSymbolMap] using
          (show binderSafeAt
              ((CostStaticColor.base.symbolsOf theory).constructor
                sourcePresentation.quoteConstructor) depth
              (mapPattern (CostStaticColor.base.symbolsOf theory) pattern) = true
            from by
              rw [CostStaticColor.binderSafeAt_mapPattern_symbolsOf]
              exact sourceSafe sourcePresentation sourceMembership)
    | wrapped =>
        have scopeEquality :=
          WellSorted.binderSafeAt_mapPattern_of_constructor_avoids
            (CostStaticColor.wrapped.symbolsOf theory)
            (costBaseConstructorName sourcePresentation.quoteConstructor)
            (fun constructor equality =>
              costBaseConstructorName_ne_wrapped
                sourcePresentation.quoteConstructor constructor equality.symm)
            depth pattern
        simpa [costBaseReflectivePresentationDecl,
          mapReflectivePresentation, CostStaticColor.symbolsOf,
          costBaseStaticSymbols, costBaseStaticReflectiveSymbols,
          costBaseLanguageDefSymbolMap] using
          (scopeEquality.trans mappedOrdinaryScope)
  · rcases List.mem_map.mp wrappedMembership with
      ⟨sourcePresentation, sourceMembership, rfl⟩
    cases color with
    | base =>
        have scopeEquality :=
          WellSorted.binderSafeAt_mapPattern_of_constructor_avoids
            (CostStaticColor.base.symbolsOf theory)
            (costWrappedConstructorName sourcePresentation.quoteConstructor)
            (fun constructor =>
              costBaseConstructorName_ne_wrapped constructor
                sourcePresentation.quoteConstructor)
            depth pattern
        simpa [costWrappedReflectivePresentationDecl,
          mapReflectivePresentation, CostStaticColor.symbolsOf,
          costWrappedStaticSymbols, costWrappedStaticReflectiveSymbols] using
          (scopeEquality.trans mappedOrdinaryScope)
    | wrapped =>
        simpa [costWrappedReflectivePresentationDecl,
          mapReflectivePresentation, CostStaticColor.symbolsOf,
          costWrappedStaticReflectiveSymbols] using
          (show binderSafeAt
              ((CostStaticColor.wrapped.symbolsOf theory).constructor
                sourcePresentation.quoteConstructor) depth
              (mapPattern (CostStaticColor.wrapped.symbolsOf theory) pattern) = true
            from by
              rw [CostStaticColor.binderSafeAt_mapPattern_symbolsOf]
              exact sourceSafe sourcePresentation sourceMembership)


@[simp]
theorem reflectiveIsQuoteConstructor_mapStatic
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (profile : ContinuationDecorationProfile cut) (reflection : ReflectionProfile)
    (color : CostStaticColor) (constructor : String) :
    ReflectiveContextSupport.isQuoteConstructor
        (profile.costWholeReflectionProfile reflection)
        ((color.symbolsOf theory).constructor constructor) =
      ReflectiveContextSupport.isQuoteConstructor
        reflection constructor := by
  unfold ReflectiveContextSupport.isQuoteConstructor
  simp only [costWholeReflectionProfile, costStaticReflectivePresentations, List.any_append]
  cases color with
  | base =>
      rw [Bool.eq_iff_iff]
      simp only [List.any_map, Function.comp_apply, Bool.or_eq_true,
        List.any_eq_true, beq_iff_eq]
      constructor
      · rintro (⟨declaration, membership, equality⟩ |
          ⟨declaration, _membership, equality⟩)
        · refine ⟨declaration, membership, ?_⟩
          apply costBaseConstructorName_injective
          simpa [CostStaticColor.symbolsOf,
            costBaseReflectivePresentationDecl, mapReflectivePresentation,
            costBaseStaticSymbols, costBaseStaticReflectiveSymbols,
            costBaseLanguageDefSymbolMap] using equality
        · have impossible :
              costWrappedConstructorName declaration.quoteConstructor =
                costBaseConstructorName constructor := by
            simpa [CostStaticColor.symbolsOf,
              costWrappedReflectivePresentationDecl,
              mapReflectivePresentation, costWrappedStaticSymbols,
              costWrappedStaticReflectiveSymbols, costBaseStaticSymbols,
              costBaseLanguageDefSymbolMap] using equality
          exact False.elim
            (costBaseConstructorName_ne_wrapped constructor
              declaration.quoteConstructor impossible.symm)
      · rintro ⟨declaration, membership, equality⟩
        left
        refine ⟨declaration, membership, ?_⟩
        simp [CostStaticColor.symbolsOf,
          costBaseReflectivePresentationDecl, mapReflectivePresentation,
          costBaseStaticSymbols, costBaseStaticReflectiveSymbols,
          costBaseLanguageDefSymbolMap, equality]
  | wrapped =>
      rw [Bool.eq_iff_iff]
      simp only [List.any_map, Function.comp_apply, Bool.or_eq_true,
        List.any_eq_true, beq_iff_eq]
      constructor
      · rintro (⟨declaration, _membership, equality⟩ |
          ⟨declaration, membership, equality⟩)
        · have impossible :
              costBaseConstructorName declaration.quoteConstructor =
                costWrappedConstructorName constructor := by
            simpa [CostStaticColor.symbolsOf,
              costBaseReflectivePresentationDecl, mapReflectivePresentation,
              costBaseStaticSymbols, costBaseStaticReflectiveSymbols,
              costBaseLanguageDefSymbolMap,
              costWrappedStaticSymbols] using equality
          exact False.elim
            (costBaseConstructorName_ne_wrapped
              declaration.quoteConstructor constructor impossible)
        · refine ⟨declaration, membership, ?_⟩
          apply costWrappedConstructorName_injective
          simpa [CostStaticColor.symbolsOf,
            costWrappedReflectivePresentationDecl,
            mapReflectivePresentation, costWrappedStaticSymbols,
            costWrappedStaticReflectiveSymbols] using equality
      · rintro ⟨declaration, membership, equality⟩
        right
        refine ⟨declaration, membership, ?_⟩
        simp [CostStaticColor.symbolsOf,
          costWrappedReflectivePresentationDecl, mapReflectivePresentation,
          costWrappedStaticSymbols, costWrappedStaticReflectiveSymbols,
          equality]

end ContinuationDecorationProfile

/-- Static Cost transport preserves every authored reflective scope boundary.
The selected color transports the corresponding source quotation exactly;
the opposite color is disjoint from every constructor in the mapped term and
therefore contributes only the ordinary locally nameless scope check. -/
theorem reflectiveScopeSafeAt_mapCostStatic
    (source : CIGSLT) (color : CostStaticColor)
    {depth : Nat} {pattern : Pattern}
    (sourceSafe : ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.reflection.1 depth pattern)
    (mappedOrdinaryScope :
      (mapPattern (color.symbols source) pattern).isWellScopedAt depth = true) :
    ReflectiveWellSorted.ReflectiveScopeSafeAt
      source.costWholeReflectionProfile depth
      (mapPattern (color.symbols source) pattern) :=
  (ContinuationDecorationProfile.ofRetypingPlan
    source.continuationRetyping).reflectiveScopeSafeAt_mapStatic source.reflection.1 color
      sourceSafe mappedOrdinaryScope

/-- Static tagging preserves exactly the authored quotation boundaries.
The opposite static color cannot contribute a false positive because the
base and wrapped constructor namespaces are disjoint. -/
@[simp]
theorem reflectiveIsQuoteConstructor_mapCostStatic
    (source : CIGSLT) (color : CostStaticColor) (constructor : String) :
    ReflectiveContextSupport.isQuoteConstructor
        source.costWholeReflectionProfile
        ((color.symbols source).constructor constructor) =
      ReflectiveContextSupport.isQuoteConstructor
        source.reflection.1 constructor :=
  (ContinuationDecorationProfile.ofRetypingPlan
    source.continuationRetyping).reflectiveIsQuoteConstructor_mapStatic source.reflection.1
      color constructor

/-- The sole extra law required by typed static transport: declarations
whose bare collection representation hides its label must belong to the
hereditary continuation fragment.  The law is stated on the retyping plan,
not on a completed `CIGSLT`, so it can be used while constructing the next
continued object. -/
def ContinuationRetypingPlan.BareCollectionConstructorsWrapped
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) : Prop :=
  ∀ rule ∈ theory.presentation.presentation.language.terms,
    WellSorted.UsesBareCollection rule →
      rule.label ∈ plan.wrappedLabels

/-- A completed continued object supplies the minimal bare-collection law
consumed by the non-circular static transport layer. -/
theorem CIGSLT.bareCollectionConstructorsWrappedForPlan (source : CIGSLT) :
    source.continuationRetyping.BareCollectionConstructorsWrapped :=
  source.bareCollectionConstructorsWrapped

@[simp]
theorem mapTermParam_costBaseStaticSymbols (parameter : TermParam) :
    mapTermParam costBaseStaticSymbols parameter =
      mapParameterType costBaseTypeExpr parameter := by
  cases parameter <;>
    simp [mapTermParam, mapParameterType,
      mapTypeExpr_costBaseStaticSymbols]

@[simp]
theorem mapTermParam_costWrappedStaticSymbols (theory : IGSLT)
    (parameter : TermParam) :
    mapTermParam (costWrappedStaticSymbols theory) parameter =
      mapParameterType
        (costWrappedTypeExpr theory.presentation.interactingSort.1.name)
        parameter := by
  cases parameter <;>
    simp [mapTermParam, mapParameterType,
      mapTypeExpr_costWrappedStaticSymbols]

namespace ContinuationDecorationProfile

variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

/-- Additional slots still belong to the selected principal declarations. -/
theorem selectedParameter_eq_false_of_nonprincipal
    (profile : ContinuationDecorationProfile cut) (constructor : GrammarRule)
    (notProgram : constructor ≠ cut.program.constructor.1)
    (notEnvironment : constructor ≠ cut.environment.constructor.1) (index : Nat) :
    profile.selectedParameter constructor index = false := by
  simp [selectedParameter, isSelectedContinuation, notProgram, notEnvironment]

/-- No parameter is positionally retyped in a nonprincipal base row. -/
theorem baseConstructor_params_eq_map_of_nonprincipal
    (profile : ContinuationDecorationProfile cut) (constructor : GrammarRule)
    (notProgram : constructor ≠ cut.program.constructor.1)
    (notEnvironment : constructor ≠ cut.environment.constructor.1) :
    (profile.baseConstructor constructor).params =
      constructor.params.map (mapTermParam costBaseStaticSymbols) := by
  apply List.ext_getElem
  · simp [baseConstructor]
  · intro index leftBound rightBound
    rw [baseConstructor_parameter _ _ _ (by simpa [baseConstructor] using leftBound)]
    simp [List.getElem_map, baseParameter,
      profile.selectedParameter_eq_false_of_nonprincipal constructor notProgram notEnvironment]

/-- The two-slot profile of a retyping plan contains neither principal. -/
theorem ofRetypingPlan_nonprincipal (plan : ContinuationRetypingPlan cut) :
    ∀ constructor ∈ (ofRetypingPlan plan).constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor :=
  fun constructor included => (plan.mem_wrappedConstructors_iff constructor).mp included

/-- A row of an inventory without the two principals keeps the uniform base
parameter map. -/
theorem baseConstructor_params_eq_map_of_mem_wrappedLabels
    (profile : ContinuationDecorationProfile cut)
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor)
    (rule : GrammarRule)
    (member : rule ∈ theory.presentation.presentation.language.terms)
    (supported : rule.label ∈ profile.wrappedLabels) :
    (profile.baseConstructor rule).params =
      rule.params.map (mapTermParam costBaseStaticSymbols) := by
  have excluded := nonprincipal ⟨rule, member⟩
    ((profile.mem_wrappedLabels_iff ⟨rule, member⟩).mp supported)
  exact profile.baseConstructor_params_eq_map_of_nonprincipal rule
    (fun same => excluded.1 (Subtype.ext same))
    (fun same => excluded.2 (Subtype.ext same))

end ContinuationDecorationProfile

/-- Away from the two selected principals, base-constructor parameter
retyping is exactly the uniform base static symbol action. -/
theorem costBaseConstructor_params_eq_map_of_mem_wrappedLabels
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) (rule : GrammarRule)
    (membership : rule ∈ theory.presentation.presentation.language.terms)
    (wrapped : rule.label ∈ plan.wrappedLabels) :
    (costBaseConstructor cut rule).params =
      rule.params.map (mapTermParam costBaseStaticSymbols) :=
  (ContinuationDecorationProfile.ofRetypingPlan plan).baseConstructor_params_eq_map_of_mem_wrappedLabels
    (ContinuationDecorationProfile.ofRetypingPlan_nonprincipal plan) rule membership wrapped

/-- If a generated constructor has a wrapped-tagged label, its untagged
source label belongs to the exact hereditary continuation fragment.
Disjoint generated namespaces exclude the base-image alternative. -/
theorem ContinuationRetypingPlan.sourceLabel_mem_wrappedLabels_of_generated
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) (rule : GrammarRule)
    (membership : rule ∈ plan.generatedLanguage.terms)
    (sourceLabel : String)
    (label : rule.label = costWrappedConstructorName sourceLabel) :
    sourceLabel ∈ plan.wrappedLabels := by
  have labelMembership : rule.label ∈
      plan.generatedLanguage.terms.map (·.label) :=
    List.mem_map.mpr ⟨rule, membership, rfl⟩
  rw [plan.generatedLanguage_constructorLabels, label] at labelMembership
  rcases List.mem_append.mp labelMembership with
      baseMembership | wrappedMembership
  · rcases List.mem_map.mp baseMembership with
      ⟨baseLabel, _baseMembership, equality⟩
    exact False.elim
      (costBaseConstructorName_ne_wrapped baseLabel sourceLabel equality)
  · rcases List.mem_map.mp wrappedMembership with
      ⟨wrappedLabel, wrappedMembership, equality⟩
    exact (costWrappedConstructorName_injective equality).symm ▸
      wrappedMembership

/-- Successful wrapped reflective validation entails that each constructor
named by the source declaration belongs to the hereditary continuation
fragment.  This extracts a structural consequence of the existing validator;
it does not introduce a second validity judgment. -/
theorem ReflectivePresentationRetypable.constructorLabels_mem_wrapped
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    {plan : ContinuationRetypingPlan cut}
    {declaration : ReflectivePresentationDecl}
    (stable : ReflectivePresentationRetypable plan declaration) :
    declaration.quoteConstructor ∈ plan.wrappedLabels ∧
      declaration.dropConstructor ∈ plan.wrappedLabels ∧
      declaration.parallelUnitConstructor ∈ plan.wrappedLabels := by
  rcases LanguageDef.reflectivePresentationWitness_of_validate_eq_nil
      (reflectiveRetypingLanguage plan)
      (costWrappedReflectivePresentationDecl theory declaration)
      stable.2 with ⟨witness⟩
  have quoteFiltered : witness.quote ∈
      (reflectiveRetypingLanguage plan).terms.filter
        (fun term => term.label ==
          (costWrappedReflectivePresentationDecl theory declaration
            ).quoteConstructor) := by
    rw [witness.quoteUnique]
    simp
  have dropFiltered : witness.drop ∈
      (reflectiveRetypingLanguage plan).terms.filter
        (fun term => term.label ==
          (costWrappedReflectivePresentationDecl theory declaration
            ).dropConstructor) := by
    rw [witness.dropUnique]
    simp
  have unitFiltered : witness.unit ∈
      (reflectiveRetypingLanguage plan).terms.filter
        (fun term => term.label ==
          (costWrappedReflectivePresentationDecl theory declaration
            ).parallelUnitConstructor) := by
    rw [witness.unitUnique]
    simp
  refine ⟨?_, ?_, ?_⟩
  · apply plan.sourceLabel_mem_wrappedLabels_of_generated witness.quote
      (List.mem_filter.mp quoteFiltered).1
    simpa [costWrappedReflectivePresentationDecl,
      mapReflectivePresentation, costWrappedStaticSymbols,
      costWrappedStaticReflectiveSymbols] using
        beq_iff_eq.mp (List.mem_filter.mp quoteFiltered).2
  · apply plan.sourceLabel_mem_wrappedLabels_of_generated witness.drop
      (List.mem_filter.mp dropFiltered).1
    simpa [costWrappedReflectivePresentationDecl,
      mapReflectivePresentation, costWrappedStaticSymbols,
      costWrappedStaticReflectiveSymbols] using
        beq_iff_eq.mp (List.mem_filter.mp dropFiltered).2
  · apply plan.sourceLabel_mem_wrappedLabels_of_generated witness.unit
      (List.mem_filter.mp unitFiltered).1
    simpa [costWrappedReflectivePresentationDecl,
      mapReflectivePresentation, costWrappedStaticSymbols,
      costWrappedStaticReflectiveSymbols] using
        beq_iff_eq.mp (List.mem_filter.mp unitFiltered).2

/-- Structural symbol transport preserves the exact quote/drop equation
shape recognized by the sole reflective-presentation validator. -/
theorem quoteDropShape_mapEquationSymbols
    (symbols : ReflectiveSymbols)
    (declaration : ReflectivePresentationDecl) (equation : Equation)
    (shape : LanguageDef.QuoteDropShape declaration equation) :
    LanguageDef.QuoteDropShape
      (mapReflectivePresentation symbols declaration)
      (mapEquation symbols.toLanguageDefSymbolMap equation) := by
  rw [LanguageDef.quoteDropShape_iff] at shape ⊢
  rcases shape with ⟨name, forward | reverse⟩
  · refine ⟨name, Or.inl ?_⟩
    simp only [mapReflectivePresentation, LanguageDef.mapEquation]
    rw [forward.1, forward.2]
    simp [mapPattern, mapPatternList]
  · refine ⟨name, Or.inr ?_⟩
    simp only [mapReflectivePresentation, LanguageDef.mapEquation]
    rw [reverse.1, reverse.2]
    simp [mapPattern, mapPatternList]

/-- Base and wrapped equation names remain duplicate-free in the exact
intermediate reflective-retyping language. -/
theorem reflectiveRetypingLanguage_equationNames_nodup
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) :
    ((reflectiveRetypingLanguage plan).equations.map (·.name)).Nodup := by
  have names :
      (reflectiveRetypingLanguage plan).equations.map (·.name) =
        (theory.presentation.presentation.language.equations.map
            (·.name)).map costBaseEquationName ++
          (theory.presentation.presentation.language.equations.map
            (·.name)).map costWrappedEquationName := by
    simp [reflectiveRetypingLanguage_def, Function.comp_def,
      costBaseEquation, costWrappedEquation, mapEquation,
      costBaseStaticSymbols, costWrappedStaticSymbols]
  rw [names, List.nodup_append]
  have sourceNodup := LanguageDef.equationNames_nodup_of_validate_eq_nil
    theory.presentation.presentation.language
    theory.presentation.presentation.valid
  refine ⟨sourceNodup.map costBaseEquationName_injective,
    sourceNodup.map costWrappedEquationName_injective, ?_⟩
  intro base baseMembership wrapped wrappedMembership
  rcases List.mem_map.mp baseMembership with ⟨baseName, _, rfl⟩
  rcases List.mem_map.mp wrappedMembership with ⟨wrappedName, _, rfl⟩
  exact costBaseEquationName_ne_wrapped baseName wrappedName

/-- A valid reflective presentation whose named constructors lie in the
hereditary fragment has a valid base image in the exact continuation-retyped
language. -/
theorem validateReflectivePresentation_costBase_of_wrapped
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut)
    (declaration : ReflectivePresentationDecl)
    (valid :
      theory.presentation.presentation.language.validateReflectivePresentation
        declaration = [])
    (quoteWrapped : declaration.quoteConstructor ∈ plan.wrappedLabels)
    (dropWrapped : declaration.dropConstructor ∈ plan.wrappedLabels)
    (unitWrapped :
      declaration.parallelUnitConstructor ∈ plan.wrappedLabels) :
    (reflectiveRetypingLanguage plan).validateReflectivePresentation
      (costBaseReflectivePresentationDecl declaration) = [] := by
  rcases LanguageDef.reflectivePresentationWitness_of_validate_eq_nil
      theory.presentation.presentation.language declaration valid with
    ⟨witness⟩
  have quoteFiltered : witness.quote ∈
      theory.presentation.presentation.language.terms.filter
        (fun term => term.label == declaration.quoteConstructor) := by
    rw [witness.quoteUnique]
    simp
  have quoteMembership := (List.mem_filter.mp quoteFiltered).1
  have quoteLabel : witness.quote.label = declaration.quoteConstructor :=
    beq_iff_eq.mp (List.mem_filter.mp quoteFiltered).2
  have dropFiltered : witness.drop ∈
      theory.presentation.presentation.language.terms.filter
        (fun term => term.label == declaration.dropConstructor) := by
    rw [witness.dropUnique]
    simp
  have dropMembership := (List.mem_filter.mp dropFiltered).1
  have dropLabel : witness.drop.label = declaration.dropConstructor :=
    beq_iff_eq.mp (List.mem_filter.mp dropFiltered).2
  have unitFiltered : witness.unit ∈
      theory.presentation.presentation.language.terms.filter
        (fun term =>
          term.label == declaration.parallelUnitConstructor) := by
    rw [witness.unitUnique]
    simp
  have unitMembership := (List.mem_filter.mp unitFiltered).1
  have unitLabel :
      witness.unit.label = declaration.parallelUnitConstructor :=
    beq_iff_eq.mp (List.mem_filter.mp unitFiltered).2
  have equationFiltered : witness.equation ∈
      theory.presentation.presentation.language.equations.filter
        (fun equation =>
          equation.name == declaration.quoteDropEquation) := by
    rw [witness.equationUnique]
    simp
  have equationMembership := (List.mem_filter.mp equationFiltered).1
  have equationName :
      witness.equation.name = declaration.quoteDropEquation :=
    beq_iff_eq.mp (List.mem_filter.mp equationFiltered).2
  let targetDeclaration :=
    costBaseReflectivePresentationDecl declaration
  let targetQuote := costBaseConstructor cut witness.quote
  let targetDrop := costBaseConstructor cut witness.drop
  let targetUnit := costBaseConstructor cut witness.unit
  let targetEquation := costBaseEquation witness.equation
  have targetQuoteUnique :
      (reflectiveRetypingLanguage plan).terms.filter
          (fun term =>
            term.label == targetDeclaration.quoteConstructor) =
        [targetQuote] := by
    change plan.generatedLanguage.terms.filter
        (fun term =>
          term.label ==
            costBaseConstructorName declaration.quoteConstructor) =
      [costBaseConstructor cut witness.quote]
    simpa [quoteLabel] using
      plan.costBaseConstructor_filter_generated witness.quote quoteMembership
  have targetDropUnique :
      (reflectiveRetypingLanguage plan).terms.filter
          (fun term =>
            term.label == targetDeclaration.dropConstructor) =
        [targetDrop] := by
    change plan.generatedLanguage.terms.filter
        (fun term =>
          term.label ==
            costBaseConstructorName declaration.dropConstructor) =
      [costBaseConstructor cut witness.drop]
    simpa [dropLabel] using
      plan.costBaseConstructor_filter_generated witness.drop dropMembership
  have targetUnitUnique :
      (reflectiveRetypingLanguage plan).terms.filter
          (fun term =>
            term.label == targetDeclaration.parallelUnitConstructor) =
        [targetUnit] := by
    change plan.generatedLanguage.terms.filter
        (fun term =>
          term.label ==
            costBaseConstructorName declaration.parallelUnitConstructor) =
      [costBaseConstructor cut witness.unit]
    simpa [unitLabel] using
      plan.costBaseConstructor_filter_generated witness.unit unitMembership
  have targetEquationMembership :
      targetEquation ∈ (reflectiveRetypingLanguage plan).equations := by
    change costBaseEquation witness.equation ∈ _
    rw [reflectiveRetypingLanguage_def]
    exact List.mem_append_left _
      (List.mem_map.mpr ⟨witness.equation, equationMembership, rfl⟩)
  have targetEquationName :
      targetEquation.name = targetDeclaration.quoteDropEquation := by
    simp [targetEquation, targetDeclaration, costBaseEquation,
      costBaseReflectivePresentationDecl, mapEquation,
      mapReflectivePresentation, costBaseStaticSymbols,
      costBaseStaticReflectiveSymbols, equationName]
  have targetEquationUnique :
      (reflectiveRetypingLanguage plan).equations.filter
          (fun equation =>
            equation.name == targetDeclaration.quoteDropEquation) =
        [targetEquation] := by
    rw [← targetEquationName]
    exact LanguageDef.filter_equations_by_name_eq_singleton
      (reflectiveRetypingLanguage plan).equations targetEquation
      (reflectiveRetypingLanguage_equationNames_nodup plan)
      targetEquationMembership
  apply (LanguageDef.ReflectivePresentationWitness.validate
    ({ quote := targetQuote
       drop := targetDrop
       unit := targetUnit
       equation := targetEquation
       quoteParameter := witness.quoteParameter
       dropParameter := witness.dropParameter
       processSort := by
         change costBaseSortName declaration.processSort ∈
           plan.generatedLanguage.typeNames
         exact plan.costBaseSortName_mem_generated declaration.processSort
           witness.processSort
       nameSort := by
         change costBaseSortName declaration.nameSort ∈
           plan.generatedLanguage.typeNames
         exact plan.costBaseSortName_mem_generated declaration.nameSort
           witness.nameSort
       sortsDistinct := by
         change costBaseSortName declaration.processSort ≠
           costBaseSortName declaration.nameSort
         exact costBaseSortName_injective.ne witness.sortsDistinct
       quoteUnique := targetQuoteUnique
       quoteCategory := by
         change costBaseSortName witness.quote.category =
           costBaseSortName declaration.nameSort
         rw [witness.quoteCategory]
       quoteParameters := by
         change (costBaseConstructor cut witness.quote).params =
           [.simple witness.quoteParameter
             (.base (costBaseSortName declaration.processSort))]
         rw [costBaseConstructor_params_eq_map_of_mem_wrappedLabels
           plan witness.quote quoteMembership
             (by simpa [quoteLabel] using quoteWrapped)]
         rw [witness.quoteParameters]
         simp [mapParameterType, costBaseTypeExpr]
       dropUnique := targetDropUnique
       dropCategory := by
         change costBaseSortName witness.drop.category =
           costBaseSortName declaration.processSort
         rw [witness.dropCategory]
       dropParameters := by
         change (costBaseConstructor cut witness.drop).params =
           [.simple witness.dropParameter
             (.base (costBaseSortName declaration.nameSort))]
         rw [costBaseConstructor_params_eq_map_of_mem_wrappedLabels
           plan witness.drop dropMembership
             (by simpa [dropLabel] using dropWrapped)]
         rw [witness.dropParameters]
         simp [mapParameterType, costBaseTypeExpr]
       unitUnique := targetUnitUnique
       unitCategory := by
         change costBaseSortName witness.unit.category =
           costBaseSortName declaration.processSort
         rw [witness.unitCategory]
       unitParameters := by
         change (costBaseConstructor cut witness.unit).params = []
         rw [costBaseConstructor_params_eq_map_of_mem_wrappedLabels
           plan witness.unit unitMembership
             (by simpa [unitLabel] using unitWrapped)]
         simp [witness.unitParameters]
       equationUnique := targetEquationUnique
       equationShape := by
         change LanguageDef.QuoteDropShape
           (costBaseReflectivePresentationDecl declaration)
           (costBaseEquation witness.equation)
         exact quoteDropShape_mapEquationSymbols costBaseStaticReflectiveSymbols
           declaration witness.equation witness.equationShape } :
      LanguageDef.ReflectivePresentationWitness
        (reflectiveRetypingLanguage plan) targetDeclaration))

/-- A valid reflective presentation whose named constructors lie in the
hereditary fragment also has a valid wrapped image in the exact
continuation-retyped language. -/
theorem validateReflectivePresentation_costWrapped_of_wrapped
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut)
    (declaration : ReflectivePresentationDecl)
    (valid :
      theory.presentation.presentation.language.validateReflectivePresentation
        declaration = [])
    (quoteWrapped : declaration.quoteConstructor ∈ plan.wrappedLabels)
    (dropWrapped : declaration.dropConstructor ∈ plan.wrappedLabels)
    (unitWrapped :
      declaration.parallelUnitConstructor ∈ plan.wrappedLabels) :
    (reflectiveRetypingLanguage plan).validateReflectivePresentation
      (costWrappedReflectivePresentationDecl theory declaration) = [] := by
  rcases LanguageDef.reflectivePresentationWitness_of_validate_eq_nil
      theory.presentation.presentation.language declaration valid with
    ⟨witness⟩
  have quoteFiltered : witness.quote ∈
      theory.presentation.presentation.language.terms.filter
        (fun term => term.label == declaration.quoteConstructor) := by
    rw [witness.quoteUnique]
    simp
  have quoteMembership := (List.mem_filter.mp quoteFiltered).1
  have quoteLabel : witness.quote.label = declaration.quoteConstructor :=
    beq_iff_eq.mp (List.mem_filter.mp quoteFiltered).2
  have dropFiltered : witness.drop ∈
      theory.presentation.presentation.language.terms.filter
        (fun term => term.label == declaration.dropConstructor) := by
    rw [witness.dropUnique]
    simp
  have dropMembership := (List.mem_filter.mp dropFiltered).1
  have dropLabel : witness.drop.label = declaration.dropConstructor :=
    beq_iff_eq.mp (List.mem_filter.mp dropFiltered).2
  have unitFiltered : witness.unit ∈
      theory.presentation.presentation.language.terms.filter
        (fun term =>
          term.label == declaration.parallelUnitConstructor) := by
    rw [witness.unitUnique]
    simp
  have unitMembership := (List.mem_filter.mp unitFiltered).1
  have unitLabel :
      witness.unit.label = declaration.parallelUnitConstructor :=
    beq_iff_eq.mp (List.mem_filter.mp unitFiltered).2
  have equationFiltered : witness.equation ∈
      theory.presentation.presentation.language.equations.filter
        (fun equation =>
          equation.name == declaration.quoteDropEquation) := by
    rw [witness.equationUnique]
    simp
  have equationMembership := (List.mem_filter.mp equationFiltered).1
  have equationName :
      witness.equation.name = declaration.quoteDropEquation :=
    beq_iff_eq.mp (List.mem_filter.mp equationFiltered).2
  let quoteAuthored :
      DeclaredConstructor theory.presentation.presentation :=
    ⟨witness.quote, quoteMembership⟩
  let dropAuthored :
      DeclaredConstructor theory.presentation.presentation :=
    ⟨witness.drop, dropMembership⟩
  let unitAuthored :
      DeclaredConstructor theory.presentation.presentation :=
    ⟨witness.unit, unitMembership⟩
  have quoteSelected : quoteAuthored ∈ plan.wrappedConstructors :=
    (plan.mem_wrappedLabels_iff quoteAuthored).mp (by
      simpa [quoteAuthored, quoteLabel] using quoteWrapped)
  have dropSelected : dropAuthored ∈ plan.wrappedConstructors :=
    (plan.mem_wrappedLabels_iff dropAuthored).mp (by
      simpa [dropAuthored, dropLabel] using dropWrapped)
  have unitSelected : unitAuthored ∈ plan.wrappedConstructors :=
    (plan.mem_wrappedLabels_iff unitAuthored).mp (by
      simpa [unitAuthored, unitLabel] using unitWrapped)
  let targetDeclaration :=
    costWrappedReflectivePresentationDecl theory declaration
  let targetQuote :=
    costWrappedConstructor (theory := theory) witness.quote
  let targetDrop :=
    costWrappedConstructor (theory := theory) witness.drop
  let targetUnit :=
    costWrappedConstructor (theory := theory) witness.unit
  let targetEquation := costWrappedEquation theory witness.equation
  have targetQuoteUnique :
      (reflectiveRetypingLanguage plan).terms.filter
          (fun term =>
            term.label == targetDeclaration.quoteConstructor) =
        [targetQuote] := by
    change plan.generatedLanguage.terms.filter
        (fun term =>
          term.label ==
            costWrappedConstructorName declaration.quoteConstructor) =
      [costWrappedConstructor (theory := theory) witness.quote]
    simpa [quoteLabel, quoteAuthored] using
      plan.costWrappedConstructor_filter_generated quoteAuthored quoteSelected
  have targetDropUnique :
      (reflectiveRetypingLanguage plan).terms.filter
          (fun term =>
            term.label == targetDeclaration.dropConstructor) =
        [targetDrop] := by
    change plan.generatedLanguage.terms.filter
        (fun term =>
          term.label ==
            costWrappedConstructorName declaration.dropConstructor) =
      [costWrappedConstructor (theory := theory) witness.drop]
    simpa [dropLabel, dropAuthored] using
      plan.costWrappedConstructor_filter_generated dropAuthored dropSelected
  have targetUnitUnique :
      (reflectiveRetypingLanguage plan).terms.filter
          (fun term =>
            term.label == targetDeclaration.parallelUnitConstructor) =
        [targetUnit] := by
    change plan.generatedLanguage.terms.filter
        (fun term =>
          term.label ==
            costWrappedConstructorName declaration.parallelUnitConstructor) =
      [costWrappedConstructor (theory := theory) witness.unit]
    simpa [unitLabel, unitAuthored] using
      plan.costWrappedConstructor_filter_generated unitAuthored unitSelected
  have targetEquationMembership :
      targetEquation ∈ (reflectiveRetypingLanguage plan).equations := by
    change costWrappedEquation theory witness.equation ∈ _
    rw [reflectiveRetypingLanguage_def]
    exact List.mem_append_right _
      (List.mem_map.mpr ⟨witness.equation, equationMembership, rfl⟩)
  have targetEquationName :
      targetEquation.name = targetDeclaration.quoteDropEquation := by
    simp [targetEquation, targetDeclaration, costWrappedEquation,
      costWrappedReflectivePresentationDecl, mapEquation,
      mapReflectivePresentation, costWrappedStaticSymbols,
      costWrappedStaticReflectiveSymbols, equationName]
  have targetEquationUnique :
      (reflectiveRetypingLanguage plan).equations.filter
          (fun equation =>
            equation.name == targetDeclaration.quoteDropEquation) =
        [targetEquation] := by
    rw [← targetEquationName]
    exact LanguageDef.filter_equations_by_name_eq_singleton
      (reflectiveRetypingLanguage plan).equations targetEquation
      (reflectiveRetypingLanguage_equationNames_nodup plan)
      targetEquationMembership
  apply (LanguageDef.ReflectivePresentationWitness.validate
    ({ quote := targetQuote
       drop := targetDrop
       unit := targetUnit
       equation := targetEquation
       quoteParameter := witness.quoteParameter
       dropParameter := witness.dropParameter
       processSort := by
         change (costWrappedStaticSymbols theory).sort
             declaration.processSort ∈
           plan.generatedLanguage.typeNames
         exact (CostStaticColor.wrapped.mapGeneratedLangSort plan
           ⟨declaration.processSort, witness.processSort⟩).2
       nameSort := by
         change (costWrappedStaticSymbols theory).sort declaration.nameSort ∈
           plan.generatedLanguage.typeNames
         exact (CostStaticColor.wrapped.mapGeneratedLangSort plan
           ⟨declaration.nameSort, witness.nameSort⟩).2
       sortsDistinct := by
         change (costWrappedStaticSymbols theory).sort
             declaration.processSort ≠
           (costWrappedStaticSymbols theory).sort declaration.nameSort
         intro equality
         by_cases processInteracting :
             declaration.processSort =
               theory.presentation.interactingSort.1.name
         · by_cases nameInteracting :
               declaration.nameSort =
                 theory.presentation.interactingSort.1.name
           · exact witness.sortsDistinct
               (processInteracting.trans nameInteracting.symm)
           · have impossible :
                 costWrappedSortName =
                   costBaseSortName declaration.nameSort := by
               simpa [costWrappedStaticSymbols, processInteracting,
                 nameInteracting] using equality
             exact costBaseSortName_ne_wrapped _ impossible.symm
         · by_cases nameInteracting :
               declaration.nameSort =
                 theory.presentation.interactingSort.1.name
           · have impossible :
                 costBaseSortName declaration.processSort =
                   costWrappedSortName := by
               simpa [costWrappedStaticSymbols, processInteracting,
                 nameInteracting] using equality
             exact costBaseSortName_ne_wrapped _ impossible
           · exact witness.sortsDistinct (costBaseSortName_injective (by
               simpa [costWrappedStaticSymbols, processInteracting,
                 nameInteracting] using equality))
       quoteUnique := targetQuoteUnique
       quoteCategory := by
         change (if witness.quote.category =
             theory.presentation.interactingSort.1.name then
               costWrappedSortName
             else costBaseSortName witness.quote.category) =
           (costWrappedStaticSymbols theory).sort declaration.nameSort
         rw [witness.quoteCategory]
         rfl
       quoteParameters := by
         change
           witness.quote.params.map
               (mapParameterType
                 (costWrappedTypeExpr
                   theory.presentation.interactingSort.1.name)) =
            [.simple witness.quoteParameter
              (.base ((costWrappedStaticSymbols theory).sort
                declaration.processSort))]
         rw [witness.quoteParameters]
         by_cases interacting :
             declaration.processSort =
               theory.presentation.interactingSort.1.name <;>
           simp [mapParameterType, costWrappedTypeExpr,
             costWrappedStaticSymbols, interacting]
       dropUnique := targetDropUnique
       dropCategory := by
         change (if witness.drop.category =
             theory.presentation.interactingSort.1.name then
               costWrappedSortName
             else costBaseSortName witness.drop.category) =
           (costWrappedStaticSymbols theory).sort declaration.processSort
         rw [witness.dropCategory]
         rfl
       dropParameters := by
         change
           witness.drop.params.map
               (mapParameterType
                 (costWrappedTypeExpr
                   theory.presentation.interactingSort.1.name)) =
            [.simple witness.dropParameter
              (.base ((costWrappedStaticSymbols theory).sort
                declaration.nameSort))]
         rw [witness.dropParameters]
         by_cases interacting :
             declaration.nameSort =
               theory.presentation.interactingSort.1.name <;>
           simp [mapParameterType, costWrappedTypeExpr,
             costWrappedStaticSymbols, interacting]
       unitUnique := targetUnitUnique
       unitCategory := by
         change (if witness.unit.category =
             theory.presentation.interactingSort.1.name then
               costWrappedSortName
             else costBaseSortName witness.unit.category) =
           (costWrappedStaticSymbols theory).sort declaration.processSort
         rw [witness.unitCategory]
         rfl
       unitParameters := by
         change
           (costWrappedConstructor
              (theory := theory) witness.unit).params = []
         simp [costWrappedConstructor, witness.unitParameters]
       equationUnique := targetEquationUnique
       equationShape := by
         change LanguageDef.QuoteDropShape
           (costWrappedReflectivePresentationDecl theory declaration)
           (costWrappedEquation theory witness.equation)
         exact quoteDropShape_mapEquationSymbols
           (costWrappedStaticReflectiveSymbols theory) declaration witness.equation
             witness.equationShape } :
      LanguageDef.ReflectivePresentationWitness
        (reflectiveRetypingLanguage plan) targetDeclaration))

/-- Exact criterion for reflective retyping: ordinary validation plus
hereditary membership of the declaration's three named constructors produces
both deterministic static images. -/
theorem reflectivePresentationRetypable_of_validate_of_wrapped
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut)
    (declaration : ReflectivePresentationDecl)
    (valid :
      theory.presentation.presentation.language.validateReflectivePresentation
        declaration = [])
    (quoteWrapped : declaration.quoteConstructor ∈ plan.wrappedLabels)
    (dropWrapped : declaration.dropConstructor ∈ plan.wrappedLabels)
    (unitWrapped :
      declaration.parallelUnitConstructor ∈ plan.wrappedLabels) :
    ReflectivePresentationRetypable plan declaration :=
  ⟨validateReflectivePresentation_costBase_of_wrapped plan declaration valid
      quoteWrapped dropWrapped unitWrapped,
    validateReflectivePresentation_costWrapped_of_wrapped plan declaration
      valid quoteWrapped dropWrapped unitWrapped⟩

/-- Transport the declared reflective binder support of free parameters into
one generated static Cost fiber.  Free-variable names are unchanged; only
their binder types are mapped. -/
def mapCostStaticSupport (source : CIGSLT) (color : CostStaticColor)
    (support : ContextSupport.Support) : ContextSupport.Support :=
  fun name => (support name).map (mapTypeExpr (color.symbols source))

@[simp]
theorem mapCostStaticSupport_apply (source : CIGSLT)
    (color : CostStaticColor) (support : ContextSupport.Support)
    (name : String) :
    mapCostStaticSupport source color support name =
      (support name).map (mapTypeExpr (color.symbols source)) :=
  rfl

mutual
  /-- If the wrapped image of a pattern is typable in the generated
  continuation signature, every source constructor visible in that pattern
  belongs to the hereditary continuation fragment.  The generated base and
  wrapped constructor namespaces are disjoint, so a wrapped wire label can
  only have arisen from a declaration selected by `wrappedConstructors`.

  Bare collection declarations do not occur in raw `Pattern`; their hidden
  identity is handled separately by `HasType.withConstructors`. -/
  theorem WellSorted.HasType.sourceConstructorsWithin_of_wrappedImage
      {theory : IGSLT} {cut : InteractionCutPresentation theory}
      (plan : ContinuationRetypingPlan cut)
      {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      (typed : WellSorted.HasType plan.generatedLanguage
        free bound
        (mapPattern (CostStaticColor.wrapped.symbolsOf theory) pattern)
        type) :
      ConstructorsWithin (· ∈ plan.wrappedLabels) pattern := by
    induction pattern using Pattern.inductionOn generalizing free bound type with
    | hbvar index => trivial
    | hfvar name => trivial
    | happly constructor arguments inductionHypothesis =>
        generalize patternEquality :
            mapPattern
                (CostStaticColor.wrapped.symbolsOf theory)
                (.apply constructor arguments) = mappedPattern at typed
        cases typed <;> simp [mapPattern] at patternEquality
        case constructor rule arguments' membership notBare argumentsTyped =>
            rcases patternEquality with
              ⟨mappedLabelEquality, argumentsEquality⟩
            change costWrappedConstructorName constructor = rule.label at mappedLabelEquality
            have sourceArgumentsTyped :
                WellSorted.ArgumentsHaveTypes plan.generatedLanguage
                  free bound
                  (arguments.map
                    (mapPattern
                      (CostStaticColor.wrapped.symbolsOf theory)))
                  rule.params := by
              rw [argumentsEquality]
              exact argumentsTyped
            constructor
            · change rule ∈
                  theory.presentation.presentation.language.terms.map
                    (costBaseConstructor cut) ++
                  plan.wrappedConstructors.map (fun constructor =>
                    costWrappedConstructor (theory := theory) constructor.1)
                at membership
              rw [List.mem_append] at membership
              simp only [List.mem_map] at membership
              rcases membership with
                ⟨sourceRule, _sourceMembership, equality⟩ |
                ⟨wrappedRule, wrappedMembership, equality⟩
              · have generatedLabelEquality :=
                  congrArg GrammarRule.label equality
                exact False.elim
                  (costBaseConstructorName_ne_wrapped
                    sourceRule.label constructor
                    (generatedLabelEquality.trans mappedLabelEquality.symm))
              · have generatedLabelEquality :=
                  congrArg GrammarRule.label equality
                have sourceLabelEquality :
                    wrappedRule.1.label = constructor :=
                  costWrappedConstructorName_injective
                    (generatedLabelEquality.trans mappedLabelEquality.symm)
                exact List.mem_map.mpr
                  ⟨wrappedRule, wrappedMembership, sourceLabelEquality⟩
            · exact
                WellSorted.ArgumentsHaveTypes.sourceConstructorListWithin_of_wrappedImage
                  plan sourceArgumentsTyped inductionHypothesis
    | hlambda binder body inductionHypothesis =>
        cases typed with
        | lambda bodyTyped => exact inductionHypothesis bodyTyped
    | hmultiLambda arity binders body inductionHypothesis =>
        cases typed with
        | multiLambda bodyTyped => exact inductionHypothesis bodyTyped
    | hsubst body replacement bodyInduction replacementInduction =>
        cases typed with
        | subst bodyTyped replacementTyped =>
            exact
              ⟨bodyInduction bodyTyped,
                replacementInduction replacementTyped⟩
    | hcollection collectionType elements rest inductionHypothesis =>
        cases typed with
        | collection elementsTyped =>
            exact
              WellSorted.ElementsHaveType.sourceConstructorListWithin_of_wrappedImage
                plan
                (by simpa [mapPatternList_eq_map] using elementsTyped)
                inductionHypothesis
        | collectionConstructor membership parameterShape elementsTyped =>
            exact
              WellSorted.ElementsHaveType.sourceConstructorListWithin_of_wrappedImage
                plan
                (by simpa [mapPatternList_eq_map] using elementsTyped)
                inductionHypothesis

  /-- Ordered-argument companion to
  `HasType.sourceConstructorsWithin_of_wrappedImage`. -/
  theorem WellSorted.ArgumentsHaveTypes.sourceConstructorListWithin_of_wrappedImage
      {theory : IGSLT} {cut : InteractionCutPresentation theory}
      (plan : ContinuationRetypingPlan cut)
      {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {patterns : List Pattern} {parameters : List TermParam}
      (typed : WellSorted.ArgumentsHaveTypes plan.generatedLanguage
        free bound
        (patterns.map
          (mapPattern (CostStaticColor.wrapped.symbolsOf theory)))
        parameters)
      (inductionHypothesis : ∀ pattern ∈ patterns,
        ∀ {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
          {type : TypeExpr},
          WellSorted.HasType plan.generatedLanguage free bound
            (mapPattern (CostStaticColor.wrapped.symbolsOf theory) pattern)
            type →
          ConstructorsWithin (· ∈ plan.wrappedLabels) pattern) :
      ConstructorListWithin (· ∈ plan.wrappedLabels) patterns := by
    induction patterns generalizing parameters with
    | nil => trivial
    | cons pattern patterns tailInduction =>
        cases typed with
        | cons representation parameterType headTyped tailTyped =>
            exact
              ⟨inductionHypothesis pattern (by simp) headTyped,
                tailInduction tailTyped
                  (fun nested membership =>
                    inductionHypothesis nested (by simp [membership]))⟩

  /-- Collection-element companion to
  `HasType.sourceConstructorsWithin_of_wrappedImage`. -/
  theorem WellSorted.ElementsHaveType.sourceConstructorListWithin_of_wrappedImage
      {theory : IGSLT} {cut : InteractionCutPresentation theory}
      (plan : ContinuationRetypingPlan cut)
      {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
      {patterns : List Pattern} {type : TypeExpr}
      (typed : WellSorted.ElementsHaveType plan.generatedLanguage
        free bound
        (patterns.map
          (mapPattern (CostStaticColor.wrapped.symbolsOf theory)))
        type)
      (inductionHypothesis : ∀ pattern ∈ patterns,
        ∀ {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
          {type : TypeExpr},
          WellSorted.HasType plan.generatedLanguage free bound
            (mapPattern (CostStaticColor.wrapped.symbolsOf theory) pattern)
            type →
          ConstructorsWithin (· ∈ plan.wrappedLabels) pattern) :
      ConstructorListWithin (· ∈ plan.wrappedLabels) patterns := by
    induction patterns with
    | nil => trivial
    | cons pattern patterns tailInduction =>
        cases typed with
        | cons headTyped tailTyped =>
            exact
              ⟨inductionHypothesis pattern (by simp) headTyped,
                tailInduction tailTyped
                  (fun nested membership =>
                    inductionHypothesis nested (by simp [membership]))⟩
end

namespace ContinuationDecorationProfile

open WellSorted

variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

/-- Row transport is derived from the actual closure inventory, including
bare collection declarations whose labels are absent from raw patterns. -/
theorem staticRows (profile : ContinuationDecorationProfile cut)
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor)
    (color : CostStaticColor) (rule : GrammarRule)
    (member : rule ∈ theory.presentation.presentation.language.terms)
    (supported : rule.label ∈ profile.wrappedLabels) :
    ∃ targetRule ∈ profile.generatedLanguage.terms,
      targetRule.label = (color.symbolsOf theory).constructor rule.label ∧
      targetRule.category = (color.symbolsOf theory).sort rule.category ∧
      targetRule.params = rule.params.map (mapTermParam (color.symbolsOf theory)) := by
  let authored : DeclaredConstructor theory.presentation.presentation := ⟨rule, member⟩
  have included : authored ∈ profile.constructorClosure :=
    (profile.mem_wrappedLabels_iff authored).mp supported
  cases color with
  | base =>
      refine ⟨profile.baseConstructor rule, profile.baseConstructor_mem rule member,
        rfl, rfl, ?_⟩
      exact profile.baseConstructor_params_eq_map_of_mem_wrappedLabels nonprincipal
        rule member supported
  | wrapped =>
      refine ⟨costWrappedConstructor (theory := theory) rule,
        profile.wrappedConstructor_mem authored included, rfl, rfl, ?_⟩
      simp [costWrappedConstructor, CostStaticColor.symbolsOf]

/-- Uniform static transport into the actual finite generated signature. -/
theorem mapStatic_hasType_generated (profile : ContinuationDecorationProfile cut)
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor)
    (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasTypeWithConstructors theory.presentation.presentation.language
      (· ∈ profile.wrappedLabels) free bound pattern type) :
    HasType profile.generatedLanguage (free.map (color.symbolsOf theory))
      (bound.map (mapTypeExpr (color.symbolsOf theory)))
      (mapPattern (color.symbolsOf theory) pattern) (mapTypeExpr (color.symbolsOf theory) type) :=
  typed.mapRows (color.symbolsOf theory) (profile.staticRows nonprincipal color)

/-- The same derivation lives in the generated Cost language with its
apparatus, source equations, and selected funded rule. -/
theorem mapStatic_hasType (profile : ContinuationDecorationProfile cut)
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor)
    (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasTypeWithConstructors theory.presentation.presentation.language
      (· ∈ profile.wrappedLabels) free bound pattern type) :
    HasType profile.costWholeLanguage (free.map (color.symbolsOf theory))
      (bound.map (mapTypeExpr (color.symbolsOf theory)))
      (mapPattern (color.symbolsOf theory) pattern) (mapTypeExpr (color.symbolsOf theory) type) :=
  (profile.mapStatic_hasType_generated nonprincipal color typed).weakenTerms
    profile.generatedTerms_mem_costWhole

/-- A principal introduction cannot be smuggled into the uniform static
fragment by retaining its label alone. -/
theorem principal_labels_excluded (profile : ContinuationDecorationProfile cut)
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor) :
    cut.program.constructor.1.label ∉ profile.wrappedLabels ∧
      cut.environment.constructor.1.label ∉ profile.wrappedLabels := by
  constructor
  · intro supported
    exact (nonprincipal cut.program.constructor
      ((profile.mem_wrappedLabels_iff _).mp supported)).1 rfl
  · intro supported
    exact (nonprincipal cut.environment.constructor
      ((profile.mem_wrappedLabels_iff _).mp supported)).2 rfl

end ContinuationDecorationProfile

/-- Every row of the cut-derived non-principal fragment has its uniformly
mapped row in the complete Cost language of a continued theory. -/
theorem CIGSLT.costStaticRows (source : CIGSLT) (color : CostStaticColor)
    (rule : GrammarRule)
    (member : rule ∈ source.theory.presentation.presentation.language.terms)
    (supported : rule.label ∈ source.continuationRetyping.wrappedLabels) :
    ∃ targetRule ∈ source.costWholeLanguage.terms,
      targetRule.label = (color.symbols source).constructor rule.label ∧
      targetRule.category = (color.symbols source).sort rule.category ∧
      targetRule.params = rule.params.map (mapTermParam (color.symbols source)) := by
  obtain ⟨targetRule, targetMember, rest⟩ :=
    (ContinuationDecorationProfile.ofRetypingPlan source.continuationRetyping).staticRows
      (ContinuationDecorationProfile.ofRetypingPlan_nonprincipal source.continuationRetyping)
      color rule member supported
  exact ⟨targetRule, List.mem_append_left _ targetMember, rest⟩

/-- Non-circular static transport into the bare generated continuation
signature.  It depends only on the authored theory, cut, and retyping
plan; a completed continued object is not required. -/
theorem WellSorted.HasTypeWithConstructors.mapCostStaticGenerated
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) (color : CostStaticColor)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    (typed : WellSorted.HasTypeWithConstructors
      theory.presentation.presentation.language
      (· ∈ plan.wrappedLabels) free bound pattern type) :
    WellSorted.HasType plan.generatedLanguage
      (free.map (color.symbolsOf theory))
      (bound.map (mapTypeExpr (color.symbolsOf theory)))
      (mapPattern (color.symbolsOf theory) pattern)
      (mapTypeExpr (color.symbolsOf theory) type) :=
  typed.mapRows (color.symbolsOf theory)
    ((ContinuationDecorationProfile.ofRetypingPlan plan).staticRows
      (ContinuationDecorationProfile.ofRetypingPlan_nonprincipal plan) color)

theorem WellSorted.ArgumentsHaveTypesWithConstructors.mapCostStaticGenerated
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) (color : CostStaticColor)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {arguments : List Pattern} {parameters : List TermParam}
    (typed : WellSorted.ArgumentsHaveTypesWithConstructors
      theory.presentation.presentation.language
      (· ∈ plan.wrappedLabels) free bound arguments parameters) :
    WellSorted.ArgumentsHaveTypes plan.generatedLanguage
      (free.map (color.symbolsOf theory))
      (bound.map (mapTypeExpr (color.symbolsOf theory)))
      (arguments.map (mapPattern (color.symbolsOf theory)))
      (parameters.map (mapTermParam (color.symbolsOf theory))) :=
  typed.mapRows (color.symbolsOf theory)
    ((ContinuationDecorationProfile.ofRetypingPlan plan).staticRows
      (ContinuationDecorationProfile.ofRetypingPlan_nonprincipal plan) color)

theorem WellSorted.ElementsHaveTypeWithConstructors.mapCostStaticGenerated
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) (color : CostStaticColor)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern} {elementType : TypeExpr}
    (typed : WellSorted.ElementsHaveTypeWithConstructors
      theory.presentation.presentation.language
      (· ∈ plan.wrappedLabels) free bound elements elementType) :
    WellSorted.ElementsHaveType plan.generatedLanguage
      (free.map (color.symbolsOf theory))
      (bound.map (mapTypeExpr (color.symbolsOf theory)))
      (elements.map (mapPattern (color.symbolsOf theory)))
      (mapTypeExpr (color.symbolsOf theory) elementType) :=
  typed.mapRows (color.symbolsOf theory)
    ((ContinuationDecorationProfile.ofRetypingPlan plan).staticRows
      (ContinuationDecorationProfile.ofRetypingPlan_nonprincipal plan) color)

/-- Typed source terms in the declaration-derived non-principal fragment
transport into either generated Cost static namespace. -/
theorem WellSorted.HasTypeWithConstructors.mapCostStatic
    (source : CIGSLT) (color : CostStaticColor)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    (typed : WellSorted.HasTypeWithConstructors
      source.theory.presentation.presentation.language
      (· ∈ source.continuationRetyping.wrappedLabels)
      free bound pattern type) :
    WellSorted.HasType source.costWholeLanguage
      (free.map (color.symbols source))
      (bound.map (mapTypeExpr (color.symbols source)))
      (mapPattern (color.symbols source) pattern)
      (mapTypeExpr (color.symbols source) type) :=
  typed.mapRows (color.symbols source) (source.costStaticRows color)

theorem WellSorted.ArgumentsHaveTypesWithConstructors.mapCostStatic
    (source : CIGSLT) (color : CostStaticColor)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {arguments : List Pattern} {parameters : List TermParam}
    (typed : WellSorted.ArgumentsHaveTypesWithConstructors
      source.theory.presentation.presentation.language
      (· ∈ source.continuationRetyping.wrappedLabels)
      free bound arguments parameters) :
    WellSorted.ArgumentsHaveTypes source.costWholeLanguage
      (free.map (color.symbols source))
      (bound.map (mapTypeExpr (color.symbols source)))
      (arguments.map (mapPattern (color.symbols source)))
      (parameters.map (mapTermParam (color.symbols source))) :=
  typed.mapRows (color.symbols source) (source.costStaticRows color)

theorem WellSorted.ElementsHaveTypeWithConstructors.mapCostStatic
    (source : CIGSLT) (color : CostStaticColor)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern} {elementType : TypeExpr}
    (typed : WellSorted.ElementsHaveTypeWithConstructors
      source.theory.presentation.presentation.language
      (· ∈ source.continuationRetyping.wrappedLabels)
      free bound elements elementType) :
    WellSorted.ElementsHaveType source.costWholeLanguage
      (free.map (color.symbols source))
      (bound.map (mapTypeExpr (color.symbols source)))
      (elements.map (mapPattern (color.symbols source)))
      (mapTypeExpr (color.symbols source) elementType) :=
  typed.mapRows (color.symbols source) (source.costStaticRows color)

mutual
  /-- Re-express source reflective support in one generated Cost binder
  codomain without changing the source typing derivation.  This is the
  naturality bridge between ordinary source support and the target-support
  form consumed by `mapCostStatic`. -/
  theorem WellSorted.HasType.ReflectiveSupportSafeAt.mapCostStaticSupport
      (source : CIGSLT) (color : CostStaticColor)
      {language : LanguageDef} {free : WellSorted.FreeTypeContext}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      {typed : WellSorted.HasType language free bound pattern type}
      {profile : ReflectionProfile}
      {support : ContextSupport.Support} {available : List TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt profile support available) :
      typed.ReflectiveSupportSafeAt profile
        (mapCostStaticSupport source color support)
        (available.map (mapTypeExpr (color.symbols source)))
        (mapTypeExpr (color.symbols source)) := by
    cases safe with
    | bvar lookup available => exact .bvar lookup _
    | fvar lookup available shape =>
        rcases shape with ⟨inner, rfl⟩
        exact .fvar lookup _
          ⟨inner.map (mapTypeExpr (color.symbols source)), by
            simp [mapCostStaticSupport, List.map_append]⟩
    | @constructorQuote _ rule arguments membership notBare argumentsTyped
        available _ quoted argumentsSafe =>
        exact .constructorQuote (membership := membership)
          (notBare := notBare) quoted
          (by simpa using argumentsSafe.mapCostStaticSupport source color)
    | @constructorOrdinary _ rule arguments membership notBare argumentsTyped
        available _ ordinary argumentsSafe =>
        exact .constructorOrdinary (membership := membership)
          (notBare := notBare) ordinary
          (argumentsSafe.mapCostStaticSupport source color)
    | lambda bodySafe =>
        exact .lambda (by simpa using bodySafe.mapCostStaticSupport source color)
    | multiLambda bodySafe =>
        exact .multiLambda (by
          simpa [List.map_append, List.map_replicate] using
            bodySafe.mapCostStaticSupport source color)
    | subst bodySafe replacementSafe =>
        exact .subst
          (by simpa using bodySafe.mapCostStaticSupport source color)
          (replacementSafe.mapCostStaticSupport source color)
    | collection elementsSafe =>
        exact .collection (elementsSafe.mapCostStaticSupport source color)
    | @collectionConstructor _ rule parameterName collectionType elements rest
        elementType membership parameterShape elementsTyped available _
        elementsSafe =>
        exact .collectionConstructor (membership := membership)
          (parameterShape := parameterShape)
          (elementsSafe.mapCostStaticSupport source color)

  /-- Ordered-argument companion to reflective-support codomain mapping. -/
  theorem WellSorted.ArgumentsHaveTypes.ReflectiveSupportSafeAt.mapCostStaticSupport
      (source : CIGSLT) (color : CostStaticColor)
      {language : LanguageDef} {free : WellSorted.FreeTypeContext}
      {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      {typed : WellSorted.ArgumentsHaveTypes language free bound arguments
        parameters}
      {profile : ReflectionProfile}
      {support : ContextSupport.Support} {available : List TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt profile support available) :
      typed.ReflectiveSupportSafeAt profile
        (mapCostStaticSupport source color support)
        (available.map (mapTypeExpr (color.symbols source)))
        (mapTypeExpr (color.symbols source)) := by
    cases safe with
    | nil => exact .nil _ _
    | @cons _ argument arguments parameter parameters expected representation
        parameterType argumentTyped argumentsTyped available _ argumentSafe
        argumentsSafe =>
        exact .cons (representation := representation)
          (parameterType := parameterType)
          (argumentSafe.mapCostStaticSupport source color)
          (argumentsSafe.mapCostStaticSupport source color)

  /-- Homogeneous-element companion to reflective-support codomain mapping. -/
  theorem WellSorted.ElementsHaveType.ReflectiveSupportSafeAt.mapCostStaticSupport
      (source : CIGSLT) (color : CostStaticColor)
      {language : LanguageDef} {free : WellSorted.FreeTypeContext}
      {bound : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      {typed : WellSorted.ElementsHaveType language free bound elements
        elementType}
      {profile : ReflectionProfile}
      {support : ContextSupport.Support} {available : List TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt profile support available) :
      typed.ReflectiveSupportSafeAt profile
        (mapCostStaticSupport source color support)
        (available.map (mapTypeExpr (color.symbols source)))
        (mapTypeExpr (color.symbols source)) := by
    cases safe with
    | nil => exact .nil _ _ _
    | cons elementSafe elementsSafe =>
        exact .cons
          (elementSafe.mapCostStaticSupport source color)
          (elementsSafe.mapCostStaticSupport source color)
end

/-- A reflectively support-safe source derivation whose visible
constructors lie in the declaration-derived non-principal fragment has a
support-safe image in either static Cost fiber.  Reflective support already
lives in the target binder codomain: source binders are interpreted by the
selected static type map, while foreign target binders remain unchanged.
The result is existential in its proof term because typing derivations are
proof-irrelevant. -/
theorem WellSorted.HasType.ReflectiveSupportSafeAt.mapCostStatic
    (source : CIGSLT) (color : CostStaticColor)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    {typed : WellSorted.HasType
      source.theory.presentation.presentation.language
      free bound pattern type}
    {support : ContextSupport.Support} {available : List TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt source.reflection.1 support available
      (mapTypeExpr (color.symbols source)))
    (supported : ConstructorsWithin
      (· ∈ source.continuationRetyping.wrappedLabels) pattern) :
    ∃ targetTyped : WellSorted.HasType source.costWholeLanguage
        (free.map (color.symbols source))
        (bound.map (mapTypeExpr (color.symbols source)))
        (mapPattern (color.symbols source) pattern)
        (mapTypeExpr (color.symbols source) type),
      targetTyped.ReflectiveSupportSafeAt source.costWholeReflectionProfile
        support available :=
  safe.mapRows (color.symbols source) (source.costStaticRows color)
    source.bareCollectionConstructorsWrapped
    (fun rule _ _ => reflectiveIsQuoteConstructor_mapCostStatic source color rule.label)
    supported

theorem WellSorted.ArgumentsHaveTypes.ReflectiveSupportSafeAt.mapCostStatic
    (source : CIGSLT) (color : CostStaticColor)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {arguments : List Pattern} {parameters : List TermParam}
    {typed : WellSorted.ArgumentsHaveTypes
      source.theory.presentation.presentation.language
      free bound arguments parameters}
    {support : ContextSupport.Support} {available : List TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt source.reflection.1 support available
      (mapTypeExpr (color.symbols source)))
    (supported : ConstructorListWithin
      (· ∈ source.continuationRetyping.wrappedLabels) arguments) :
    ∃ targetTyped : WellSorted.ArgumentsHaveTypes source.costWholeLanguage
        (free.map (color.symbols source))
        (bound.map (mapTypeExpr (color.symbols source)))
        (arguments.map (mapPattern (color.symbols source)))
        (parameters.map (mapTermParam (color.symbols source))),
      targetTyped.ReflectiveSupportSafeAt source.costWholeReflectionProfile
        support available :=
  safe.mapRows (color.symbols source) (source.costStaticRows color)
    source.bareCollectionConstructorsWrapped
    (fun rule _ _ => reflectiveIsQuoteConstructor_mapCostStatic source color rule.label)
    supported

theorem WellSorted.ElementsHaveType.ReflectiveSupportSafeAt.mapCostStatic
    (source : CIGSLT) (color : CostStaticColor)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern} {elementType : TypeExpr}
    {typed : WellSorted.ElementsHaveType
      source.theory.presentation.presentation.language
      free bound elements elementType}
    {support : ContextSupport.Support} {available : List TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt source.reflection.1 support available
      (mapTypeExpr (color.symbols source)))
    (supported : ConstructorListWithin
      (· ∈ source.continuationRetyping.wrappedLabels) elements) :
    ∃ targetTyped : WellSorted.ElementsHaveType source.costWholeLanguage
        (free.map (color.symbols source))
        (bound.map (mapTypeExpr (color.symbols source)))
        (elements.map (mapPattern (color.symbols source)))
        (mapTypeExpr (color.symbols source) elementType),
      targetTyped.ReflectiveSupportSafeAt source.costWholeReflectionProfile
        support available :=
  safe.mapRows (color.symbols source) (source.costStaticRows color)
    source.bareCollectionConstructorsWrapped
    (fun rule _ _ => reflectiveIsQuoteConstructor_mapCostStatic source color rule.label)
    supported

end Mettapedia.GSLT.LanguageDef
