import Mettapedia.GSLT.LanguageDef.ConstructorSupport
import Mettapedia.GSLT.LanguageDef.ContextSupport
import Mettapedia.GSLT.LanguageDef.CostInteractionClosure

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
def symbolsOf (theory : IGSLT) : CostStaticColor → PresentationSymbols
  | .base => costBaseStaticSymbols
  | .wrapped => costWrappedStaticSymbols theory

/-- Uniform presentation action that embeds one static copy. -/
def symbols (source : CIGSLT) : CostStaticColor → PresentationSymbols
  | .base => costBaseStaticSymbols
  | .wrapped => costWrappedStaticSymbols source.theory

/-- The corresponding action on the independently authored reflection
fibre.  Its core projection is exactly `symbols`; the additional component
renames presentation and reflective-rule identifiers. -/
def reflectiveSymbols (source : CIGSLT) : CostStaticColor → ReflectiveSymbols
  | .base => costBaseStaticReflectiveSymbols
  | .wrapped => costWrappedStaticReflectiveSymbols source.theory

@[simp]
theorem reflectiveSymbols_toPresentationSymbols
    (source : CIGSLT) (color : CostStaticColor) :
    (color.reflectiveSymbols source).toPresentationSymbols =
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

theorem symbols_eq_symbolsOf (source : CIGSLT) (color : CostStaticColor) :
    color.symbols source = color.symbolsOf source.theory := by
  cases color <;> rfl

@[simp]
theorem symbols_constructor (source : CIGSLT) (color : CostStaticColor)
    (constructor : String) :
    (color.symbols source).constructor constructor =
      color.constructorTag ++ constructor := by
  cases color <;>
    rfl

@[simp]
theorem symbolsOf_constructor (theory : IGSLT) (color : CostStaticColor)
    (constructor : String) :
    (color.symbolsOf theory).constructor constructor =
      color.constructorTag ++ constructor := by
  cases color <;>
    rfl

/-- Each static Cost color embeds the source constructor namespace
injectively. -/
theorem symbols_constructor_injective (source : CIGSLT)
    (color : CostStaticColor) :
    Function.Injective (color.symbols source).constructor := by
  cases color with
  | base => exact costBaseConstructorName_injective
  | wrapped => exact costWrappedConstructorName_injective

/-- The theory-indexed static constructor action is injective in either
generated namespace. -/
theorem symbolsOf_constructor_injective (theory : IGSLT)
    (color : CostStaticColor) :
    Function.Injective (color.symbolsOf theory).constructor := by
  cases color with
  | base => exact costBaseConstructorName_injective
  | wrapped => exact costWrappedConstructorName_injective

/-- Quotation-aware scope is transported exactly inside either injectively
tagged static Cost fiber. -/
@[simp]
theorem binderSafeAt_mapPattern_symbols (source : CIGSLT)
    (color : CostStaticColor) (quoteConstructor : String)
    (depth : Nat) (pattern : Pattern) :
    binderSafeAt ((color.symbols source).constructor quoteConstructor) depth
        (mapPattern (color.symbols source) pattern) =
      binderSafeAt quoteConstructor depth pattern :=
  WellSorted.binderSafeAt_mapPattern_of_constructor_injective
    (color.symbols source) (color.symbols_constructor_injective source)
    quoteConstructor depth pattern

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
      · simp only [CostStaticColor.symbols, costWrappedStaticSymbols,
          interacting, if_pos]
        exact source.costWrappedSortName_mem_costWhole
      · simp only [CostStaticColor.symbols, costWrappedStaticSymbols,
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
  simp only [CostStaticColor.symbols, mapTypeExpr_costBaseStaticSymbols,
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
      simpa [CostStaticColor.symbols,
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
            simpa [CostStaticColor.symbols, costWrappedStaticSymbols,
              firstInteracting, secondInteracting] using nameEquality
          exact (costBaseSortName_ne_wrapped second.1 impossible.symm).elim
      · by_cases secondInteracting :
            second.1 = source.theory.presentation.interactingSort.1.name
        · have impossible : costBaseSortName first.1 = costWrappedSortName := by
            simpa [CostStaticColor.symbols, costWrappedStaticSymbols,
              firstInteracting, secondInteracting] using nameEquality
          exact (costBaseSortName_ne_wrapped first.1 impossible).elim
        · exact costBaseSortName_injective (by
            simpa [CostStaticColor.symbols, costWrappedStaticSymbols,
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
      simpa [CostStaticColor.mapLangSort_name, CostStaticColor.symbols,
        costBaseStaticSymbols, costBasePresentationSymbols,
        costWrappedStaticSymbols, firstInteracting, secondInteracting] using
        nameEquality
    exact (costBaseSortName_ne_wrapped _ impossible).elim
  · have impossible :
        costWrappedSortName =
          costBaseSortName
            source.theory.presentation.interactingSort.1.name := by
      simpa [CostStaticColor.mapLangSort_name, CostStaticColor.symbols,
        costBaseStaticSymbols, costBasePresentationSymbols,
        costWrappedStaticSymbols, firstInteracting, secondInteracting] using
        nameEquality
    exact (costBaseSortName_ne_wrapped _ impossible.symm).elim
  · rfl

end CostStaticColor

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
      (mapPattern (color.symbols source) pattern) := by
  intro targetPresentation targetMembership
  rw [CIGSLT.costWholeReflectionProfile_presentations,
    CIGSLT.costStaticReflectivePresentations, List.mem_append]
    at targetMembership
  rcases targetMembership with baseMembership | wrappedMembership
  · rcases List.mem_map.mp baseMembership with
      ⟨sourcePresentation, sourceMembership, rfl⟩
    cases color with
    | base =>
        simpa [costBaseReflectivePresentationDecl,
          mapReflectivePresentation, CostStaticColor.symbols,
          costBaseStaticSymbols, costBaseStaticReflectiveSymbols,
          costBasePresentationSymbols] using
          (show binderSafeAt
              ((CostStaticColor.base.symbols source).constructor
                sourcePresentation.quoteConstructor) depth
              (mapPattern (CostStaticColor.base.symbols source) pattern) = true
            from by
              rw [CostStaticColor.binderSafeAt_mapPattern_symbols]
              exact sourceSafe sourcePresentation sourceMembership)
    | wrapped =>
        have scopeEquality :=
          WellSorted.binderSafeAt_mapPattern_of_constructor_avoids
            (CostStaticColor.wrapped.symbols source)
            (costBaseConstructorName sourcePresentation.quoteConstructor)
            (fun constructor equality =>
              costBaseConstructorName_ne_wrapped
                sourcePresentation.quoteConstructor constructor equality.symm)
            depth pattern
        simpa [costBaseReflectivePresentationDecl,
          mapReflectivePresentation, CostStaticColor.symbols,
          costBaseStaticSymbols, costBaseStaticReflectiveSymbols,
          costBasePresentationSymbols] using
          (scopeEquality.trans mappedOrdinaryScope)
  · rcases List.mem_map.mp wrappedMembership with
      ⟨sourcePresentation, sourceMembership, rfl⟩
    cases color with
    | base =>
        have scopeEquality :=
          WellSorted.binderSafeAt_mapPattern_of_constructor_avoids
            (CostStaticColor.base.symbols source)
            (costWrappedConstructorName sourcePresentation.quoteConstructor)
            (fun constructor =>
              costBaseConstructorName_ne_wrapped constructor
                sourcePresentation.quoteConstructor)
            depth pattern
        simpa [costWrappedReflectivePresentationDecl,
          mapReflectivePresentation, CostStaticColor.symbols,
          costWrappedStaticSymbols, costWrappedStaticReflectiveSymbols] using
          (scopeEquality.trans mappedOrdinaryScope)
    | wrapped =>
        simpa [costWrappedReflectivePresentationDecl,
          mapReflectivePresentation, CostStaticColor.symbols,
          costWrappedStaticReflectiveSymbols] using
          (show binderSafeAt
              ((CostStaticColor.wrapped.symbols source).constructor
                sourcePresentation.quoteConstructor) depth
              (mapPattern (CostStaticColor.wrapped.symbols source) pattern) = true
            from by
              rw [CostStaticColor.binderSafeAt_mapPattern_symbols]
              exact sourceSafe sourcePresentation sourceMembership)

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
        source.reflection.1 constructor := by
  unfold ReflectiveContextSupport.isQuoteConstructor
  rw [CIGSLT.costWholeReflectionProfile_presentations]
  rw [CIGSLT.costStaticReflectivePresentations, List.any_append]
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
          simpa [CostStaticColor.symbols,
            costBaseReflectivePresentationDecl, mapReflectivePresentation,
            costBaseStaticSymbols, costBaseStaticReflectiveSymbols,
            costBasePresentationSymbols] using equality
        · have impossible :
              costWrappedConstructorName declaration.quoteConstructor =
                costBaseConstructorName constructor := by
            simpa [CostStaticColor.symbols,
              costWrappedReflectivePresentationDecl,
              mapReflectivePresentation, costWrappedStaticSymbols,
              costWrappedStaticReflectiveSymbols, costBaseStaticSymbols,
              costBasePresentationSymbols] using equality
          exact False.elim
            (costBaseConstructorName_ne_wrapped constructor
              declaration.quoteConstructor impossible.symm)
      · rintro ⟨declaration, membership, equality⟩
        left
        refine ⟨declaration, membership, ?_⟩
        simp [CostStaticColor.symbols,
          costBaseReflectivePresentationDecl, mapReflectivePresentation,
          costBaseStaticSymbols, costBaseStaticReflectiveSymbols,
          costBasePresentationSymbols, equality]
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
            simpa [CostStaticColor.symbols,
              costBaseReflectivePresentationDecl, mapReflectivePresentation,
              costBaseStaticSymbols, costBaseStaticReflectiveSymbols,
              costBasePresentationSymbols,
              costWrappedStaticSymbols] using equality
          exact False.elim
            (costBaseConstructorName_ne_wrapped
              declaration.quoteConstructor constructor impossible)
        · refine ⟨declaration, membership, ?_⟩
          apply costWrappedConstructorName_injective
          simpa [CostStaticColor.symbols,
            costWrappedReflectivePresentationDecl,
            mapReflectivePresentation, costWrappedStaticSymbols,
            costWrappedStaticReflectiveSymbols] using equality
      · rintro ⟨declaration, membership, equality⟩
        right
        refine ⟨declaration, membership, ?_⟩
        simp [CostStaticColor.symbols,
          costWrappedReflectivePresentationDecl, mapReflectivePresentation,
          costWrappedStaticSymbols, costWrappedStaticReflectiveSymbols,
          equality]

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

/-- A constructor in the cut-derived wrapped fragment is not either selected
interaction principal, so none of its argument positions is a selected
continuation. -/
theorem isSelectedContinuation_eq_false_of_mem_wrappedLabelsFor
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) (rule : GrammarRule)
    (membership : rule ∈ theory.presentation.presentation.language.terms)
    (wrapped : rule.label ∈ plan.wrappedLabels)
    (index : Nat) :
    isSelectedContinuation cut rule index = false := by
  let authored : AuthoredConstructor theory.presentation.presentation :=
    ⟨rule, membership⟩
  have wrappedConstructor : authored ∈ plan.wrappedConstructors :=
    (plan.mem_wrappedLabels_iff authored).mp wrapped
  have inequalities :=
    (plan.mem_wrappedConstructors_iff authored).mp wrappedConstructor
  have programNe : rule ≠ cut.program.constructor.1 := by
    intro equality
    apply inequalities.1
    apply Subtype.ext
    exact equality
  have environmentNe : rule ≠ cut.environment.constructor.1 := by
    intro equality
    apply inequalities.2
    apply Subtype.ext
    exact equality
  simp [isSelectedContinuation, programNe, environmentNe]

theorem isSelectedContinuation_eq_false_of_mem_wrappedLabels
    (source : CIGSLT) (rule : GrammarRule)
    (membership : rule ∈
      source.theory.presentation.presentation.language.terms)
    (wrapped : rule.label ∈
      source.continuationRetyping.wrappedLabels)
    (index : Nat) :
    isSelectedContinuation source.cut rule index = false := by
  exact isSelectedContinuation_eq_false_of_mem_wrappedLabelsFor
    source.continuationRetyping rule membership wrapped index

@[simp]
theorem mapTermParam_costBaseStaticSymbols (parameter : TermParam) :
    mapTermParam costBaseStaticSymbols parameter =
      mapParameterType costBaseTypeExpr parameter := by
  cases parameter <;>
    simp [mapTermParam, mapParameterType,
      mapTypeExpr_costBaseStaticSymbols]

@[simp]
theorem mapTermParam_costWrappedStaticSymbols (source : CIGSLT)
    (parameter : TermParam) :
    mapTermParam (costWrappedStaticSymbols source.theory) parameter =
      mapParameterType
        (costWrappedTypeExpr
          source.theory.presentation.interactingSort.1.name) parameter := by
  cases parameter <;>
    simp [mapTermParam, mapParameterType,
      mapTypeExpr_costWrappedStaticSymbols]

@[simp]
theorem mapTermParam_costWrappedStaticSymbolsFor (theory : IGSLT)
    (parameter : TermParam) :
    mapTermParam (costWrappedStaticSymbols theory) parameter =
      mapParameterType
        (costWrappedTypeExpr theory.presentation.interactingSort.1.name)
        parameter := by
  cases parameter <;>
    simp [mapTermParam, mapParameterType,
      mapTypeExpr_costWrappedStaticSymbols]

/-- Generic parameter transport before a complete continued object exists. -/
theorem costBaseConstructor_params_eq_map_of_mem_wrappedLabelsFor
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (plan : ContinuationRetypingPlan cut) (rule : GrammarRule)
    (membership : rule ∈ theory.presentation.presentation.language.terms)
    (wrapped : rule.label ∈ plan.wrappedLabels) :
    (costBaseConstructor cut rule).params =
      rule.params.map (mapTermParam costBaseStaticSymbols) := by
  apply List.ext_getElem
  · simp [costBaseConstructor]
  · intro index leftBound rightBound
    rw [costBaseConstructor_parameter cut rule index (by
      simpa [costBaseConstructor] using leftBound)]
    simp [List.getElem_map, costBaseParameter,
      isSelectedContinuation_eq_false_of_mem_wrappedLabelsFor plan rule
        membership wrapped index]

/-- Away from the two selected principals, base-constructor parameter
retyping is exactly the uniform base static symbol action. -/
theorem costBaseConstructor_params_eq_map_of_mem_wrappedLabels
    (source : CIGSLT) (rule : GrammarRule)
    (membership : rule ∈
      source.theory.presentation.presentation.language.terms)
    (wrapped : rule.label ∈
      source.continuationRetyping.wrappedLabels) :
    (costBaseConstructor source.cut rule).params =
      rule.params.map (mapTermParam costBaseStaticSymbols) := by
  exact costBaseConstructor_params_eq_map_of_mem_wrappedLabelsFor
    source.continuationRetyping rule membership wrapped

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
      (mapEquation symbols.toPresentationSymbols equation) := by
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
    simp [reflectiveRetypingLanguage, Function.comp_def,
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
    rw [reflectiveRetypingLanguage]
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
         rw [costBaseConstructor_params_eq_map_of_mem_wrappedLabelsFor
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
         rw [costBaseConstructor_params_eq_map_of_mem_wrappedLabelsFor
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
         rw [costBaseConstructor_params_eq_map_of_mem_wrappedLabelsFor
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
      AuthoredConstructor theory.presentation.presentation :=
    ⟨witness.quote, quoteMembership⟩
  let dropAuthored :
      AuthoredConstructor theory.presentation.presentation :=
    ⟨witness.drop, dropMembership⟩
  let unitAuthored :
      AuthoredConstructor theory.presentation.presentation :=
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
    rw [reflectiveRetypingLanguage]
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
            · simp only [ContinuationRetypingPlan.generatedLanguage,
                List.mem_append, List.mem_map] at membership
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

mutual
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
        (mapTypeExpr (color.symbolsOf theory) type) := by
    cases typed with
    | @bvar bound index type lookup =>
        have mappedLookup :
            (bound.map (mapTypeExpr (color.symbolsOf theory)))[index]? =
              some (mapTypeExpr (color.symbolsOf theory) type) := by
          simpa using congrArg
            (Option.map (mapTypeExpr (color.symbolsOf theory))) lookup
        simpa [mapPattern] using
          (WellSorted.HasType.bvar
            (free := free.map (color.symbolsOf theory)) mappedLookup)
    | @fvar bound name type lookup =>
        have mappedLookup :
            (free.map (color.symbolsOf theory)) name =
              some (mapTypeExpr (color.symbolsOf theory) type) := by
          simp [WellSorted.FreeTypeContext.map, lookup]
        simpa [mapPattern] using
          (WellSorted.HasType.fvar
            (bound := bound.map (mapTypeExpr (color.symbolsOf theory)))
            mappedLookup)
    | @constructor bound rule arguments labelSupported membership notBare
        argumentsTyped =>
        let authored : AuthoredConstructor theory.presentation.presentation :=
          ⟨rule, membership⟩
        have wrappedConstructor : authored ∈ plan.wrappedConstructors :=
          (plan.mem_wrappedLabels_iff authored).mp labelSupported
        cases color with
        | base =>
            have mappedArguments :=
              argumentsTyped.mapCostStaticGenerated plan .base
            have parameterEquality :=
              costBaseConstructor_params_eq_map_of_mem_wrappedLabelsFor
                plan rule membership labelSupported
            have targetArguments :
                WellSorted.ArgumentsHaveTypes plan.generatedLanguage
                  (free.map
                    (CostStaticColor.base.symbolsOf theory))
                  (bound.map
                    (mapTypeExpr
                      (CostStaticColor.base.symbolsOf theory)))
                  (arguments.map
                    (mapPattern
                      (CostStaticColor.base.symbolsOf theory)))
                  (costBaseConstructor cut rule).params := by
              simpa only [parameterEquality, CostStaticColor.symbolsOf] using
                mappedArguments
            have targetNotBare :
                ¬ WellSorted.UsesBareCollection
                  (costBaseConstructor cut rule) := by
              intro targetBare
              exact notBare
                ((usesBareCollection_costBaseConstructor_iff cut rule).mp
                  targetBare)
            simpa [mapPattern, CostStaticColor.symbolsOf,
              costBaseConstructor, costBaseStaticSymbols,
              costBasePresentationSymbols, mapTypeExpr] using
              (WellSorted.HasType.constructor
                (plan.costBaseConstructor_mem_generated rule membership)
                targetNotBare targetArguments)
        | wrapped =>
            have mappedArguments :=
              argumentsTyped.mapCostStaticGenerated plan .wrapped
            have parameterMapEquality :
                rule.params.map
                    (mapTermParam (costWrappedStaticSymbols theory)) =
                  rule.params.map
                    (mapParameterType
                      (costWrappedTypeExpr
                        theory.presentation.interactingSort.1.name)) := by
              apply List.map_congr_left
              intro parameter _membership
              exact mapTermParam_costWrappedStaticSymbolsFor theory parameter
            have targetArguments :
                WellSorted.ArgumentsHaveTypes plan.generatedLanguage
                  (free.map
                    (CostStaticColor.wrapped.symbolsOf theory))
                  (bound.map
                    (mapTypeExpr
                      (CostStaticColor.wrapped.symbolsOf theory)))
                  (arguments.map
                    (mapPattern
                      (CostStaticColor.wrapped.symbolsOf theory)))
                  (costWrappedConstructor (theory := theory) rule).params := by
              simpa only [costWrappedConstructor,
                CostStaticColor.symbolsOf, parameterMapEquality] using
                mappedArguments
            have targetNotBare :
                ¬ WellSorted.UsesBareCollection
                  (costWrappedConstructor (theory := theory) rule) := by
              intro targetBare
              exact notBare
                ((usesBareCollection_costWrappedConstructor_iff
                  (theory := theory) rule).mp targetBare)
            simpa [mapPattern, CostStaticColor.symbolsOf,
              costWrappedStaticSymbols, costWrappedConstructor, mapTypeExpr,
              costWrappedTypeExpr] using
              (WellSorted.HasType.constructor
                (plan.costWrappedConstructor_mem_generated authored
                  wrappedConstructor)
                targetNotBare targetArguments)
    | @lambda bound binder body domain codomain bodyTyped =>
        have mappedBody := bodyTyped.mapCostStaticGenerated plan color
        simpa [mapPattern, mapTypeExpr] using
          WellSorted.HasType.lambda mappedBody
    | @multiLambda bound arity binders body domain codomain bodyTyped =>
        have mappedBody := bodyTyped.mapCostStaticGenerated plan color
        have mappedBody' :
            WellSorted.HasType plan.generatedLanguage
              (free.map (color.symbolsOf theory))
              (List.replicate arity
                  (mapTypeExpr (color.symbolsOf theory) domain) ++
                bound.map (mapTypeExpr (color.symbolsOf theory)))
              (mapPattern (color.symbolsOf theory) body)
              (mapTypeExpr (color.symbolsOf theory) codomain) := by
          simpa [List.map_append, List.map_replicate] using mappedBody
        simpa [mapPattern, mapTypeExpr] using
          WellSorted.HasType.multiLambda mappedBody'
    | @subst bound body replacement domain codomain bodyTyped replacementTyped =>
        have mappedBody :=
          bodyTyped.mapCostStaticGenerated plan color
        have mappedReplacement :=
          replacementTyped.mapCostStaticGenerated plan color
        simpa [mapPattern] using
          WellSorted.HasType.subst mappedBody mappedReplacement
    | @collection bound collectionType elements rest elementType elementsTyped =>
        have mappedElements :=
          elementsTyped.mapCostStaticGenerated plan color
        simpa [mapPattern, mapTypeExpr] using
          (WellSorted.HasType.collection (rest := rest) mappedElements)
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType labelSupported membership parameterShape
        elementsTyped =>
        let authored : AuthoredConstructor theory.presentation.presentation :=
          ⟨rule, membership⟩
        have wrappedConstructor : authored ∈ plan.wrappedConstructors :=
          (plan.mem_wrappedLabels_iff authored).mp labelSupported
        cases color with
        | base =>
            have mappedElements :=
              elementsTyped.mapCostStaticGenerated plan .base
            have parameterEquality :=
              costBaseConstructor_params_eq_map_of_mem_wrappedLabelsFor
                plan rule membership labelSupported
            have targetShape :
                (costBaseConstructor cut rule).params =
                  [.simple parameterName
                    (.collection collectionType
                      (mapTypeExpr
                        (CostStaticColor.base.symbolsOf theory)
                        elementType))] := by
              simp [parameterEquality, parameterShape,
                mapTermParam_costBaseStaticSymbols,
                CostStaticColor.symbolsOf, mapParameterType,
                costBaseTypeExpr]
            simpa [mapPattern, CostStaticColor.symbolsOf,
              costBaseConstructor, costBaseStaticSymbols,
              costBasePresentationSymbols, mapTypeExpr] using
              (WellSorted.HasType.collectionConstructor
                (plan.costBaseConstructor_mem_generated rule membership)
                targetShape mappedElements)
        | wrapped =>
            have mappedElements :=
              elementsTyped.mapCostStaticGenerated plan .wrapped
            have targetShape :
                (costWrappedConstructor (theory := theory) rule).params =
                  [.simple parameterName
                    (.collection collectionType
                      (mapTypeExpr
                        (CostStaticColor.wrapped.symbolsOf theory)
                        elementType))] := by
              simp [costWrappedConstructor, parameterShape,
                CostStaticColor.symbolsOf, mapParameterType,
                costWrappedTypeExpr]
            simpa [mapPattern, CostStaticColor.symbolsOf,
              costWrappedStaticSymbols, costWrappedConstructor, mapTypeExpr,
              costWrappedTypeExpr] using
              (WellSorted.HasType.collectionConstructor
                (plan.costWrappedConstructor_mem_generated authored
                  wrappedConstructor)
                targetShape mappedElements)

  /-- Ordered-argument companion to non-circular generated transport. -/
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
        (parameters.map (mapTermParam (color.symbolsOf theory))) := by
    cases typed with
    | nil => exact .nil
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped =>
        have mappedParameterType :
            WellSorted.parameterType?
                (mapTermParam (color.symbolsOf theory) parameter) =
              some (mapTypeExpr (color.symbolsOf theory) expected) := by
          rw [WellSorted.parameterType?_mapTermParam, parameterType]
          rfl
        exact .cons
          ((WellSorted.matchesParameterRepresentation_map_iff
            (color.symbolsOf theory) parameter argument).2 representation)
          mappedParameterType
          (argumentTyped.mapCostStaticGenerated plan color)
          (argumentsTyped.mapCostStaticGenerated plan color)

  /-- Homogeneous-element companion to non-circular generated transport. -/
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
        (mapTypeExpr (color.symbolsOf theory) elementType) := by
    cases typed with
    | nil => exact .nil _ _
    | cons elementTyped elementsTyped =>
        exact .cons
          (elementTyped.mapCostStaticGenerated plan color)
          (elementsTyped.mapCostStaticGenerated plan color)
end

mutual
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
        (mapTypeExpr (color.symbols source) type) := by
    cases typed with
    | @bvar bound index type lookup =>
        have mappedLookup :
            (bound.map (mapTypeExpr (color.symbols source)))[index]? =
              some (mapTypeExpr (color.symbols source) type) := by
          simpa using congrArg
            (Option.map (mapTypeExpr (color.symbols source))) lookup
        simpa [mapPattern] using
          (WellSorted.HasType.bvar
            (free := free.map (color.symbols source)) mappedLookup)
    | @fvar bound name type lookup =>
        have mappedLookup :
            (free.map (color.symbols source)) name =
              some (mapTypeExpr (color.symbols source) type) := by
          simp [WellSorted.FreeTypeContext.map, lookup]
        simpa [mapPattern] using
          (WellSorted.HasType.fvar
            (bound := bound.map (mapTypeExpr (color.symbols source)))
            mappedLookup)
    | @constructor bound rule arguments labelSupported membership notBare
        argumentsTyped =>
        let authored : AuthoredConstructor
            source.theory.presentation.presentation := ⟨rule, membership⟩
        have wrappedConstructor : authored ∈
            source.continuationRetyping.wrappedConstructors :=
          (source.continuationRetyping.mem_wrappedLabels_iff authored).mp
            labelSupported
        cases color with
        | base =>
            have mappedArguments :=
              argumentsTyped.mapCostStatic source .base
            have parameterEquality :=
              costBaseConstructor_params_eq_map_of_mem_wrappedLabels source
                rule membership labelSupported
            have targetArguments :
                WellSorted.ArgumentsHaveTypes source.costWholeLanguage
                  (free.map (CostStaticColor.base.symbols source))
                  (bound.map
                    (mapTypeExpr (CostStaticColor.base.symbols source)))
                  (arguments.map
                    (mapPattern (CostStaticColor.base.symbols source)))
                  (costBaseConstructor source.cut rule).params := by
              simpa only [parameterEquality, CostStaticColor.symbols] using
                mappedArguments
            have targetNotBare :
                ¬ WellSorted.UsesBareCollection
                  (costBaseConstructor source.cut rule) := by
              intro targetBare
              exact notBare
                ((usesBareCollection_costBaseConstructor_iff source.cut rule).mp
                  targetBare)
            simpa [mapPattern, CostStaticColor.symbols, costBaseConstructor,
              costBaseStaticSymbols, costBasePresentationSymbols,
              mapTypeExpr] using
              (WellSorted.HasType.constructor
                (source.costBaseConstructor_mem_costWhole rule membership)
                targetNotBare targetArguments)
        | wrapped =>
            have mappedArguments :=
              argumentsTyped.mapCostStatic source .wrapped
            have parameterMapEquality :
                rule.params.map
                    (mapTermParam (costWrappedStaticSymbols source.theory)) =
                  rule.params.map
                    (mapParameterType
                      (costWrappedTypeExpr
                        source.theory.presentation.interactingSort.1.name)) := by
              apply List.map_congr_left
              intro parameter _membership
              exact mapTermParam_costWrappedStaticSymbols source parameter
            have targetArguments :
                WellSorted.ArgumentsHaveTypes source.costWholeLanguage
                  (free.map (CostStaticColor.wrapped.symbols source))
                  (bound.map
                    (mapTypeExpr (CostStaticColor.wrapped.symbols source)))
                  (arguments.map
                    (mapPattern (CostStaticColor.wrapped.symbols source)))
                  (costWrappedConstructor
                    (theory := source.theory) rule).params := by
              simpa only [costWrappedConstructor, CostStaticColor.symbols,
                parameterMapEquality] using mappedArguments
            have targetNotBare :
                ¬ WellSorted.UsesBareCollection
                  (costWrappedConstructor (theory := source.theory) rule) := by
              intro targetBare
              exact notBare
                ((usesBareCollection_costWrappedConstructor_iff
                  (theory := source.theory) rule).mp targetBare)
            simpa [mapPattern, CostStaticColor.symbols,
              costWrappedStaticSymbols, costWrappedConstructor, mapTypeExpr,
              costWrappedTypeExpr] using
              (WellSorted.HasType.constructor
                (source.costWrappedConstructor_mem_costWhole authored
                  wrappedConstructor)
                targetNotBare targetArguments)
    | @lambda bound binder body domain codomain bodyTyped =>
        have mappedBody := bodyTyped.mapCostStatic source color
        simpa [mapPattern, mapTypeExpr] using
          WellSorted.HasType.lambda mappedBody
    | @multiLambda bound arity binders body domain codomain bodyTyped =>
        have mappedBody := bodyTyped.mapCostStatic source color
        have mappedBody' :
            WellSorted.HasType source.costWholeLanguage
              (free.map (color.symbols source))
              (List.replicate arity
                  (mapTypeExpr (color.symbols source) domain) ++
                bound.map (mapTypeExpr (color.symbols source)))
              (mapPattern (color.symbols source) body)
              (mapTypeExpr (color.symbols source) codomain) := by
          simpa [List.map_append, List.map_replicate] using mappedBody
        simpa [mapPattern, mapTypeExpr] using
          WellSorted.HasType.multiLambda mappedBody'
    | @subst bound body replacement domain codomain bodyTyped replacementTyped =>
        have mappedBody := bodyTyped.mapCostStatic source color
        have mappedReplacement :=
          replacementTyped.mapCostStatic source color
        simpa [mapPattern] using
          WellSorted.HasType.subst mappedBody mappedReplacement
    | @collection bound collectionType elements rest elementType elementsTyped =>
        have mappedElements :=
          elementsTyped.mapCostStatic source color
        simpa [mapPattern, mapTypeExpr] using
          (WellSorted.HasType.collection (rest := rest) mappedElements)
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType labelSupported membership parameterShape
        elementsTyped =>
        let authored : AuthoredConstructor
            source.theory.presentation.presentation := ⟨rule, membership⟩
        have wrappedConstructor : authored ∈
            source.continuationRetyping.wrappedConstructors :=
          (source.continuationRetyping.mem_wrappedLabels_iff authored).mp
            labelSupported
        cases color with
        | base =>
            have mappedElements :=
              elementsTyped.mapCostStatic source .base
            have parameterEquality :=
              costBaseConstructor_params_eq_map_of_mem_wrappedLabels source
                rule membership labelSupported
            have targetShape :
                (costBaseConstructor source.cut rule).params =
                  [.simple parameterName
                    (.collection collectionType
              (mapTypeExpr
                        (CostStaticColor.base.symbols source) elementType))] := by
              simp [parameterEquality, parameterShape,
                mapTermParam_costBaseStaticSymbols,
                CostStaticColor.symbols, mapParameterType,
                costBaseTypeExpr]
            simpa [mapPattern, CostStaticColor.symbols, costBaseConstructor,
              costBaseStaticSymbols, costBasePresentationSymbols,
              mapTypeExpr] using
              (WellSorted.HasType.collectionConstructor
                (source.costBaseConstructor_mem_costWhole rule membership)
                targetShape mappedElements)
        | wrapped =>
            have mappedElements :=
              elementsTyped.mapCostStatic source .wrapped
            have targetShape :
                (costWrappedConstructor (theory := source.theory) rule).params =
                  [.simple parameterName
                    (.collection collectionType
                      (mapTypeExpr
                        (CostStaticColor.wrapped.symbols source)
                        elementType))] := by
              simp [costWrappedConstructor, parameterShape,
                CostStaticColor.symbols, mapParameterType,
                costWrappedTypeExpr]
            simpa [mapPattern, CostStaticColor.symbols,
              costWrappedStaticSymbols, costWrappedConstructor, mapTypeExpr,
              costWrappedTypeExpr] using
              (WellSorted.HasType.collectionConstructor
                (source.costWrappedConstructor_mem_costWhole authored
                  wrappedConstructor)
                targetShape mappedElements)

  /-- Ordered constructor arguments transport pointwise with their exact
  constructor-support certificate. -/
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
        (parameters.map (mapTermParam (color.symbols source))) := by
    cases typed with
    | nil => exact .nil
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped =>
        have mappedParameterType :
            WellSorted.parameterType?
                (mapTermParam (color.symbols source) parameter) =
              some (mapTypeExpr (color.symbols source) expected) := by
          rw [WellSorted.parameterType?_mapTermParam, parameterType]
          rfl
        exact .cons
          ((WellSorted.matchesParameterRepresentation_map_iff
            (color.symbols source) parameter argument).2 representation)
          mappedParameterType
          (argumentTyped.mapCostStatic source color)
          (argumentsTyped.mapCostStatic source color)

  /-- Collection elements transport pointwise with their exact constructor
  support certificate. -/
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
        (mapTypeExpr (color.symbols source) elementType) := by
    cases typed with
    | nil => exact .nil _ _
    | cons elementTyped elementsTyped =>
        exact .cons
          (elementTyped.mapCostStatic source color)
          (elementsTyped.mapCostStatic source color)
end

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

mutual
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
          support available := by
    cases safe with
    | @bvar bound index type lookup available _binderImage =>
        have mappedLookup :
            (bound.map (mapTypeExpr (color.symbols source)))[index]? =
              some (mapTypeExpr (color.symbols source) type) := by
          simpa using congrArg
            (Option.map (mapTypeExpr (color.symbols source))) lookup
        let targetTyped : WellSorted.HasType source.costWholeLanguage
            (free.map (color.symbols source))
            (bound.map (mapTypeExpr (color.symbols source)))
            (.bvar index) (mapTypeExpr (color.symbols source) type) :=
          WellSorted.HasType.bvar mappedLookup
        have targetSafe : targetTyped.ReflectiveSupportSafeAt
            source.costWholeReflectionProfile support available :=
          .bvar mappedLookup _
        simp only [mapPattern]
        exact ⟨targetTyped, targetSafe⟩
    | @fvar bound name type lookup available _binderImage shape =>
        have mappedLookup :
            (free.map (color.symbols source)) name =
              some (mapTypeExpr (color.symbols source) type) := by
          unfold WellSorted.FreeTypeContext.map
          rw [lookup]
          rfl
        let targetTyped := WellSorted.HasType.fvar
          (language := source.costWholeLanguage)
          (bound := bound.map (mapTypeExpr (color.symbols source)))
          mappedLookup
        simp only [mapPattern]
        refine ⟨targetTyped, .fvar mappedLookup _ ?_⟩
        exact shape
    | @constructorQuote bound rule arguments membership notBare argumentsTyped
        available _binderImage quoted argumentsSafe =>
        obtain ⟨mappedArguments, mappedArgumentsSafe⟩ :=
          argumentsSafe.mapCostStatic (bound := bound) source color supported.2
        have labelSupported :
            rule.label ∈ source.continuationRetyping.wrappedLabels :=
          supported.1
        cases color with
        | base =>
            have parameterEquality :=
              costBaseConstructor_params_eq_map_of_mem_wrappedLabels source
                rule membership labelSupported
            have targetArguments :
                WellSorted.ArgumentsHaveTypes source.costWholeLanguage
                  (free.map (CostStaticColor.base.symbols source))
                  (bound.map
                    (mapTypeExpr (CostStaticColor.base.symbols source)))
                  (arguments.map
                    (mapPattern (CostStaticColor.base.symbols source)))
                  (costBaseConstructor source.cut rule).params := by
              simpa only [parameterEquality, CostStaticColor.symbols] using
                mappedArguments
            have targetArgumentsSafe :
                targetArguments.ReflectiveSupportSafeAt
                  source.costWholeReflectionProfile support [] := by
              have mappedArgumentsSafe' :
                  targetArguments.ReflectiveSupportSafeAt
                    source.costWholeReflectionProfile support [] := by
                simpa only [parameterEquality, CostStaticColor.symbols,
                  List.map_nil] using
                  mappedArgumentsSafe
              exact mappedArgumentsSafe'
            have targetNotBare :
                ¬ WellSorted.UsesBareCollection
                  (costBaseConstructor source.cut rule) := by
              intro targetBare
              exact notBare
                ((usesBareCollection_costBaseConstructor_iff source.cut rule).mp
                  targetBare)
            have targetQuoted :
                ReflectiveContextSupport.isQuoteConstructor
                    source.costWholeReflectionProfile
                    ((CostStaticColor.base.symbols source).constructor
                      rule.label) = true := by
              rw [reflectiveIsQuoteConstructor_mapCostStatic]
              exact quoted
            let targetTyped := WellSorted.HasType.constructor
              (source.costBaseConstructor_mem_costWhole rule membership)
              targetNotBare targetArguments
            have targetSafe : targetTyped.ReflectiveSupportSafeAt
                source.costWholeReflectionProfile support available :=
              WellSorted.HasType.ReflectiveSupportSafeAt.constructorQuote
                (membership :=
                  source.costBaseConstructor_mem_costWhole rule membership)
                (notBare := targetNotBare)
                (argumentsTyped := targetArguments)
                targetQuoted targetArgumentsSafe
            simpa [targetTyped, mapPattern, CostStaticColor.symbols,
              costBaseConstructor, costBaseStaticSymbols,
              costBasePresentationSymbols, mapTypeExpr] using
                Exists.intro targetTyped targetSafe
        | wrapped =>
            let authored : AuthoredConstructor
                source.theory.presentation.presentation := ⟨rule, membership⟩
            have wrappedConstructor : authored ∈
                source.continuationRetyping.wrappedConstructors :=
              (source.continuationRetyping.mem_wrappedLabels_iff authored).mp
                labelSupported
            have parameterMapEquality :
                rule.params.map
                    (mapTermParam (costWrappedStaticSymbols source.theory)) =
                  rule.params.map
                    (mapParameterType
                      (costWrappedTypeExpr
                        source.theory.presentation.interactingSort.1.name)) := by
              apply List.map_congr_left
              intro parameter _membership
              exact mapTermParam_costWrappedStaticSymbols source parameter
            have targetArguments :
                WellSorted.ArgumentsHaveTypes source.costWholeLanguage
                  (free.map (CostStaticColor.wrapped.symbols source))
                  (bound.map
                    (mapTypeExpr (CostStaticColor.wrapped.symbols source)))
                  (arguments.map
                    (mapPattern (CostStaticColor.wrapped.symbols source)))
                  (costWrappedConstructor
                    (theory := source.theory) rule).params := by
              simpa only [costWrappedConstructor, CostStaticColor.symbols,
                parameterMapEquality] using mappedArguments
            have targetArgumentsSafe :
                targetArguments.ReflectiveSupportSafeAt
                  source.costWholeReflectionProfile support [] := by
              have mappedArgumentsSafe' :
                  targetArguments.ReflectiveSupportSafeAt
                    source.costWholeReflectionProfile support [] := by
                simpa only [costWrappedConstructor, CostStaticColor.symbols,
                  parameterMapEquality, List.map_nil] using
                  mappedArgumentsSafe
              exact mappedArgumentsSafe'
            have targetNotBare :
                ¬ WellSorted.UsesBareCollection
                  (costWrappedConstructor (theory := source.theory) rule) := by
              intro targetBare
              exact notBare
                ((usesBareCollection_costWrappedConstructor_iff
                  (theory := source.theory) rule).mp targetBare)
            have targetQuoted :
                ReflectiveContextSupport.isQuoteConstructor
                    source.costWholeReflectionProfile
                    ((CostStaticColor.wrapped.symbols source).constructor
                      rule.label) = true := by
              rw [reflectiveIsQuoteConstructor_mapCostStatic]
              exact quoted
            let targetTyped := WellSorted.HasType.constructor
              (source.costWrappedConstructor_mem_costWhole authored
                wrappedConstructor)
              targetNotBare targetArguments
            have targetSafe : targetTyped.ReflectiveSupportSafeAt
                source.costWholeReflectionProfile support available :=
              WellSorted.HasType.ReflectiveSupportSafeAt.constructorQuote
                (membership :=
                  source.costWrappedConstructor_mem_costWhole authored
                    wrappedConstructor)
                (notBare := targetNotBare)
                (argumentsTyped := targetArguments)
                targetQuoted targetArgumentsSafe
            simpa [targetTyped, mapPattern, CostStaticColor.symbols,
              costWrappedConstructor, costWrappedStaticSymbols,
              mapTypeExpr, costWrappedTypeExpr] using
                Exists.intro targetTyped targetSafe
    | @constructorOrdinary bound rule arguments membership notBare
        argumentsTyped available _binderImage ordinary argumentsSafe =>
        obtain ⟨mappedArguments, mappedArgumentsSafe⟩ :=
          argumentsSafe.mapCostStatic (bound := bound) source color supported.2
        have labelSupported :
            rule.label ∈ source.continuationRetyping.wrappedLabels :=
          supported.1
        cases color with
        | base =>
            have parameterEquality :=
              costBaseConstructor_params_eq_map_of_mem_wrappedLabels source
                rule membership labelSupported
            have targetArguments :
                WellSorted.ArgumentsHaveTypes source.costWholeLanguage
                  (free.map (CostStaticColor.base.symbols source))
                  (bound.map
                    (mapTypeExpr (CostStaticColor.base.symbols source)))
                  (arguments.map
                    (mapPattern (CostStaticColor.base.symbols source)))
                  (costBaseConstructor source.cut rule).params := by
              simpa only [parameterEquality, CostStaticColor.symbols] using
                mappedArguments
            have targetArgumentsSafe :
                targetArguments.ReflectiveSupportSafeAt
                  source.costWholeReflectionProfile support available := by
              have mappedArgumentsSafe' :
                  targetArguments.ReflectiveSupportSafeAt
                    source.costWholeReflectionProfile support available := by
                simpa only [parameterEquality, CostStaticColor.symbols] using
                  mappedArgumentsSafe
              exact mappedArgumentsSafe'
            have targetNotBare :
                ¬ WellSorted.UsesBareCollection
                  (costBaseConstructor source.cut rule) := by
              intro targetBare
              exact notBare
                ((usesBareCollection_costBaseConstructor_iff source.cut rule).mp
                  targetBare)
            have targetOrdinary :
                ReflectiveContextSupport.isQuoteConstructor
                    source.costWholeReflectionProfile
                    ((CostStaticColor.base.symbols source).constructor
                      rule.label) = false := by
              rw [reflectiveIsQuoteConstructor_mapCostStatic]
              exact ordinary
            let targetTyped := WellSorted.HasType.constructor
              (source.costBaseConstructor_mem_costWhole rule membership)
              targetNotBare targetArguments
            have targetSafe : targetTyped.ReflectiveSupportSafeAt
                source.costWholeReflectionProfile support available :=
              WellSorted.HasType.ReflectiveSupportSafeAt.constructorOrdinary
                (membership :=
                  source.costBaseConstructor_mem_costWhole rule membership)
                (notBare := targetNotBare)
                (argumentsTyped := targetArguments)
                targetOrdinary targetArgumentsSafe
            simpa [targetTyped, mapPattern, CostStaticColor.symbols,
              costBaseConstructor, costBaseStaticSymbols,
              costBasePresentationSymbols, mapTypeExpr] using
                Exists.intro targetTyped targetSafe
        | wrapped =>
            let authored : AuthoredConstructor
                source.theory.presentation.presentation := ⟨rule, membership⟩
            have wrappedConstructor : authored ∈
                source.continuationRetyping.wrappedConstructors :=
              (source.continuationRetyping.mem_wrappedLabels_iff authored).mp
                labelSupported
            have parameterMapEquality :
                rule.params.map
                    (mapTermParam (costWrappedStaticSymbols source.theory)) =
                  rule.params.map
                    (mapParameterType
                      (costWrappedTypeExpr
                        source.theory.presentation.interactingSort.1.name)) := by
              apply List.map_congr_left
              intro parameter _membership
              exact mapTermParam_costWrappedStaticSymbols source parameter
            have targetArguments :
                WellSorted.ArgumentsHaveTypes source.costWholeLanguage
                  (free.map (CostStaticColor.wrapped.symbols source))
                  (bound.map
                    (mapTypeExpr (CostStaticColor.wrapped.symbols source)))
                  (arguments.map
                    (mapPattern (CostStaticColor.wrapped.symbols source)))
                  (costWrappedConstructor
                    (theory := source.theory) rule).params := by
              simpa only [costWrappedConstructor, CostStaticColor.symbols,
                parameterMapEquality] using mappedArguments
            have targetArgumentsSafe :
                targetArguments.ReflectiveSupportSafeAt
                  source.costWholeReflectionProfile support available := by
              have mappedArgumentsSafe' :
                  targetArguments.ReflectiveSupportSafeAt
                    source.costWholeReflectionProfile support available := by
                simpa only [costWrappedConstructor, CostStaticColor.symbols,
                  parameterMapEquality] using mappedArgumentsSafe
              exact mappedArgumentsSafe'
            have targetNotBare :
                ¬ WellSorted.UsesBareCollection
                  (costWrappedConstructor (theory := source.theory) rule) := by
              intro targetBare
              exact notBare
                ((usesBareCollection_costWrappedConstructor_iff
                  (theory := source.theory) rule).mp targetBare)
            have targetOrdinary :
                ReflectiveContextSupport.isQuoteConstructor
                    source.costWholeReflectionProfile
                    ((CostStaticColor.wrapped.symbols source).constructor
                      rule.label) = false := by
              rw [reflectiveIsQuoteConstructor_mapCostStatic]
              exact ordinary
            let targetTyped := WellSorted.HasType.constructor
              (source.costWrappedConstructor_mem_costWhole authored
                wrappedConstructor)
              targetNotBare targetArguments
            have targetSafe : targetTyped.ReflectiveSupportSafeAt
                source.costWholeReflectionProfile support available :=
              WellSorted.HasType.ReflectiveSupportSafeAt.constructorOrdinary
                (membership :=
                  source.costWrappedConstructor_mem_costWhole authored
                    wrappedConstructor)
                (notBare := targetNotBare)
                (argumentsTyped := targetArguments)
                targetOrdinary targetArgumentsSafe
            simpa [targetTyped, mapPattern, CostStaticColor.symbols,
              costWrappedConstructor, costWrappedStaticSymbols,
              mapTypeExpr, costWrappedTypeExpr] using
                Exists.intro targetTyped targetSafe
    | @lambda bound binder body domain codomain bodyTyped available
        _binderImage bodySafe =>
        obtain ⟨mappedBody, mappedBodySafe⟩ :=
          bodySafe.mapCostStatic (bound := domain :: bound) source color supported
        have mappedBodySafe' :
            mappedBody.ReflectiveSupportSafeAt
              source.costWholeReflectionProfile support
              (mapTypeExpr (color.symbols source) domain :: available) :=
          mappedBodySafe
        let targetTyped := WellSorted.HasType.lambda
          (binder := binder) mappedBody
        have targetSafe : targetTyped.ReflectiveSupportSafeAt
            source.costWholeReflectionProfile support available :=
          .lambda mappedBodySafe'
        simp only [mapPattern, mapTypeExpr]
        exact ⟨targetTyped, targetSafe⟩
    | @multiLambda bound arity binders body domain codomain bodyTyped available
        _binderImage bodySafe =>
        obtain ⟨mappedBody, mappedBodySafe⟩ :=
          bodySafe.mapCostStatic
            (bound := List.replicate arity domain ++ bound)
            source color supported
        have mappedBody' : WellSorted.HasType source.costWholeLanguage
            (free.map (color.symbols source))
            (List.replicate arity
                (mapTypeExpr (color.symbols source) domain) ++
              bound.map (mapTypeExpr (color.symbols source)))
            (mapPattern (color.symbols source) body)
            (mapTypeExpr (color.symbols source) codomain) := by
          simpa [List.map_append, List.map_replicate] using mappedBody
        have mappedBodySafe' : mappedBody'.ReflectiveSupportSafeAt
            source.costWholeReflectionProfile support
            (List.replicate arity
                (mapTypeExpr (color.symbols source) domain) ++
              available) :=
          by
            simpa [List.map_append, List.map_replicate] using mappedBodySafe
        let targetTyped := WellSorted.HasType.multiLambda
          (binders := binders) mappedBody'
        have targetSafe : targetTyped.ReflectiveSupportSafeAt
            source.costWholeReflectionProfile support available :=
          .multiLambda mappedBodySafe'
        simp only [mapPattern, mapTypeExpr]
        exact ⟨targetTyped, targetSafe⟩
    | @subst bound body replacement domain codomain bodyTyped replacementTyped
        available _binderImage bodySafe replacementSafe =>
        obtain ⟨mappedBody, mappedBodySafe⟩ :=
          bodySafe.mapCostStatic (bound := domain :: bound)
            source color supported.1
        obtain ⟨mappedReplacement, mappedReplacementSafe⟩ :=
          replacementSafe.mapCostStatic (bound := bound)
            source color supported.2
        have mappedBodySafe' :
            mappedBody.ReflectiveSupportSafeAt
              source.costWholeReflectionProfile support
              (mapTypeExpr (color.symbols source) domain :: available) :=
          mappedBodySafe
        let targetTyped := WellSorted.HasType.subst mappedBody mappedReplacement
        have targetSafe : targetTyped.ReflectiveSupportSafeAt
            source.costWholeReflectionProfile support available :=
          .subst mappedBodySafe' mappedReplacementSafe
        simp only [mapPattern]
        exact ⟨targetTyped, targetSafe⟩
    | @collection bound collectionType elements rest elementType elementsTyped
        available _binderImage elementsSafe =>
        obtain ⟨mappedElements, mappedElementsSafe⟩ :=
          elementsSafe.mapCostStatic (bound := bound) source color supported
        let targetTyped := WellSorted.HasType.collection
          (collectionType := collectionType) (rest := rest) mappedElements
        have targetSafe : targetTyped.ReflectiveSupportSafeAt
            source.costWholeReflectionProfile support available :=
          .collection mappedElementsSafe
        simp only [mapPattern, mapPatternList_eq_map, mapTypeExpr]
        exact ⟨targetTyped, targetSafe⟩
    | @collectionConstructor bound rule parameterName collectionType elements
        rest elementType membership parameterShape elementsTyped available
        _binderImage elementsSafe =>
        obtain ⟨mappedElements, mappedElementsSafe⟩ :=
          elementsSafe.mapCostStatic (bound := bound) source color supported
        have bare : WellSorted.UsesBareCollection rule :=
          ⟨parameterName, collectionType, elementType, parameterShape⟩
        have labelSupported :
            rule.label ∈ source.continuationRetyping.wrappedLabels :=
          source.bareCollectionConstructorsWrapped rule membership bare
        cases color with
        | base =>
            have parameterEquality :=
              costBaseConstructor_params_eq_map_of_mem_wrappedLabels source
                rule membership labelSupported
            have targetShape :
                (costBaseConstructor source.cut rule).params =
                  [.simple parameterName
                    (.collection collectionType
                      (mapTypeExpr (CostStaticColor.base.symbols source)
                        elementType))] := by
              simp [parameterEquality, parameterShape,
                mapTermParam_costBaseStaticSymbols, CostStaticColor.symbols,
                mapParameterType, costBaseTypeExpr]
            let targetTyped := WellSorted.HasType.collectionConstructor
              (rest := rest)
              (source.costBaseConstructor_mem_costWhole rule membership)
              targetShape mappedElements
            have targetSafe : targetTyped.ReflectiveSupportSafeAt
                source.costWholeReflectionProfile support available :=
              WellSorted.HasType.ReflectiveSupportSafeAt.collectionConstructor
                (rule := costBaseConstructor source.cut rule)
                (parameterName := parameterName)
                (membership :=
                  source.costBaseConstructor_mem_costWhole rule membership)
                (parameterShape := targetShape)
                (elementsTyped := mappedElements)
                mappedElementsSafe
            simpa [targetTyped, mapPattern, mapPatternList_eq_map,
              CostStaticColor.symbols,
              costBaseConstructor, costBaseStaticSymbols,
              costBasePresentationSymbols, mapTypeExpr] using
                Exists.intro targetTyped targetSafe
        | wrapped =>
            let authored : AuthoredConstructor
                source.theory.presentation.presentation := ⟨rule, membership⟩
            have wrappedConstructor : authored ∈
                source.continuationRetyping.wrappedConstructors :=
              (source.continuationRetyping.mem_wrappedLabels_iff authored).mp
                labelSupported
            have targetShape :
                (costWrappedConstructor (theory := source.theory) rule).params =
                  [.simple parameterName
                    (.collection collectionType
                      (mapTypeExpr (CostStaticColor.wrapped.symbols source)
                        elementType))] := by
              simp [costWrappedConstructor, parameterShape,
                CostStaticColor.symbols, mapParameterType,
                costWrappedTypeExpr]
            let targetTyped := WellSorted.HasType.collectionConstructor
              (rest := rest)
              (source.costWrappedConstructor_mem_costWhole authored
                wrappedConstructor)
              targetShape mappedElements
            have targetSafe : targetTyped.ReflectiveSupportSafeAt
                source.costWholeReflectionProfile support available :=
              WellSorted.HasType.ReflectiveSupportSafeAt.collectionConstructor
                (rule := costWrappedConstructor (theory := source.theory) rule)
                (parameterName := parameterName)
                (membership :=
                  source.costWrappedConstructor_mem_costWhole authored
                    wrappedConstructor)
                (parameterShape := targetShape)
                (elementsTyped := mappedElements)
                mappedElementsSafe
            simpa [targetTyped, mapPattern, mapPatternList_eq_map,
              CostStaticColor.symbols,
              costWrappedConstructor, costWrappedStaticSymbols,
              mapTypeExpr, costWrappedTypeExpr] using
                Exists.intro targetTyped targetSafe

  /-- Argument-spine companion to static reflective-support transport. -/
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
          support available := by
    cases safe with
    | nil =>
        let targetTyped := WellSorted.ArgumentsHaveTypes.nil
          (language := source.costWholeLanguage)
          (free := free.map (color.symbols source))
          (bound := bound.map (mapTypeExpr (color.symbols source)))
        exact ⟨targetTyped, .nil _ _⟩
    | @cons bound argument arguments parameter parameters expected
        representation parameterType argumentTyped argumentsTyped available
        _binderImage argumentSafe argumentsSafe =>
        obtain ⟨mappedArgument, mappedArgumentSafe⟩ :=
          argumentSafe.mapCostStatic (bound := bound) source color supported.1
        obtain ⟨mappedArguments, mappedArgumentsSafe⟩ :=
          argumentsSafe.mapCostStatic (bound := bound) source color supported.2
        have mappedParameterType :
            WellSorted.parameterType?
                (mapTermParam (color.symbols source) parameter) =
              some (mapTypeExpr (color.symbols source) expected) := by
          rw [WellSorted.parameterType?_mapTermParam, parameterType]
          rfl
        have mappedRepresentation :
            WellSorted.MatchesParameterRepresentation
              (mapTermParam (color.symbols source) parameter)
              (mapPattern (color.symbols source) argument) :=
          (WellSorted.matchesParameterRepresentation_map_iff
            (color.symbols source) parameter argument).2 representation
        let targetTyped := WellSorted.ArgumentsHaveTypes.cons
          mappedRepresentation
          mappedParameterType mappedArgument mappedArguments
        have targetSafe : targetTyped.ReflectiveSupportSafeAt
            source.costWholeReflectionProfile support available :=
          WellSorted.ArgumentsHaveTypes.ReflectiveSupportSafeAt.cons
            (representation := mappedRepresentation)
            (parameterType := mappedParameterType)
            (argumentTyped := mappedArgument)
            (argumentsTyped := mappedArguments)
            mappedArgumentSafe mappedArgumentsSafe
        exact ⟨targetTyped, targetSafe⟩

  /-- Collection-spine companion to static reflective-support transport. -/
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
          support available := by
    cases safe with
    | nil =>
        let targetTyped := WellSorted.ElementsHaveType.nil
          (language := source.costWholeLanguage)
          (free := free.map (color.symbols source))
          (bound.map (mapTypeExpr (color.symbols source)))
          (mapTypeExpr (color.symbols source) elementType)
        exact ⟨targetTyped, .nil _ _ _⟩
    | @cons bound element elements elementType elementTyped elementsTyped
        available _binderImage elementSafe elementsSafe =>
        obtain ⟨mappedElement, mappedElementSafe⟩ :=
          elementSafe.mapCostStatic (bound := bound) source color supported.1
        obtain ⟨mappedElements, mappedElementsSafe⟩ :=
          elementsSafe.mapCostStatic (bound := bound) source color supported.2
        let targetTyped := WellSorted.ElementsHaveType.cons
          mappedElement mappedElements
        have targetSafe : targetTyped.ReflectiveSupportSafeAt
            source.costWholeReflectionProfile support available :=
          WellSorted.ElementsHaveType.ReflectiveSupportSafeAt.cons
            (elementTyped := mappedElement)
            (elementsTyped := mappedElements)
            mappedElementSafe mappedElementsSafe
        exact ⟨targetTyped, targetSafe⟩
end


end Mettapedia.GSLT.LanguageDef
