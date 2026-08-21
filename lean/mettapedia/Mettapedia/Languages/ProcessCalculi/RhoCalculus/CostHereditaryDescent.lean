/-
# The rho hereditary-cost descent

The recursive middle of the rho Cost1 development: every colour-static
region plan of rho whose concrete pattern canonicalizes to a drop tower
admits a stopped-state quintuple at the same tower height, with an
authored abstract filling of the same canonical shape (`rhoDescend`).

The theorem is proved together with its supporting structure:

* colour-tag decoding and constructor-role facts
  (`decodeDeclared_{drop,quote,unit}`, `declC_dropNeQuote`);
* the typing-pin chain (typed drop-tower contributors live at
  Name/Proc leaf chains, `rho_dropTower_typed_chain`);
* the abstract tower-over-unit coherence theorem
  (`plan_abstract_iterDropUnit_of_iterDropUnit`), absorbing quote-drop
  pairs one level at a time;
* the sibling-unit machinery (a parallel collapse to a rigid value has
  exactly one rigid contributor; blocks in the spliced contents are
  counted, not elements);
* the boundaryCollection gate: rho has no foreign boundary collections
  at all (`boundaryCollection_choices_absurd`,
  `rho_collectionPlan_isStaticRoot`);
* the active-context length certificate (`elementPlan_activeAt_lenCert`),
  the positional invariant the sibling-unit lift needs.

This file lives under the umbrella on purpose: the descent is the
recursive argument every hereditary-cost apex obligation consumes.
-/

import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryExposureClosure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCrossColorLeafHinge

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryLeafDichotomyProbe

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

theorem decodeDeclared_drop (color : CostStaticColor) :
    decodeDeclaredCostStaticConstructor rhoCIGSLT color
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl).dropConstructor =
      some "PDrop" := by
  cases color <;> decide

theorem decodeDeclared_quote (color : CostStaticColor) :
    decodeDeclaredCostStaticConstructor rhoCIGSLT color
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl).quoteConstructor =
      some "NQuote" := by
  cases color <;> decide

theorem decodeDeclared_unit (color : CostStaticColor) :
    decodeDeclaredCostStaticConstructor rhoCIGSLT color
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).parallelUnitConstructor =
      some "PZero" := by
  cases color <;> decide

theorem rhoDecl_dropConstructor (color : CostStaticColor) :
    (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).dropConstructor =
      (color.symbols rhoCIGSLT).constructor "PDrop" := by
  cases color <;> rfl

theorem auth_dropConstructor :
    rhoReflectivePresentation.toReflectivePresentationDecl.dropConstructor =
      "PDrop" := rfl

theorem auth_unitConstructor :
    rhoReflectivePresentation.toReflectivePresentationDecl.parallelUnitConstructor =
      "PZero" := rfl

theorem rhoDecl_unitConstructor (color : CostStaticColor) :
    (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        ).parallelUnitConstructor =
      (color.symbols rhoCIGSLT).constructor "PZero" := by
  cases color <;> rfl

/-- The base static sort action is the uniform base tag. -/
theorem costStaticColor_symbols_sort_base (t : String) :
    (CostStaticColor.symbols rhoCIGSLT .base).sort t = costBaseSortName t :=
  rfl

/-- The wrapped static sort action wraps the interacting sort and base-tags
everything else. -/
theorem costStaticColor_symbols_sort_wrapped (t : String) :
    (CostStaticColor.symbols rhoCIGSLT .wrapped).sort t =
      (if t = "Proc" then costWrappedSortName else costBaseSortName t) := by
  simp only [CostStaticColor.symbols, costWrappedStaticSymbols,
    rho_interactingSort_name]

theorem mapTypeExpr_cross_base_eq_of_ne_interacting (color : CostStaticColor)
    (t : String) (notInteracting : t ≠ "Proc") :
    mapTypeExpr (color.symbols rhoCIGSLT) (.base t) =
      mapTypeExpr (color.flip.symbols rhoCIGSLT) (.base t) := by
  cases color with
  | base =>
      simp [CostStaticColor.flip, mapTypeExpr, costStaticColor_symbols_sort_base,
        costStaticColor_symbols_sort_wrapped, notInteracting]
  | wrapped =>
      simp [CostStaticColor.flip, mapTypeExpr,
        costStaticColor_symbols_sort_base, costStaticColor_symbols_sort_wrapped,
        notInteracting]

/-- The base sort tag is injective: decoding recovers the payload. -/
theorem costBaseSortName_injective {left right : String}
    (equality : costBaseSortName left = costBaseSortName right) :
    left = right := by
  have decoded := congrArg decodeCostBaseSortName equality
  simpa [decodeCostBaseSortName_encode] using decoded

/-- The wrapped sort never equals a base-tagged sort. -/
theorem costWrappedSortName_ne_costBaseSortName (t : String) :
    costWrappedSortName ≠ costBaseSortName t := by
  intro equality
  have characters := congrArg String.toList equality
  simp [costWrappedSortName, costBaseSortName, costBaseSortTag] at characters

/-- rho's authored drop is a wrapped fragment member. -/
theorem rho_drop_mem_wrappedConstructors :
    (⟨rhoCalc.terms[1], by
        change rhoCalc.terms[1] ∈ rhoCalc.terms
        exact List.getElem_mem (by simp [rhoCalc])⟩ :
      AuthoredConstructor rhoIGSLT.presentation.presentation) ∈
      rhoContinuationRetyping.wrappedConstructors := by
  rw [rhoContinuationRetyping.mem_wrappedConstructors_iff]
  constructor <;> decide

/-- rho's authored quote is a wrapped fragment member. -/
theorem rho_quote_mem_wrappedConstructors :
    (⟨rhoCalc.terms[2], by
        change rhoCalc.terms[2] ∈ rhoCalc.terms
        exact List.getElem_mem (by simp [rhoCalc])⟩ :
      AuthoredConstructor rhoIGSLT.presentation.presentation) ∈
      rhoContinuationRetyping.wrappedConstructors := by
  rw [rhoContinuationRetyping.mem_wrappedConstructors_iff]
  constructor <;> decide

/-- The whole-language rule behind a colour-static drop wire is rho's
authored drop, with the colour image of `Proc` as category. -/
theorem rho_costWhole_rule_category_of_dropWire (color : CostStaticColor)
    {rule : GrammarRule}
    (membership : rule ∈ rhoCIGSLT.costWholeLanguage.terms)
    (labelEq : rule.label = (color.symbols rhoCIGSLT).constructor "PDrop") :
    TypeExpr.base rule.category =
      mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc") := by
  cases color with
  | base =>
      have labelRendered :
          (rhoCIGSLT.materializeDeclaredCostConstructor
            ⟨CostConstructor.base ⟨rhoCalc.terms[1],
                List.getElem_mem (by simp [rhoCalc])⟩, True.intro⟩).label =
            (CostStaticColor.symbols rhoCIGSLT .base).constructor "PDrop" := by
        simp [CIGSLT.materializeDeclaredCostConstructor, costBaseConstructor,
          rhoCalc, CostStaticColor.symbols, costBaseStaticSymbols,
          costBasePresentationSymbols]
      have materialized :=
        CIGSLT.materializeDeclaredCostConstructor_eq_of_mem_of_label rhoCIGSLT
          rule membership _ (labelRendered.trans labelEq.symm)
      subst rule
      simp [CIGSLT.materializeDeclaredCostConstructor, costBaseConstructor,
        rhoCalc, mapTypeExpr, CostStaticColor.symbols, costBaseStaticSymbols,
        costBasePresentationSymbols]
  | wrapped =>
      have labelRendered :
          (rhoCIGSLT.materializeDeclaredCostConstructor
            ⟨CostConstructor.wrapped ⟨rhoCalc.terms[1],
                List.getElem_mem (by simp [rhoCalc])⟩,
              rho_drop_mem_wrappedConstructors⟩).label =
            (CostStaticColor.symbols rhoCIGSLT .wrapped).constructor "PDrop" := by
        simp [CIGSLT.materializeDeclaredCostConstructor, costWrappedConstructor,
          rhoCalc, CostStaticColor.symbols, costWrappedStaticSymbols]
      have materialized :=
        CIGSLT.materializeDeclaredCostConstructor_eq_of_mem_of_label rhoCIGSLT
          rule membership _ (labelRendered.trans labelEq.symm)
      subst rule
      simp [CIGSLT.materializeDeclaredCostConstructor, costWrappedConstructor,
        rhoCalc, mapTypeExpr, CostStaticColor.symbols,
        costWrappedStaticSymbols, rho_interactingSort_name]

/-- The whole-language rule behind a colour-static quote wire is rho's
authored quote, with the colour image of `Name` as category. -/
theorem rho_costWhole_rule_category_of_quoteWire (color : CostStaticColor)
    {rule : GrammarRule}
    (membership : rule ∈ rhoCIGSLT.costWholeLanguage.terms)
    (labelEq : rule.label = (color.symbols rhoCIGSLT).constructor "NQuote") :
    TypeExpr.base rule.category =
      mapTypeExpr (color.symbols rhoCIGSLT) (.base "Name") := by
  cases color with
  | base =>
      have labelRendered :
          (rhoCIGSLT.materializeDeclaredCostConstructor
            ⟨CostConstructor.base ⟨rhoCalc.terms[2],
                List.getElem_mem (by simp [rhoCalc])⟩, True.intro⟩).label =
            (CostStaticColor.symbols rhoCIGSLT .base).constructor "NQuote" := by
        simp [CIGSLT.materializeDeclaredCostConstructor, costBaseConstructor,
          rhoCalc, CostStaticColor.symbols, costBaseStaticSymbols,
          costBasePresentationSymbols]
      have materialized :=
        CIGSLT.materializeDeclaredCostConstructor_eq_of_mem_of_label rhoCIGSLT
          rule membership _ (labelRendered.trans labelEq.symm)
      subst rule
      simp [CIGSLT.materializeDeclaredCostConstructor, costBaseConstructor,
        rhoCalc, mapTypeExpr, CostStaticColor.symbols, costBaseStaticSymbols,
        costBasePresentationSymbols]
  | wrapped =>
      have labelRendered :
          (rhoCIGSLT.materializeDeclaredCostConstructor
            ⟨CostConstructor.wrapped ⟨rhoCalc.terms[2],
                List.getElem_mem (by simp [rhoCalc])⟩,
              rho_quote_mem_wrappedConstructors⟩).label =
            (CostStaticColor.symbols rhoCIGSLT .wrapped).constructor "NQuote" := by
        simp [CIGSLT.materializeDeclaredCostConstructor, costWrappedConstructor,
          rhoCalc, CostStaticColor.symbols, costWrappedStaticSymbols]
      have materialized :=
        CIGSLT.materializeDeclaredCostConstructor_eq_of_mem_of_label rhoCIGSLT
          rule membership _ (labelRendered.trans labelEq.symm)
      subst rule
      simp [CIGSLT.materializeDeclaredCostConstructor, costWrappedConstructor,
        rhoCalc, mapTypeExpr, CostStaticColor.symbols,
        costWrappedStaticSymbols, rho_interactingSort_name]

/-- The interacting sort never coincides across the two colour actions. -/
theorem mapTypeExpr_cross_proc_ne (color : CostStaticColor) (t : String)
    (notInteracting : t ≠ "Proc") :
    mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc") ≠
      mapTypeExpr (color.flip.symbols rhoCIGSLT) (.base t) := by
  cases color with
  | base =>
      simp only [CostStaticColor.flip, mapTypeExpr,
        costStaticColor_symbols_sort_base, costStaticColor_symbols_sort_wrapped]
      rw [if_neg notInteracting] at *
      intro equality
      have inner := TypeExpr.base.inj equality
      exact notInteracting (costBaseSortName_injective inner).symm
  | wrapped =>
      simp only [CostStaticColor.flip, mapTypeExpr,
        costStaticColor_symbols_sort_base, costStaticColor_symbols_sort_wrapped]
      intro equality
      exact costWrappedSortName_ne_costBaseSortName t
        (TypeExpr.base.inj equality)

theorem auth_quoteConstructor :
    rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor =
      "NQuote" := rfl

/-- Colour-tagged constructor names are injective in the authored label. -/
theorem costStaticColor_constructor_inj {color : CostStaticColor}
    {left right : String}
    (equation : (color.symbols rhoCIGSLT).constructor left =
      (color.symbols rhoCIGSLT).constructor right) : left = right := by
  have decoded := congrArg (decodeCostStaticConstructor color) equation
  rw [decodeCostStaticConstructor_symbols, decodeCostStaticConstructor_symbols]
    at decoded
  exact Option.some.inj decoded

/-- A quote over a drop evaporates onto the dropped body, at any body. -/
theorem canonicalize_quote_drop_general (declaration : ReflectivePresentationDecl)
    (dropNeQuote : declaration.dropConstructor ≠ declaration.quoteConstructor)
    (body : Pattern) :
    canonicalize declaration
        (.apply declaration.quoteConstructor
          [.apply declaration.dropConstructor [body]]) =
      canonicalize declaration body := by
  rw [canonicalize_apply_eq_finish, List.map_cons, List.map_nil,
    canonicalize_apply_of_ne_quote declaration dropNeQuote]
  simp [finishNormalizeReflectiveApply]

/-- The descent target is a non-collection application rooted outside this
colour's static namespace.  Callers instantiate this through sort parity:
the partner's canonical value is Name- or Proc-sorted, hence never a hashBag
collection, and its head is foreign to the collapsing side's colour only in
the cross-colour corner the descent serves. -/
def RhoDescendEscape (color : CostStaticColor) (target : Pattern) : Prop :=
  (∀ collectionType elements rest,
      target ≠ .collection collectionType elements rest) ∧
    ∃ wire arguments, target = .apply wire arguments ∧
      decodeDeclaredCostStaticConstructor rhoCIGSLT color wire = none

/-- A pattern that is neither an application nor a collection is never a drop
tower over an escaped target. -/
theorem not_eq_iterDrop_of_escape {color : CostStaticColor} {level : Nat}
    {target pattern : Pattern}
    (escape : RhoDescendEscape color target)
    (notApply : ∀ wire arguments, pattern ≠ .apply wire arguments) :
    pattern ≠
      iterDrop
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) level target := by
  cases level with
  | zero =>
      simp only [iterDrop_zero]
      intro equation
      obtain ⟨_, w, a, shape, _⟩ := escape
      subst shape
      exact notApply w a equation
  | succ level =>
      intro equation
      exact notApply _ _ equation

/-- The opposite colour cannot read this colour's tagging of the interacting
sort.  Flipped instance of `rho_decodeCostStaticTypeExpr_flip_process_eq_none`. -/
theorem rho_decode_flipProcess_eq_none (color : CostStaticColor) :
    decodeCostStaticTypeExpr rhoCIGSLT color
        (.base
          (costStaticReflectivePresentationDecl rhoCIGSLT color.flip
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).processSort) = none := by
  have flipped := rho_decodeCostStaticTypeExpr_flip_process_eq_none color.flip
  simpa [CostStaticColor.flip_flip] using flipped

end Mettapedia.Languages.ProcessCalculi.RhoCalculus

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- **The opposite colour's image of the interacting sort is never this
colour's image of anything.**  This is the whole content of the cross-colour
boundary gate: `Proc` is the one sort the two static fibres tag differently,
so a type written in one colour's namespace can never be read by the other as
the interacting sort. -/
theorem mapTypeExpr_flipProc_ne (color : CostStaticColor) (sourceType : TypeExpr) :
    mapTypeExpr (color.flip.symbols rhoCIGSLT) (.base "Proc") ≠
      mapTypeExpr (color.symbols rhoCIGSLT) sourceType := by
  intro equation
  have decoded := congrArg (decodeCostStaticTypeExpr rhoCIGSLT color) equation
  rw [decodeCostStaticTypeExpr_mapTypeExpr] at decoded
  rw [show mapTypeExpr (color.flip.symbols rhoCIGSLT) (TypeExpr.base "Proc") =
      .base (costStaticReflectivePresentationDecl rhoCIGSLT color.flip
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort from
      by cases color <;> rfl] at decoded
  rw [rho_decode_flipProcess_eq_none] at decoded
  simp at decoded

end Mettapedia.Languages.ProcessCalculi.RhoCalculus

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- **rho declares one bare collection, at `Proc`.**  So an authored-rule
collection choice can only be offered at the interacting sort. -/
theorem rho_bareChoices_eq_nil_of_ne_proc (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext) (targetBound : List TypeExpr)
    (collectionType : CollType) (elements : List Pattern) {sort : String}
    (notProc : sort ≠ "Proc") :
    bareCostStaticCollectionTypingChoices rhoCIGSLT color targetFree targetBound
        collectionType elements (.base sort)
        rhoCIGSLT.theory.presentation.presentation.language.terms = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro rule membership
  have shape : WellSorted.bareCollectionElementType? rule collectionType
      (.base sort) = none := by
    revert membership
    simp only [show rhoCIGSLT.theory.presentation.presentation.language =
      rhoCalc from rfl, rhoCalc, List.mem_cons, List.not_mem_nil, or_false]
    rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp [WellSorted.bareCollectionElementType?, TypeExpr.name, TypeExpr.proc,
        TypeExpr.bag, TypeExpr.funType, TypeExpr.baseType,
        Ne.symm notProc]
  simp [shape]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- Authored bare-collection choices are offered only at a base sort. -/
theorem rho_bareChoices_eq_nil_of_not_base (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext) (targetBound : List TypeExpr)
    (collectionType : CollType) (elements : List Pattern) {expected : TypeExpr}
    (notBase : ∀ sort, expected ≠ .base sort) :
    bareCostStaticCollectionTypingChoices rhoCIGSLT color targetFree targetBound
        collectionType elements expected
        rhoCIGSLT.theory.presentation.presentation.language.terms = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro rule _membership
  have shape : WellSorted.bareCollectionElementType? rule collectionType
      expected = none := by
    cases expected with
    | base sort => exact absurd rfl (notBase sort)
    | arrow _ _ => rfl
    | multiBinder _ => rfl
    | collection _ _ => rfl
  simp [shape]

/-- **The cross-colour boundary-collection gate is empty.**

A cell rejected by its own static colour and accepted by the opposite one, at
a type written in its own colour's namespace, does not exist.  The authored
route needs the interacting sort, which the opposite colour cannot read; the
direct route reads the same element type in both colours, so acceptance
there transfers back. -/
theorem rho_boundaryCollection_choices_absurd (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext) (targetBound : List TypeExpr)
    (collectionType : CollType) (elements : List Pattern) (sourceType : TypeExpr)
    {oppositeChoice : CostCollectionTypingChoice}
    (oppositeSelected : oppositeChoice ∈
      costStaticCollectionTypingChoices rhoCIGSLT color.flip targetFree
        targetBound collectionType elements
        (mapTypeExpr (color.symbols rhoCIGSLT) sourceType))
    (currentRejected :
      costStaticCollectionTypingChoices rhoCIGSLT color targetFree targetBound
        collectionType elements
        (mapTypeExpr (color.symbols rhoCIGSLT) sourceType) = []) :
    False := by
  unfold costStaticCollectionTypingChoices at oppositeSelected currentRejected
  rw [decodeCostStaticTypeExpr_mapTypeExpr] at currentRejected
  cases flipDecoded : decodeCostStaticTypeExpr rhoCIGSLT color.flip
      (mapTypeExpr (color.symbols rhoCIGSLT) sourceType) with
  | none =>
      rw [flipDecoded] at oppositeSelected
      simp at oppositeSelected
  | some flipExpected =>
      rw [flipDecoded] at oppositeSelected
      have back := mapTypeExpr_decodeCostStaticTypeExpr rhoCIGSLT color.flip
        flipDecoded
      cases flipExpected with
      | base sort =>
          dsimp only at oppositeSelected
          by_cases procSort : sort = "Proc"
          · subst procSort
            exact mapTypeExpr_flipProc_ne color sourceType back
          · rw [rho_bareChoices_eq_nil_of_ne_proc color.flip targetFree
              targetBound collectionType elements procSort] at oppositeSelected
            simp at oppositeSelected
      | arrow domain codomain =>
          dsimp only at oppositeSelected
          rw [rho_bareChoices_eq_nil_of_not_base color.flip targetFree
            targetBound collectionType elements (by intro s; simp)]
            at oppositeSelected
          simp at oppositeSelected
      | multiBinder body =>
          dsimp only at oppositeSelected
          rw [rho_bareChoices_eq_nil_of_not_base color.flip targetFree
            targetBound collectionType elements (by intro s; simp)]
            at oppositeSelected
          simp at oppositeSelected
      | collection actual element =>
          dsimp only at oppositeSelected
          rw [rho_bareChoices_eq_nil_of_not_base color.flip targetFree
            targetBound collectionType elements (by intro s; simp)]
            at oppositeSelected
          cases sourceType with
          | base _ => simp [mapTypeExpr] at back
          | arrow _ _ => simp [mapTypeExpr] at back
          | multiBinder _ => simp [mapTypeExpr] at back
          | collection currentActual currentElement =>
              simp only [mapTypeExpr, TypeExpr.collection.injEq] at back
              obtain ⟨actualEq, elementEq⟩ := back
              subst actualEq
              rw [elementEq] at oppositeSelected
              dsimp only at currentRejected
              by_cases fires : actual = collectionType ∧
                  WellSorted.checkElementsHaveType rhoCIGSLT.costWholeLanguage
                    targetFree targetBound elements
                    (mapTypeExpr (color.symbols rhoCIGSLT) currentElement) = true
              · rw [if_pos (by simp [fires.1, fires.2])] at currentRejected
                simp at currentRejected
              · rw [if_neg (by simpa using fires)] at oppositeSelected
                simp at oppositeSelected

end Mettapedia.Languages.ProcessCalculi.RhoCalculus

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- **rho never stops at a collection boundary.**  The foreign-boundary
collection plan is uninhabited, so every rho collection plan is a static
root. -/
theorem rho_collectionPlan_isStaticRoot
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {collectionType : CollType} {elements : List Pattern} {rest : Option String}
    {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer
      (.collection collectionType elements rest) sourceType) :
    plan.isStaticRoot = true := by
  cases plan with
  | collection choice selected children => rfl
  | boundaryCollection currentRejected oppositeChoice oppositeSelected
      certified certifies =>
      exact absurd oppositeSelected (fun selected =>
        rho_boundaryCollection_choices_absurd _ _ _ _ _ _ selected
          currentRejected)

/-- Every member of a typed element list is typed at the list's element
type. -/
theorem hasType_of_mem_elements {language : LanguageDef}
    {free : FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern} {elementType : TypeExpr}
    (typed : WellSorted.ElementsHaveType language free bound elements
      elementType)
    {element : Pattern} (membership : element ∈ elements) :
    WellSorted.HasType language free bound element elementType := by
  induction elements with
  | nil => simp at membership
  | cons head tail inductionHypothesis =>
      cases typed with
      | cons headTyped tailTyped =>
          cases membership with
          | head => exact headTyped
          | tail _ membershipTail =>
              exact inductionHypothesis tailTyped membershipTail

/-- The value chains a typed drop-tower contributor can live at: a leaf
in the three concrete colour-image value forms, optionally wrapped in hash
bags. -/
inductive RhoTypedChainColour (color : CostStaticColor) : TypeExpr → Prop
  | nameLeaf : RhoTypedChainColour color (.base (costBaseSortName "Name"))
  | procLeafBase : RhoTypedChainColour color
      (.base (costBaseSortName "Proc"))
  | procLeafWrapped : RhoTypedChainColour color (.base costWrappedSortName)
  | collection {inner : TypeExpr} :
      RhoTypedChainColour color inner →
      RhoTypedChainColour color (.collection .hashBag inner)

/-- A cost declaration's parallel collection is rho's hash bag. -/
theorem rhoDeclC_parallelCollection_hashBag (color : CostStaticColor) :
    (costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation.toReflectivePresentationDecl
      ).parallelCollection = .hashBag := by
  cases color <;> rfl

/-- Rho's only bare-collection rule is the parallel: any authored rule
using a bare collection has category `Proc`. -/
theorem rho_bare_src_category (src : GrammarRule)
    (membership : src ∈ rhoCalc.terms)
    (bare : WellSorted.UsesBareCollection src) :
    src.category = "Proc" := by
  change src ∈ [rhoCalc.terms[0], rhoCalc.terms[1], rhoCalc.terms[2],
    rhoCalc.terms[3], rhoCalc.terms[4], rhoCalc.terms[5]] at membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  obtain ⟨parameterName, bareCollectionType, bareElementType, bareShape⟩ :=
    bare
  rcases membership with first | second | third | fourth | fifth | sixth <;>
    subst src <;> (simp [rhoCalc] at bareShape ⊢ ;(try
      (exact TypeExpr.noConfusion bareShape.2)))

/-- The whole-language rule behind a bare singleton-collection parameter
has category a `Proc` colour image: rho's parallel, in either copy. -/
theorem bare_whole_rule_category {rule : GrammarRule}
    (membership : rule ∈ rhoCIGSLT.costWholeLanguage.terms)
    (bare : WellSorted.UsesBareCollection rule) :
    rule.category = costBaseSortName "Proc" ∨
      rule.category = costWrappedSortName := by
  have coreMembership : rule ∈ rhoCIGSLT.costCoreLanguage.terms := by
    simpa only [rhoCIGSLT.costWholeLanguage_terms] using membership
  obtain ⟨constructor, materializes⟩ :=
    rhoCIGSLT.exists_declaredCostConstructor_of_mem rule coreMembership
  rw [← materializes] at bare ⊢
  rcases constructor with ⟨shape, declared⟩
  cases shape with
  | base sourceConstructor =>
      have sourceBare : WellSorted.UsesBareCollection sourceConstructor.1 :=
        (usesBareCollection_costBaseConstructor_iff rhoInteractionCut
          sourceConstructor.1).mp bare
      left
      simp [CIGSLT.materializeDeclaredCostConstructor, costBaseConstructor,
        rho_bare_src_category sourceConstructor.1 sourceConstructor.2
          sourceBare]
  | wrapped sourceConstructor =>
      have sourceBare : WellSorted.UsesBareCollection sourceConstructor.1 :=
        (usesBareCollection_costWrappedConstructor_iff sourceConstructor.1
          ).mp bare
      right
      simp [CIGSLT.materializeDeclaredCostConstructor, costWrappedConstructor,
        rho_bare_src_category sourceConstructor.1 sourceConstructor.2
          sourceBare, rho_interactingSort_name]
  | apparatus kind =>
      obtain ⟨parameterName, collectionType, elementType, shape⟩ := bare
      cases kind <;>
        simp [CIGSLT.materializeDeclaredCostConstructor,
          CostApparatusConstructor.grammarRule,
          costSignatureUnitConstructor, costSignatureProductConstructor,
          costSignedConstructor, costTokenStackEmptyConstructor,
          costTokenStackConsConstructor, costFundingConstructor,
          costContactConstructor] at shape

/-- Canonical units filter out of parallel contents. -/
theorem parallelContents_units_eq_nil
    (declaration : ReflectivePresentationDecl)
    (list : List Pattern)
    (units : ∀ b ∈ list, canonicalize declaration b =
      .apply declaration.parallelUnitConstructor []) :
    parallelContents declaration (list.map (canonicalize declaration)) = [] := by
  induction list with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have headUnit := units head List.mem_cons_self
      have tailUnits : ∀ b ∈ tail, canonicalize declaration b =
          .apply declaration.parallelUnitConstructor [] :=
        fun b membership => units b (List.mem_cons_of_mem head membership)
      have tailNil := inductionHypothesis tailUnits
      have headSplice : parallelSplice declaration
          (canonicalize declaration head) =
          [.apply declaration.parallelUnitConstructor []] := by
        rw [headUnit]
        simp [parallelSplice]
      simp only [parallelContents] at tailNil
      simp only [parallelContents, List.map_cons, List.flatMap_cons,
        List.filter_append, headSplice]
      have singletonNil : List.filter (fun pattern =>
          decide (pattern ≠ Pattern.apply declaration.parallelUnitConstructor
            [])) [.apply declaration.parallelUnitConstructor []] = [] := by
        simp []
      rw [singletonNil, List.nil_append]
      exact tailNil

/-- A mid element flanked by canonical units collapses the surrounding
parallel frame to its own value. -/
theorem canonicalize_parallel_units_around
    (declaration : ReflectivePresentationDecl)
    {before after : List Pattern} {mid : Pattern}
    (beforeUnits : ∀ b ∈ before, canonicalize declaration b =
      .apply declaration.parallelUnitConstructor [])
    (afterUnits : ∀ a ∈ after, canonicalize declaration a =
      .apply declaration.parallelUnitConstructor [])
    (midCanonical : canonicalize declaration mid = mid)
    (midNotUnit : mid ≠ .apply declaration.parallelUnitConstructor [])
    (midNotParallel : ∀ nested,
      mid ≠ .collection declaration.parallelCollection nested none) :
    canonicalize declaration
        (.collection declaration.parallelCollection (before ++ mid :: after)
          none) = mid := by
  rw [canonicalize_parallel]
  have contentsNil : ∀ list : List Pattern,
      (∀ b ∈ list, canonicalize declaration b =
        .apply declaration.parallelUnitConstructor []) →
      parallelContents declaration (list.map (canonicalize declaration)) = [] :=
    parallelContents_units_eq_nil declaration
  rw [List.map_append, List.map_cons, midCanonical]
  rw [normalizeParallelElements_eq_sort_parallelContents]
  have midSplice : parallelSplice declaration mid = [mid] := by
    cases mid with
    | collection collectionType elements rest =>
        cases rest with
        | some restName => simp [parallelSplice]
        | none =>
            by_cases parallelEq : collectionType =
                declaration.parallelCollection
            · subst parallelEq
              exact absurd rfl (midNotParallel elements)
            · simp [parallelSplice, parallelEq]
    | _ => simp [parallelSplice]
  have parallelContents_append : ∀ xs ys : List Pattern,
      parallelContents declaration (xs ++ ys) =
        parallelContents declaration xs ++
          parallelContents declaration ys := by
    intro xs ys
    simp only [parallelContents, List.flatMap_append, List.filter_append]
  have midContents : parallelContents declaration [mid] = [mid] := by
    simp only [parallelContents, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, midSplice, List.filter_cons, List.filter_nil]
    simp [midNotUnit]
  have contentsEq : parallelContents declaration
      (before.map (canonicalize declaration) ++
        mid :: after.map (canonicalize declaration)) = [mid] := by
    rw [show before.map (canonicalize declaration) ++
        mid :: after.map (canonicalize declaration) =
      (before.map (canonicalize declaration) ++ [mid]) ++
        after.map (canonicalize declaration) from by simp]
    rw [parallelContents_append, parallelContents_append,
      contentsNil _ beforeUnits, contentsNil _ afterUnits, midContents,
      List.nil_append, List.append_nil]
  rw [contentsEq]
  have sorted :
      Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns [mid] = [mid] :=
    List.perm_singleton.mp (sortPatterns_perm [mid])
  rw [sorted]
  rfl

/-- A canonical element that is neither unit nor parallel has a singleton
splice. -/
theorem parallelSplice_singleton_of_canonical_notUnit_notParallel
    (declaration : ReflectivePresentationDecl) {pattern : Pattern}
    (canonical : canonicalize declaration pattern = pattern)
    (notUnit : pattern ≠ .apply declaration.parallelUnitConstructor [])
    (notParallel : ∀ nested,
      pattern ≠ .collection declaration.parallelCollection nested none) :
    parallelSplice declaration pattern = [pattern] := by
  cases pattern with
  | collection collectionType elements rest =>
      cases rest with
      | some restName => rfl
      | none =>
          by_cases parallelEq : collectionType =
              declaration.parallelCollection
          · exact absurd parallelEq (fun equality =>
              notParallel elements (congrArg
                (fun t => Pattern.collection t elements none) equality))
          · simp [parallelSplice, parallelEq]
  | _ => rfl

/-- The elements of a parallel collapse onto a single value are themselves
units besides a canonical result. -/
theorem parallelCollapse_members_result_or_unit
    (declaration : ReflectivePresentationDecl)
    {elements : List Pattern} {result : Pattern}
    (notUnit : result ≠ .apply declaration.parallelUnitConstructor [])
    (notParallel : ∀ nested,
      result ≠ .collection declaration.parallelCollection nested none)
    (collapsed : canonicalize declaration
        (.collection declaration.parallelCollection elements none) = result)
    {other : Pattern}
    (otherMem : other ∈ elements) :
    canonicalize declaration other = result ∨
      canonicalize declaration other =
        .apply declaration.parallelUnitConstructor [] := by
  have normalizedEq : normalizeParallelElements declaration
      (elements.map (canonicalize declaration)) = [result] := by
    rw [canonicalize_parallel] at collapsed
    cases listEq : normalizeParallelElements declaration
        (elements.map (canonicalize declaration)) with
    | nil =>
        rw [listEq] at collapsed
        simp only [collapseParallel] at collapsed
        exact absurd collapsed.symm notUnit
    | cons first rest =>
        cases rest with
        | nil =>
            rw [listEq] at collapsed
            simp only [collapseParallel] at collapsed
            rw [collapsed]
        | cons second tail =>
            rw [listEq] at collapsed
            exact absurd collapsed.symm (notParallel _)
  rw [normalizeParallelElements_eq_sort_parallelContents] at normalizedEq
  have contentsPerm := sortPatterns_perm
    (parallelContents declaration
      (elements.map (canonicalize declaration)))
  rw [normalizedEq] at contentsPerm
  have contentsEq : parallelContents declaration
      (elements.map (canonicalize declaration)) = [result] :=
    List.perm_singleton.mp contentsPerm.symm
  by_cases otherUnit : canonicalize declaration other =
      .apply declaration.parallelUnitConstructor []
  · exact Or.inr otherUnit
  · left
    have otherIdem : canonicalize declaration (canonicalize declaration
        other) = canonicalize declaration other :=
      canonicalize_idempotent declaration other
    have canonIsCanonical := canonicalize_isCanonical declaration other
    have inContents : canonicalize declaration other ∈
        parallelContents declaration
          (elements.map (canonicalize declaration)) := by
      refine List.mem_filter.mpr ⟨?_, ?_⟩
      · refine List.mem_flatMap.mpr ⟨canonicalize declaration other,
          List.mem_map.mpr (show ∃ x ∈ elements,
                (canonicalize declaration) x =
                  canonicalize declaration other from
            ⟨other, otherMem, rfl⟩), ?_⟩
        cases canonShape : canonicalize declaration other with
        | collection collectionType elementsInner rest =>
            cases rest with
            | some _ =>
                simp [parallelSplice]
            | none =>
                by_cases parallelEq : collectionType =
                    declaration.parallelCollection
                · subst parallelEq
                  exfalso
                  have canonicalForm := canonIsCanonical
                  rw [canonShape] at canonicalForm
                  obtain ⟨innerCanonList, innerProperties⟩ := canonicalForm
                  have innerResp := innerProperties ⟨rfl, rfl⟩
                  obtain ⟨innerLong, _sorted, innerClean⟩ := innerResp
                  obtain ⟨pre, post, elementsSplit⟩ :=
                    List.mem_iff_append.mp otherMem
                  have filterInner : List.filter (fun pattern =>
                      !decide (pattern = Pattern.apply declaration.parallelUnitConstructor [])) elementsInner =
                      elementsInner := by
                    rw [List.filter_eq_self]
                    intro e emem
                    simp [(innerClean e emem).1]
                  rw [elementsSplit, List.map_append, List.map_cons,
                    parallelContents, List.flatMap_append, List.flatMap_cons,
                    List.filter_append, List.filter_append, canonShape]
                    at contentsEq
                  simp [parallelSplice] at contentsEq
                  rw [filterInner] at contentsEq
                  have lengths := congrArg List.length contentsEq
                  simp only [List.length_append, List.length_cons,
                    List.length_nil] at lengths
                  have innerLen : 2 ≤ elementsInner.length := innerLong
                  omega
                · simp [parallelSplice, parallelEq]
        | _ =>
            simp [parallelSplice]
      · exact decide_eq_true otherUnit
    rw [contentsEq, List.mem_singleton] at inContents
    exact inContents

/-- A rigid pattern is its own parallel-contents block: splicing leaves it
alone and unit filtering keeps it. -/
theorem parallelContents_singleton_of_rigid
    (declaration : ReflectivePresentationDecl) {pattern : Pattern}
    (notUnit : pattern ≠ .apply declaration.parallelUnitConstructor [])
    (notParallel : ∀ nested,
      pattern ≠ .collection declaration.parallelCollection nested none) :
    parallelContents declaration [pattern] = [pattern] := by
  unfold parallelContents
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    parallelSplice_eq_singleton_of_not_parallel declaration pattern notParallel]
  simp [notUnit]

/-- **Two rigid contributors cannot survive a singleton collapse.**

Each contributes exactly one block to the spliced contents, so the contents
list has length at least two — but a singleton collapse pins it at one. -/
theorem two_rigid_contributors_absurd
    (declaration : ReflectivePresentationDecl) {result : Pattern}
    (notUnit : result ≠ .apply declaration.parallelUnitConstructor [])
    (notParallel : ∀ nested,
      result ≠ .collection declaration.parallelCollection nested none)
    {before middle after : List Pattern} {first second : Pattern}
    (firstCanon : canonicalize declaration first = result)
    (secondCanon : canonicalize declaration second = result)
    (contentsEq : parallelContents declaration
        ((before ++ first :: middle ++ second :: after).map
          (canonicalize declaration)) = [result]) :
    False := by
  have block := parallelContents_singleton_of_rigid declaration notUnit
    notParallel
  have expand : (before ++ first :: middle ++ second :: after).map
      (canonicalize declaration) =
      before.map (canonicalize declaration) ++ [result] ++
        (middle.map (canonicalize declaration) ++ [result] ++
          after.map (canonicalize declaration)) := by
    simp [firstCanon, secondCanon]
  rw [expand] at contentsEq
  rw [parallelContents_append, parallelContents_append,
    parallelContents_append, parallelContents_append, block] at contentsEq
  have lengths := congrArg List.length contentsEq
  simp only [List.length_append, List.length_cons, List.length_nil] at lengths
  omega

/-- **The residual of GAP B'-a, closed.**

Two distinct elements of a collapsing bare parallel cannot both canonicalize
to the surviving singleton: split the element list at each of them and the
spliced contents carries two blocks where the collapse allows one. -/
theorem sibling_unit_residual
    (declaration : ReflectivePresentationDecl) {result : Pattern}
    (notUnit : result ≠ .apply declaration.parallelUnitConstructor [])
    (notParallel : ∀ nested,
      result ≠ .collection declaration.parallelCollection nested none)
    {elements pre post : List Pattern} {active other : Pattern}
    (elementsSplit : elements = pre ++ other :: post)
    (activeInContexts : active ∈ pre ∨ active ∈ post)
    (activeCanon : canonicalize declaration active = result)
    (otherResult : canonicalize declaration other = result)
    (contentsEq : parallelContents declaration
        (elements.map (canonicalize declaration)) = [result]) :
    False := by
  subst elementsSplit
  rcases activeInContexts with activeInPre | activeInPost
  · obtain ⟨beforeActive, afterActive, preSplit⟩ :=
      List.mem_iff_append.mp activeInPre
    subst preSplit
    refine two_rigid_contributors_absurd declaration notUnit notParallel
      (before := beforeActive) (first := active)
      (middle := afterActive) (second := other) (after := post)
      activeCanon otherResult ?_
    simpa using contentsEq
  · obtain ⟨beforeActive, afterActive, postSplit⟩ :=
      List.mem_iff_append.mp activeInPost
    subst postSplit
    refine two_rigid_contributors_absurd declaration notUnit notParallel
      (before := pre) (first := other)
      (middle := beforeActive) (second := active) (after := afterActive)
      otherResult activeCanon ?_
    simpa using contentsEq

/-- In a parallel collapse onto one value, every sibling of the
contributor is a parallel unit. -/
theorem sibling_unit_of_singleton_collapse
    (declaration : ReflectivePresentationDecl)
    {elements : List Pattern} {result : Pattern}
    (notUnit : result ≠ .apply declaration.parallelUnitConstructor [])
    (notParallel : ∀ nested,
      result ≠ .collection declaration.parallelCollection nested none)
    (collapsed : canonicalize declaration
        (.collection declaration.parallelCollection elements none) = result)
    {active other : Pattern}
    (activeMem : active ∈ elements)
    (activeCanon : canonicalize declaration active = result)
    (otherMem : other ∈ elements)
    (otherNe : other ≠ active) :
    canonicalize declaration other =
      .apply declaration.parallelUnitConstructor [] := by
  rcases parallelCollapse_members_result_or_unit declaration notUnit
      notParallel collapsed otherMem with otherResult | otherUnit
  · -- both active and other canonicalize to result: positional duplicate
    -- contradiction inside the singleton contents.
    exfalso
    obtain ⟨pre, post, elementsSplit⟩ := List.mem_iff_append.mp otherMem
    have normalizedEq : normalizeParallelElements declaration
        (elements.map (canonicalize declaration)) = [result] := by
      rw [canonicalize_parallel] at collapsed
      cases listEq : normalizeParallelElements declaration
          (elements.map (canonicalize declaration)) with
      | nil =>
          rw [listEq] at collapsed
          simp only [collapseParallel] at collapsed
          exact absurd collapsed.symm notUnit
      | cons first rest =>
          cases rest with
          | nil =>
              rw [listEq] at collapsed
              simp only [collapseParallel] at collapsed
              rw [collapsed]
          | cons second tail =>
              rw [listEq] at collapsed
              exact absurd collapsed.symm (notParallel _)
    rw [normalizeParallelElements_eq_sort_parallelContents] at normalizedEq
    have contentsPerm := sortPatterns_perm
      (parallelContents declaration (elements.map (canonicalize declaration)))
    rw [normalizedEq] at contentsPerm
    have contentsEq : parallelContents declaration
        (elements.map (canonicalize declaration)) = [result] :=
      List.perm_singleton.mp contentsPerm.symm
    have activeInContexts : active ∈ pre ∨ active ∈ post := by
      have fullMem : active ∈ pre ++ other :: post := by
        rw [← elementsSplit]
        exact activeMem
      rcases List.mem_append.mp fullMem with preMem | postOrActive
      · exact Or.inl preMem
      · cases postOrActive with
        | head => exact absurd rfl otherNe
        | tail _ postMem => exact Or.inr postMem
    -- GAP B'-a-residual, by length: two rigid contributors force two
    -- blocks into singleton contents (ClaudeGapB.lean, merged).
    exact sibling_unit_residual declaration notUnit notParallel
      elementsSplit activeInContexts activeCanon otherResult contentsEq
  · exact otherUnit

/-- Rho's authored parallel collection is the hash bag. -/
theorem auth_parallelCollection :
    rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection =
      .hashBag := rfl

/-- The unit apply is canonical, at any declaration. -/
theorem isCanonical_unitApply (declaration : ReflectivePresentationDecl) :
    IsCanonical declaration
      (.apply declaration.parallelUnitConstructor []) := by
  unfold IsCanonical IsCanonicalList
  exact ⟨trivial, fun name _ headEq => by simp at headEq⟩

/-- Drop towers over the unit are canonical whenever drop is not quote. -/
theorem isCanonical_iterDropUnit (declaration : ReflectivePresentationDecl)
    (dropNeQuote : declaration.dropConstructor ≠ declaration.quoteConstructor) :
    ∀ level : Nat, IsCanonical declaration
      (iterDrop declaration level
        (.apply declaration.parallelUnitConstructor [])) := by
  intro level
  induction level with
  | zero => exact isCanonical_unitApply declaration
  | succ level inductionHypothesis =>
      simp only [iterDrop]
      unfold IsCanonical IsCanonicalList
      exact ⟨⟨inductionHypothesis, trivial⟩,
        fun name headEq => absurd headEq dropNeQuote⟩

/-- The canonicalizer fixes drop towers over the unit. -/
theorem canonicalize_iterDropUnit (declaration : ReflectivePresentationDecl)
    (dropNeQuote : declaration.dropConstructor ≠ declaration.quoteConstructor)
    (level : Nat) :
    canonicalize declaration
      (iterDrop declaration level
        (.apply declaration.parallelUnitConstructor [])) =
      iterDrop declaration level
        (.apply declaration.parallelUnitConstructor []) :=
  canonicalize_eq_of_isCanonical declaration
    (isCanonical_iterDropUnit declaration dropNeQuote level)

/-- A parallel collapsing to the colour unit has singleton-normalized
contents `[]`: the spliced canonical contents of the elements are empty. -/
theorem contents_nil_of_collapsed_unit
    (declaration : ReflectivePresentationDecl) {elements : List Pattern}
    (collapsed : canonicalize declaration
        (.collection declaration.parallelCollection elements none) =
      .apply declaration.parallelUnitConstructor []) :
    parallelContents declaration (elements.map (canonicalize declaration)) =
      [] := by
  rw [canonicalize_parallel, normalizeParallelElements_eq_sort_parallelContents]
    at collapsed
  cases listEq : Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns (parallelContents declaration
      (elements.map (canonicalize declaration))) with
  | nil =>
      have contentsPerm := sortPatterns_perm (parallelContents declaration
        (elements.map (canonicalize declaration)))
      rw [listEq] at contentsPerm
      exact List.perm_nil.mp contentsPerm.symm
  | cons head tail =>
      cases tail with
      | nil =>
          rw [listEq] at collapsed
          simp only [collapseParallel] at collapsed
          have contentsPerm := sortPatterns_perm (parallelContents declaration
            (elements.map (canonicalize declaration)))
          rw [listEq] at contentsPerm
          have contentsEqOne : parallelContents declaration
              (elements.map (canonicalize declaration)) = [head] :=
            List.perm_singleton.mp contentsPerm.symm
          have headMem : head ∈ parallelContents declaration
              (elements.map (canonicalize declaration)) := by
            rw [contentsEqOne]
            exact List.mem_singleton_self head
          simp only [parallelContents, List.mem_filter, List.mem_flatMap]
            at headMem
          obtain ⟨_, headPass⟩ := headMem
          have headNe : head ≠ .apply declaration.parallelUnitConstructor [] :=
            of_decide_eq_true headPass
          exact absurd collapsed headNe
      | cons second rest =>
          rw [listEq] at collapsed
          exact absurd collapsed.symm (by simp [collapseParallel])

/-- Every element of a parallel collapsing to the colour unit
canonicalizes to the colour unit. -/
theorem all_units_of_collapsed_unit
    (declaration : ReflectivePresentationDecl) {elements : List Pattern}
    (collapsed : canonicalize declaration
        (.collection declaration.parallelCollection elements none) =
      .apply declaration.parallelUnitConstructor []) :
    ∀ e ∈ elements, canonicalize declaration e =
      .apply declaration.parallelUnitConstructor [] := by
  intro e emem
  have contentsNil := contents_nil_of_collapsed_unit declaration collapsed
  by_contra canonNonUnit
  have canonNonParallel : ∀ nested, canonicalize declaration e ≠
      .collection declaration.parallelCollection nested none := by
    intro nested bareEq
    have canonIsCanonical := canonicalize_isCanonical declaration e
    rw [bareEq] at canonIsCanonical
    obtain ⟨_innerCanons, innerProps⟩ := canonIsCanonical
    obtain ⟨innerLong, _sorted, innerClean⟩ := innerProps ⟨rfl, rfl⟩
    obtain ⟨innerFirst, innerFirstMem⟩ : ∃ x, x ∈ nested := by
      cases nested with
      | nil => simp at innerLong
      | cons h t => exact ⟨h, List.mem_cons_self⟩
    have innerNotUnit := (innerClean innerFirst innerFirstMem).1
    have inFlat : innerFirst ∈ (elements.map (canonicalize declaration)).flatMap
        (parallelSplice declaration) := by
      refine List.mem_flatMap.mpr ⟨canonicalize declaration e,
        List.mem_map.mpr ⟨e, emem, rfl⟩, ?_⟩
      rw [bareEq]
      simp only [parallelSplice, beq_self_eq_true, if_true]
      exact innerFirstMem
    have inContents : innerFirst ∈ parallelContents declaration
        (elements.map (canonicalize declaration)) :=
      List.mem_filter.mpr ⟨inFlat, decide_eq_true innerNotUnit⟩
    rw [contentsNil] at inContents
    exact List.not_mem_nil inContents
  have spliceSingleton := parallelSplice_eq_singleton_of_not_parallel
    declaration (canonicalize declaration e) canonNonParallel
  have inFlat : canonicalize declaration e ∈
      (elements.map (canonicalize declaration)).flatMap
      (parallelSplice declaration) := by
    refine List.mem_flatMap.mpr ⟨canonicalize declaration e,
      List.mem_map.mpr ⟨e, emem, rfl⟩, ?_⟩
    rw [spliceSingleton]
    exact List.mem_singleton_self _
  have inContents : canonicalize declaration e ∈ parallelContents declaration
      (elements.map (canonicalize declaration)) :=
    List.mem_filter.mpr ⟨inFlat, decide_eq_true canonNonUnit⟩
  rw [contentsNil] at inContents
  exact List.not_mem_nil inContents

/-- Element-spine abstracts match the element list in length. -/
theorem elementPlan_abstractPatterns_length
    (color : CostStaticColor) {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {collectionType : CollType} {rest : Option String}
    {sourceElementType : TypeExpr} :
    ∀ {before elements : List Pattern}
      (spine : CostStaticElementPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
          elements rest sourceElementType),
      spine.abstractPatterns.length = elements.length
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      simp only [CostStaticElementPlan.abstractPatterns, List.length_cons,
        elementPlan_abstractPatterns_length color tail]

/-- **Indexed reification.**  If the element list has `element` at position
`i`, the spine's abstract list has, at the same position, the abstract of a
plan of `element`. -/
theorem elementSpine_getElem?_abstracts
    (color : CostStaticColor) {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {collectionType : CollType} {rest : Option String}
    {sourceElementType : TypeExpr} :
    ∀ {before elements : List Pattern}
      (spine : CostStaticElementPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
          elements rest sourceElementType)
      (i : Nat) {element : Pattern},
      elements[i]? = some element →
      ∃ ou : OneHoleContext,
        ∃ plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
          targetBound thinning sourceAvailable ou element sourceElementType,
        spine.abstractPatterns[i]? = some plan.abstractPattern
  | _, _, .nil, i, element, ithEq => by
      cases i <;> simp at ithEq
  | _, _, .cons head tail, i, element, ithEq => by
      cases i with
      | zero =>
          rw [List.getElem?_cons_zero] at ithEq
          cases ithEq
          refine ⟨_, head, ?_⟩
          rw [CostStaticElementPlan.abstractPatterns, List.getElem?_cons_zero]
      | succ j =>
          rw [List.getElem?_cons_succ] at ithEq
          obtain ⟨ou, p, position⟩ := elementSpine_getElem?_abstracts
            color tail j ithEq
          refine ⟨ou, p, ?_⟩
          rw [CostStaticElementPlan.abstractPatterns, List.getElem?_cons_succ]
          exact position

/-- The singleton spliced contents of a parallel collapse onto a rigid
result. -/
theorem contents_singleton_of_collapse
    (declaration : ReflectivePresentationDecl)
    {elements : List Pattern} {result : Pattern}
    (notUnit : result ≠ .apply declaration.parallelUnitConstructor [])
    (notParallel : ∀ nested,
      result ≠ .collection declaration.parallelCollection nested none)
    (collapsed : canonicalize declaration
        (.collection declaration.parallelCollection elements none) =
      result) :
    parallelContents declaration (elements.map (canonicalize declaration)) =
      [result] := by
  have normalizedEq : normalizeParallelElements declaration
      (elements.map (canonicalize declaration)) = [result] := by
    rw [canonicalize_parallel] at collapsed
    cases listEq : normalizeParallelElements declaration
        (elements.map (canonicalize declaration)) with
    | nil =>
        rw [listEq] at collapsed
        simp only [collapseParallel] at collapsed
        exact absurd collapsed.symm notUnit
    | cons first rest =>
        cases rest with
        | nil =>
            rw [listEq] at collapsed
            simp only [collapseParallel] at collapsed
            rw [collapsed]
        | cons second tail =>
            rw [listEq] at collapsed
            exact absurd collapsed.symm (notParallel _)
  rw [normalizeParallelElements_eq_sort_parallelContents] at normalizedEq
  have contentsPerm := sortPatterns_perm
    (parallelContents declaration (elements.map (canonicalize declaration)))
  rw [normalizedEq] at contentsPerm
  exact List.perm_singleton.mp contentsPerm.symm

/-- **A collapsed-tower value occurs at most once.**  Positionally: an
element in the members' list around the carrier whose canonical form is
also the result forces two contents blocks against the singleton. -/
theorem collapse_duplicate_value_absurd
    (declaration : ReflectivePresentationDecl)
    {result : Pattern}
    (notUnit : result ≠ .apply declaration.parallelUnitConstructor [])
    (notParallel : ∀ nested,
      result ≠ .collection declaration.parallelCollection nested none)
    {elements : List Pattern} {carrier other : Pattern}
    {contextBefore contextAfter : List Pattern}
    (elementsSplit : elements = contextBefore ++ carrier :: contextAfter)
    (carrierCanon : canonicalize declaration carrier = result)
    (otherPosition : other ∈ contextBefore ∨ other ∈ contextAfter)
    (otherCanon : canonicalize declaration other = result)
    (contentsEq : parallelContents declaration
        (elements.map (canonicalize declaration)) = [result]) :
    False := by
  rcases otherPosition with prefixMem | suffixMem
  · obtain ⟨pre, post, beforeSplit⟩ := List.mem_iff_append.mp prefixMem
    subst beforeSplit
    rw [elementsSplit] at contentsEq
    exact two_rigid_contributors_absurd declaration notUnit notParallel
      (before := pre) (middle := post) (after := contextAfter)
      otherCanon carrierCanon
      (by simpa [List.append_assoc] using contentsEq)
  · obtain ⟨pre, post, afterSplit⟩ := List.mem_iff_append.mp suffixMem
    subst afterSplit
    rw [elementsSplit] at contentsEq
    exact two_rigid_contributors_absurd declaration notUnit notParallel
      (before := contextBefore) (middle := pre) (after := post)
      carrierCanon otherCanon
      (by simpa [List.append_assoc] using contentsEq)

/-- Drop is not quote, at either colour of the colour declarations. -/
theorem declC_dropNeQuote (color : CostStaticColor) :
    (costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation.toReflectivePresentationDecl
      ).dropConstructor ≠
    (costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation.toReflectivePresentationDecl
      ).quoteConstructor := by
  intro headEq
  rw [rhoDecl_dropConstructor, rhoDecl_quoteConstructor] at headEq
  exact absurd (costStaticColor_constructor_inj headEq) (by decide)

/-- Drop is not quote in the authored declaration. -/
theorem auth_dropNeQuote :
    (rhoReflectivePresentation.toReflectivePresentationDecl).dropConstructor ≠
      (rhoReflectivePresentation.toReflectivePresentationDecl
        ).quoteConstructor := by
  rw [auth_dropConstructor, auth_quoteConstructor]
  decide

/-- Transport of canonicalization across a parallel-collection type
equality: the collection constructor only sees the type. -/
theorem canonicalize_collection_ct_transport
    (declaration : ReflectivePresentationDecl) {collectionType : CollType}
    (typeEq : collectionType = declaration.parallelCollection)
    (list : List Pattern) :
    canonicalize declaration (.collection collectionType list none) =
    canonicalize declaration
      (.collection declaration.parallelCollection list none) := by
  subst typeEq
  rfl

/-- **Positional sibling units.**  In a bare parallel collapsing onto a rigid
result, every element outside the contributor's own slot canonicalizes to the
unit — whether or not it is the same pattern as the contributor. -/
theorem sibling_unit_positional
    (declaration : ReflectivePresentationDecl)
    {elements before after : List Pattern} {element other result : Pattern}
    (notUnit : result ≠ .apply declaration.parallelUnitConstructor [])
    (notParallel : ∀ nested,
      result ≠ .collection declaration.parallelCollection nested none)
    (collapsed : canonicalize declaration
        (.collection declaration.parallelCollection elements none) = result)
    (elementsEq : elements = before ++ element :: after)
    (elementCanon : canonicalize declaration element = result)
    (otherSide : other ∈ before ∨ other ∈ after) :
    canonicalize declaration other =
      .apply declaration.parallelUnitConstructor [] := by
  have contentsEq := contents_singleton_of_collapse declaration notUnit
    notParallel collapsed
  have otherMem : other ∈ elements := by
    rw [elementsEq]
    rcases otherSide with inBefore | inAfter
    · exact List.mem_append_left _ inBefore
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ inAfter)
  rcases parallelCollapse_members_result_or_unit declaration notUnit
      notParallel collapsed otherMem with otherResult | otherUnit
  · exfalso
    rcases otherSide with inBefore | inAfter
    · obtain ⟨b1, b2, beforeSplit⟩ := List.mem_iff_append.mp inBefore
      subst elementsEq
      subst beforeSplit
      refine two_rigid_contributors_absurd declaration notUnit
        notParallel (before := b1) (first := other) (middle := b2)
        (second := element) (after := after) otherResult elementCanon ?_
      simpa using contentsEq
    · obtain ⟨a1, a2, afterSplit⟩ := List.mem_iff_append.mp inAfter
      subst elementsEq
      subst afterSplit
      refine two_rigid_contributors_absurd declaration notUnit
        notParallel (before := before) (first := element) (middle := a1)
        (second := other) (after := a2) elementCanon otherResult ?_
      simpa using contentsEq
  · exact otherUnit

/-- A bare parallel collapsing to a rigid result can be split at a surviving
contributor, and every sibling on either side canonicalizes to the unit.

The list itself need not be a singleton: unit siblings are deliberately
retained in this positional formulation. -/
theorem exists_parallel_contributor_with_unit_siblings
    (declaration : ReflectivePresentationDecl)
    {elements : List Pattern} {result : Pattern}
    (notUnit : result ≠ .apply declaration.parallelUnitConstructor [])
    (notParallel : ∀ nested,
      result ≠ .collection declaration.parallelCollection nested none)
    (collapsed : canonicalize declaration
        (.collection declaration.parallelCollection elements none) = result) :
    ∃ before contributor after,
      elements = before ++ contributor :: after ∧
      canonicalize declaration contributor = result ∧
      (∀ sibling ∈ before,
        canonicalize declaration sibling =
          .apply declaration.parallelUnitConstructor []) ∧
      (∀ sibling ∈ after,
        canonicalize declaration sibling =
          .apply declaration.parallelUnitConstructor []) := by
  obtain ⟨contributor, membership, contributorCanonical⟩ :=
    exists_member_of_parallel_collapse declaration collapsed notUnit notParallel
  obtain ⟨before, after, elementsEq⟩ := List.mem_iff_append.mp membership
  refine ⟨before, contributor, after, elementsEq, contributorCanonical, ?_, ?_⟩
  · intro sibling siblingMem
    exact sibling_unit_positional declaration notUnit notParallel collapsed
      elementsEq contributorCanonical (Or.inl siblingMem)
  · intro sibling siblingMem
    exact sibling_unit_positional declaration notUnit notParallel collapsed
      elementsEq contributorCanonical (Or.inr siblingMem)

/-- A single-slot canonical congruence for collections. -/
theorem canonicalize_collection_congr_canonical_slot
    (declaration : ReflectivePresentationDecl)
    (collectionType : CollType) (rest : Option String)
    (before after : List Pattern) {middle middle' : Pattern}
    (slotEq : canonicalize declaration middle =
      canonicalize declaration middle') :
    canonicalize declaration
      (.collection collectionType (before ++ middle :: after) rest) =
    canonicalize declaration
      (.collection collectionType (before ++ middle' :: after) rest) := by
  cases rest with
  | some restName =>
      rw [canonicalize_collection_rest, canonicalize_collection_rest]
      rw [List.map_append, List.map_append, List.map_cons, List.map_cons,
        slotEq]
  | none =>
      by_cases parallelType : collectionType = declaration.parallelCollection
      · rw [parallelType, canonicalize_parallel, canonicalize_parallel]
        simp only [normalizeParallelElements_eq_sort_parallelContents]
        rw [List.map_append, List.map_append, List.map_cons, List.map_cons,
          slotEq]
      · rw [canonicalize_collection_of_ne_parallel _ parallelType,
          canonicalize_collection_of_ne_parallel _ parallelType]
        rw [List.map_append, List.map_append, List.map_cons, List.map_cons,
          slotEq]

/-- **GAP B′-b: abstract tower-over-unit coherence.**  A static plan whose
concrete pattern canonicalizes under the colour declaration to a drop tower
over the colour parallel unit has an authored abstract pattern
canonicalizing under the authored declaration to the same tower height over
the authored parallel unit.  This is the tower generalization that makes
quote–drop chains recurse by absorbing one shell pair at a time. -/
theorem plan_abstract_iterDropUnit_of_iterDropUnit
    (color : CostStaticColor) {targetFree : FreeTypeContext} :
    ∀ (fuel : Nat) {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType)
      (level : Nat),
      sizeOf pattern ≤ fuel →
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        pattern =
      iterDrop
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) level
        (.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).parallelUnitConstructor []) →
      canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
        plan.abstractPattern =
      iterDrop rhoReflectivePresentation.toReflectivePresentationDecl level
        (.apply (rhoReflectivePresentation.toReflectivePresentationDecl
          ).parallelUnitConstructor []) := by
  intro fuel
  induction fuel with
  | zero =>
      intro sourceBound targetBound thinning sourceAvailable outer pattern
        sourceType plan level measure towerCanonical
      exact absurd measure (by cases pattern <;> simp)
  | succ fuel inductionHypothesis =>
      intro sourceBound targetBound thinning sourceAvailable outer pattern
        sourceType plan level measure towerCanonical
      cases plan with
      | bvar sourceIndex lookup correspondence availableScope =>
          cases level <;> simp [canonicalize, iterDrop] at towerCanonical
      | fvar lookup =>
          cases level <;> simp [canonicalize, iterDrop] at towerCanonical
      | lambda bodyPlan =>
          cases level <;> simp [canonicalize, iterDrop] at towerCanonical
      | multiLambda bodyPlan =>
          cases level <;> simp [canonicalize, iterDrop] at towerCanonical
      | boundaryApplication declared rendered outsideCurrent certified
          certifies =>
          rename_i wireName arguments
          have decodedNone := decodeDeclaredCostStaticConstructor_render_of_role_ne
            rhoCIGSLT declared color outsideCurrent
          rw [rendered] at decodedNone
          rw [canonicalize_apply_of_ne_quote _ (by
            intro headEq
            exact not_collapsingRoot_of_boundaryHead declared rendered
              outsideCurrent (Or.inl ⟨arguments, by rw [headEq]⟩))]
            at towerCanonical
          cases level with
          | zero =>
              simp only [iterDrop] at towerCanonical
              have wireEq := (Pattern.apply.inj towerCanonical).1
              rw [wireEq, decodeDeclared_unit] at decodedNone
              exact absurd decodedNone (by simp)
          | succ innerLevel =>
              simp only [iterDrop] at towerCanonical
              have wireEq := (Pattern.apply.inj towerCanonical).1
              rw [wireEq, decodeDeclared_drop] at decodedNone
              exact absurd decodedNone (by simp)
      | @boundaryCollection sourceBound targetBound sourceAvailable thinning
          outer collectionType elements rest sourceType currentRejected
          oppositeChoice oppositeSelected certified certifies =>
          exact absurd oppositeSelected (fun selected =>
            rho_boundaryCollection_choices_absurd color targetFree targetBound
              collectionType elements _ selected currentRejected)
      | collection choice selected children =>
          rename_i collectionType elements rest
          cases rest with
          | some restName =>
              rw [canonicalize_collection_rest] at towerCanonical
              cases level <;> simp [iterDrop] at towerCanonical
          | none =>
              by_cases parallelType : collectionType =
                  (costStaticReflectivePresentationDecl rhoCIGSLT color
                    rhoReflectivePresentation.toReflectivePresentationDecl
                    ).parallelCollection
              · rw [parallelType] at towerCanonical
                subst parallelType
                cases level with
                | zero =>
                    -- all-units lane: every element canonicalizes to the
                    -- colour unit; lift through the spine to abstracts.
                    simp only [iterDrop] at towerCanonical
                    have allUnits := all_units_of_collapsed_unit
                      (costStaticReflectivePresentationDecl rhoCIGSLT color
                        rhoReflectivePresentation.toReflectivePresentationDecl)
                      towerCanonical
                    have abstractsUnits : ∀ b ∈ children.abstractPatterns,
                        canonicalize
                            rhoReflectivePresentation.toReflectivePresentationDecl
                            b =
                          .apply ((rhoReflectivePresentation.toReflectivePresentationDecl)
                            ).parallelUnitConstructor [] := by
                      intro b bmem
                      obtain ⟨i, ib⟩ := List.mem_iff_getElem?.mp bmem
                      obtain ⟨ibound, -⟩ := List.getElem?_eq_some_iff.mp ib
                      have aLen : children.abstractPatterns.length =
                          elements.length :=
                        elementPlan_abstractPatterns_length color children
                      have iLen : i < elements.length := by omega
                      have eAt : elements[i]? = some (getElem elements i iLen) :=
                        List.getElem?_eq_some_iff.mpr ⟨iLen, rfl⟩
                      obtain ⟨ou, p, pAbstract⟩ :=
                        elementSpine_getElem?_abstracts color children i
                          eAt
                      have bEq : b = p.abstractPattern := by
                        have eqTwo := ib.symm.trans pAbstract
                        exact Option.some.inj eqTwo
                      have measureElement : sizeOf (getElem elements i iLen) ≤ fuel := by
                        have shrink := List.sizeOf_lt_of_mem
                          ((List.mem_iff_getElem.mpr ⟨_, iLen, rfl⟩))
                        have spineBound : sizeOf elements < sizeOf
                            (Pattern.collection (costStaticReflectivePresentationDecl
                              rhoCIGSLT color (rhoReflectivePresentation.toReflectivePresentationDecl)).parallelCollection
                              elements none) := by
                          simp_wf
                          omega
                        omega
                      have unitSource := allUnits (getElem elements i iLen)
                        ((List.mem_iff_getElem.mpr ⟨_, iLen, rfl⟩))
                      have lifted := inductionHypothesis p 0 measureElement
                        (by simpa only [iterDrop] using unitSource)
                      rw [bEq]
                      simpa only [iterDrop] using lifted
                    -- finish: the abstract collection collapses to the unit
                    simp only [CostStaticRegionPlan.abstractPattern,
                      Option.map_none]
                    rw [canonicalize_collection_ct_transport
                      rhoReflectivePresentation.toReflectivePresentationDecl
                      ((rhoDeclC_parallelCollection_hashBag color).trans
                        auth_parallelCollection.symm)]
                    rw [canonicalize_parallel]
                    rw [normalizeParallelElements_eq_sort_parallelContents,
                      parallelContents_units_eq_nil
                        rhoReflectivePresentation.toReflectivePresentationDecl
                        _ abstractsUnits]
                    rw [show Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns [] =
                        [] from List.perm_nil.mp (sortPatterns_perm [])]
                    simp [collapseParallel, iterDrop]
                | succ innerLevel =>
                    -- singleton-tower lane: one carrier, units elsewhere
                    simp only [iterDrop] at towerCanonical
                    have notUnit : Pattern.apply
                          (costStaticReflectivePresentationDecl rhoCIGSLT color
                            rhoReflectivePresentation.toReflectivePresentationDecl
                            ).dropConstructor
                          [iterDrop
                            (costStaticReflectivePresentationDecl rhoCIGSLT
                              color
                              (rhoReflectivePresentation.toReflectivePresentationDecl))
                            innerLevel
                            (.apply (costStaticReflectivePresentationDecl
                              rhoCIGSLT color
                              (rhoReflectivePresentation.toReflectivePresentationDecl)
                              ).parallelUnitConstructor [])] ≠
                        .apply (costStaticReflectivePresentationDecl rhoCIGSLT
                          color (rhoReflectivePresentation.toReflectivePresentationDecl)
                          ).parallelUnitConstructor [] := by
                      intro unitEq
                      have wireEq := (Pattern.apply.inj unitEq).1
                      rw [rhoDecl_dropConstructor, rhoDecl_unitConstructor]
                        at wireEq
                      exact absurd (costStaticColor_constructor_inj wireEq)
                        (by decide)
                    have notParallelResult : ∀ nested, Pattern.apply
                          (costStaticReflectivePresentationDecl rhoCIGSLT color
                            rhoReflectivePresentation.toReflectivePresentationDecl
                            ).dropConstructor
                          [iterDrop
                            (costStaticReflectivePresentationDecl rhoCIGSLT
                              color (rhoReflectivePresentation.toReflectivePresentationDecl))
                            innerLevel
                            (.apply (costStaticReflectivePresentationDecl
                              rhoCIGSLT color (rhoReflectivePresentation.toReflectivePresentationDecl)
                              ).parallelUnitConstructor [])] ≠
                        .collection (costStaticReflectivePresentationDecl
                          rhoCIGSLT color (rhoReflectivePresentation.toReflectivePresentationDecl)
                          ).parallelCollection nested none := by
                      intro nested equality
                      exact Pattern.noConfusion equality
                    obtain ⟨carrier, carrierMem, carrierCanon⟩ :=
                      exists_member_of_parallel_collapse _ towerCanonical
                        notUnit notParallelResult
                    obtain ⟨contextBefore, contextAfter, elementsSplit⟩ :=
                      List.mem_iff_append.mp carrierMem
                    have kLen : children.abstractPatterns.length =
                        elements.length :=
                      elementPlan_abstractPatterns_length color children
                    have elementsLenEq : elements.length =
                        contextBefore.length + (contextAfter.length + 1) := by
                      have l := congrArg List.length elementsSplit
                      rw [List.length_append, List.length_cons] at l
                      exact l
                    have kElements : contextBefore.length < elements.length :=
                      by omega
                    have kAbs : contextBefore.length <
                        children.abstractPatterns.length := by omega
                    -- the carrier's own abstract at the carrier position
                    have carrierAt : elements[contextBefore.length]? =
                        some carrier := by
                      rw [elementsSplit,
                        List.getElem?_append_right (by omega)]
                      rw [Nat.sub_self]
                      exact List.getElem?_cons_zero
                    obtain ⟨ouC, pC, pCAbs⟩ :=
                      elementSpine_getElem?_abstracts color children
                        contextBefore.length carrierAt
                    have contentsEq := contents_singleton_of_collapse
                      (costStaticReflectivePresentationDecl rhoCIGSLT color
                        (rhoReflectivePresentation.toReflectivePresentationDecl))
                      notUnit notParallelResult towerCanonical
                    -- sibling pointwise coherence, by global position
                    have siblingUnitAbs : ∀ {j : Nat}
                        (jBound : j < children.abstractPatterns.length)
                        (jNe : j ≠ contextBefore.length),
                        canonicalize
                            (rhoReflectivePresentation.toReflectivePresentationDecl)
                            (getElem children.abstractPatterns j jBound) =
                          .apply ((rhoReflectivePresentation.toReflectivePresentationDecl)
                            ).parallelUnitConstructor [] := by
                      intro j jBound jNe
                      have jElements : j < elements.length := by omega
                      have jAt : elements[j]? = some
                          (getElem elements j jElements) :=
                        List.getElem?_eq_some_iff.mpr ⟨jElements, rfl⟩
                      obtain ⟨ouJ, pJ, pJAbs⟩ :=
                        elementSpine_getElem?_abstracts color children j
                          jAt
                      have jEq : (getElem children.abstractPatterns j jBound) =
                          pJ.abstractPattern :=
                        (List.getElem_eq_iff jBound).mpr pJAbs
                      have ememJ : getElem elements j jElements ∈ elements :=
                        List.mem_iff_getElem.mpr ⟨j, jElements, rfl⟩
                      have measureJ : sizeOf (getElem elements j
                          jElements) ≤ fuel := by
                        have shrink := List.sizeOf_lt_of_mem ememJ
                        have spineBound : sizeOf elements < sizeOf
                            (Pattern.collection
                              (costStaticReflectivePresentationDecl rhoCIGSLT
                                color (rhoReflectivePresentation.toReflectivePresentationDecl)
                                ).parallelCollection elements none) := by
                          simp_wf
                          omega
                        omega
                      have elemCases :=
                        parallelCollapse_members_result_or_unit
                          (costStaticReflectivePresentationDecl rhoCIGSLT
                            color (rhoReflectivePresentation.toReflectivePresentationDecl))
                          notUnit notParallelResult towerCanonical ememJ
                      rcases elemCases with elemTower | elemUnit
                      · exfalso
                        rcases Nat.lt_trichotomy j contextBefore.length with
                          jLt | jEq | jGt
                        · have elemInPrefix : getElem elements j jElements ∈
                              contextBefore := by
                            have elemsAt : elements[j]? =
                                contextBefore[j]? := by
                              rw [elementsSplit]
                              exact List.getElem?_append_left (by omega)
                            have eSome : elements[j]? =
                                some (getElem elements j jElements) :=
                              List.getElem?_eq_some_iff.mpr ⟨jElements, rfl⟩
                            have cBSome : contextBefore[j]? =
                                some (getElem elements j jElements) :=
                              elemsAt ▸ eSome
                            exact List.mem_of_getElem? cBSome
                          exact collapse_duplicate_value_absurd
                            (costStaticReflectivePresentationDecl rhoCIGSLT
                              color (rhoReflectivePresentation.toReflectivePresentationDecl))
                            notUnit notParallelResult elementsSplit
                            carrierCanon (Or.inl elemInPrefix) elemTower
                            contentsEq
                        · exact absurd jEq jNe
                        · have elemInSuffix : getElem elements j jElements ∈
                              contextAfter := by
                            have elemsAt : elements[j]? =
                                contextAfter[j - (contextBefore.length + 1)]? := by
                              rw [elementsSplit]
                              rw [List.getElem?_append_right (by omega)]
                              rw [show j - contextBefore.length =
                                  (j - (contextBefore.length + 1)) + 1 by omega]
                              exact List.getElem?_cons_succ
                            have eSome : elements[j]? =
                                some (getElem elements j jElements) :=
                              List.getElem?_eq_some_iff.mpr ⟨jElements, rfl⟩
                            have cASome : contextAfter[
                                j - (contextBefore.length + 1)]? =
                                some (getElem elements j jElements) :=
                              elemsAt ▸ eSome
                            exact List.mem_of_getElem? cASome
                          exact collapse_duplicate_value_absurd
                            (costStaticReflectivePresentationDecl rhoCIGSLT
                              color (rhoReflectivePresentation.toReflectivePresentationDecl))
                            notUnit notParallelResult elementsSplit
                            carrierCanon (Or.inr elemInSuffix) elemTower
                            contentsEq
                      · rw [jEq]
                        have lifted := inductionHypothesis pJ 0 measureJ
                          (by simpa only [iterDrop] using elemUnit)
                        simpa only [iterDrop] using lifted
                    -- carrier plan coherence at the next tower level
                    have measureCarrier : sizeOf carrier ≤ fuel := by
                      have shrink := List.sizeOf_lt_of_mem carrierMem
                      have spineBound : sizeOf elements < sizeOf
                          (Pattern.collection
                            (costStaticReflectivePresentationDecl rhoCIGSLT
                              color (rhoReflectivePresentation.toReflectivePresentationDecl)
                              ).parallelCollection elements none) := by
                        simp_wf
                        omega
                      omega
                    have carrierTower := inductionHypothesis pC
                      (innerLevel + 1) measureCarrier carrierCanon
                    -- AUTH-side fixpoint of the tower value
                    have towerAuthFixpoint : canonicalize
                        rhoReflectivePresentation.toReflectivePresentationDecl
                        (iterDrop
                          rhoReflectivePresentation.toReflectivePresentationDecl
                          (innerLevel + 1)
                          (.apply ((rhoReflectivePresentation.toReflectivePresentationDecl)
                            ).parallelUnitConstructor [])) =
                        iterDrop
                          rhoReflectivePresentation.toReflectivePresentationDecl
                          (innerLevel + 1)
                          (.apply ((rhoReflectivePresentation.toReflectivePresentationDecl)
                            ).parallelUnitConstructor []) :=
                      canonicalize_iterDropUnit
                        rhoReflectivePresentation.toReflectivePresentationDecl
                        auth_dropNeQuote (innerLevel + 1)
                    -- abstract split at the carrier position
                    have midEq : (getElem children.abstractPatterns 
                        contextBefore.length kAbs) = pC.abstractPattern :=
                      (List.getElem_eq_iff kAbs).mpr pCAbs
                    have beforeUnits : ∀ b ∈ children.abstractPatterns.take
                        contextBefore.length,
                        canonicalize
                            (rhoReflectivePresentation.toReflectivePresentationDecl)
                            b =
                          .apply ((rhoReflectivePresentation.toReflectivePresentationDecl)
                            ).parallelUnitConstructor [] := by
                      intro b bmem
                      obtain ⟨i, ib⟩ := List.mem_iff_getElem?.mp bmem
                      rw [List.getElem?_take] at ib
                      have iLtK : i < contextBefore.length := by
                        by_contra h
                        rw [if_neg (by omega)] at ib
                        simp at ib
                      rw [if_pos iLtK] at ib
                      obtain ⟨_, iBound⟩ := List.getElem?_eq_some_iff.mp ib
                      have iAbs : i < children.abstractPatterns.length := by
                        omega
                      rw [show b = (getElem children.abstractPatterns i iAbs)
                        from (List.getElem_eq_iff iAbs).mpr ib ▸ rfl]
                      exact siblingUnitAbs iAbs (by omega)
                    have afterUnits : ∀ b ∈ children.abstractPatterns.drop
                        (contextBefore.length + 1),
                        canonicalize
                            (rhoReflectivePresentation.toReflectivePresentationDecl)
                            b =
                          .apply ((rhoReflectivePresentation.toReflectivePresentationDecl)
                            ).parallelUnitConstructor [] := by
                      intro b bmem
                      obtain ⟨i, ib⟩ := List.mem_iff_getElem?.mp bmem
                      rw [List.getElem?_drop] at ib
                      -- ib : abstracts[(|cB|+1) + i]? = some b
                      obtain ⟨jBound, -⟩ := List.getElem?_eq_some_iff.mp ib
                      have jAbs : contextBefore.length + 1 + i <
                          children.abstractPatterns.length := jBound
                      rw [show b = (getElem children.abstractPatterns
                            (contextBefore.length + 1 + i) jAbs)
                        from (List.getElem_eq_iff jAbs).mpr ib ▸ rfl]
                      exact siblingUnitAbs jAbs (by omega)

                    -- final assembly at the abstract frame
                    have spineSplit : children.abstractPatterns =
                        children.abstractPatterns.take contextBefore.length ++
                          (getElem children.abstractPatterns contextBefore.length kAbs) ::
                            children.abstractPatterns.drop
                              (contextBefore.length + 1) := by
                      have tcd := List.take_append_drop
                        (contextBefore.length + 1) children.abstractPatterns
                      rw (occs := .pos [1]) [← tcd]
                      rw [← List.take_concat_get kAbs]
                      simp [List.concat_eq_append]
                    have notUnitAUTH : Pattern.apply
                        ((rhoReflectivePresentation.toReflectivePresentationDecl).dropConstructor)
                        [iterDrop
                          (rhoReflectivePresentation.toReflectivePresentationDecl)
                          innerLevel
                          (.apply ((rhoReflectivePresentation.toReflectivePresentationDecl)
                            ).parallelUnitConstructor [])] ≠
                        .apply ((rhoReflectivePresentation.toReflectivePresentationDecl)
                          ).parallelUnitConstructor [] := by
                      intro unitEq
                      have wireEq := (Pattern.apply.inj unitEq).1
                      rw [auth_dropConstructor, auth_unitConstructor] at wireEq
                      exact absurd wireEq (by decide)
                    have notParallelAUTH : ∀ nested, Pattern.apply
                        ((rhoReflectivePresentation.toReflectivePresentationDecl).dropConstructor)
                        [iterDrop
                          (rhoReflectivePresentation.toReflectivePresentationDecl)
                          innerLevel
                          (.apply ((rhoReflectivePresentation.toReflectivePresentationDecl)
                            ).parallelUnitConstructor [])] ≠
                        .collection ((rhoReflectivePresentation.toReflectivePresentationDecl)
                          ).parallelCollection nested none := by
                      intro nested equality
                      exact Pattern.noConfusion equality
                    have slotEq : canonicalize
                        (rhoReflectivePresentation.toReflectivePresentationDecl)
                        ((getElem children.abstractPatterns contextBefore.length kAbs)) =
                        canonicalize
                          (rhoReflectivePresentation.toReflectivePresentationDecl)
                          (iterDrop
                            (rhoReflectivePresentation.toReflectivePresentationDecl)
                            (innerLevel + 1)
                            (.apply ((rhoReflectivePresentation.toReflectivePresentationDecl)
                              ).parallelUnitConstructor [])) := by
                      rw [midEq]
                      exact carrierTower.trans towerAuthFixpoint.symm
                    simp only [CostStaticRegionPlan.abstractPattern,
                      Option.map_none]
                    suffices finalForm : canonicalize
                        (rhoReflectivePresentation.toReflectivePresentationDecl)
                        (Pattern.collection
                          (costStaticReflectivePresentationDecl rhoCIGSLT color
                            (rhoReflectivePresentation.toReflectivePresentationDecl)
                            ).parallelCollection
                          children.abstractPatterns none) =
                      iterDrop
                        (rhoReflectivePresentation.toReflectivePresentationDecl)
                        (innerLevel + 1)
                        (.apply ((rhoReflectivePresentation.toReflectivePresentationDecl)
                          ).parallelUnitConstructor []) by
                      exact finalForm
                    rw [spineSplit,
                      canonicalize_collection_congr_canonical_slot
                        rhoReflectivePresentation.toReflectivePresentationDecl
                        _ none _ _ slotEq,
                      canonicalize_collection_ct_transport
                        rhoReflectivePresentation.toReflectivePresentationDecl
                        ((rhoDeclC_parallelCollection_hashBag color).trans
                          auth_parallelCollection.symm)]
                    apply canonicalize_parallel_units_around
                    · exact beforeUnits
                    · exact afterUnits
                    · exact towerAuthFixpoint
                    · simpa only [iterDrop] using notUnitAUTH
                    · intro nested equality
                      exact Pattern.noConfusion equality
              · rw [canonicalize_collection_of_ne_parallel _ parallelType]
                  at towerCanonical
                cases level <;> simp [iterDrop] at towerCanonical
      | application declared rendered current preimage notBare children =>
          rename_i wireName arguments
          have wireForm : wireName =
              (color.symbols rhoCIGSLT).constructor
                preimage.sourceConstructor.1.label := by
            rw [← rendered, ← rhoCIGSLT.materializeDeclaredCostConstructor_label
              declared, preimage.labelMap]
          by_cases quoteHead : wireName =
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl
                ).quoteConstructor
          · have labelQuote : preimage.sourceConstructor.1.label =
                "NQuote" := by
              apply costStaticColor_constructor_inj (color := color)
              rw [← wireForm, quoteHead, rhoDecl_quoteConstructor]
            subst quoteHead
            rw [canonicalize_apply_eq_finish] at towerCanonical
            rcases finishNormalizeReflectiveApply_quote_cases
                (costStaticReflectivePresentationDecl rhoCIGSLT color
                  rhoReflectivePresentation.toReflectivePresentationDecl)
                (arguments.map (canonicalize
                  (costStaticReflectivePresentationDecl rhoCIGSLT color
                    rhoReflectivePresentation.toReflectivePresentationDecl)))
              with ⟨inner, mappedEq, resultEq⟩ | resultEq
            · -- quote-drop collapse: the source argument is the next tower
              -- level; the absorb lemma evaporates one quote-drop pair.
              rw [resultEq] at towerCanonical
              obtain ⟨argument, argumentsEq, canonArgument⟩ :
                  ∃ argument, arguments = [argument] ∧
                    canonicalize
                      (costStaticReflectivePresentationDecl rhoCIGSLT color
                        rhoReflectivePresentation.toReflectivePresentationDecl)
                      argument =
                    iterDrop
                      (costStaticReflectivePresentationDecl rhoCIGSLT color
                        rhoReflectivePresentation.toReflectivePresentationDecl)
                      (level + 1)
                      (.apply (costStaticReflectivePresentationDecl rhoCIGSLT
                        color (rhoReflectivePresentation.toReflectivePresentationDecl)
                        ).parallelUnitConstructor []) := by
                cases arguments with
                | nil => simp at mappedEq
                | cons head tail =>
                    cases tail with
                    | nil =>
                        refine ⟨head, rfl, ?_⟩
                        have headEq : canonicalize
                            (costStaticReflectivePresentationDecl rhoCIGSLT
                              color (rhoReflectivePresentation.toReflectivePresentationDecl)) head =
                          .apply (costStaticReflectivePresentationDecl
                            rhoCIGSLT color (rhoReflectivePresentation.toReflectivePresentationDecl)
                            ).dropConstructor [inner] := by
                          simpa using mappedEq
                        rw [headEq, towerCanonical]
                        rfl
                    | cons second rest => simp at mappedEq
              subst argumentsEq
              obtain ⟨active⟩ :=
                CostStaticArgumentPlan.nonempty_activeAt children
                  (contextBefore := []) (middle := argument)
                  (contextAfter := []) rfl
              have measureChild : sizeOf argument ≤ fuel := by
                have shrink :=
                  CostHereditaryCrossColorLeafHinge.rhoCalc_sizeOf_singleton_child
                    (costStaticReflectivePresentationDecl rhoCIGSLT color
                      rhoReflectivePresentation.toReflectivePresentationDecl
                      ).quoteConstructor argument
                omega
              have childTower := inductionHypothesis active.head (level + 1)
                measureChild canonArgument
              have lengthOne : children.abstractPatterns.length = 1 := by
                rw [(CostHereditaryCrossColorLeafHinge.CostStaticArgumentPlan.abstractPatterns_length children).1]
                simp
              have splitLen := congrArg List.length active.abstracts_eq
              rw [lengthOne, List.length_append, List.length_cons] at splitLen
              have beforeNil : active.beforeAbstracts = [] :=
                List.eq_nil_of_length_eq_zero (by omega)
              have afterNil : active.afterAbstracts = [] :=
                List.eq_nil_of_length_eq_zero (by omega)
              simp only [CostStaticRegionPlan.abstractPattern, labelQuote]
              rw [active.abstracts_eq, beforeNil, afterNil, List.nil_append]
              rw [show ([active.head.abstractPattern] :
                  List Pattern) = [_] from rfl]
              rw [← auth_quoteConstructor]
              rw [canonicalize_apply_eq_finish, List.map_cons, List.map_nil,
                childTower]
              rw [show iterDrop
                  rhoReflectivePresentation.toReflectivePresentationDecl
                  (level + 1)
                  (.apply ((rhoReflectivePresentation.toReflectivePresentationDecl)
                    ).parallelUnitConstructor []) =
                .apply
                  (rhoReflectivePresentation.toReflectivePresentationDecl).dropConstructor
                  [iterDrop
                    rhoReflectivePresentation.toReflectivePresentationDecl
                    level
                    (.apply ((rhoReflectivePresentation.toReflectivePresentationDecl)
                      ).parallelUnitConstructor [])] from rfl]
              rw [show iterDrop
                  rhoReflectivePresentation.toReflectivePresentationDecl
                  level
                  (.apply ((rhoReflectivePresentation.toReflectivePresentationDecl)
                    ).parallelUnitConstructor []) =
                iterDrop
                  rhoReflectivePresentation.toReflectivePresentationDecl
                  level
                  (.apply ((rhoReflectivePresentation.toReflectivePresentationDecl)
                    ).parallelUnitConstructor []) from rfl]
              simp only [finishNormalizeReflectiveApply, beq_self_eq_true,
                if_true]
            · rw [resultEq] at towerCanonical
              cases level with
              | zero =>
                  simp only [iterDrop] at towerCanonical
                  have wireEq := (Pattern.apply.inj towerCanonical).1
                  rw [rhoDecl_quoteConstructor, rhoDecl_unitConstructor]
                    at wireEq
                  exact absurd (costStaticColor_constructor_inj wireEq)
                    (by decide)
              | succ innerLevel =>
                  simp only [iterDrop] at towerCanonical
                  have wireEq := (Pattern.apply.inj towerCanonical).1
                  rw [rhoDecl_quoteConstructor, rhoDecl_dropConstructor]
                    at wireEq
                  exact absurd (costStaticColor_constructor_inj wireEq)
                    (by decide)
          · rw [canonicalize_apply_of_ne_quote _ quoteHead] at towerCanonical
            cases level with
            | zero =>
                -- static unit wire
                simp only [iterDrop] at towerCanonical
                obtain ⟨wireEq, argsNil⟩ :=
                  Pattern.apply.inj towerCanonical
                have labelUnit : preimage.sourceConstructor.1.label =
                    "PZero" := by
                  apply costStaticColor_constructor_inj (color := color)
                  rw [← wireForm, wireEq, rhoDecl_unitConstructor]
                have argumentsNil : arguments = [] :=
                  List.map_eq_nil_iff.mp argsNil
                subst argumentsNil
                have abstractsNil : children.abstractPatterns = [] := by
                  have len := (CostHereditaryCrossColorLeafHinge.CostStaticArgumentPlan.abstractPatterns_length children).1
                  exact List.eq_nil_of_length_eq_zero (by rw [len]; simp)
                simp only [CostStaticRegionPlan.abstractPattern, labelUnit,
                  abstractsNil]
                rw [← auth_unitConstructor]
                rw [canonicalize_eq_of_isCanonical _ (isCanonical_unitApply
                  rhoReflectivePresentation.toReflectivePresentationDecl)]
                simp only [iterDrop]
            | succ innerLevel =>
                -- static drop wire: peel one tower level
                simp only [iterDrop] at towerCanonical
                obtain ⟨wireEq, argsTower⟩ :=
                  Pattern.apply.inj towerCanonical
                have labelDrop : preimage.sourceConstructor.1.label =
                    "PDrop" := by
                  apply costStaticColor_constructor_inj (color := color)
                  rw [← wireForm, wireEq, rhoDecl_dropConstructor]
                obtain ⟨argument, argumentsEq, canonArgument⟩ :
                    ∃ argument, arguments = [argument] ∧
                      canonicalize
                        (costStaticReflectivePresentationDecl rhoCIGSLT color
                          (rhoReflectivePresentation.toReflectivePresentationDecl)) argument =
                      iterDrop
                        (costStaticReflectivePresentationDecl rhoCIGSLT color
                          (rhoReflectivePresentation.toReflectivePresentationDecl)) innerLevel
                        (.apply (costStaticReflectivePresentationDecl
                          rhoCIGSLT color (rhoReflectivePresentation.toReflectivePresentationDecl)
                          ).parallelUnitConstructor []) := by
                  cases arguments with
                  | nil => simp at argsTower
                  | cons head tail =>
                      cases tail with
                      | nil =>
                          exact ⟨head, rfl, by simpa using argsTower⟩
                      | cons second rest => simp at argsTower
                subst argumentsEq
                obtain ⟨active⟩ :=
                  CostStaticArgumentPlan.nonempty_activeAt children
                    (contextBefore := []) (middle := argument)
                    (contextAfter := []) rfl
                have measureChild : sizeOf argument ≤ fuel := by
                  have shrink :=
                    CostHereditaryCrossColorLeafHinge.rhoCalc_sizeOf_singleton_child
                      wireName argument
                  omega
                have childTower := inductionHypothesis active.head innerLevel
                  measureChild canonArgument
                have lengthOne : children.abstractPatterns.length = 1 := by
                  rw [(CostHereditaryCrossColorLeafHinge.CostStaticArgumentPlan.abstractPatterns_length children).1]
                  simp
                have splitLen := congrArg List.length active.abstracts_eq
                rw [lengthOne, List.length_append, List.length_cons]
                  at splitLen
                have beforeNil : active.beforeAbstracts = [] :=
                  List.eq_nil_of_length_eq_zero (by omega)
                have afterNil : active.afterAbstracts = [] :=
                  List.eq_nil_of_length_eq_zero (by omega)
                simp only [CostStaticRegionPlan.abstractPattern, labelDrop]
                rw [active.abstracts_eq, beforeNil, afterNil, List.nil_append]
                rw [← auth_dropConstructor]
                rw [canonicalize_apply_of_ne_quote _ (by
                  rw [auth_dropConstructor, auth_quoteConstructor]
                  decide)]
                rw [List.map_cons, List.map_nil, childTower]
                rfl

/-- The level-zero instance: abstract-unit coherence. -/
theorem plan_abstract_unit_of_colour_unit
    (color : CostStaticColor) {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (canonicalUnit : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        pattern =
      .apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).parallelUnitConstructor []) :
    canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
      plan.abstractPattern =
    .apply (rhoReflectivePresentation.toReflectivePresentationDecl
      ).parallelUnitConstructor [] := by
  have tower := plan_abstract_iterDropUnit_of_iterDropUnit color
    (sizeOf pattern) plan 0 (Nat.le_refl _)
    (by simpa only [iterDrop] using canonicalUnit)
  simpa only [iterDrop] using tower

/-- **activeAt with a length certificate.**  The canonically constructed
element-spine active for a context split carries a before-abstract list
whose length matches the split prefix.  This is the construction-level
invariant the sibling-unit lift needs: sibling abstracts sit off the
carrier position. -/
theorem elementPlan_activeAt_lenCert
    {color : CostStaticColor} {targetFree : FreeTypeContext} :
    ∀ {contextBefore : List Pattern}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {collectionType : CollType} {before elements : List Pattern}
      {rest : Option String} {sourceElementType : TypeExpr}
      (spine : CostStaticElementPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
        elements rest sourceElementType)
      {middle : Pattern} {contextAfter : List Pattern},
      elements = contextBefore ++ middle :: contextAfter →
      ∃ active : CostStaticElementPlanActive rhoCIGSLT color targetFree spine
        contextBefore middle contextAfter,
        active.beforeAbstracts.length = contextBefore.length
  | [], _, _, _, _, _, _, _, _, _, _, spine, middle, contextAfter, split => by
      cases spine with
      | nil => simp at split
      | cons head tail =>
          obtain ⟨headEq, tailEq⟩ := List.cons.inj split
          subst headEq
          subst tailEq
          exact
            ⟨{ position := _
               position_eq := (List.append_nil _).symm
               head := head
               beforeAbstracts := []
               afterAbstracts := tail.abstractPatterns
               abstracts_eq := rfl
               entryEmbedding := by
                 change CostStaticPlanEntryEmbedding rhoCIGSLT color
                   targetFree head.boundaryTable.entries
                   (TypedCostRegionBoundaryTable.append head.boundaryTable
                     tail.boundaryTable).entries
                 rw [TypedCostRegionBoundaryTable.entries_append]
                 exact CostStaticPlanEntryEmbedding.appendLeft _ _ },
             rfl⟩
  | sibling :: contextRest, _, _, _, _, _, _, _, _, _, _, spine, middle,
      contextAfter, split => by
      cases spine with
      | nil => simp at split
      | cons head tail =>
          obtain ⟨headEq, tailEq⟩ := List.cons.inj split
          subst headEq
          obtain ⟨active, activeLen⟩ := elementPlan_activeAt_lenCert
            tail tailEq
          refine
            ⟨{ position := active.position
               position_eq := active.position_eq.trans (by simp)
               head := active.head
               beforeAbstracts :=
                 head.abstractPattern :: active.beforeAbstracts
               afterAbstracts := active.afterAbstracts
               abstracts_eq := ?_
               entryEmbedding := ?_ }, ?_⟩
          · simp [CostStaticElementPlan.abstractPatterns,
              active.abstracts_eq]
          · change CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
              active.head.boundaryTable.entries
              (TypedCostRegionBoundaryTable.append head.boundaryTable
                tail.boundaryTable).entries
            rw [TypedCostRegionBoundaryTable.entries_append]
            exact active.entryEmbedding.comp
              (CostStaticPlanEntryEmbedding.appendRight _ _)
          · simp [List.length_cons, activeLen]

/-- **Self-typing of drop-tower contributors.**

typed at a chain: a colour `Name`/`Proc` image under hash bags. -/
theorem rho_dropTower_typed_chain
    (color : CostStaticColor) {targetFree : FreeTypeContext}
    {targetBound : List TypeExpr} :
    ∀ (fuel : Nat) {V : TypeExpr} {element : Pattern} {y : Pattern},
      sizeOf element ≤ fuel →
      HasType rhoCIGSLT.costWholeLanguage targetFree targetBound
        element V →
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) element =
        .apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).dropConstructor [y] →
      RhoTypedChainColour color V := by
  intro fuel
  induction fuel with
  | zero =>
      intro V element y measure typed canonicalElement
      exact absurd measure (by cases element <;> simp)
  | succ fuel inductionHypothesis =>
      intro V element y measure typed canonicalElement
      cases element with
      | bvar index =>
          simp [canonicalize] at canonicalElement
      | fvar name =>
          simp [canonicalize] at canonicalElement
      | lambda binder body =>
          simp [canonicalize] at canonicalElement
      | multiLambda arity binders body =>
          simp [canonicalize] at canonicalElement
      | subst body replacement =>
          simp [canonicalize] at canonicalElement
      | apply wire arguments =>
          by_cases quoteHead : wire =
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl
                ).quoteConstructor
          · obtain ⟨rule, ruleMembership, labelEquality, _notBare,
                typeEquality, _argumentsTyped⟩ :=
              WellSorted.hasType_apply_inversion typed
            have categoryForm :=
              rho_costWhole_rule_category_of_quoteWire color ruleMembership
                (labelEquality.symm.trans (quoteHead.trans (rhoDecl_quoteConstructor color)))
            rw [canonicalize_apply_eq_finish,
              quoteHead] at canonicalElement
            rcases finishNormalizeReflectiveApply_quote_cases
                (costStaticReflectivePresentationDecl rhoCIGSLT color
                  rhoReflectivePresentation.toReflectivePresentationDecl)
                (arguments.map (canonicalize
                  (costStaticReflectivePresentationDecl rhoCIGSLT color
                    rhoReflectivePresentation.toReflectivePresentationDecl)))
              with ⟨inner, mappedEq, resultEq⟩ | resultEq
            · rw [typeEquality.trans categoryForm]
              cases color <;>
                simp [CostStaticColor.symbols, mapTypeExpr,
                  costBaseStaticSymbols, costWrappedStaticSymbols,
                  costBasePresentationSymbols, rho_interactingSort_name]
              · exact .nameLeaf
              · exact .nameLeaf
            · rw [resultEq] at canonicalElement
              exact absurd (Pattern.apply.inj canonicalElement).1 (by
                intro quoteIsDrop
                rw [rhoDecl_quoteConstructor, rhoDecl_dropConstructor]
                  at quoteIsDrop
                exact absurd (costStaticColor_constructor_inj quoteIsDrop)
                  (by decide))
          · rw [canonicalize_apply_of_ne_quote _ quoteHead] at canonicalElement
            have wireEq := (Pattern.apply.inj canonicalElement).1
            obtain ⟨rule, ruleMembership, labelEquality, _notBare,
                typeEquality, _argumentsTyped⟩ :=
              WellSorted.hasType_apply_inversion typed
            have categoryForm :=
              rho_costWhole_rule_category_of_dropWire color ruleMembership
                (labelEquality.symm.trans (wireEq.trans (rhoDecl_dropConstructor color)))
            rw [typeEquality.trans categoryForm]
            cases color with
            | base =>
                simp [CostStaticColor.symbols, mapTypeExpr,
                  costBaseStaticSymbols, costBasePresentationSymbols]
                exact .procLeafBase
            | wrapped =>
                simp [CostStaticColor.symbols, mapTypeExpr,
                  costWrappedStaticSymbols, rho_interactingSort_name]
                exact .procLeafWrapped
      | collection collectionType elements rest =>
          cases rest with
          | some restName =>
              rw [canonicalize_collection_rest] at canonicalElement
              simp at canonicalElement
          | none =>
              by_cases parallelType : collectionType =
                  (costStaticReflectivePresentationDecl rhoCIGSLT color
                    rhoReflectivePresentation.toReflectivePresentationDecl
                    ).parallelCollection
              · rw [parallelType] at canonicalElement
                have notUnit : Pattern.apply
                      (costStaticReflectivePresentationDecl rhoCIGSLT color
                        rhoReflectivePresentation.toReflectivePresentationDecl
                        ).dropConstructor [y] ≠ Pattern.apply
                      (costStaticReflectivePresentationDecl rhoCIGSLT color
                        rhoReflectivePresentation.toReflectivePresentationDecl
                        ).parallelUnitConstructor [] := by
                  intro unitEq
                  have wireEq := (Pattern.apply.inj unitEq).1
                  rw [rhoDecl_dropConstructor, rhoDecl_unitConstructor]
                    at wireEq
                  exact absurd (costStaticColor_constructor_inj wireEq)
                    (by decide)
                have notParallelResult : ∀ nested, Pattern.apply
                      (costStaticReflectivePresentationDecl rhoCIGSLT color
                        rhoReflectivePresentation.toReflectivePresentationDecl
                        ).dropConstructor [y] ≠
                    .collection
                      (costStaticReflectivePresentationDecl rhoCIGSLT color
                        rhoReflectivePresentation.toReflectivePresentationDecl
                        ).parallelCollection nested none := by
                  intro nested equality
                  exact Pattern.noConfusion equality
                obtain ⟨member, memberMem, memberCanonical⟩ :=
                  exists_member_of_parallel_collapse _ canonicalElement
                    notUnit notParallelResult
                rcases WellSorted.hasType_collection_inversion typed with
                  ⟨elementTypeInner, typeEquality, elementsTyped⟩ |
                  ⟨rule, parameterName, elementTypeInner, ruleMembership,
                    parameterShape, typeEquality, elementsTyped⟩
                · -- direct collection typing: recurse the contributor
                  have memberTyped :=
                    hasType_of_mem_elements elementsTyped memberMem
                  have memberChain :=
                    inductionHypothesis (V := elementTypeInner)
                      (by
                        have memberBound := List.sizeOf_lt_of_mem memberMem
                        have collBound : sizeOf elements <
                            sizeOf (Pattern.collection collectionType
                              elements none) := by
                          simp_wf
                          omega
                        omega)
                      memberTyped memberCanonical
                  rw [parallelType, rhoDeclC_parallelCollection_hashBag]
                    at typeEquality
                  subst typeEquality
                  exact .collection memberChain
                · -- bare-rule collection typing: the rule is rho's parallel
                  -- (base or wrapped copy), whose category is a leaf
                  have categoryRestricted := bare_whole_rule_category
                    ruleMembership ⟨_, _, _, parameterShape⟩
                  subst typeEquality
                  rcases categoryRestricted with catB | catW
                  · rw [catB]
                    exact .procLeafBase
                  · rw [catW]
                    exact .procLeafWrapped
              · rw [canonicalize_collection_of_ne_parallel _ parallelType]
                  at canonicalElement
                simp at canonicalElement




theorem canonicalize_iterDrop_fvar (level : Nat) (name : String) :
    canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
        (iterDrop rhoReflectivePresentation.toReflectivePresentationDecl level
          (.fvar name)) =
      iterDrop rhoReflectivePresentation.toReflectivePresentationDecl level
        (.fvar name) := by
  induction level with
  | zero => simp [iterDrop, canonicalize]
  | succ level inner =>
      rw [iterDrop, canonicalize_apply_of_ne_quote _ auth_dropNeQuote,
        List.map_cons, List.map_nil, inner]

theorem iterDrop_fvar_ne_unit (level : Nat) (name : String) :
    iterDrop rhoReflectivePresentation.toReflectivePresentationDecl level
        (.fvar name) ≠
      Pattern.apply rhoReflectivePresentation.toReflectivePresentationDecl.parallelUnitConstructor
        [] := by
  cases level with
  | zero => simp [iterDrop]
  | succ level => simp [iterDrop, auth_dropConstructor]

theorem iterDrop_fvar_ne_parallel (level : Nat) (name : String)
    (nested : List Pattern) :
    iterDrop rhoReflectivePresentation.toReflectivePresentationDecl level
        (.fvar name) ≠
      Pattern.collection rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
        nested none := by
  cases level <;> simp [iterDrop]


theorem rhoDescend {color : CostStaticColor} {targetFree : FreeTypeContext} :
    ∀ (fuel : Nat) {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType)
      (level : Nat) (target : Pattern),
      sizeOf pattern ≤ fuel →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl) pattern =
        iterDrop
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl) level target →
      RhoDescendEscape color target →
      ∃ payload, Nonempty
        { state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
            plan.abstractPattern //
          canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
              (state.skeletonContext.fill
                (.fvar (costRegionBoundaryVariableName
                  state.certified.typed.boundary))) =
            iterDrop rhoReflectivePresentation.toReflectivePresentationDecl level
              (.fvar (costRegionBoundaryVariableName
                state.certified.typed.boundary))
          ∧ Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
              [state.certified.typed] plan.boundaryTable.entries)
          ∧ canonicalize
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl)
              state.certified.typed.boundary.content = target } := by
  intro fuel
  induction fuel with
  | zero =>
      intro sourceBound targetBound thinning sourceAvailable outer pattern
        sourceType plan level target measure canonical escape
      exact absurd measure (by cases pattern <;> simp)
  | succ fuel inductionHypothesis =>
      intro sourceBound targetBound thinning sourceAvailable outer pattern
        sourceType plan level target measure canonical escape
      cases plan with
      | bvar sourceIndex lookup correspondence availableScope =>
          simp only [canonicalize] at canonical
          exact absurd canonical
            (not_eq_iterDrop_of_escape escape (by simp))
      | fvar lookup =>
          simp only [canonicalize] at canonical
          exact absurd canonical
            (not_eq_iterDrop_of_escape escape (by simp))
      | lambda bodyPlan =>
          simp only [canonicalize] at canonical
          exact absurd canonical
            (not_eq_iterDrop_of_escape escape (by simp))
      | multiLambda bodyPlan =>
          simp only [canonicalize] at canonical
          exact absurd canonical
            (not_eq_iterDrop_of_escape escape (by simp))
      | boundaryApplication declared rendered outsideCurrent certified certifies =>
          rename_i wireName arguments
          have headNe : wireName ≠
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl
                ).quoteConstructor := by
            intro headEq
            exact not_collapsingRoot_of_boundaryHead declared rendered
              outsideCurrent (Or.inl ⟨arguments, by rw [headEq]⟩)
          have canonAp := canonicalize_apply_of_ne_quote
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl) headNe arguments
          have decodedNone := decodeDeclaredCostStaticConstructor_render_of_role_ne
            rhoCIGSLT declared color outsideCurrent
          rw [rendered] at decodedNone
          cases level with
          | succ level =>
              rw [canonAp] at canonical
              have wireEq := (Pattern.apply.inj canonical).1
              rw [wireEq, decodeDeclared_drop] at decodedNone
              exact absurd decodedNone (by simp)
          | zero =>
              simp only [iterDrop_zero] at canonical
              refine ⟨.apply wireName arguments, ⟨⟨
                { boundarySupport := _, boundaryType := _, content := _
                  certified := certified
                  certifies := certifies
                  residual := .hole
                  content_eq := rfl
                  skeletonContext := .hole
                  abstract_eq := rfl }, ?_, ⟨CostStaticPlanEntryEmbedding.refl _⟩,
                ?_⟩⟩⟩
              · simp [OneHoleContext.fill, canonicalize]
              · show canonicalize _ certified.typed.boundary.content = target
                rw [certified.content_eq]
                exact canonical
      | application declared rendered current preimage notBare children =>
          rename_i wireName arguments
          have wireForm : wireName =
              (color.symbols rhoCIGSLT).constructor
                preimage.sourceConstructor.1.label := by
            rw [← rendered, ← rhoCIGSLT.materializeDeclaredCostConstructor_label
              declared, preimage.labelMap]
          have decodedSome :
              decodeDeclaredCostStaticConstructor rhoCIGSLT color wireName =
                some preimage.sourceConstructor.1.label := by
            unfold decodeDeclaredCostStaticConstructor
            rw [← rendered, rhoCIGSLT.decodeDeclaredCostConstructor_render]
            dsimp only
            rw [current]
            simp only []
            rw [rendered, wireForm, decodeCostStaticConstructor_symbols]
            simp
          by_cases quoteHead : wireName =
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl
                ).quoteConstructor
          · have labelQuote : preimage.sourceConstructor.1.label = "NQuote" := by
              apply costStaticColor_constructor_inj (color := color)
              rw [← wireForm, quoteHead, rhoDecl_quoteConstructor]
            subst quoteHead
            rw [canonicalize_apply_eq_finish] at canonical
            rcases finishNormalizeReflectiveApply_quote_cases
                (costStaticReflectivePresentationDecl rhoCIGSLT color
                  rhoReflectivePresentation.toReflectivePresentationDecl)
                (arguments.map (canonicalize
                  (costStaticReflectivePresentationDecl rhoCIGSLT color
                    rhoReflectivePresentation.toReflectivePresentationDecl)))
              with ⟨inner, mappedEq, resultEq⟩ | resultEq
            · rw [resultEq] at canonical
              obtain ⟨argument, argumentsEq, canonArgument⟩ :
                  ∃ argument, arguments = [argument] ∧
                    canonicalize
                      (costStaticReflectivePresentationDecl rhoCIGSLT color
                        rhoReflectivePresentation.toReflectivePresentationDecl)
                      argument =
                    iterDrop
                      (costStaticReflectivePresentationDecl rhoCIGSLT color
                        rhoReflectivePresentation.toReflectivePresentationDecl)
                      (level + 1) target := by
                cases arguments with
                | nil => simp at mappedEq
                | cons head tail =>
                    cases tail with
                    | nil =>
                        refine ⟨head, rfl, ?_⟩
                        have headEq : canonicalize
                            (costStaticReflectivePresentationDecl rhoCIGSLT
                              color (rhoReflectivePresentation.toReflectivePresentationDecl)) head =
                          .apply (costStaticReflectivePresentationDecl
                            rhoCIGSLT color (rhoReflectivePresentation.toReflectivePresentationDecl)
                            ).dropConstructor [inner] := by
                          simpa using mappedEq
                        rw [headEq, canonical]
                        rfl
                    | cons second rest => simp at mappedEq
              subst argumentsEq
              obtain ⟨active⟩ :=
                CostStaticArgumentPlan.nonempty_activeAt children
                  (contextBefore := []) (middle := argument)
                  (contextAfter := []) rfl
              have measureChild : sizeOf argument ≤ fuel := by
                have shrink :=
                  CostHereditaryCrossColorLeafHinge.rhoCalc_sizeOf_singleton_child
                    (costStaticReflectivePresentationDecl rhoCIGSLT color
                      rhoReflectivePresentation.toReflectivePresentationDecl
                      ).quoteConstructor argument
                omega
              obtain ⟨payload, ⟨childState, childCollapse, ⟨childEmbedding⟩,
                  childCanonical⟩⟩ :=
                inductionHypothesis active.head (level + 1) target measureChild
                  canonArgument escape
              have lengthOne : children.abstractPatterns.length = 1 := by
                rw [(CostHereditaryCrossColorLeafHinge.CostStaticArgumentPlan.abstractPatterns_length
                  children).1]
                simp
              have split := congrArg List.length active.abstracts_eq
              rw [lengthOne, List.length_append, List.length_cons] at split
              have beforeNil : active.beforeAbstracts = [] :=
                List.eq_nil_of_length_eq_zero (by omega)
              have afterNil : active.afterAbstracts = [] :=
                List.eq_nil_of_length_eq_zero (by omega)
              have frameFill : ∀ pattern,
                  (OneHoleContext.apply preimage.sourceConstructor.1.label
                      active.beforeAbstracts .hole active.afterAbstracts
                    ).fill pattern = Pattern.apply "NQuote" [pattern] := by
                intro pattern
                rw [beforeNil, afterNil, labelQuote]
                rfl
              refine ⟨payload, ⟨⟨{ childState with
                  skeletonContext :=
                    (OneHoleContext.apply preimage.sourceConstructor.1.label
                      active.beforeAbstracts .hole active.afterAbstracts).comp
                      childState.skeletonContext
                  abstract_eq := by
                    rw [OneHoleContext.fill_comp, ← childState.abstract_eq]
                    simp [CostStaticRegionPlan.abstractPattern,
                      OneHoleContext.fill, active.abstracts_eq] },
                ?_, ⟨childEmbedding.comp active.entryEmbedding⟩,
                childCanonical⟩⟩⟩
              dsimp only
              rw [OneHoleContext.fill_comp, frameFill]
              show canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
                  (Pattern.apply
                    rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor
                    [_]) = _
              rw [canonicalize_apply_eq_finish, List.map_cons, List.map_nil,
                childCollapse]
              simp [finishNormalizeReflectiveApply, iterDrop]
            · rw [resultEq] at canonical
              cases level with
              | zero =>
                  simp only [iterDrop_zero] at canonical
                  obtain ⟨_, w, a, shape, decodedNone⟩ := escape
                  rw [← canonical] at shape
                  have headEq := (Pattern.apply.inj shape).1
                  rw [← headEq, decodeDeclared_quote] at decodedNone
                  exact absurd decodedNone (by simp)
              | succ level =>
                  have headEq := (Pattern.apply.inj canonical).1
                  rw [rhoDecl_quoteConstructor, rhoDecl_dropConstructor] at headEq
                  exact absurd (costStaticColor_constructor_inj headEq) (by decide)
          · have canonAp := canonicalize_apply_of_ne_quote
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl)
              quoteHead arguments
            rw [canonAp] at canonical
            cases level with
            | zero =>
                simp only [iterDrop_zero] at canonical
                obtain ⟨_, w, a, shape, decodedNone⟩ := escape
                rw [← canonical] at shape
                rw [(Pattern.apply.inj shape).1] at decodedSome
                rw [decodedSome] at decodedNone
                exact absurd decodedNone (by simp)
            | succ level =>
                have headEq := (Pattern.apply.inj canonical).1
                have argsEq := (Pattern.apply.inj canonical).2
                obtain ⟨argument, argumentsEq, canonArgument⟩ :
                    ∃ argument, arguments = [argument] ∧
                      canonicalize
                        (costStaticReflectivePresentationDecl rhoCIGSLT color
                          rhoReflectivePresentation.toReflectivePresentationDecl)
                        argument =
                      iterDrop
                        (costStaticReflectivePresentationDecl rhoCIGSLT color
                          rhoReflectivePresentation.toReflectivePresentationDecl)
                        level target := by
                  cases arguments with
                  | nil => simp at argsEq
                  | cons head tail =>
                      cases tail with
                      | nil => exact ⟨head, rfl, by simpa using argsEq⟩
                      | cons second rest => simp at argsEq
                have labelDrop : preimage.sourceConstructor.1.label = "PDrop" := by
                  apply costStaticColor_constructor_inj (color := color)
                  rw [← wireForm, headEq, rhoDecl_dropConstructor]
                subst argumentsEq
                obtain ⟨active⟩ :=
                  CostStaticArgumentPlan.nonempty_activeAt children
                    (contextBefore := []) (middle := argument)
                    (contextAfter := []) rfl
                have measureChild : sizeOf argument ≤ fuel := by
                  have shrink :=
                    CostHereditaryCrossColorLeafHinge.rhoCalc_sizeOf_singleton_child
                      wireName argument
                  omega
                obtain ⟨payload, ⟨childState, childCollapse, ⟨childEmbedding⟩,
                    childCanonical⟩⟩ :=
                  inductionHypothesis active.head level target measureChild
                    canonArgument escape
                have lengthOne : children.abstractPatterns.length = 1 := by
                  rw [(CostHereditaryCrossColorLeafHinge.CostStaticArgumentPlan.abstractPatterns_length
                    children).1]
                  simp
                have split := congrArg List.length active.abstracts_eq
                rw [lengthOne, List.length_append, List.length_cons] at split
                have beforeNil : active.beforeAbstracts = [] :=
                  List.eq_nil_of_length_eq_zero (by omega)
                have afterNil : active.afterAbstracts = [] :=
                  List.eq_nil_of_length_eq_zero (by omega)
                have frameFill : ∀ pattern,
                    (OneHoleContext.apply preimage.sourceConstructor.1.label
                        active.beforeAbstracts .hole active.afterAbstracts
                      ).fill pattern = Pattern.apply "PDrop" [pattern] := by
                  intro pattern
                  rw [beforeNil, afterNil, labelDrop]
                  rfl
                refine ⟨payload, ⟨⟨{ childState with
                    skeletonContext :=
                      (OneHoleContext.apply preimage.sourceConstructor.1.label
                        active.beforeAbstracts .hole active.afterAbstracts).comp
                        childState.skeletonContext
                    abstract_eq := by
                      rw [OneHoleContext.fill_comp, ← childState.abstract_eq]
                      simp [CostStaticRegionPlan.abstractPattern,
                        OneHoleContext.fill, active.abstracts_eq] },
                  ?_, ⟨childEmbedding.comp active.entryEmbedding⟩,
                  childCanonical⟩⟩⟩
                dsimp only
                rw [OneHoleContext.fill_comp, frameFill,
                  canonicalize_apply_of_ne_quote _ (by decide),
                  List.map_cons, List.map_nil, childCollapse]
                rfl
      | collection choice selected children =>
          rename_i collectionType elements rest
          cases rest with
          | some restName =>
              rw [canonicalize_collection_rest] at canonical
              cases level with
              | succ level => exact absurd canonical (by simp [iterDrop])
              | zero =>
                  simp only [iterDrop_zero] at canonical
                  exact absurd canonical.symm (escape.1 _ _ _)
          | none =>
              by_cases parallelType : collectionType =
                  (costStaticReflectivePresentationDecl rhoCIGSLT color
                    rhoReflectivePresentation.toReflectivePresentationDecl
                    ).parallelCollection
              · rw [parallelType] at canonical
                have notUnit : iterDrop
                      (costStaticReflectivePresentationDecl rhoCIGSLT color
                        rhoReflectivePresentation.toReflectivePresentationDecl)
                      level target ≠
                    .apply
                      (costStaticReflectivePresentationDecl rhoCIGSLT color
                        rhoReflectivePresentation.toReflectivePresentationDecl
                        ).parallelUnitConstructor [] := by
                  cases level with
                  | zero =>
                      simp only [iterDrop_zero]
                      intro unitEq
                      obtain ⟨_, w, a, shape, decodedNone⟩ := escape
                      rw [unitEq] at shape
                      have wireEq := (Pattern.apply.inj shape).1
                      rw [← wireEq, decodeDeclared_unit] at decodedNone
                      exact absurd decodedNone (by simp)
                  | succ level =>
                      simp [iterDrop,
]
                have notParallelResult : ∀ nested,
                    iterDrop
                        (costStaticReflectivePresentationDecl rhoCIGSLT color
                          rhoReflectivePresentation.toReflectivePresentationDecl)
                        level target ≠
                      .collection
                        (costStaticReflectivePresentationDecl rhoCIGSLT color
                          rhoReflectivePresentation.toReflectivePresentationDecl
                          ).parallelCollection nested none := by
                  intro nested iterEq
                  cases level with
                  | zero =>
                      simp only [iterDrop_zero] at iterEq
                      exact escape.1 _ _ _ iterEq
                  | succ level => simp [iterDrop] at iterEq
                obtain ⟨element, elementMem, elementCanonical⟩ :=
                  exists_member_of_parallel_collapse _ canonical notUnit
                    notParallelResult
                obtain ⟨before, after, elementsEq⟩ :=
                  List.mem_iff_append.mp elementMem
                obtain ⟨active, lenCert⟩ :=
                  elementPlan_activeAt_lenCert children elementsEq
                have measureChild : sizeOf element ≤ fuel := by
                  have elementBound := List.sizeOf_lt_of_mem elementMem
                  have spineBound :
                      sizeOf elements < sizeOf
                        (Pattern.collection collectionType elements none) := by
                    simp_wf
                    omega
                  omega
                obtain ⟨payload, ⟨childState, childCollapse, ⟨childEmbedding⟩,
                    childCanonical⟩⟩ :=
                  inductionHypothesis active.head level target measureChild
                    elementCanonical escape
                refine ⟨payload, ⟨⟨{ childState with
                    skeletonContext :=
                      (OneHoleContext.collection collectionType
                        active.beforeAbstracts .hole active.afterAbstracts
                          none).comp childState.skeletonContext
                    abstract_eq := by
                      rw [OneHoleContext.fill_comp, ← childState.abstract_eq]
                      simp [CostStaticRegionPlan.abstractPattern,
                        OneHoleContext.fill, active.abstracts_eq] },
                  ?_, ⟨childEmbedding.comp active.entryEmbedding⟩,
                  childCanonical⟩⟩⟩
                dsimp only
                rw [OneHoleContext.fill_comp, OneHoleContext.fill]
                -- GAP B' assembly.
                have authParallel : collectionType =
                    rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection := by
                  rw [parallelType, rhoDeclC_parallelCollection_hashBag,
                    auth_parallelCollection]
                have spineBound :
                    sizeOf elements < sizeOf
                      (Pattern.collection collectionType elements none) := by
                  simp_wf
                  omega
                have beforeUnits : ∀ b ∈ active.beforeAbstracts,
                    canonicalize rhoReflectivePresentation.toReflectivePresentationDecl b =
                      Pattern.apply rhoReflectivePresentation.toReflectivePresentationDecl.parallelUnitConstructor
                        [] := by
                  intro b bMem
                  obtain ⟨i, iLt, bAt⟩ := List.mem_iff_getElem.mp bMem
                  have beforeAt : active.beforeAbstracts[i]? = some b :=
                    List.getElem?_eq_some_iff.mpr ⟨iLt, bAt⟩
                  have absAt : children.abstractPatterns[i]? = some b := by
                    rw [active.abstracts_eq, List.getElem?_append_left iLt]
                    exact beforeAt
                  have iLtBefore : i < before.length := lenCert ▸ iLt
                  have eAt : before[i]? = some before[i] :=
                    List.getElem?_eq_getElem iLtBefore
                  have eMemBefore : before[i] ∈ before := List.getElem_mem iLtBefore
                  have elemsSome : elements[i]? = some before[i] := by
                    rw [elementsEq, List.getElem?_append_left iLtBefore]
                    exact eAt
                  obtain ⟨ou, plan, planAt⟩ :=
                    elementSpine_getElem?_abstracts color children i elemsSome
                  have bEq : b = plan.abstractPattern :=
                    Option.some.inj (absAt.symm.trans planAt)
                  subst bEq
                  have eUnit := sibling_unit_positional
                    (costStaticReflectivePresentationDecl rhoCIGSLT color
                      rhoReflectivePresentation.toReflectivePresentationDecl)
                    notUnit notParallelResult canonical elementsEq
                    elementCanonical (Or.inl eMemBefore)
                  have eMem : before[i] ∈ elements := by
                    rw [elementsEq]
                    exact List.mem_append_left _ eMemBefore
                  have measureE : sizeOf before[i] ≤ fuel := by
                    have eBound := List.sizeOf_lt_of_mem eMem
                    omega
                  have tower := plan_abstract_iterDropUnit_of_iterDropUnit
                    color fuel plan 0 measureE (by simpa using eUnit)
                  simpa using tower
                have afterLen : active.afterAbstracts.length = after.length := by
                  have total := elementPlan_abstractPatterns_length color
                    children
                  have lenAbs := congrArg List.length active.abstracts_eq
                  have lenEls := congrArg List.length elementsEq
                  simp only [List.length_append, List.length_cons] at lenAbs lenEls
                  omega
                have afterUnits : ∀ a ∈ active.afterAbstracts,
                    canonicalize rhoReflectivePresentation.toReflectivePresentationDecl a =
                      Pattern.apply rhoReflectivePresentation.toReflectivePresentationDecl.parallelUnitConstructor
                        [] := by
                  intro a aMem
                  obtain ⟨j, jLt, aAt⟩ := List.mem_iff_getElem.mp aMem
                  have jLtAfter : j < after.length := afterLen ▸ jLt
                  have absAt : children.abstractPatterns[
                      active.beforeAbstracts.length + 1 + j]? = some a := by
                    rw [active.abstracts_eq,
                      List.getElem?_append_right (by omega),
                      show active.beforeAbstracts.length + 1 + j -
                          active.beforeAbstracts.length = j + 1 by omega,
                      List.getElem?_cons_succ]
                    exact List.getElem?_eq_some_iff.mpr ⟨jLt, aAt⟩
                  have eMemAfter : after[j] ∈ after := List.getElem_mem jLtAfter
                  have elemsSome : elements[
                      active.beforeAbstracts.length + 1 + j]? = some after[j] := by
                    have transport := congrArg
                      (fun list => list[active.beforeAbstracts.length + 1 + j]?)
                      elementsEq
                    rw [transport, List.getElem?_append_right (by omega),
                      show active.beforeAbstracts.length + 1 + j -
                          before.length = j + 1 by omega,
                      List.getElem?_cons_succ]
                    exact List.getElem?_eq_getElem jLtAfter
                  obtain ⟨ou, plan, planAt⟩ :=
                    elementSpine_getElem?_abstracts color children
                      (active.beforeAbstracts.length + 1 + j) elemsSome
                  have aEq : a = plan.abstractPattern :=
                    Option.some.inj (absAt.symm.trans planAt)
                  subst aEq
                  have eUnit := sibling_unit_positional
                    (costStaticReflectivePresentationDecl rhoCIGSLT color
                      rhoReflectivePresentation.toReflectivePresentationDecl)
                    notUnit notParallelResult canonical elementsEq
                    elementCanonical (Or.inr eMemAfter)
                  have eMem : after[j] ∈ elements := by
                    rw [elementsEq]
                    exact List.mem_append_right _ (List.mem_cons_of_mem _ eMemAfter)
                  have measureE : sizeOf after[j] ≤ fuel := by
                    have eBound := List.sizeOf_lt_of_mem eMem
                    omega
                  have tower := plan_abstract_iterDropUnit_of_iterDropUnit
                    color fuel plan 0 measureE (by simpa using eUnit)
                  simpa using tower
                rw [canonicalize_collection_congr_canonical_slot
                  rhoReflectivePresentation.toReflectivePresentationDecl
                  collectionType none active.beforeAbstracts
                  active.afterAbstracts
                  (middle' := iterDrop rhoReflectivePresentation.toReflectivePresentationDecl
                    level (.fvar (costRegionBoundaryVariableName
                      childState.certified.typed.boundary)))
                  (by simp only [OneHoleContext.fill]
                      rw [childCollapse, canonicalize_iterDrop_fvar])]
                rw [canonicalize_collection_ct_transport _ authParallel]
                exact canonicalize_parallel_units_around _ beforeUnits
                  afterUnits (canonicalize_iterDrop_fvar _ _)
                  (iterDrop_fvar_ne_unit _ _)
                  (fun nested => iterDrop_fvar_ne_parallel _ _ nested)
              · rw [canonicalize_collection_of_ne_parallel _ parallelType]
                  at canonical
                cases level with
                | succ level =>
                    exact absurd canonical (by simp [iterDrop])
                | zero =>
                    simp only [iterDrop_zero] at canonical
                    exact absurd canonical.symm (escape.1 _ _ _)
      | @boundaryCollection sourceBound targetBound sourceAvailable thinning
          outer collectionType elements rest sourceType currentRejected
          oppositeChoice oppositeSelected certified certifies =>
          exact absurd oppositeSelected (fun selected =>
            rho_boundaryCollection_choices_absurd color targetFree targetBound
              collectionType elements _ selected currentRejected)
