import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryDescent
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalScopeCollapse

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryLeafDichotomyProbe
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryExposureClosure

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

structure RhoBVarTowerSource
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (level index : Nat) : Type where
  sourceIndex : Nat
  index_eq : thinning.embedIndexAt 0 sourceIndex = index
  abstractCanonical :
    canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
        plan.abstractPattern =
      iterDrop rhoReflectivePresentation.toReflectivePresentationDecl level
        (.bvar sourceIndex)

theorem canonicalize_iterDrop_bvar (level index : Nat) :
    canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
        (iterDrop rhoReflectivePresentation.toReflectivePresentationDecl level
          (.bvar index)) =
      iterDrop rhoReflectivePresentation.toReflectivePresentationDecl level
        (.bvar index) := by
  induction level with
  | zero => simp [iterDrop, canonicalize]
  | succ level inner =>
      rw [iterDrop, canonicalize_apply_of_ne_quote _ auth_dropNeQuote,
        List.map_cons, List.map_nil, inner]

theorem iterDrop_bvar_ne_unit (level index : Nat) :
    iterDrop rhoReflectivePresentation.toReflectivePresentationDecl level
        (.bvar index) ≠
      .apply rhoReflectivePresentation.toReflectivePresentationDecl.parallelUnitConstructor
        [] := by
  cases level with
  | zero => simp [iterDrop]
  | succ level => simp [iterDrop, auth_dropConstructor]

theorem iterDrop_bvar_ne_parallel (level index : Nat)
    (nested : List Pattern) :
    iterDrop rhoReflectivePresentation.toReflectivePresentationDecl level
        (.bvar index) ≠
      .collection rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
        nested none := by
  cases level <;> simp [iterDrop]

/-- The whole-language rule behind a colour-static parallel unit is rho's
authored zero, with the colour image of `Proc` as category. -/
theorem rho_costWhole_rule_category_of_unitWire
    (color : CostStaticColor) {rule : GrammarRule}
    (membership : rule ∈ rhoCIGSLT.costWholeLanguage.terms)
    (labelEq : rule.label = (color.symbols rhoCIGSLT).constructor "PZero") :
    TypeExpr.base rule.category =
      mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc") := by
  cases color with
  | base =>
      have labelRendered :
          (rhoCIGSLT.materializeDeclaredCostConstructor
            ⟨CostConstructor.base ⟨rhoCalc.terms[0],
                List.getElem_mem (by simp [rhoCalc])⟩, True.intro⟩).label =
            (CostStaticColor.symbols rhoCIGSLT .base).constructor "PZero" := by
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
            ⟨CostConstructor.wrapped ⟨rhoCalc.terms[0],
                List.getElem_mem (by simp [rhoCalc])⟩,
              rhoZero_mem_wrappedConstructors⟩).label =
            (CostStaticColor.symbols rhoCIGSLT .wrapped).constructor "PZero" := by
        simp [CIGSLT.materializeDeclaredCostConstructor, costWrappedConstructor,
          rhoCalc, CostStaticColor.symbols, costWrappedStaticSymbols]
      have materialized :=
        CIGSLT.materializeDeclaredCostConstructor_eq_of_mem_of_label rhoCIGSLT
          rule membership _ (labelRendered.trans labelEq.symm)
      subst rule
      simp [CIGSLT.materializeDeclaredCostConstructor, costWrappedConstructor,
        rhoCalc, mapTypeExpr, CostStaticColor.symbols,
        costWrappedStaticSymbols, rho_interactingSort_name]

theorem rho_process_collection_choice_sourceElementType
    (color : CostStaticColor) {targetFree : FreeTypeContext}
    {targetBound : List TypeExpr} {collectionType : CollType}
    {elements : List Pattern} (choice : CostCollectionTypingChoice)
    (selected : choice ∈ costStaticCollectionTypingChoices rhoCIGSLT color
      targetFree targetBound collectionType elements
      (mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc"))) :
    choice.sourceElementType = .base "Proc" := by
  unfold costStaticCollectionTypingChoices at selected
  rw [decodeCostStaticTypeExpr_mapTypeExpr] at selected
  dsimp only at selected
  rw [mem_bareCostStaticCollectionTypingChoices_iff] at selected
  obtain ⟨rule, sourceElementType, choiceEq, membership, _wrapped,
    elementTypeResult, _checked⟩ := selected
  subst choice
  have shape := (WellSorted.bareCollectionElementType?_eq_some_iff
    rule collectionType (.base "Proc") sourceElementType).mp elementTypeResult
  simp only [rhoCIGSLT] at membership
  change rule ∈ rhoCalc.terms at membership
  simp only [rhoCalc, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [TypeExpr.name, TypeExpr.proc, TypeExpr.bag, TypeExpr.funType,
      TypeExpr.baseType] at shape
  exact shape.2.symm

theorem rhoBVarTowerSource_sameColor
    {color : CostStaticColor} {targetFree : FreeTypeContext} :
    ∀ (fuel : Nat) {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType)
      (level index : Nat),
      sizeOf pattern ≤ fuel →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl) pattern =
        iterDrop
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl) level
          (.bvar index) →
      Nonempty (RhoBVarTowerSource plan level index) := by
  intro fuel
  induction fuel with
  | zero =>
      intro sourceBound targetBound thinning sourceAvailable outer pattern
        sourceType plan level index measure canonical
      exact absurd measure (by cases pattern <;> simp)
  | succ fuel inductionHypothesis =>
      intro sourceBound targetBound thinning sourceAvailable outer pattern
        sourceType plan level index measure canonical
      cases plan with
      | bvar sourceIndex lookup correspondence availableScope =>
          cases level with
          | succ level => simp [canonicalize, iterDrop] at canonical
          | zero =>
              simp only [canonicalize, iterDrop_zero, Pattern.bvar.injEq]
                at canonical
              have embedded :=
                thinning.toTargetIndex_of_toSourceIndex?_eq_some correspondence
              exact ⟨
                { sourceIndex := sourceIndex
                  index_eq := by
                    rw [← canonical]
                    simpa [CostStaticBinderThinning.embedIndexAt] using embedded
                  abstractCanonical := by
                    simp [CostStaticRegionPlan.abstractPattern, iterDrop,
                      canonicalize] }⟩
      | fvar lookup =>
          cases level <;> simp [canonicalize, iterDrop] at canonical
      | lambda bodyPlan =>
          cases level <;> simp [canonicalize, iterDrop] at canonical
      | multiLambda bodyPlan =>
          cases level <;> simp [canonicalize, iterDrop] at canonical
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
          cases level with
          | zero =>
              simp only [iterDrop_zero] at canonical
              exact absurd canonical
                (boundaryHead_canonicalize_ne_bvar declared rendered outsideCurrent)
          | succ level =>
              rw [canonAp] at canonical
              have wireEq := (Pattern.apply.inj canonical).1
              have decodedNone := decodeDeclaredCostStaticConstructor_render_of_role_ne
                rhoCIGSLT declared color outsideCurrent
              rw [rendered, wireEq, decodeDeclared_drop] at decodedNone
              simp at decodedNone
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
          · have labelQuote : preimage.sourceConstructor.1.label = "NQuote" := by
              apply costStaticColor_constructor_inj (color := color)
              rw [← wireForm, quoteHead, rhoDecl_quoteConstructor]
            rw [canonicalize_apply_eq_finish, quoteHead] at canonical
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
                      (level + 1) (.bvar index) := by
                cases arguments with
                | nil => simp at mappedEq
                | cons head tail =>
                    cases tail with
                    | nil =>
                        refine ⟨head, rfl, ?_⟩
                        have headEq : canonicalize
                            (costStaticReflectivePresentationDecl rhoCIGSLT color
                              rhoReflectivePresentation.toReflectivePresentationDecl) head =
                            .apply (costStaticReflectivePresentationDecl rhoCIGSLT color
                              rhoReflectivePresentation.toReflectivePresentationDecl
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
                have measure' : sizeOf (Pattern.apply
                    (costStaticReflectivePresentationDecl rhoCIGSLT color
                      rhoReflectivePresentation.toReflectivePresentationDecl
                      ).quoteConstructor [argument]) ≤ fuel + 1 := by
                  simpa [quoteHead] using measure
                omega
              obtain ⟨child⟩ := inductionHypothesis active.head
                (level + 1) index measureChild canonArgument
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
              exact ⟨
                { sourceIndex := child.sourceIndex
                  index_eq := child.index_eq
                  abstractCanonical := by
                    simp only [CostStaticRegionPlan.abstractPattern,
                      active.abstracts_eq, beforeNil, afterNil, List.nil_append,
                      labelQuote]
                    change canonicalize
                        rhoReflectivePresentation.toReflectivePresentationDecl
                        (.apply
                          rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor
                          [active.head.abstractPattern]) = _
                    rw [canonicalize_apply_eq_finish, List.map_cons, List.map_nil,
                      child.abstractCanonical]
                    simp [finishNormalizeReflectiveApply, iterDrop] }⟩
            · rw [resultEq] at canonical
              cases level with
              | zero => simp [iterDrop] at canonical
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
            | zero => simp [iterDrop] at canonical
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
                        level (.bvar index) := by
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
                obtain ⟨child⟩ := inductionHypothesis active.head level index
                  measureChild canonArgument
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
                exact ⟨
                  { sourceIndex := child.sourceIndex
                    index_eq := child.index_eq
                    abstractCanonical := by
                      simp only [CostStaticRegionPlan.abstractPattern,
                        active.abstracts_eq, beforeNil, afterNil,
                        List.nil_append, labelDrop]
                      rw [canonicalize_apply_of_ne_quote _ (by decide),
                        List.map_cons, List.map_nil, child.abstractCanonical]
                      rfl }⟩
      | collection choice selected children =>
          rename_i collectionType elements rest
          cases rest with
          | some restName =>
              rw [canonicalize_collection_rest] at canonical
              cases level <;> simp [iterDrop] at canonical
          | none =>
              by_cases parallelType : collectionType =
                  (costStaticReflectivePresentationDecl rhoCIGSLT color
                    rhoReflectivePresentation.toReflectivePresentationDecl
                    ).parallelCollection
              · rw [parallelType] at canonical
                have notUnit : iterDrop
                      (costStaticReflectivePresentationDecl rhoCIGSLT color
                        rhoReflectivePresentation.toReflectivePresentationDecl)
                      level (.bvar index) ≠
                    .apply
                      (costStaticReflectivePresentationDecl rhoCIGSLT color
                        rhoReflectivePresentation.toReflectivePresentationDecl
                        ).parallelUnitConstructor [] := by
                  cases level with
                  | zero => simp [iterDrop]
                  | succ level => simp [iterDrop]
                have notParallelResult : ∀ nested,
                    iterDrop
                        (costStaticReflectivePresentationDecl rhoCIGSLT color
                          rhoReflectivePresentation.toReflectivePresentationDecl)
                        level (.bvar index) ≠
                      .collection
                        (costStaticReflectivePresentationDecl rhoCIGSLT color
                          rhoReflectivePresentation.toReflectivePresentationDecl
                          ).parallelCollection nested none := by
                  intro nested
                  cases level <;> simp [iterDrop]
                obtain ⟨element, elementMem, elementCanonical⟩ :=
                  exists_member_of_parallel_collapse _ canonical notUnit
                    notParallelResult
                obtain ⟨before, after, elementsEq⟩ :=
                  List.mem_iff_append.mp elementMem
                obtain ⟨active, lenCert⟩ :=
                  elementPlan_activeAt_lenCert children elementsEq
                have measureChild : sizeOf element ≤ fuel := by
                  have elementBound := List.sizeOf_lt_of_mem elementMem
                  have spineBound : sizeOf elements < sizeOf
                      (Pattern.collection collectionType elements none) := by
                    simp_wf
                    omega
                  omega
                obtain ⟨child⟩ := inductionHypothesis active.head level index
                  measureChild elementCanonical
                have authParallel : collectionType =
                    rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection := by
                  rw [parallelType, rhoDeclC_parallelCollection_hashBag,
                    auth_parallelCollection]
                have spineBound : sizeOf elements < sizeOf
                    (Pattern.collection collectionType elements none) := by
                  simp_wf
                  omega
                have beforeUnits : ∀ b ∈ active.beforeAbstracts,
                    canonicalize rhoReflectivePresentation.toReflectivePresentationDecl b =
                      .apply rhoReflectivePresentation.toReflectivePresentationDecl.parallelUnitConstructor
                        [] := by
                  intro b bMem
                  obtain ⟨i, iLt, bAt⟩ := List.mem_iff_getElem.mp bMem
                  have beforeAt : active.beforeAbstracts[i]? = some b :=
                    List.getElem?_eq_some_iff.mpr ⟨iLt, bAt⟩
                  have absAt : children.abstractPatterns[i]? = some b := by
                    rw [active.abstracts_eq, List.getElem?_append_left iLt]
                    exact beforeAt
                  have iLtBefore : i < before.length := lenCert ▸ iLt
                  have elemsSome : elements[i]? = some before[i] := by
                    rw [elementsEq, List.getElem?_append_left iLtBefore]
                    exact List.getElem?_eq_getElem iLtBefore
                  obtain ⟨ou, siblingPlan, planAt⟩ :=
                    elementSpine_getElem?_abstracts color children i elemsSome
                  have bEq : b = siblingPlan.abstractPattern :=
                    Option.some.inj (absAt.symm.trans planAt)
                  subst bEq
                  have eUnit := sibling_unit_positional
                    (costStaticReflectivePresentationDecl rhoCIGSLT color
                      rhoReflectivePresentation.toReflectivePresentationDecl)
                    notUnit notParallelResult canonical elementsEq
                    elementCanonical (Or.inl (List.getElem_mem iLtBefore))
                  have measureE : sizeOf before[i] ≤ fuel := by
                    have eMem : before[i] ∈ elements := by
                      rw [elementsEq]
                      exact List.mem_append_left _ (List.getElem_mem iLtBefore)
                    have eBound := List.sizeOf_lt_of_mem eMem
                    omega
                  have tower := plan_abstract_iterDropUnit_of_iterDropUnit
                    color fuel siblingPlan 0 measureE (by simpa using eUnit)
                  simpa using tower
                have afterLen : active.afterAbstracts.length = after.length := by
                  have total := elementPlan_abstractPatterns_length color children
                  have lenAbs := congrArg List.length active.abstracts_eq
                  have lenEls := congrArg List.length elementsEq
                  simp only [List.length_append, List.length_cons] at lenAbs lenEls
                  omega
                have afterUnits : ∀ a ∈ active.afterAbstracts,
                    canonicalize rhoReflectivePresentation.toReflectivePresentationDecl a =
                      .apply rhoReflectivePresentation.toReflectivePresentationDecl.parallelUnitConstructor
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
                  obtain ⟨ou, siblingPlan, planAt⟩ :=
                    elementSpine_getElem?_abstracts color children
                      (active.beforeAbstracts.length + 1 + j) elemsSome
                  have aEq : a = siblingPlan.abstractPattern :=
                    Option.some.inj (absAt.symm.trans planAt)
                  subst aEq
                  have eUnit := sibling_unit_positional
                    (costStaticReflectivePresentationDecl rhoCIGSLT color
                      rhoReflectivePresentation.toReflectivePresentationDecl)
                    notUnit notParallelResult canonical elementsEq
                    elementCanonical (Or.inr (List.getElem_mem jLtAfter))
                  have measureE : sizeOf after[j] ≤ fuel := by
                    have eMem : after[j] ∈ elements := by
                      rw [elementsEq]
                      exact List.mem_append_right _
                        (List.mem_cons_of_mem _ (List.getElem_mem jLtAfter))
                    have eBound := List.sizeOf_lt_of_mem eMem
                    omega
                  have tower := plan_abstract_iterDropUnit_of_iterDropUnit
                    color fuel siblingPlan 0 measureE (by simpa using eUnit)
                  simpa using tower
                exact ⟨
                  { sourceIndex := child.sourceIndex
                    index_eq := child.index_eq
                    abstractCanonical := by
                      simp only [CostStaticRegionPlan.abstractPattern,
                        active.abstracts_eq, Option.map_none]
                      rw [canonicalize_collection_congr_canonical_slot
                        rhoReflectivePresentation.toReflectivePresentationDecl
                        collectionType none active.beforeAbstracts
                        active.afterAbstracts
                        (middle' := iterDrop
                          rhoReflectivePresentation.toReflectivePresentationDecl
                          level (.bvar child.sourceIndex))
                        (child.abstractCanonical.trans
                          (canonicalize_iterDrop_bvar _ _).symm)]
                      rw [canonicalize_collection_ct_transport _ authParallel]
                      exact canonicalize_parallel_units_around _ beforeUnits
                        afterUnits (canonicalize_iterDrop_bvar _ _)
                        (iterDrop_bvar_ne_unit _ _)
                        (fun nested => iterDrop_bvar_ne_parallel _ _ nested) }⟩
              · rw [canonicalize_collection_of_ne_parallel _ parallelType]
                  at canonical
                cases level <;> simp [iterDrop] at canonical
      | @boundaryCollection sourceBound targetBound sourceAvailable thinning
          outer collectionType elements rest sourceType currentRejected
          oppositeChoice oppositeSelected certified certifies =>
          exact absurd oppositeSelected (fun selected =>
            rho_boundaryCollection_choices_absurd color targetFree targetBound
              collectionType elements _ selected currentRejected)

structure RhoFVarTowerSource
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (level : Nat) (name : String) : Type where
  abstractCanonical :
    canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
        plan.abstractPattern =
      iterDrop rhoReflectivePresentation.toReflectivePresentationDecl level
        (.fvar (costRegionSourceVariableName name))

theorem rhoFVarTowerSource_sameColor
    {color : CostStaticColor} {targetFree : FreeTypeContext} :
    ∀ (fuel : Nat) {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType)
      (level : Nat) (name : String),
      sizeOf pattern ≤ fuel →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl) pattern =
        iterDrop
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl) level
          (.fvar name) →
      Nonempty (RhoFVarTowerSource plan level name) := by
  intro fuel
  induction fuel with
  | zero =>
      intro sourceBound targetBound thinning sourceAvailable outer pattern
        sourceType plan level name measure canonical
      exact absurd measure (by cases pattern <;> simp)
  | succ fuel inductionHypothesis =>
      intro sourceBound targetBound thinning sourceAvailable outer pattern
        sourceType plan level name measure canonical
      cases plan with
      | bvar sourceIndex lookup correspondence availableScope =>
          cases level <;> simp [canonicalize, iterDrop] at canonical
      | fvar lookup =>
          cases level with
          | succ level => simp [canonicalize, iterDrop] at canonical
          | zero =>
              simp only [canonicalize, iterDrop_zero, Pattern.fvar.injEq]
                at canonical
              exact ⟨
                { abstractCanonical := by
                    simp [CostStaticRegionPlan.abstractPattern, iterDrop,
                      canonicalize, canonical] }⟩
      | lambda bodyPlan =>
          cases level <;> simp [canonicalize, iterDrop] at canonical
      | multiLambda bodyPlan =>
          cases level <;> simp [canonicalize, iterDrop] at canonical
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
          cases level with
          | zero =>
              simp only [iterDrop_zero] at canonical
              exact absurd canonical
                (boundaryHead_canonicalize_ne_fvar declared rendered outsideCurrent)
          | succ level =>
              rw [canonAp] at canonical
              have wireEq := (Pattern.apply.inj canonical).1
              have decodedNone := decodeDeclaredCostStaticConstructor_render_of_role_ne
                rhoCIGSLT declared color outsideCurrent
              rw [rendered, wireEq, decodeDeclared_drop] at decodedNone
              simp at decodedNone
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
          · have labelQuote : preimage.sourceConstructor.1.label = "NQuote" := by
              apply costStaticColor_constructor_inj (color := color)
              rw [← wireForm, quoteHead, rhoDecl_quoteConstructor]
            rw [canonicalize_apply_eq_finish, quoteHead] at canonical
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
                      (level + 1) (.fvar name) := by
                cases arguments with
                | nil => simp at mappedEq
                | cons head tail =>
                    cases tail with
                    | nil =>
                        refine ⟨head, rfl, ?_⟩
                        have headEq : canonicalize
                            (costStaticReflectivePresentationDecl rhoCIGSLT color
                              rhoReflectivePresentation.toReflectivePresentationDecl) head =
                            .apply (costStaticReflectivePresentationDecl rhoCIGSLT color
                              rhoReflectivePresentation.toReflectivePresentationDecl
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
                have measure' : sizeOf (Pattern.apply
                    (costStaticReflectivePresentationDecl rhoCIGSLT color
                      rhoReflectivePresentation.toReflectivePresentationDecl
                      ).quoteConstructor [argument]) ≤ fuel + 1 := by
                  simpa [quoteHead] using measure
                omega
              obtain ⟨child⟩ := inductionHypothesis active.head
                (level + 1) name measureChild canonArgument
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
              exact ⟨
                { abstractCanonical := by
                    simp only [CostStaticRegionPlan.abstractPattern,
                      active.abstracts_eq, beforeNil, afterNil, List.nil_append,
                      labelQuote]
                    change canonicalize
                        rhoReflectivePresentation.toReflectivePresentationDecl
                        (.apply
                          rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor
                          [active.head.abstractPattern]) = _
                    rw [canonicalize_apply_eq_finish, List.map_cons, List.map_nil,
                      child.abstractCanonical]
                    simp [finishNormalizeReflectiveApply, iterDrop] }⟩
            · rw [resultEq] at canonical
              cases level with
              | zero => simp [iterDrop] at canonical
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
            | zero => simp [iterDrop] at canonical
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
                        level (.fvar name) := by
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
                obtain ⟨child⟩ := inductionHypothesis active.head level name
                  measureChild canonArgument
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
                exact ⟨
                  { abstractCanonical := by
                      simp only [CostStaticRegionPlan.abstractPattern,
                        active.abstracts_eq, beforeNil, afterNil,
                        List.nil_append, labelDrop]
                      rw [canonicalize_apply_of_ne_quote _ (by decide),
                        List.map_cons, List.map_nil, child.abstractCanonical]
                      rfl }⟩
      | collection choice selected children =>
          rename_i collectionType elements rest
          cases rest with
          | some restName =>
              rw [canonicalize_collection_rest] at canonical
              cases level <;> simp [iterDrop] at canonical
          | none =>
              by_cases parallelType : collectionType =
                  (costStaticReflectivePresentationDecl rhoCIGSLT color
                    rhoReflectivePresentation.toReflectivePresentationDecl
                    ).parallelCollection
              · rw [parallelType] at canonical
                have notUnit : iterDrop
                      (costStaticReflectivePresentationDecl rhoCIGSLT color
                        rhoReflectivePresentation.toReflectivePresentationDecl)
                      level (.fvar name) ≠
                    .apply
                      (costStaticReflectivePresentationDecl rhoCIGSLT color
                        rhoReflectivePresentation.toReflectivePresentationDecl
                        ).parallelUnitConstructor [] := by
                  cases level with
                  | zero => simp [iterDrop]
                  | succ level => simp [iterDrop]
                have notParallelResult : ∀ nested,
                    iterDrop
                        (costStaticReflectivePresentationDecl rhoCIGSLT color
                          rhoReflectivePresentation.toReflectivePresentationDecl)
                        level (.fvar name) ≠
                      .collection
                        (costStaticReflectivePresentationDecl rhoCIGSLT color
                          rhoReflectivePresentation.toReflectivePresentationDecl
                          ).parallelCollection nested none := by
                  intro nested
                  cases level <;> simp [iterDrop]
                obtain ⟨element, elementMem, elementCanonical⟩ :=
                  exists_member_of_parallel_collapse _ canonical notUnit
                    notParallelResult
                obtain ⟨before, after, elementsEq⟩ :=
                  List.mem_iff_append.mp elementMem
                obtain ⟨active, lenCert⟩ :=
                  elementPlan_activeAt_lenCert children elementsEq
                have measureChild : sizeOf element ≤ fuel := by
                  have elementBound := List.sizeOf_lt_of_mem elementMem
                  have spineBound : sizeOf elements < sizeOf
                      (Pattern.collection collectionType elements none) := by
                    simp_wf
                    omega
                  omega
                obtain ⟨child⟩ := inductionHypothesis active.head level name
                  measureChild elementCanonical
                have authParallel : collectionType =
                    rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection := by
                  rw [parallelType, rhoDeclC_parallelCollection_hashBag,
                    auth_parallelCollection]
                have spineBound : sizeOf elements < sizeOf
                    (Pattern.collection collectionType elements none) := by
                  simp_wf
                  omega
                have beforeUnits : ∀ b ∈ active.beforeAbstracts,
                    canonicalize rhoReflectivePresentation.toReflectivePresentationDecl b =
                      .apply rhoReflectivePresentation.toReflectivePresentationDecl.parallelUnitConstructor
                        [] := by
                  intro b bMem
                  obtain ⟨i, iLt, bAt⟩ := List.mem_iff_getElem.mp bMem
                  have beforeAt : active.beforeAbstracts[i]? = some b :=
                    List.getElem?_eq_some_iff.mpr ⟨iLt, bAt⟩
                  have absAt : children.abstractPatterns[i]? = some b := by
                    rw [active.abstracts_eq, List.getElem?_append_left iLt]
                    exact beforeAt
                  have iLtBefore : i < before.length := lenCert ▸ iLt
                  have elemsSome : elements[i]? = some before[i] := by
                    rw [elementsEq, List.getElem?_append_left iLtBefore]
                    exact List.getElem?_eq_getElem iLtBefore
                  obtain ⟨ou, siblingPlan, planAt⟩ :=
                    elementSpine_getElem?_abstracts color children i elemsSome
                  have bEq : b = siblingPlan.abstractPattern :=
                    Option.some.inj (absAt.symm.trans planAt)
                  subst bEq
                  have eUnit := sibling_unit_positional
                    (costStaticReflectivePresentationDecl rhoCIGSLT color
                      rhoReflectivePresentation.toReflectivePresentationDecl)
                    notUnit notParallelResult canonical elementsEq
                    elementCanonical (Or.inl (List.getElem_mem iLtBefore))
                  have measureE : sizeOf before[i] ≤ fuel := by
                    have eMem : before[i] ∈ elements := by
                      rw [elementsEq]
                      exact List.mem_append_left _ (List.getElem_mem iLtBefore)
                    have eBound := List.sizeOf_lt_of_mem eMem
                    omega
                  have tower := plan_abstract_iterDropUnit_of_iterDropUnit
                    color fuel siblingPlan 0 measureE (by simpa using eUnit)
                  simpa using tower
                have afterLen : active.afterAbstracts.length = after.length := by
                  have total := elementPlan_abstractPatterns_length color children
                  have lenAbs := congrArg List.length active.abstracts_eq
                  have lenEls := congrArg List.length elementsEq
                  simp only [List.length_append, List.length_cons] at lenAbs lenEls
                  omega
                have afterUnits : ∀ a ∈ active.afterAbstracts,
                    canonicalize rhoReflectivePresentation.toReflectivePresentationDecl a =
                      .apply rhoReflectivePresentation.toReflectivePresentationDecl.parallelUnitConstructor
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
                  obtain ⟨ou, siblingPlan, planAt⟩ :=
                    elementSpine_getElem?_abstracts color children
                      (active.beforeAbstracts.length + 1 + j) elemsSome
                  have aEq : a = siblingPlan.abstractPattern :=
                    Option.some.inj (absAt.symm.trans planAt)
                  subst aEq
                  have eUnit := sibling_unit_positional
                    (costStaticReflectivePresentationDecl rhoCIGSLT color
                      rhoReflectivePresentation.toReflectivePresentationDecl)
                    notUnit notParallelResult canonical elementsEq
                    elementCanonical (Or.inr (List.getElem_mem jLtAfter))
                  have measureE : sizeOf after[j] ≤ fuel := by
                    have eMem : after[j] ∈ elements := by
                      rw [elementsEq]
                      exact List.mem_append_right _
                        (List.mem_cons_of_mem _ (List.getElem_mem jLtAfter))
                    have eBound := List.sizeOf_lt_of_mem eMem
                    omega
                  have tower := plan_abstract_iterDropUnit_of_iterDropUnit
                    color fuel siblingPlan 0 measureE (by simpa using eUnit)
                  simpa using tower
                exact ⟨
                  { abstractCanonical := by
                      simp only [CostStaticRegionPlan.abstractPattern,
                        active.abstracts_eq, Option.map_none]
                      rw [canonicalize_collection_congr_canonical_slot
                        rhoReflectivePresentation.toReflectivePresentationDecl
                        collectionType none active.beforeAbstracts
                        active.afterAbstracts
                        (middle' := iterDrop
                          rhoReflectivePresentation.toReflectivePresentationDecl
                          level (.fvar (costRegionSourceVariableName name)))
                        (child.abstractCanonical.trans
                          (canonicalize_iterDrop_fvar _ _).symm)]
                      rw [canonicalize_collection_ct_transport _ authParallel]
                      exact canonicalize_parallel_units_around _ beforeUnits
                        afterUnits (canonicalize_iterDrop_fvar _ _)
                        (iterDrop_fvar_ne_unit _ _)
                        (fun nested => iterDrop_fvar_ne_parallel _ _ nested) }⟩
              · rw [canonicalize_collection_of_ne_parallel _ parallelType]
                  at canonical
                cases level <;> simp [iterDrop] at canonical
      | @boundaryCollection sourceBound targetBound sourceAvailable thinning
          outer collectionType elements rest sourceType currentRejected
          oppositeChoice oppositeSelected certified certifies =>
          exact absurd oppositeSelected (fun selected =>
            rho_boundaryCollection_choices_absurd color targetFree targetBound
              collectionType elements _ selected currentRejected)

inductive RhoProcBVarTarget where
  | unit
  | bvar (index : Nat)
  | fvar (name : String)

def RhoProcBVarTarget.pattern (color : CostStaticColor) :
    RhoProcBVarTarget → Pattern
  | .unit =>
      .apply (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        ).parallelUnitConstructor []
  | .bvar index => .bvar index
  | .fvar name => .fvar name

def castCostStaticRegionPlanSourceType
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {leftType rightType : TypeExpr}
    (typeEq : leftType = rightType)
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern leftType) :
    CostStaticRegionPlan source color targetFree sourceBound targetBound
      thinning sourceAvailable outer pattern rightType := by
  subst rightType
  exact plan

@[simp]
theorem castCostStaticRegionPlanSourceType_abstractPattern
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {leftType rightType : TypeExpr}
    (typeEq : leftType = rightType)
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern leftType) :
    (castCostStaticRegionPlanSourceType typeEq plan).abstractPattern =
      plan.abstractPattern := by
  subst rightType
  rfl

@[simp]
theorem castCostStaticRegionPlanSourceType_boundaryTable_entries
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {leftType rightType : TypeExpr}
    (typeEq : leftType = rightType)
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern leftType) :
    (castCostStaticRegionPlanSourceType typeEq plan).boundaryTable.entries =
      plan.boundaryTable.entries := by
  subst rightType
  rfl

theorem boundaryApplication_flipTarget_absurd
    (color : CostStaticColor) {targetFree : FreeTypeContext}
    {sourceAvailable : List TypeExpr} {wireName : String}
    {arguments : List Pattern}
    (declared : rhoCIGSLT.DeclaredCostConstructor)
    (_rendered : rhoCIGSLT.renderDeclaredCostConstructor declared = wireName)
    (certified : CertifiedCostRegionBoundary rhoCIGSLT color targetFree
      sourceAvailable
      (mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc"))
      (.apply wireName arguments))
    (target : RhoProcBVarTarget)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color.flip
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply wireName arguments) = target.pattern color.flip) : False := by
  let flipDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color.flip rhoReflectivePresentation.toReflectivePresentationDecl
  by_cases quoteHead : wireName = flipDeclaration.quoteConstructor
  · have typed : HasType rhoCIGSLT.costWholeLanguage targetFree
        sourceAvailable (.apply wireName arguments)
        (mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc")) := by
      simpa only [certified.content_eq, certified.targetSupport_eq,
        certified.targetType_eq] using certified.typed.contentTyped
    obtain ⟨rule, ruleMembership, labelEquality, _notBare,
        typeEquality, _argumentsTyped⟩ :=
      WellSorted.hasType_apply_inversion typed
    have categoryForm := rho_costWhole_rule_category_of_quoteWire color.flip
      ruleMembership
      (labelEquality.symm.trans
        (quoteHead.trans (rhoDecl_quoteConstructor color.flip)))
    have cross : mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc") =
        mapTypeExpr (color.flip.symbols rhoCIGSLT) (.base "Name") :=
      typeEquality.trans categoryForm
    exact mapTypeExpr_cross_proc_ne color "Name" (by decide) cross
  · rw [canonicalize_apply_of_ne_quote _ quoteHead] at canonical
    cases target with
    | bvar index => exact Pattern.noConfusion canonical
    | fvar name => exact Pattern.noConfusion canonical
    | unit =>
        have wireEq := (Pattern.apply.inj canonical).1
        have typed : HasType rhoCIGSLT.costWholeLanguage targetFree
            sourceAvailable (.apply wireName arguments)
            (mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc")) := by
          simpa only [certified.content_eq, certified.targetSupport_eq,
            certified.targetType_eq] using certified.typed.contentTyped
        obtain ⟨rule, ruleMembership, labelEquality, _notBare,
            typeEquality, _argumentsTyped⟩ :=
          WellSorted.hasType_apply_inversion typed
        have categoryForm := rho_costWhole_rule_category_of_unitWire
          color.flip ruleMembership
          (labelEquality.symm.trans
            (wireEq.trans (rhoDecl_unitConstructor color.flip)))
        have cross : mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc") =
            mapTypeExpr (color.flip.symbols rhoCIGSLT) (.base "Proc") :=
          typeEquality.trans categoryForm
        exact mapTypeExpr_flipProc_ne color (.base "Proc") cross.symm

theorem currentApplication_flipTarget_absurd
    (color : CostStaticColor) {wireName : String}
    {arguments : List Pattern}
    (declared : rhoCIGSLT.DeclaredCostConstructor)
    (rendered : rhoCIGSLT.renderDeclaredCostConstructor declared = wireName)
    (current : rhoCIGSLT.declaredCostConstructorRole declared = .static color)
    (target : RhoProcBVarTarget)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color.flip
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply wireName arguments) = target.pattern color.flip) : False := by
  let flipDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color.flip rhoReflectivePresentation.toReflectivePresentationDecl
  by_cases quoteHead : wireName = flipDeclaration.quoteConstructor
  · have flipRole := rhoRole_static_of_render_eq_quote declared
      (rendered.trans quoteHead)
    rw [current] at flipRole
    exact CostStaticColor.ne_flip color (CIGSLT.GeneratedCostConstructorRole.static.inj flipRole)
  · rw [canonicalize_apply_of_ne_quote _ quoteHead] at canonical
    cases target with
    | bvar index => exact Pattern.noConfusion canonical
    | fvar name => exact Pattern.noConfusion canonical
    | unit =>
        have wireEq := (Pattern.apply.inj canonical).1
        have flipRole := rhoRole_static_of_render_eq_parallelUnit declared
          (rendered.trans wireEq)
        rw [current] at flipRole
        exact CostStaticColor.ne_flip color
          (CIGSLT.GeneratedCostConstructorRole.static.inj flipRole)

theorem rhoProc_flipTarget_transfer
    {color : CostStaticColor} {targetFree : FreeTypeContext} :
    ∀ (fuel : Nat) {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {pattern : Pattern}
      (_plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern (.base "Proc"))
      (target : RhoProcBVarTarget),
      sizeOf pattern ≤ fuel →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color.flip
            rhoReflectivePresentation.toReflectivePresentationDecl) pattern =
        target.pattern color.flip →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl) pattern =
        target.pattern color := by
  intro fuel
  induction fuel with
  | zero =>
      intro sourceBound targetBound thinning sourceAvailable outer pattern
        plan target measure canonical
      exact absurd measure (by cases pattern <;> simp)
  | succ fuel inductionHypothesis =>
      intro sourceBound targetBound thinning sourceAvailable outer pattern
        plan target measure canonical
      generalize sourceTypeEq : (TypeExpr.base "Proc") = sourceType at plan
      cases plan with
      | bvar sourceIndex lookup correspondence availableScope =>
          cases target with
          | unit => simp [RhoProcBVarTarget.pattern, canonicalize] at canonical
          | fvar name =>
              simp [RhoProcBVarTarget.pattern, canonicalize] at canonical
          | bvar index =>
              simp only [RhoProcBVarTarget.pattern, canonicalize,
                Pattern.bvar.injEq] at canonical ⊢
              exact canonical
      | fvar lookup =>
          cases target with
          | unit => simp [RhoProcBVarTarget.pattern, canonicalize] at canonical
          | bvar index =>
              simp [RhoProcBVarTarget.pattern, canonicalize] at canonical
          | fvar name =>
              simpa [RhoProcBVarTarget.pattern, canonicalize] using canonical
      | boundaryApplication declared rendered outsideCurrent certified certifies =>
          subst sourceType
          exact False.elim (boundaryApplication_flipTarget_absurd color
            declared rendered certified target canonical)
      | application declared rendered current preimage notBare children =>
          exact False.elim (currentApplication_flipTarget_absurd color
            declared rendered current target canonical)
      | lambda bodyPlan => exact TypeExpr.noConfusion sourceTypeEq
      | multiLambda bodyPlan => exact TypeExpr.noConfusion sourceTypeEq
      | collection choice selected children =>
          subst sourceType
          rename_i collectionType elements rest
          cases rest with
          | some restName =>
              rw [canonicalize_collection_rest] at canonical
              cases target <;>
                simp [RhoProcBVarTarget.pattern] at canonical
          | none =>
              let flipDeclaration := costStaticReflectivePresentationDecl
                rhoCIGSLT color.flip
                  rhoReflectivePresentation.toReflectivePresentationDecl
              let ownDeclaration := costStaticReflectivePresentationDecl
                rhoCIGSLT color
                  rhoReflectivePresentation.toReflectivePresentationDecl
              by_cases parallelType : collectionType =
                  flipDeclaration.parallelCollection
              · rw [parallelType] at canonical
                have elementType := rho_process_collection_choice_sourceElementType
                  color choice selected
                have ownParallel : collectionType =
                    ownDeclaration.parallelCollection := by
                  calc
                    collectionType = flipDeclaration.parallelCollection :=
                      parallelType
                    _ = .hashBag := by
                      exact rhoDeclC_parallelCollection_hashBag color.flip
                    _ = ownDeclaration.parallelCollection := by
                      exact (rhoDeclC_parallelCollection_hashBag color).symm
                cases target with
                | unit =>
                    have flipUnits := all_units_of_collapsed_unit
                      flipDeclaration canonical
                    have ownUnits : ∀ element ∈ elements,
                        canonicalize ownDeclaration element =
                          .apply ownDeclaration.parallelUnitConstructor [] := by
                      intro element membership
                      obtain ⟨i, iLt, atIndex⟩ := List.mem_iff_getElem.mp membership
                      have elemsSome : elements[i]? = some element :=
                        List.getElem?_eq_some_iff.mpr ⟨iLt, atIndex⟩
                      obtain ⟨ou, elementPlan, _planAt⟩ :=
                        elementSpine_getElem?_abstracts color children i elemsSome
                      let elementPlanProc := elementType ▸ elementPlan
                      have measureElement : sizeOf element ≤ fuel := by
                        have elementBound := List.sizeOf_lt_of_mem membership
                        have spineBound : sizeOf elements < sizeOf
                            (Pattern.collection collectionType elements none) := by
                          simp_wf
                          omega
                        omega
                      exact inductionHypothesis elementPlanProc .unit measureElement
                        (flipUnits element membership)
                    rw [ownParallel, canonicalize_parallel]
                    have contentsNil := parallelContents_units_eq_nil
                      ownDeclaration elements ownUnits
                    rw [normalizeParallelElements_eq_sort_parallelContents,
                      contentsNil]
                    rw [show Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns [] =
                        [] from List.perm_nil.mp (sortPatterns_perm [])]
                    rfl
                | bvar index =>
                    have notUnit : Pattern.bvar index ≠
                        .apply flipDeclaration.parallelUnitConstructor [] := by
                      simp
                    have notParallel : ∀ nested, Pattern.bvar index ≠
                        .collection flipDeclaration.parallelCollection nested none := by
                      simp
                    obtain ⟨before, contributor, after, elementsEq,
                        contributorFlip, beforeFlipUnits, afterFlipUnits⟩ :=
                      exists_parallel_contributor_with_unit_siblings
                        flipDeclaration notUnit notParallel canonical
                    obtain ⟨active, lenCert⟩ :=
                      elementPlan_activeAt_lenCert children elementsEq
                    let contributorPlan : CostStaticRegionPlan rhoCIGSLT color
                        targetFree sourceBound targetBound thinning
                        sourceAvailable _ contributor (.base "Proc") :=
                      castCostStaticRegionPlanSourceType elementType active.head
                    have spineBound : sizeOf elements < sizeOf
                        (Pattern.collection collectionType elements none) := by
                      simp_wf
                      omega
                    have contributorMem : contributor ∈ elements := by
                      rw [elementsEq]
                      exact List.mem_append_right _ (List.mem_cons_self)
                    have measureContributor : sizeOf contributor ≤ fuel := by
                      have contributorBound := List.sizeOf_lt_of_mem contributorMem
                      omega
                    have contributorOwn := inductionHypothesis contributorPlan
                      (.bvar index) measureContributor contributorFlip
                    have beforeOwnUnits : ∀ element ∈ before,
                        canonicalize ownDeclaration element =
                          .apply ownDeclaration.parallelUnitConstructor [] := by
                      intro element membership
                      obtain ⟨i, iLt, atIndex⟩ := List.mem_iff_getElem.mp membership
                      have elemsSome : elements[i]? = some element := by
                        rw [elementsEq, List.getElem?_append_left iLt]
                        exact List.getElem?_eq_some_iff.mpr ⟨iLt, atIndex⟩
                      obtain ⟨ou, elementPlan, _planAt⟩ :=
                        elementSpine_getElem?_abstracts color children i elemsSome
                      let elementPlanProc := elementType ▸ elementPlan
                      have elementMem : element ∈ elements := by
                        rw [elementsEq]
                        exact List.mem_append_left _ membership
                      have measureElement : sizeOf element ≤ fuel := by
                        have elementBound := List.sizeOf_lt_of_mem elementMem
                        omega
                      exact inductionHypothesis elementPlanProc .unit measureElement
                        (beforeFlipUnits element membership)
                    have afterOwnUnits : ∀ element ∈ after,
                        canonicalize ownDeclaration element =
                          .apply ownDeclaration.parallelUnitConstructor [] := by
                      intro element membership
                      obtain ⟨j, jLt, atIndex⟩ := List.mem_iff_getElem.mp membership
                      have elemsSome : elements[before.length + 1 + j]? =
                          some element := by
                        have transport := congrArg
                          (fun list => list[before.length + 1 + j]?)
                          elementsEq
                        rw [transport, List.getElem?_append_right (by omega),
                          show before.length + 1 + j - before.length = j + 1 by
                            omega,
                          List.getElem?_cons_succ]
                        exact List.getElem?_eq_some_iff.mpr ⟨jLt, atIndex⟩
                      obtain ⟨ou, elementPlan, _planAt⟩ :=
                        elementSpine_getElem?_abstracts color children
                          (before.length + 1 + j) elemsSome
                      let elementPlanProc := elementType ▸ elementPlan
                      have elementMem : element ∈ elements := by
                        rw [elementsEq]
                        exact List.mem_append_right _
                          (List.mem_cons_of_mem _ membership)
                      have measureElement : sizeOf element ≤ fuel := by
                        have elementBound := List.sizeOf_lt_of_mem elementMem
                        omega
                      exact inductionHypothesis elementPlanProc .unit measureElement
                        (afterFlipUnits element membership)
                    have contributorOwn' : canonicalize ownDeclaration contributor =
                        .bvar index := by
                      simpa [RhoProcBVarTarget.pattern, ownDeclaration] using
                        contributorOwn
                    rw [elementsEq]
                    rw [canonicalize_collection_congr_canonical_slot
                      ownDeclaration collectionType none before after
                      (middle' := .bvar index) (by
                        simpa [canonicalize] using contributorOwn')]
                    rw [canonicalize_collection_ct_transport _ ownParallel]
                    exact canonicalize_parallel_units_around ownDeclaration
                      beforeOwnUnits afterOwnUnits (by simp [canonicalize])
                      (by simp)
                      (by simp)
                | fvar name =>
                    have notUnit : Pattern.fvar name ≠
                        .apply flipDeclaration.parallelUnitConstructor [] := by
                      simp
                    have notParallel : ∀ nested, Pattern.fvar name ≠
                        .collection flipDeclaration.parallelCollection nested none := by
                      simp
                    obtain ⟨before, contributor, after, elementsEq,
                        contributorFlip, beforeFlipUnits, afterFlipUnits⟩ :=
                      exists_parallel_contributor_with_unit_siblings
                        flipDeclaration notUnit notParallel canonical
                    obtain ⟨active, lenCert⟩ :=
                      elementPlan_activeAt_lenCert children elementsEq
                    let contributorPlan : CostStaticRegionPlan rhoCIGSLT color
                        targetFree sourceBound targetBound thinning
                        sourceAvailable _ contributor (.base "Proc") :=
                      castCostStaticRegionPlanSourceType elementType active.head
                    have spineBound : sizeOf elements < sizeOf
                        (Pattern.collection collectionType elements none) := by
                      simp_wf
                      omega
                    have contributorMem : contributor ∈ elements := by
                      rw [elementsEq]
                      exact List.mem_append_right _ (List.mem_cons_self)
                    have measureContributor : sizeOf contributor ≤ fuel := by
                      have contributorBound := List.sizeOf_lt_of_mem contributorMem
                      omega
                    have contributorOwn := inductionHypothesis contributorPlan
                      (.fvar name) measureContributor contributorFlip
                    have beforeOwnUnits : ∀ element ∈ before,
                        canonicalize ownDeclaration element =
                          .apply ownDeclaration.parallelUnitConstructor [] := by
                      intro element membership
                      obtain ⟨i, iLt, atIndex⟩ := List.mem_iff_getElem.mp membership
                      have elemsSome : elements[i]? = some element := by
                        rw [elementsEq, List.getElem?_append_left iLt]
                        exact List.getElem?_eq_some_iff.mpr ⟨iLt, atIndex⟩
                      obtain ⟨ou, elementPlan, _planAt⟩ :=
                        elementSpine_getElem?_abstracts color children i elemsSome
                      let elementPlanProc := elementType ▸ elementPlan
                      have elementMem : element ∈ elements := by
                        rw [elementsEq]
                        exact List.mem_append_left _ membership
                      have measureElement : sizeOf element ≤ fuel := by
                        have elementBound := List.sizeOf_lt_of_mem elementMem
                        omega
                      exact inductionHypothesis elementPlanProc .unit measureElement
                        (beforeFlipUnits element membership)
                    have afterOwnUnits : ∀ element ∈ after,
                        canonicalize ownDeclaration element =
                          .apply ownDeclaration.parallelUnitConstructor [] := by
                      intro element membership
                      obtain ⟨j, jLt, atIndex⟩ := List.mem_iff_getElem.mp membership
                      have elemsSome : elements[before.length + 1 + j]? =
                          some element := by
                        have transport := congrArg
                          (fun list => list[before.length + 1 + j]?)
                          elementsEq
                        rw [transport, List.getElem?_append_right (by omega),
                          show before.length + 1 + j - before.length = j + 1 by
                            omega,
                          List.getElem?_cons_succ]
                        exact List.getElem?_eq_some_iff.mpr ⟨jLt, atIndex⟩
                      obtain ⟨ou, elementPlan, _planAt⟩ :=
                        elementSpine_getElem?_abstracts color children
                          (before.length + 1 + j) elemsSome
                      let elementPlanProc := elementType ▸ elementPlan
                      have elementMem : element ∈ elements := by
                        rw [elementsEq]
                        exact List.mem_append_right _
                          (List.mem_cons_of_mem _ membership)
                      have measureElement : sizeOf element ≤ fuel := by
                        have elementBound := List.sizeOf_lt_of_mem elementMem
                        omega
                      exact inductionHypothesis elementPlanProc .unit measureElement
                        (afterFlipUnits element membership)
                    have contributorOwn' : canonicalize ownDeclaration contributor =
                        .fvar name := by
                      simpa [RhoProcBVarTarget.pattern, ownDeclaration] using
                        contributorOwn
                    rw [elementsEq]
                    rw [canonicalize_collection_congr_canonical_slot
                      ownDeclaration collectionType none before after
                      (middle' := .fvar name) (by
                        simpa [canonicalize] using contributorOwn')]
                    rw [canonicalize_collection_ct_transport _ ownParallel]
                    exact canonicalize_parallel_units_around ownDeclaration
                      beforeOwnUnits afterOwnUnits (by simp [canonicalize])
                      (by simp)
                      (by simp)
              · rw [canonicalize_collection_of_ne_parallel _ parallelType]
                  at canonical
                cases target <;>
                  simp [RhoProcBVarTarget.pattern] at canonical
      | @boundaryCollection sourceBound targetBound sourceAvailable thinning
          outer collectionType elements rest sourceType currentRejected
          oppositeChoice oppositeSelected certified certifies =>
          exact absurd oppositeSelected (fun selected =>
            rho_boundaryCollection_choices_absurd color targetFree targetBound
              collectionType elements _ selected currentRejected)

structure RhoProcApplyBoundaryDescent
    {color declarationColor : CostStaticColor}
    {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern target : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType) :
    Type where
  payload : Pattern
  state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
    plan.abstractPattern
  contextCollapse :
    canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
        (state.skeletonContext.fill
          (.fvar (costRegionBoundaryVariableName
            state.certified.typed.boundary))) =
      .fvar (costRegionBoundaryVariableName state.certified.typed.boundary)
  entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
    [state.certified.typed] plan.boundaryTable.entries
  boundaryCanonical :
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        state.certified.typed.boundary.content = target
  boundarySupport : state.certified.typed.boundary.targetSupport =
    sourceAvailable
  boundaryType : state.certified.typed.boundary.targetType =
    mapTypeExpr (color.symbols rhoCIGSLT) sourceType

theorem rhoProc_canonicalize_flip_bvar_transfer
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern (.base "Proc"))
    (index : Nat)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color.flip
          rhoReflectivePresentation.toReflectivePresentationDecl) pattern =
      .bvar index) :
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) pattern =
      .bvar index := by
  exact rhoProc_flipTarget_transfer (sizeOf pattern) plan (.bvar index)
    (by omega) canonical

theorem rhoProc_canonicalize_flip_fvar_transfer
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern (.base "Proc"))
    (name : String)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color.flip
          rhoReflectivePresentation.toReflectivePresentationDecl) pattern =
      .fvar name) :
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) pattern =
      .fvar name := by
  exact rhoProc_flipTarget_transfer (sizeOf pattern) plan (.fvar name)
    (by omega) canonical

/-- A reached plan classified as a certified boundary cannot have a concrete
payload whose canonical form is a bare bound variable, in either declaration
colour.  Application boundaries are excluded by their retained reflective
scope certificate; collection boundaries are excluded by rho's cross-colour
collection gate. -/
theorem rho_boundaryPlan_canonicalize_ne_bvar
    {color declarationColor : CostStaticColor}
    {targetFree : FreeTypeContext}
    {sourceBound targetBound sourceAvailable : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (boundaryClass : plan.rootClass.IsCertifiedBoundary) (index : Nat) :
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        pattern ≠ .bvar index := by
  cases plan with
  | bvar => simp [CostStaticRegionPlan.rootClass,
      CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass
  | fvar => simp [CostStaticRegionPlan.rootClass,
      CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass
  | application =>
      simp [CostStaticRegionPlan.rootClass,
        CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass
  | lambda => simp [CostStaticRegionPlan.rootClass,
      CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass
  | multiLambda =>
      simp [CostStaticRegionPlan.rootClass,
        CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass
  | collection =>
      simp [CostStaticRegionPlan.rootClass,
        CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass
  | boundaryApplication declared rendered outsideCurrent certified certifies =>
      rename_i wireName arguments
      intro canonical
      let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
        declarationColor rhoReflectivePresentation.toReflectivePresentationDecl
      have collapsing : CollapsingRoot declaration
          (.apply wireName arguments) := by
        rcases eq_bvar_or_collapsingRoot_of_canonicalize_eq_bvar declaration
            canonical with shape | collapsing
        · exact absurd shape (by simp)
        · exact collapsing
      have quoteHead : wireName = declaration.quoteConstructor :=
        eq_quoteConstructor_of_collapsingRoot_apply declaration collapsing
      have scopeSafe : ReflectiveWellSorted.ReflectiveScopeSafeAt
          rhoCIGSLT.costWholeReflectionProfile sourceAvailable.length
          (.apply wireName arguments) := by
        simpa only [certified.content_eq, certified.targetSupport_eq] using
          certified.typed.contentReflectiveScopeSafe
      have safe := scopeSafe declaration
        (by
          simpa only [declaration] using
            CostHereditaryForeignBoundaryWitness.rhoDecl_mem_profile
              declarationColor)
      rw [quoteHead] at safe canonical
      exact (canonicalize_quote_ne_bvar_of_binderSafeAt declaration
        (Ne.symm
          (CostHereditaryForeignBoundaryWitness.rhoDecl_drop_ne_quote
            declarationColor)) sourceAvailable.length arguments index safe)
        canonical
  | boundaryCollection currentRejected oppositeChoice oppositeSelected
      certified certifies =>
      exact fun _ => absurd oppositeSelected (fun selected =>
        rho_boundaryCollection_choices_absurd color targetFree targetBound _ _ _
          selected currentRejected)

theorem rhoProc_applyBoundaryDescent
    {color declarationColor : CostStaticColor}
    {targetFree : FreeTypeContext} :
    ∀ (fuel : Nat) {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {pattern : Pattern}
      (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern (.base "Proc"))
      (target : Pattern),
      sizeOf pattern ≤ fuel →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl) pattern =
        target →
      RhoDescendEscape color target →
      target ≠ .apply
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).parallelUnitConstructor [] →
      Nonempty (RhoProcApplyBoundaryDescent
        (declarationColor := declarationColor) (target := target) plan) := by
  intro fuel
  induction fuel with
  | zero =>
      intro sourceBound targetBound thinning sourceAvailable outer pattern
        plan target measure canonical escape targetNeUnit
      exact absurd measure (by cases pattern <;> simp)
  | succ fuel inductionHypothesis =>
      intro sourceBound targetBound thinning sourceAvailable outer pattern
        plan target measure canonical escape targetNeUnit
      generalize sourceTypeEq : (TypeExpr.base "Proc") = sourceType at plan
      cases plan with
      | bvar sourceIndex lookup correspondence availableScope =>
          obtain ⟨_, wire, arguments, targetEq, decodedNone⟩ := escape
          rw [targetEq] at canonical
          simp [canonicalize] at canonical
      | fvar lookup =>
          obtain ⟨_, wire, arguments, targetEq, decodedNone⟩ := escape
          rw [targetEq] at canonical
          simp [canonicalize] at canonical
      | boundaryApplication declared rendered outsideCurrent certified certifies =>
          subst sourceType
          rename_i wireName arguments
          let state : CostStaticPlanStopped rhoCIGSLT color targetFree
              (.apply wireName arguments)
              (.fvar (costRegionBoundaryVariableName
                certified.typed.boundary)) :=
            { boundarySupport := _
              boundaryType := _
              content := _
              certified := certified
              certifies := certifies
              residual := .hole
              content_eq := rfl
              skeletonContext := .hole
              abstract_eq := by
                simp [OneHoleContext.fill] }
          exact ⟨
            { payload := .apply wireName arguments
              state := state
              contextCollapse := by
                simp [state, OneHoleContext.fill, canonicalize]
              entryEmbedding := CostStaticPlanEntryEmbedding.refl _
              boundaryCanonical := by
                show canonicalize _ certified.typed.boundary.content = target
                rw [certified.content_eq]
                exact canonical
              boundarySupport := certified.targetSupport_eq
              boundaryType := certified.targetType_eq }⟩
      | application declared rendered current preimage notBare children =>
          rename_i wireName arguments
          have wireForm : wireName =
              (color.symbols rhoCIGSLT).constructor
                preimage.sourceConstructor.1.label := by
            rw [← rendered,
              ← rhoCIGSLT.materializeDeclaredCostConstructor_label declared,
              preimage.labelMap]
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
              (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
                rhoReflectivePresentation.toReflectivePresentationDecl
                ).quoteConstructor
          · have quoteRole := rhoRole_static_of_render_eq_quote declared
              (rendered.trans quoteHead)
            rw [current] at quoteRole
            have colorEq : color = declarationColor :=
              CIGSLT.GeneratedCostConstructorRole.static.inj quoteRole
            subst declarationColor
            have sourceCategory :
                preimage.sourceConstructor.1.category = "Proc" :=
              (TypeExpr.base.inj sourceTypeEq).symm
            have processCategory :
                TypeExpr.base
                    (rhoCIGSLT.materializeDeclaredCostConstructor
                      declared).category =
                  mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc") := by
              rw [preimage.categoryMap, sourceCategory]
              rfl
            have quoteCategory := rho_costWhole_rule_category_of_quoteWire
              color (rhoCIGSLT.materializeDeclaredCostConstructor_mem declared)
              (by
                rw [rhoCIGSLT.materializeDeclaredCostConstructor_label,
                  rendered, quoteHead, rhoDecl_quoteConstructor])
            have cross : mapTypeExpr (color.symbols rhoCIGSLT)
                (.base "Proc") =
                mapTypeExpr (color.symbols rhoCIGSLT) (.base "Name") :=
              processCategory.symm.trans quoteCategory
            have impossible := mapTypeExpr_costStatic_injective rhoCIGSLT
              color cross
            exact absurd (TypeExpr.base.inj impossible) (by decide)
          · rw [canonicalize_apply_of_ne_quote _ quoteHead] at canonical
            obtain ⟨_, targetWire, targetArguments, targetEq, decodedNone⟩ :=
              escape
            rw [targetEq] at canonical
            have wireEq := (Pattern.apply.inj canonical).1
            rw [wireEq] at decodedSome
            rw [decodedSome] at decodedNone
            exact absurd decodedNone (by simp)
      | lambda bodyPlan => exact TypeExpr.noConfusion sourceTypeEq
      | multiLambda bodyPlan => exact TypeExpr.noConfusion sourceTypeEq
      | collection choice selected children =>
          subst sourceType
          rename_i collectionType elements rest
          cases rest with
          | some restName =>
              rw [canonicalize_collection_rest] at canonical
              exact absurd canonical.symm (escape.1 _ _ _)
          | none =>
              let declaration := costStaticReflectivePresentationDecl
                rhoCIGSLT declarationColor
                  rhoReflectivePresentation.toReflectivePresentationDecl
              by_cases parallelType : collectionType =
                  declaration.parallelCollection
              · rw [parallelType] at canonical
                have notParallel : ∀ nested, target ≠
                    .collection declaration.parallelCollection nested none := by
                  intro nested targetEq
                  exact escape.1 _ _ _ targetEq
                obtain ⟨before, contributor, after, elementsEq,
                    contributorCanonical, beforeUnitsRaw, afterUnitsRaw⟩ :=
                  exists_parallel_contributor_with_unit_siblings declaration
                    targetNeUnit notParallel canonical
                obtain ⟨active, lenCert⟩ :=
                  elementPlan_activeAt_lenCert children elementsEq
                have elementType := rho_process_collection_choice_sourceElementType
                  color choice selected
                let contributorPlan : CostStaticRegionPlan rhoCIGSLT color
                    targetFree sourceBound targetBound thinning sourceAvailable
                    _ contributor (.base "Proc") :=
                  castCostStaticRegionPlanSourceType elementType active.head
                have contributorMem : contributor ∈ elements := by
                  rw [elementsEq]
                  exact List.mem_append_right _ List.mem_cons_self
                have spineBound : sizeOf elements < sizeOf
                    (Pattern.collection collectionType elements none) := by
                  simp_wf
                  omega
                have measureContributor : sizeOf contributor ≤ fuel := by
                  have contributorBound :=
                    List.sizeOf_lt_of_mem contributorMem
                  omega
                obtain ⟨child⟩ := inductionHypothesis contributorPlan target
                  measureContributor contributorCanonical escape targetNeUnit
                let ownDeclaration := costStaticReflectivePresentationDecl
                  rhoCIGSLT color
                    rhoReflectivePresentation.toReflectivePresentationDecl
                have beforeUnits : ∀ b ∈ active.beforeAbstracts,
                  canonicalize
                      rhoReflectivePresentation.toReflectivePresentationDecl b =
                    .apply rhoReflectivePresentation.toReflectivePresentationDecl.parallelUnitConstructor
                      [] := by
                  intro b bMem
                  obtain ⟨i, iLt, bAt⟩ := List.mem_iff_getElem.mp bMem
                  have absAt : children.abstractPatterns[i]? = some b := by
                    rw [active.abstracts_eq, List.getElem?_append_left iLt]
                    exact List.getElem?_eq_some_iff.mpr ⟨iLt, bAt⟩
                  have iLtBefore : i < before.length := lenCert ▸ iLt
                  have elemsSome : elements[i]? = some before[i] := by
                    rw [elementsEq, List.getElem?_append_left iLtBefore]
                    exact List.getElem?_eq_getElem iLtBefore
                  obtain ⟨ou, siblingPlan, planAt⟩ :=
                    elementSpine_getElem?_abstracts color children i elemsSome
                  have bEq : b = siblingPlan.abstractPattern :=
                    Option.some.inj (absAt.symm.trans planAt)
                  subst bEq
                  let siblingPlanProc :=
                    castCostStaticRegionPlanSourceType elementType siblingPlan
                  have rawUnit := beforeUnitsRaw before[i]
                    (List.getElem_mem iLtBefore)
                  have ownUnit : canonicalize ownDeclaration before[i] =
                      .apply ownDeclaration.parallelUnitConstructor [] := by
                    by_cases sameColor : declarationColor = color
                    · simpa [declaration, ownDeclaration, sameColor] using rawUnit
                    · have declarationFlip : declarationColor = color.flip :=
                        CostStaticColor.eq_flip_of_ne (Ne.symm sameColor)
                      apply rhoProc_flipTarget_transfer (sizeOf before[i])
                        siblingPlanProc .unit (by omega)
                      simpa [declaration, declarationFlip,
                        RhoProcBVarTarget.pattern] using rawUnit
                  have measureElement : sizeOf before[i] ≤ fuel := by
                    have elementMem : before[i] ∈ elements := by
                      rw [elementsEq]
                      exact List.mem_append_left _
                        (List.getElem_mem iLtBefore)
                    have elementBound := List.sizeOf_lt_of_mem elementMem
                    omega
                  have tower := plan_abstract_iterDropUnit_of_iterDropUnit
                    color fuel siblingPlanProc 0 measureElement ownUnit
                  simpa [siblingPlanProc] using tower
                have afterLen : active.afterAbstracts.length = after.length := by
                  have total := elementPlan_abstractPatterns_length color children
                  have lenAbs := congrArg List.length active.abstracts_eq
                  have lenEls := congrArg List.length elementsEq
                  simp only [List.length_append, List.length_cons] at lenAbs lenEls
                  omega
                have afterUnits : ∀ a ∈ active.afterAbstracts,
                    canonicalize
                        rhoReflectivePresentation.toReflectivePresentationDecl a =
                      .apply rhoReflectivePresentation.toReflectivePresentationDecl.parallelUnitConstructor
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
                  obtain ⟨ou, siblingPlan, planAt⟩ :=
                    elementSpine_getElem?_abstracts color children
                      (active.beforeAbstracts.length + 1 + j) elemsSome
                  have aEq : a = siblingPlan.abstractPattern :=
                    Option.some.inj (absAt.symm.trans planAt)
                  subst aEq
                  let siblingPlanProc :=
                    castCostStaticRegionPlanSourceType elementType siblingPlan
                  have rawUnit := afterUnitsRaw after[j]
                    (List.getElem_mem jLtAfter)
                  have ownUnit : canonicalize ownDeclaration after[j] =
                      .apply ownDeclaration.parallelUnitConstructor [] := by
                    by_cases sameColor : declarationColor = color
                    · simpa [declaration, ownDeclaration, sameColor] using rawUnit
                    · have declarationFlip : declarationColor = color.flip :=
                        CostStaticColor.eq_flip_of_ne (Ne.symm sameColor)
                      apply rhoProc_flipTarget_transfer (sizeOf after[j])
                        siblingPlanProc .unit (by omega)
                      simpa [declaration, declarationFlip,
                        RhoProcBVarTarget.pattern] using rawUnit
                  have measureElement : sizeOf after[j] ≤ fuel := by
                    have elementMem : after[j] ∈ elements := by
                      rw [elementsEq]
                      exact List.mem_append_right _
                        (List.mem_cons_of_mem _ (List.getElem_mem jLtAfter))
                    have elementBound := List.sizeOf_lt_of_mem elementMem
                    omega
                  have tower := plan_abstract_iterDropUnit_of_iterDropUnit
                    color fuel siblingPlanProc 0 measureElement ownUnit
                  simpa [siblingPlanProc] using tower
                let parentState : CostStaticPlanStopped rhoCIGSLT color
                    targetFree child.payload
                    (CostStaticRegionPlan.collection choice selected
                      children).abstractPattern :=
                  { child.state with
                    skeletonContext :=
                      (OneHoleContext.collection collectionType
                        active.beforeAbstracts .hole active.afterAbstracts
                          none).comp child.state.skeletonContext
                    abstract_eq := by
                      rw [OneHoleContext.fill_comp, ← child.state.abstract_eq]
                      rw [show contributorPlan.abstractPattern =
                          active.head.abstractPattern by
                        exact
                          castCostStaticRegionPlanSourceType_abstractPattern
                            elementType active.head]
                      simp [CostStaticRegionPlan.abstractPattern,
                        OneHoleContext.fill, active.abstracts_eq] }
                have childEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT
                    color targetFree [child.state.certified.typed]
                    active.head.boundaryTable.entries := by
                  rw [← castCostStaticRegionPlanSourceType_boundaryTable_entries
                    elementType active.head]
                  exact child.entryEmbedding
                refine ⟨
                  { payload := child.payload
                    state := parentState
                    contextCollapse := ?_
                    entryEmbedding := childEmbedding.comp
                      active.entryEmbedding
                    boundaryCanonical := child.boundaryCanonical
                    boundarySupport := child.boundarySupport
                    boundaryType := child.boundaryType }⟩
                dsimp only [parentState]
                rw [OneHoleContext.fill_comp, OneHoleContext.fill]
                have authParallel : collectionType =
                    rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection := by
                  rw [parallelType, rhoDeclC_parallelCollection_hashBag,
                    auth_parallelCollection]
                rw [canonicalize_collection_congr_canonical_slot
                  rhoReflectivePresentation.toReflectivePresentationDecl
                  collectionType none active.beforeAbstracts
                  active.afterAbstracts
                  (middle' := .fvar (costRegionBoundaryVariableName
                    child.state.certified.typed.boundary))
                  (by
                    simp only [OneHoleContext.fill]
                    rw [child.contextCollapse]
                    simp [canonicalize])]
                rw [canonicalize_collection_ct_transport _ authParallel]
                exact canonicalize_parallel_units_around _ beforeUnits
                  afterUnits (by simp [canonicalize]) (by simp) (by simp)
              · rw [canonicalize_collection_of_ne_parallel _ parallelType]
                  at canonical
                exact absurd canonical.symm (escape.1 _ _ _)
      | @boundaryCollection sourceBound targetBound sourceAvailable thinning
          outer collectionType elements rest sourceType currentRejected
          oppositeChoice oppositeSelected certified certifies =>
          exact absurd oppositeSelected (fun selected =>
            rho_boundaryCollection_choices_absurd color targetFree targetBound
              collectionType elements _ selected currentRejected)

theorem rhoDescendEscape_of_structuralPartner
    (color declarationColor : CostStaticColor)
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {label : String} {arguments : List Pattern} {type : TypeExpr}
    (other : CostRegionTree rhoCIGSLT targetFree available outer
      (.apply label arguments) type)
    (structural : other.rootIsStatic = false) :
    RhoDescendEscape color
      (canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply label arguments)) := by
  have canonicalShape := canonicalize_apply_of_structural
    (declarationColor := declarationColor) other structural
  constructor
  · intro collectionType elements rest equality
    rw [canonicalShape] at equality
    exact Pattern.noConfusion equality
  · refine ⟨label, arguments.map (canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)),
      canonicalShape, ?_⟩
    cases other.structuralRootView structural with
    | neutralApplicationOrdinary membership notBare constructor materializes
        neutral ordinary children =>
        subst materializes
        rw [rhoCIGSLT.materializeDeclaredCostConstructor_label]
        exact decodeDeclaredCostStaticConstructor_render_of_role_ne
          rhoCIGSLT constructor color
            (role_ne_static_of_neutral (color := color) neutral)
    | neutralApplicationQuote membership notBare constructor materializes
        neutral quoted children =>
        subst materializes
        rw [rhoCIGSLT.materializeDeclaredCostConstructor_label]
        exact decodeDeclaredCostStaticConstructor_render_of_role_ne
          rhoCIGSLT constructor color
            (role_ne_static_of_neutral (color := color) neutral)

theorem canonicalize_structuralPartner_ne_unit
    (declarationColor : CostStaticColor)
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {label : String} {arguments : List Pattern} {type : TypeExpr}
    (other : CostRegionTree rhoCIGSLT targetFree available outer
      (.apply label arguments) type)
    (structural : other.rootIsStatic = false) :
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply label arguments) ≠
      .apply
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).parallelUnitConstructor [] := by
  rw [canonicalize_apply_of_structural
    (declarationColor := declarationColor) other structural]
  intro equality
  exact label_ne_parallelUnit_of_structural
    (declarationColor := declarationColor) other structural
      (Pattern.apply.inj equality).1

theorem rho_collapsingLeafExposureBVarRoute
    (declarationColor : CostStaticColor) :
    RhoCollapsingLeafExposureBVarRoute declarationColor := by
  intro targetFree available outer collapsedPattern index type collapsed color
    view other admissible otherWellSorted close collapsing canonical
  have nodeCanonical : canonicalize
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      view.node.term.1 = .bvar index := by
    rw [view.patternEq]
    exact canonical
  have sameColorCanonical : canonicalize
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      view.node.term.1 = .bvar index := by
    by_cases processSort : view.node.sourceSort.1 = "Proc"
    · by_cases sameColor : declarationColor = color
      · simpa [sameColor] using nodeCanonical
      · have declarationFlip : declarationColor = color.flip :=
          CostStaticColor.eq_flip_of_ne (Ne.symm sameColor)
        let processPlan : CostStaticRegionPlan rhoCIGSLT color targetFree
            view.node.sourceBound view.node.targetBound view.node.thinning
            view.node.targetBound .hole view.node.term.1 (.base "Proc") :=
          castCostStaticRegionPlanSourceType (congrArg TypeExpr.base processSort)
            view.node.plan
        apply rhoProc_canonicalize_flip_bvar_transfer processPlan index
        simpa [declarationFlip] using nodeCanonical
    · have nameSort : view.node.sourceSort.1 = "Name" :=
        rho_sourceSort_eq_name_of_ne_interacting processSort
      obtain ⟨arguments, skeletonArguments, patternShape, skeletonShape⟩ :=
        rhoNameFibre_view_shape view nameSort
      have declarationEq : declarationColor = color :=
        rhoNameFibre_collapsingRoot_color_eq (patternShape ▸ collapsing)
      simpa [declarationEq] using nodeCanonical
  obtain ⟨source⟩ := rhoBVarTowerSource_sameColor
    (sizeOf view.node.term.1) view.node.plan 0 index (by omega)
      sameColorCanonical
  have skeletonCanonical : canonicalize rhoReflectivePresentation
      view.node.skeleton.1 = .bvar source.sourceIndex := by
    rw [view.node.skeleton_pattern]
    simpa [iterDrop] using source.abstractCanonical
  let environment := view.node.normalizationEnvironment
    rhoHereditaryStaticNormalizer view.children
  have reifiedCanonical : canonicalize rhoReflectivePresentation
      (view.node.reifiedSourceFrame environment).1 =
        .bvar source.sourceIndex :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.RhoCollapsingLeafExposure.CostStaticRegionNode.reifiedSourceFrame_bvar_of_abstractCanonical
      view.node environment source.sourceIndex skeletonCanonical
  exact ⟨RhoCollapsingLeafExposure.rigidBVarOfSourceCanonicalAtBoundVariable
    view.node view.children other source.sourceIndex reifiedCanonical
      source.index_eq⟩

theorem rho_collapsingLeafExposureFVarRoute
    (declarationColor : CostStaticColor) :
    RhoCollapsingLeafExposureFVarRoute declarationColor := by
  intro targetFree available outer collapsedPattern name type collapsed color
    view other admissible otherWellSorted close collapsing canonical
  have nodeCanonical : canonicalize
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      view.node.term.1 = .fvar name := by
    rw [view.patternEq]
    exact canonical
  have sameColorCanonical : canonicalize
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      view.node.term.1 = .fvar name := by
    by_cases processSort : view.node.sourceSort.1 = "Proc"
    · by_cases sameColor : declarationColor = color
      · simpa [sameColor] using nodeCanonical
      · have declarationFlip : declarationColor = color.flip :=
          CostStaticColor.eq_flip_of_ne (Ne.symm sameColor)
        let processPlan : CostStaticRegionPlan rhoCIGSLT color targetFree
            view.node.sourceBound view.node.targetBound view.node.thinning
            view.node.targetBound .hole view.node.term.1 (.base "Proc") :=
          castCostStaticRegionPlanSourceType (congrArg TypeExpr.base processSort)
            view.node.plan
        apply rhoProc_canonicalize_flip_fvar_transfer processPlan name
        simpa [declarationFlip] using nodeCanonical
    · have nameSort : view.node.sourceSort.1 = "Name" :=
        rho_sourceSort_eq_name_of_ne_interacting processSort
      obtain ⟨arguments, skeletonArguments, patternShape, skeletonShape⟩ :=
        rhoNameFibre_view_shape view nameSort
      have declarationEq : declarationColor = color :=
        rhoNameFibre_collapsingRoot_color_eq (patternShape ▸ collapsing)
      simpa [declarationEq] using nodeCanonical
  obtain ⟨source⟩ := rhoFVarTowerSource_sameColor
    (sizeOf view.node.term.1) view.node.plan 0 name (by omega)
      sameColorCanonical
  have skeletonCanonical : canonicalize rhoReflectivePresentation
      view.node.skeleton.1 =
        .fvar (costRegionSourceVariableName name) := by
    rw [view.node.skeleton_pattern]
    simpa [iterDrop] using source.abstractCanonical
  obtain ⟨occurrence, slot, occurrenceName, selected, staticFrame⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.RhoCollapsingLeafExposure.CostStaticRegionNode.sourceVariableFrame_of_abstractCanonical
      view.node view.children name skeletonCanonical
  exact ⟨RhoCollapsingLeafExposure.sourceVariable view.node view.children
    occurrence name occurrenceName other slot selected staticFrame⟩

theorem rho_collapsingLeafExposureApplyRoute
    (declarationColor : CostStaticColor) :
    RhoCollapsingLeafExposureApplyRoute declarationColor := by
  intro targetFree available outer collapsedPattern label arguments type
    collapsed color view other admissible otherWellSorted close collapsing
      structural canonical
  have processSort : view.node.sourceSort.1 = "Proc" := by
    by_contra notProcess
    have nameSort : view.node.sourceSort.1 = "Name" :=
      rho_sourceSort_eq_name_of_ne_interacting notProcess
    have nameFibre : type = .base (costBaseSortName "Name") :=
      view.typeEq.symm.trans (by
        change TypeExpr.base
            ((color.symbols rhoCIGSLT).sort view.node.sourceSort.1) =
          TypeExpr.base (costBaseSortName "Name")
        rw [nameSort]
        cases color <;> rfl)
    exact no_structural_apply_of_type_eq_name other structural nameFibre
  let processPlan : CostStaticRegionPlan rhoCIGSLT color targetFree
      view.node.sourceBound view.node.targetBound view.node.thinning
      view.node.targetBound .hole view.node.term.1 (.base "Proc") :=
    castCostStaticRegionPlanSourceType (congrArg TypeExpr.base processSort)
      view.node.plan
  let target := canonicalize
    (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
      rhoReflectivePresentation.toReflectivePresentationDecl)
    (.apply label arguments)
  have nodeCanonical : canonicalize
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      view.node.term.1 = target := by
    rw [view.patternEq]
    exact canonical
  have escape : RhoDescendEscape color target :=
    rhoDescendEscape_of_structuralPartner color declarationColor other
      structural
  have targetNeUnit : target ≠ .apply
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl
        ).parallelUnitConstructor [] :=
    canonicalize_structuralPartner_ne_unit declarationColor other structural
  obtain ⟨descent⟩ := rhoProc_applyBoundaryDescent
    (sizeOf view.node.term.1) processPlan target (by omega) nodeCanonical
      escape targetNeUnit
  have processAbstract : processPlan.abstractPattern =
      view.node.plan.abstractPattern :=
    castCostStaticRegionPlanSourceType_abstractPattern
      (congrArg TypeExpr.base processSort) view.node.plan
  let state : CostStaticPlanStopped rhoCIGSLT color targetFree
      descent.payload view.node.skeleton.1 :=
    { descent.state with
      abstract_eq := view.node.skeleton_pattern.trans
        (processAbstract.symm.trans descent.state.abstract_eq) }
  have entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [state.certified.typed]
      view.node.finiteBoundaryTable.entries := by
    change CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [descent.state.certified.typed] view.node.plan.boundaryTable.entries
    rw [← castCostStaticRegionPlanSourceType_boundaryTable_entries
      (congrArg TypeExpr.base processSort) view.node.plan]
    exact descent.entryEmbedding
  have mappedProcess : mapTypeExpr (color.symbols rhoCIGSLT)
      (.base "Proc") =
      .base (color.mapLangSort rhoCIGSLT view.node.sourceSort).1 := by
    change TypeExpr.base ((color.symbols rhoCIGSLT).sort "Proc") =
      TypeExpr.base ((color.symbols rhoCIGSLT).sort view.node.sourceSort.1)
    rw [processSort]
  exact ⟨RhoCollapsingLeafExposure.stoppedCollapseOfCloseSmaller collapsed
    other view otherWellSorted state entryEmbedding
      (by simpa [state] using descent.contextCollapse)
      (by simpa [state, target] using descent.boundaryCanonical)
      (by simpa [state] using descent.boundarySupport.trans view.availableEq)
      (by
        simpa [state] using descent.boundaryType.trans
          (mappedProcess.trans view.typeEq))
      close⟩

theorem rho_collapsingLeaf_hasExposure
    (declarationColor : CostStaticColor) :
    RhoCollapsingLeaf.HasExposure declarationColor :=
  rho_collapsingLeaf_hasExposure_of_leafRoutes
    (rho_collapsingLeafExposureBVarRoute declarationColor)
    (rho_collapsingLeafExposureFVarRoute declarationColor)
    (rho_collapsingLeafExposureApplyRoute declarationColor)

theorem rho_collapsingLeaf_hasExposure_allColors :
    ∀ declarationColor, RhoCollapsingLeaf.HasExposure declarationColor :=
  rho_collapsingLeaf_hasExposure

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
