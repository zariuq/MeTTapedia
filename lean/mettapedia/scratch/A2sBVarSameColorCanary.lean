import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryDescent

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

theorem rho_costWhole_rule_category_of_unitWire_canary
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

inductive RhoProcBVarTarget where
  | unit
  | bvar (index : Nat)

def RhoProcBVarTarget.pattern (color : CostStaticColor) :
    RhoProcBVarTarget → Pattern
  | .unit =>
      .apply (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        ).parallelUnitConstructor []
  | .bvar index => .bvar index

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

theorem boundaryApplication_flipTarget_absurd
    (color : CostStaticColor) {targetFree : FreeTypeContext}
    {sourceAvailable : List TypeExpr} {wireName : String}
    {arguments : List Pattern}
    (declared : rhoCIGSLT.DeclaredCostConstructor)
    (rendered : rhoCIGSLT.renderDeclaredCostConstructor declared = wireName)
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
        have categoryForm := rho_costWhole_rule_category_of_unitWire_canary
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
      (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
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
          | bvar index =>
              simp only [RhoProcBVarTarget.pattern, canonicalize,
                Pattern.bvar.injEq] at canonical ⊢
              exact canonical
      | fvar lookup =>
          cases target <;>
            simp [RhoProcBVarTarget.pattern, canonicalize] at canonical
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

theorem rho_collapsingLeafExposureBVarRoute_canary
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

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
