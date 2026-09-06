import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryQuoteBoundaryAlignment
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryDescent

/-!
# Current/authored parallel-frontier correspondence with admissions

`parallelLeaves` of an admitted payload at the current colour declaration
corresponds pointwise, in occurrence order, to `parallelLeaves` of the plan's
authored abstract: each pair carries a reached subplan at the leaf, its raw
admission, and an entry embedding into the enclosing table.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ParallelFrontier

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.RhoCommonRestorationApex

/-! ## Member projections of the four boolean list predicates -/

theorem hasCanonicalBinderMetadataList_mem {patterns : List Pattern}
    (all : Pattern.hasCanonicalBinderMetadataList patterns = true)
    {pattern : Pattern} (membership : pattern ∈ patterns) :
    pattern.hasCanonicalBinderMetadata = true := by
  induction patterns with
  | nil => cases membership
  | cons head tail ih =>
      simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true]
        at all
      rcases List.mem_cons.mp membership with rfl | tailMem
      · exact all.1
      · exact ih all.2 tailMem

theorem isObjectPatternList_mem {patterns : List Pattern}
    (all : isObjectPatternList patterns = true)
    {pattern : Pattern} (membership : pattern ∈ patterns) :
    isObjectPattern pattern = true := by
  induction patterns with
  | nil => cases membership
  | cons head tail ih =>
      simp only [isObjectPatternList, Bool.and_eq_true] at all
      rcases List.mem_cons.mp membership with rfl | tailMem
      · exact all.1
      · exact ih all.2 tailMem

theorem isWellScopedListAt_mem {depth : Nat} {patterns : List Pattern}
    (all : Pattern.isWellScopedListAt depth patterns = true)
    {pattern : Pattern} (membership : pattern ∈ patterns) :
    pattern.isWellScopedAt depth = true := by
  induction patterns with
  | nil => cases membership
  | cons head tail ih =>
      simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at all
      rcases List.mem_cons.mp membership with rfl | tailMem
      · exact all.1
      · exact ih all.2 tailMem

theorem binderSafeListAt_mem {quote : String} {depth : Nat}
    {patterns : List Pattern}
    (all : binderSafeListAt quote depth patterns = true)
    {pattern : Pattern} (membership : pattern ∈ patterns) :
    binderSafeAt quote depth pattern = true := by
  induction patterns with
  | nil => cases membership
  | cons head tail ih =>
      simp only [binderSafeListAt, Bool.and_eq_true] at all
      rcases List.mem_cons.mp membership with rfl | tailMem
      · exact all.1
      · exact ih all.2 tailMem

/-- Pointwise relations append. -/
theorem forall₂_append {α β : Type _} {R : α → β → Prop}
    {l₁ l₂ : List α} {r₁ r₂ : List β}
    (first : List.Forall₂ R l₁ r₁) (second : List.Forall₂ R l₂ r₂) :
    List.Forall₂ R (l₁ ++ l₂) (r₁ ++ r₂) := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

/-- Retain membership in the full left list at every position of a pointwise
relation.  This is the proof-relevant ingredient needed to transport strict
frontier size bounds through a later permutation. -/
theorem forall₂_with_left_membership {α β : Type _} {R : α → β → Prop}
    {left : List α} {right : List β}
    (aligned : List.Forall₂ R left right) :
    List.Forall₂ (fun source target => source ∈ left ∧ R source target)
      left right := by
  induction aligned with
  | nil => exact .nil
  | @cons source target left right head tail inductionHypothesis =>
      exact .cons ⟨by simp, head⟩
        (inductionHypothesis.imp fun _ _ related =>
          ⟨by simp [related.1], related.2⟩)


/-! ## Child admission beneath a bare-parallel collection plan -/

/-- Every element of an admitted current-colour collection plan at `rest =
none` is itself admissible at the choice's element type: the four object
components and the reflective component all project through the element
list, and the binder split is inherited unchanged. -/
theorem childAdmission_of_collectionElement
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {collectionType : CollType} {elements : List Pattern}
    {sourceType : TypeExpr}
    {choice : CostCollectionTypingChoice}
    (selected : choice ∈
      costStaticCollectionTypingChoices rhoCIGSLT color targetFree
        targetBound collectionType elements
        (mapTypeExpr (color.symbols rhoCIGSLT) sourceType))
    {children : CostStaticElementPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer collectionType [] elements
      none choice.sourceElementType}
    (admission :
      (CostStaticRegionPlan.collection (source := rhoCIGSLT)
        (targetFree := targetFree) (thinning := thinning)
        (sourceAvailable := sourceAvailable) (outer := outer)
        (rest := none) choice selected children).RawAdmission)
    {element : Pattern} (membership : element ∈ elements) :
    ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree sourceAvailable
        (mapTypeExpr (color.symbols rhoCIGSLT) choice.sourceElementType)
        element ∧
      ∃ sealed, targetBound = sourceAvailable ++ sealed := by
  obtain ⟨sealed, split⟩ := admission.targetBound_split
  have elementScope :
      Pattern.isWellScopedListAt sourceAvailable.length elements = true := by
    simpa [WellSorted.ScopeSafeAt, Pattern.isWellScopedAt] using
      admission.wellSorted.1.2.2.2
  have elementsTyped : WellSorted.ElementsHaveType
      rhoCIGSLT.costWholeLanguage targetFree sourceAvailable elements
      (mapTypeExpr (color.symbols rhoCIGSLT) choice.sourceElementType) := by
    have typedAtTarget := WellSorted.checkElementsHaveType_sound
      (checkElementsHaveType_of_mem_costStaticCollectionTypingChoices selected)
    rw [split] at typedAtTarget
    exact typedAtTarget.restrictOuterOfScoped elementScope
  refine ⟨⟨⟨hasType_of_mem_elements elementsTyped membership, ?_, ?_, ?_⟩,
    ?_⟩, sealed, split⟩
  · exact hasCanonicalBinderMetadataList_mem
      (by simpa [Pattern.hasCanonicalBinderMetadata] using
        admission.wellSorted.1.2.1) membership
  · exact isObjectPatternList_mem
      (by simpa [WellSorted.isObjectPattern] using
        admission.wellSorted.1.2.2.1) membership
  · exact isWellScopedListAt_mem elementScope membership
  · intro presentation presentationMembership
    exact binderSafeListAt_mem
      (by simpa [binderSafeAt] using
        admission.wellSorted.2 presentation presentationMembership) membership


/-! ## Frontier evaluation helpers -/

theorem parallelLeaves_apply_of_not_unit
    (declaration : ReflectivePresentationDecl)
    {wire : String} {arguments : List Pattern}
    (notUnit : ¬ (wire = declaration.parallelUnitConstructor ∧
      arguments = [])) :
    parallelLeaves declaration (.apply wire arguments) =
      [.apply wire arguments] := by
  simp only [parallelLeaves, if_neg notUnit]

theorem parallelLeaves_apply_unit
    (declaration : ReflectivePresentationDecl) :
    parallelLeaves declaration
      (.apply declaration.parallelUnitConstructor []) = [] := by
  simp [parallelLeaves]

theorem parallelLeaves_collection_of_not_parallel
    (declaration : ReflectivePresentationDecl)
    {collectionType : CollType} {elements : List Pattern}
    {rest : Option String}
    (notParallel : ¬ (collectionType = declaration.parallelCollection ∧
      rest = none)) :
    parallelLeaves declaration (.collection collectionType elements rest) =
      [.collection collectionType elements rest] := by
  simp only [parallelLeaves, if_neg notParallel]

theorem parallelLeaves_parallel
    (declaration : ReflectivePresentationDecl) (elements : List Pattern) :
    parallelLeaves declaration
        (.collection declaration.parallelCollection elements none) =
      parallelLeavesList declaration elements := by
  simp [parallelLeaves]

theorem parallelLeaves_parallel_of_eq
    (declaration : ReflectivePresentationDecl) {collectionType : CollType}
    (typeEq : collectionType = declaration.parallelCollection)
    (elements : List Pattern) :
    parallelLeaves declaration
        (.collection collectionType elements none) =
      parallelLeavesList declaration elements := by
  subst typeEq
  exact parallelLeaves_parallel _ _

theorem parallelLeaves_default_bvar
    (declaration : ReflectivePresentationDecl) (index : Nat) :
    parallelLeaves declaration (.bvar index) = [.bvar index] := rfl

theorem parallelLeaves_default_fvar
    (declaration : ReflectivePresentationDecl) (name : String) :
    parallelLeaves declaration (.fvar name) = [.fvar name] := rfl

theorem parallelLeaves_default_lambda
    (declaration : ReflectivePresentationDecl) (binder : Option String)
    (body : Pattern) :
    parallelLeaves declaration (.lambda binder body) =
      [.lambda binder body] := rfl

theorem parallelLeaves_default_multiLambda
    (declaration : ReflectivePresentationDecl) (arity : Nat)
    (binders : List String) (body : Pattern) :
    parallelLeaves declaration (.multiLambda arity binders body) =
      [.multiLambda arity binders body] := rfl

mutual
  /-- Every recursively exposed parallel leaf is syntactically neither the
  distinguished unit nor another bare parallel. -/
  theorem parallelLeaves_mem_root_stable
      (declaration : ReflectivePresentationDecl) : ∀ pattern leaf,
      leaf ∈ parallelLeaves declaration pattern →
        leaf ≠ .apply declaration.parallelUnitConstructor [] ∧
          ∀ elements,
            leaf ≠ .collection declaration.parallelCollection elements none
    | .bvar index, leaf, membership => by
        rw [parallelLeaves_default_bvar, List.mem_singleton] at membership
        subst leaf
        simp
    | .fvar name, leaf, membership => by
        rw [parallelLeaves_default_fvar, List.mem_singleton] at membership
        subst leaf
        simp
    | .apply constructor arguments, leaf, membership => by
        by_cases unit : constructor = declaration.parallelUnitConstructor ∧
            arguments = []
        · rcases unit with ⟨rfl, rfl⟩
          rw [parallelLeaves_apply_unit] at membership
          cases membership
        · rw [parallelLeaves_apply_of_not_unit declaration unit,
            List.mem_singleton] at membership
          subst leaf
          exact ⟨fun equality => unit (Pattern.apply.inj equality),
            fun _ equality => by cases equality⟩
    | .lambda binder body, leaf, membership => by
        rw [parallelLeaves_default_lambda, List.mem_singleton] at membership
        subst leaf
        simp
    | .multiLambda arity binders body, leaf, membership => by
        rw [parallelLeaves_default_multiLambda,
          List.mem_singleton] at membership
        subst leaf
        simp
    | .subst body replacement, leaf, membership => by
        simp only [parallelLeaves, List.mem_singleton] at membership
        subst leaf
        simp
    | .collection collectionType elements rest, leaf, membership => by
        by_cases parallel : collectionType = declaration.parallelCollection ∧
            rest = none
        · rcases parallel with ⟨rfl, rfl⟩
          rw [parallelLeaves_parallel] at membership
          exact parallelLeavesList_mem_root_stable declaration elements leaf
            membership
        · rw [parallelLeaves_collection_of_not_parallel declaration parallel,
            List.mem_singleton] at membership
          subst leaf
          constructor
          · intro equality
            exact Pattern.noConfusion equality
          · intro nested equality
            have parts := Pattern.collection.inj equality
            exact parallel ⟨parts.1, parts.2.2⟩

  /-- List companion of `parallelLeaves_mem_root_stable`. -/
  theorem parallelLeavesList_mem_root_stable
      (declaration : ReflectivePresentationDecl) : ∀ patterns leaf,
      leaf ∈ parallelLeavesList declaration patterns →
        leaf ≠ .apply declaration.parallelUnitConstructor [] ∧
          ∀ elements,
            leaf ≠ .collection declaration.parallelCollection elements none
    | [], leaf, membership => by
        simp [parallelLeavesList] at membership
    | pattern :: patterns, leaf, membership => by
        simp only [parallelLeavesList, List.mem_append] at membership
        rcases membership with head | tail
        · exact parallelLeaves_mem_root_stable declaration pattern leaf head
        · exact parallelLeavesList_mem_root_stable declaration patterns leaf
            tail
end

/-! ## Keyed reconstruction from stable leaves -/

/-- Keyed canonicalization cannot splice a syntactically stable leaf when
its root is neither Quote, the parallel unit, nor a bare parallel.  The
premises mention only root shape; nested Quotes remain allowed. -/
theorem canonicalizeByAt_parallelContents_singleton_of_root_stable
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) (depth : Nat)
    (pattern : Pattern)
    (notUnit : pattern ≠ .apply declaration.parallelUnitConstructor [])
    (notParallel : ∀ elements,
      pattern ≠ .collection declaration.parallelCollection elements none)
    (notQuote : ∀ arguments,
      pattern ≠ .apply declaration.quoteConstructor arguments) :
    parallelContents declaration
        [canonicalizeByAt key declaration depth pattern] =
      [canonicalizeByAt key declaration depth pattern] := by
  cases pattern with
  | bvar index => rfl
  | fvar name => rfl
  | apply constructor arguments =>
      have constructorNotQuote : constructor ≠ declaration.quoteConstructor :=
        fun equality => notQuote arguments (by rw [equality])
      have normalizedNotUnit :
          Pattern.apply constructor
              (canonicalizeListByAt key declaration depth arguments) ≠
            Pattern.apply declaration.parallelUnitConstructor [] := by
        intro equality
        injection equality with constructorEquality argumentsEquality
        apply notUnit
        rw [constructorEquality]
        have argumentsNil : arguments = [] := by
          simpa [canonicalizeListByAt_eq_map] using argumentsEquality
        rw [argumentsNil]
      have canonicalForm :
          canonicalizeByAt key declaration depth (.apply constructor arguments) =
            .apply constructor
              (canonicalizeListByAt key declaration depth arguments) := by
        simp [canonicalizeByAt, constructorNotQuote]
      rw [canonicalForm]
      simp [parallelContents, parallelSplice, normalizedNotUnit]
  | lambda binder body =>
      simp [canonicalizeByAt, parallelContents, parallelSplice]
  | multiLambda arity binders body =>
      simp [canonicalizeByAt, parallelContents, parallelSplice]
  | subst body replacement =>
      simp [canonicalizeByAt, parallelContents, parallelSplice]
  | collection collectionType elements rest =>
      cases rest with
      | some restName =>
          simp [canonicalizeByAt, parallelContents, parallelSplice]
      | none =>
          by_cases selected : collectionType = declaration.parallelCollection
          · subst collectionType
            exact (notParallel elements rfl).elim
          · have canonicalForm :
                canonicalizeByAt key declaration depth
                    (.collection collectionType elements none) =
                  .collection collectionType
                    (canonicalizeListByAt key declaration depth elements)
                    none := by
              simp [canonicalizeByAt, selected]
            rw [canonicalForm]
            simp [parallelContents, parallelSplice, selected]

/-- Root-stable keyed leaves remain neither units nor bare parallels after
canonicalization. -/
theorem canonicalizeByAt_leaf_stable_of_root_stable
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) (depth : Nat)
    (pattern : Pattern)
    (notUnit : pattern ≠ .apply declaration.parallelUnitConstructor [])
    (notParallel : ∀ elements,
      pattern ≠ .collection declaration.parallelCollection elements none)
    (notQuote : ∀ arguments,
      pattern ≠ .apply declaration.quoteConstructor arguments) :
    canonicalizeByAt key declaration depth pattern ≠
        .apply declaration.parallelUnitConstructor [] ∧
      ∀ elements,
        canonicalizeByAt key declaration depth pattern ≠
          .collection declaration.parallelCollection elements none := by
  have stable := canonicalizeByAt_parallelContents_singleton_of_root_stable
    key declaration depth pattern notUnit notParallel notQuote
  have membership : canonicalizeByAt key declaration depth pattern ∈
      parallelContents declaration
        (canonicalizeListByAt key declaration depth [pattern]) := by
    simpa [canonicalizeListByAt] using (show
      canonicalizeByAt key declaration depth pattern ∈
        parallelContents declaration
          [canonicalizeByAt key declaration depth pattern] by
      rw [stable]
      simp)
  exact ⟨
    keyedParallelFrontier_noUnit key declaration depth [pattern]
      _ membership,
    keyedParallelFrontier_noParallel key declaration depth [pattern]
      _ membership⟩

/-- Only the authored unit rule carries the unit label. -/
theorem rhoCalc_params_nil_of_label_pzero
    (rule : Mettapedia.OSLF.MeTTaIL.Syntax.GrammarRule)
    (membership : rule ∈ rhoCalc.terms)
    (label : rule.label = "PZero") : rule.params = [] := by
  change rule ∈ [rhoCalc.terms[0], rhoCalc.terms[1], rhoCalc.terms[2],
    rhoCalc.terms[3], rhoCalc.terms[4], rhoCalc.terms[5]] at membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | rfl
      | exact absurd label (by decide)

/-- A process-plan abstract whose raw payload is already a flattened
parallel leaf has a stable authored root: it is neither unit, parallel, nor
Quote.  The conclusion concerns only the root, so nested quoted names remain
available to ordinary rho process constructors. -/
theorem processPlan_abstractPattern_root_stable
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {payload : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload sourceType)
    (processType : sourceType = .base "Proc")
    (notUnit : payload ≠ .apply
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        ).parallelUnitConstructor [])
    (notParallel : ∀ elements, payload ≠ .collection
      rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
      elements none) :
    plan.abstractPattern ≠ .apply
        rhoReflectivePresentation.toReflectivePresentationDecl.parallelUnitConstructor
        [] ∧
      (∀ elements, plan.abstractPattern ≠ .collection
        rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
        elements none) ∧
      ∀ arguments, plan.abstractPattern ≠ .apply
        rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor
        arguments := by
  cases plan with
  | bvar | fvar | boundaryApplication | boundaryCollection =>
      simp [CostStaticRegionPlan.abstractPattern]
  | @application _ _ _ _ _ wireName arguments declared rendered current
      preimage notBare children =>
      have renderedLabel : wireName =
          (color.symbols rhoCIGSLT).constructor
            preimage.sourceConstructor.1.label := by
        rw [← rendered, ← rhoCIGSLT.materializeDeclaredCostConstructor_label
          declared, preimage.labelMap]
      constructor
      · intro abstractUnit
        have labelUnit : preimage.sourceConstructor.1.label = "PZero" :=
          (Pattern.apply.inj abstractUnit).1
        have paramsNil : preimage.sourceConstructor.1.params = [] :=
          rhoCalc_params_nil_of_label_pzero preimage.sourceConstructor.1
            preimage.sourceConstructor.2 labelUnit
        have lengths :=
          CostHereditaryCrossColorLeafHinge.CostStaticArgumentPlan.abstractPatterns_length
            children
        have argumentsNil : arguments = [] :=
          List.eq_nil_of_length_eq_zero (by
            rw [lengths.2, paramsNil]
            rfl)
        apply notUnit
        rw [argumentsNil, renderedLabel, labelUnit]
        cases color <;> rfl
      · constructor
        · intro elements equality
          cases equality
        · intro quoteArguments abstractQuote
          have labelQuote : preimage.sourceConstructor.1.label = "NQuote" :=
            (Pattern.apply.inj abstractQuote).1
          have categoryName := rhoCalc_category_eq_name_of_label_eq_quote
            preimage.sourceConstructor.2 labelQuote
          have categoryProc : preimage.sourceConstructor.1.category =
              "Proc" := TypeExpr.base.inj processType
          rw [categoryProc] at categoryName
          exact (by decide : "Proc" ≠ "Name") categoryName
  | collection choice selected children =>
      rename_i collectionType elements rest
      constructor
      · intro equality
        cases equality
      · constructor
        · intro nested equality
          have collectionEq : collectionType =
              rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection :=
            (Pattern.collection.inj equality).1
          have restEq : rest.map costRegionSourceVariableName = none :=
            (Pattern.collection.inj equality).2.2
          have restNone : rest = none := by
            cases rest <;> simp_all
          apply notParallel elements
          subst rest
          rw [collectionEq]
        · intro arguments equality
          cases equality
  | lambda | multiLambda => cases processType

/-- An excluded authored application root excludes the corresponding plan
root class.  This is the elimination form used after a frontier occurrence
has retained its exact subplan. -/
theorem rootClass_ne_application_of_abstractPattern_ne_apply
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound targetBound
      thinning sourceAvailable outer pattern sourceType)
    {constructor : String}
    (excluded : ∀ arguments,
      plan.abstractPattern ≠ .apply constructor arguments) :
    plan.rootClass ≠ .application constructor := by
  intro rootClass
  cases plan <;>
    simp [CostStaticRegionPlan.rootClass,
      CostStaticRegionPlan.abstractPattern] at rootClass excluded
  contradiction

/-- For an admitted collection plan, exclusion of the bare authored
collection excludes its root class.  Admission is essential: it rules out an
open collection tail, which the root class intentionally forgets. -/
theorem rootClass_ne_collection_of_abstractPattern_ne_bare
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound targetBound
      thinning sourceAvailable outer pattern sourceType)
    {collectionType : CollType}
    (admission : plan.RawAdmission)
    (excluded : ∀ elements,
      plan.abstractPattern ≠ .collection collectionType elements none) :
    plan.rootClass ≠ .collection collectionType := by
  intro rootClass
  have object := admission.object
  cases plan <;>
    simp [CostStaticRegionPlan.rootClass,
      CostStaticRegionPlan.abstractPattern, WellSorted.isObjectPattern]
      at rootClass excluded object
  exact (excluded rootClass) object.1

/-- An admitted reached plan whose root class is a collection retains a
closed collection as its raw payload.  The root class records the collection
kind, while raw admission supplies the otherwise forgotten closed-tail
condition. -/
theorem CostStaticPlanReached.exists_payload_eq_bareCollection_of_rootClass
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {payload rootAbstract : Pattern}
    (reached : CostStaticPlanReached source color targetFree payload
      rootAbstract)
    (admission : reached.plan.RawAdmission)
    {collectionType : CollType}
    (rootClass : reached.plan.rootClass = .collection collectionType) :
    ∃ elements, payload = .collection collectionType elements none := by
  rcases reached with
    ⟨sourceBound, targetBound, thinning, sourceAvailable, outer, sourceType,
      plan, skeletonContext, abstractEq⟩
  change plan.RawAdmission at admission
  change plan.rootClass = .collection collectionType at rootClass
  have object := admission.object
  cases plan with
  | collection choice selected children =>
      rename_i actualCollection elements rest
      simp only [CostStaticRegionPlan.rootClass,
        CostStaticPlanRootClass.collection.injEq] at rootClass
      subst actualCollection
      have restNone : rest = none := by
        cases rest with
        | none => rfl
        | some rest => simp [WellSorted.isObjectPattern] at object
      subst rest
      exact ⟨elements, rfl⟩
  | boundaryApplication | boundaryCollection | bvar | fvar | application |
      lambda | multiLambda =>
      simp [CostStaticRegionPlan.rootClass] at rootClass

/-- Endpoint reification, constructor colouring, and ambient-binder
reinsertion preserve the three stable root exclusions used by keyed parallel
reconstruction. -/
theorem commonReifiedMappedThickened_root_stable
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      occurrences}
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      table values root}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    (scopeDepth : Nat) (pattern : Pattern)
    (stable : pattern ≠ .apply
          rhoReflectivePresentation.toReflectivePresentationDecl.parallelUnitConstructor
          [] ∧
      (∀ elements, pattern ≠ .collection
        rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
        elements none) ∧
      ∀ arguments, pattern ≠ .apply
        rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor
        arguments) :
    let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation
    let frame := cospan.reifyWith environment.lookupAtom? leg
      (thinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (environment.reify pattern)))
    frame ≠ .apply declaration.parallelUnitConstructor [] ∧
      (∀ elements, frame ≠
        .collection declaration.parallelCollection elements none) ∧
      ∀ arguments, frame ≠ .apply declaration.quoteConstructor arguments := by
  dsimp only
  rw [cospan.reifyWith_eq_renameFVars,
    environment.reify_eq_renameFVars]
  let sourceDeclaration :=
    rhoReflectivePresentation.toReflectivePresentationDecl
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation
  have unitMap : targetDeclaration.parallelUnitConstructor =
      (color.symbols rhoCIGSLT).constructor
        sourceDeclaration.parallelUnitConstructor := by
    cases color <;> rfl
  have quoteMap : targetDeclaration.quoteConstructor =
      (color.symbols rhoCIGSLT).constructor
        sourceDeclaration.quoteConstructor := by
    cases color <;> rfl
  have parallelMap : targetDeclaration.parallelCollection =
      sourceDeclaration.parallelCollection := by
    cases color <;> rfl
  change pattern ≠ .apply sourceDeclaration.parallelUnitConstructor [] ∧
      (∀ elements, pattern ≠
        .collection sourceDeclaration.parallelCollection elements none) ∧
      ∀ arguments, pattern ≠
        .apply sourceDeclaration.quoteConstructor arguments at stable
  change Pattern.renameFVars _
        (thinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (Pattern.renameFVars _ pattern))) ≠
        .apply targetDeclaration.parallelUnitConstructor [] ∧
      (∀ elements, Pattern.renameFVars _
        (thinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (Pattern.renameFVars _ pattern))) ≠
          .collection targetDeclaration.parallelCollection elements none) ∧
      ∀ arguments, Pattern.renameFVars _
        (thinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (Pattern.renameFVars _ pattern))) ≠
          .apply targetDeclaration.quoteConstructor arguments
  cases pattern with
  | bvar index =>
      simp [Pattern.renameFVars, mapPattern,
        CostStaticBinderThinning.thickenAmbientBVars]
  | fvar name =>
      simp [Pattern.renameFVars, mapPattern,
        CostStaticBinderThinning.thickenAmbientBVars]
  | apply constructor arguments =>
      constructor
      · intro equality
        simp only [Pattern.renameFVars, mapPattern, mapPatternList_eq_map,
          CostStaticBinderThinning.thickenAmbientBVars] at equality
        have constructorEq :
            (color.symbols rhoCIGSLT).constructor constructor =
              targetDeclaration.parallelUnitConstructor :=
          (Pattern.apply.inj equality).1
        have sourceConstructorEq : constructor =
            sourceDeclaration.parallelUnitConstructor := by
          apply CostStaticColor.symbols_constructor_injective rhoCIGSLT color
          exact constructorEq.trans unitMap
        have argumentsEq : arguments = [] := by
          have mappedEq := (Pattern.apply.inj equality).2
          simpa [Pattern.renameFVars, mapPattern, mapPatternList_eq_map,
            CostStaticBinderThinning.thickenAmbientBVars] using mappedEq
        exact stable.1 (by rw [sourceConstructorEq, argumentsEq])
      · constructor
        · intro elements equality
          simp only [Pattern.renameFVars, mapPattern, mapPatternList_eq_map,
            CostStaticBinderThinning.thickenAmbientBVars] at equality
          cases equality
        · intro quoteArguments equality
          simp only [Pattern.renameFVars, mapPattern, mapPatternList_eq_map,
            CostStaticBinderThinning.thickenAmbientBVars] at equality
          have constructorEq :
              (color.symbols rhoCIGSLT).constructor constructor =
                targetDeclaration.quoteConstructor :=
            (Pattern.apply.inj equality).1
          have sourceConstructorEq : constructor =
              sourceDeclaration.quoteConstructor := by
            apply CostStaticColor.symbols_constructor_injective rhoCIGSLT color
            exact constructorEq.trans quoteMap
          exact stable.2.2 arguments (by rw [sourceConstructorEq])
  | lambda binder body =>
      simp [Pattern.renameFVars, mapPattern,
        CostStaticBinderThinning.thickenAmbientBVars]
  | multiLambda arity binders body =>
      simp [Pattern.renameFVars, mapPattern,
        CostStaticBinderThinning.thickenAmbientBVars]
  | subst body replacement =>
      simp [Pattern.renameFVars, mapPattern,
        CostStaticBinderThinning.thickenAmbientBVars]
  | collection collectionType elements rest =>
      constructor
      · intro equality
        simp only [Pattern.renameFVars, mapPattern, mapPatternList_eq_map,
          CostStaticBinderThinning.thickenAmbientBVars] at equality
        cases equality
      · constructor
        · intro framedElements equality
          simp only [Pattern.renameFVars, mapPattern, mapPatternList_eq_map,
            CostStaticBinderThinning.thickenAmbientBVars] at equality
          have collectionEq : collectionType =
              targetDeclaration.parallelCollection :=
            (Pattern.collection.inj equality).1
          have restEq := (Pattern.collection.inj equality).2.2
          have restNone : rest = none := by
            cases rest <;> simp_all
          apply stable.2.1 elements
          subst rest
          rw [collectionEq, parallelMap]
        · intro arguments equality
          simp only [Pattern.renameFVars, mapPattern, mapPatternList_eq_map,
            CostStaticBinderThinning.thickenAmbientBVars] at equality
          cases equality

mutual
  /-- If every recursively exposed leaf remains a genuine non-unit,
  non-parallel leaf after keyed canonicalization, rebuilding the keyed
  canonical frontier preserves exactly those occurrences. -/
  theorem parallelLeaves_keyed_frontier_perm_of_leaf_stable
      {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl) (depth : Nat) :
      ∀ pattern,
      (∀ leaf, leaf ∈ parallelLeaves declaration pattern →
        canonicalizeByAt key declaration depth leaf ≠
          .apply declaration.parallelUnitConstructor [] ∧
        ∀ elements,
          canonicalizeByAt key declaration depth leaf ≠
            .collection declaration.parallelCollection elements none) →
      List.Perm
        (parallelContents declaration
          [canonicalizeByAt key declaration depth pattern])
        (canonicalizeListByAt key declaration depth
          (parallelLeaves declaration pattern))
    | .bvar index, stable => by
        simp [parallelLeaves, canonicalizeByAt, canonicalizeListByAt,
          parallelContents, parallelSplice]
    | .fvar name, stable => by
        simp [parallelLeaves, canonicalizeByAt, canonicalizeListByAt,
          parallelContents, parallelSplice]
    | .apply constructor arguments, stable => by
        by_cases unit : constructor = declaration.parallelUnitConstructor ∧
            arguments = []
        · rcases unit with ⟨rfl, rfl⟩
          simp [parallelLeaves, canonicalizeByAt, canonicalizeListByAt,
            parallelContents, parallelSplice,
            Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]
        · have leafStable := stable (.apply constructor arguments) (by
            simp [parallelLeaves, unit])
          have splice := parallelSplice_eq_singleton_of_not_parallel
            declaration
            (canonicalizeByAt key declaration depth
              (.apply constructor arguments)) leafStable.2
          simp [parallelLeaves, unit, canonicalizeListByAt,
            parallelContents, splice, leafStable.1]
    | .lambda binder body, stable => by
        simp [parallelLeaves, canonicalizeByAt, canonicalizeListByAt,
          parallelContents, parallelSplice]
    | .multiLambda arity binders body, stable => by
        simp [parallelLeaves, canonicalizeByAt, canonicalizeListByAt,
          parallelContents, parallelSplice]
    | .subst body replacement, stable => by
        simp [parallelLeaves, canonicalizeByAt, canonicalizeListByAt,
          parallelContents, parallelSplice]
    | .collection collectionType elements rest, stable => by
        by_cases parallel : collectionType = declaration.parallelCollection ∧
            rest = none
        · rcases parallel with ⟨rfl, rfl⟩
          have exposed :=
            parallelContents_canonicalizeByAt_singleton_perm key declaration
              depth (.collection declaration.parallelCollection elements none)
          have filtered :=
            parallelContents_canonicalizeListByAt_filter_unit key declaration
              depth elements
          have children :=
            parallelLeavesList_keyed_frontier_perm_of_leaf_stable key
              declaration depth elements (by
                intro leaf membership
                exact stable leaf (by
                  simpa [parallelLeaves] using membership))
          have exposed' : List.Perm
              (parallelContents declaration
                [canonicalizeByAt key declaration depth
                  (.collection declaration.parallelCollection elements none)])
              (parallelContents declaration
                (canonicalizeListByAt key declaration depth
                  (elements.filter fun element =>
                    element ≠ .apply declaration.parallelUnitConstructor
                      []))) := by
            simpa [parallelContents, parallelSplice] using exposed
          simpa [parallelLeaves] using exposed'.trans
            ((List.Perm.of_eq filtered).trans children)
        · have leafStable :=
            stable (.collection collectionType elements rest) (by
            simp [parallelLeaves, parallel])
          have splice := parallelSplice_eq_singleton_of_not_parallel
            declaration
            (canonicalizeByAt key declaration depth
              (.collection collectionType elements rest)) leafStable.2
          simp [parallelLeaves, parallel, canonicalizeListByAt,
            parallelContents, splice, leafStable.1]

  /-- List companion of
  `parallelLeaves_keyed_frontier_perm_of_leaf_stable`. -/
  theorem parallelLeavesList_keyed_frontier_perm_of_leaf_stable
      {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl) (depth : Nat) :
      ∀ patterns,
      (∀ leaf, leaf ∈ parallelLeavesList declaration patterns →
        canonicalizeByAt key declaration depth leaf ≠
          .apply declaration.parallelUnitConstructor [] ∧
        ∀ elements,
          canonicalizeByAt key declaration depth leaf ≠
            .collection declaration.parallelCollection elements none) →
      List.Perm
        (parallelContents declaration
          (canonicalizeListByAt key declaration depth patterns))
        (canonicalizeListByAt key declaration depth
          (parallelLeavesList declaration patterns))
    | [], stable => by
        simp [parallelLeavesList, canonicalizeListByAt, parallelContents]
    | pattern :: patterns, stable => by
        have head :=
          parallelLeaves_keyed_frontier_perm_of_leaf_stable key declaration
            depth pattern (by
              intro leaf membership
              exact stable leaf (by
                simp [parallelLeavesList, membership]))
        have tail :=
          parallelLeavesList_keyed_frontier_perm_of_leaf_stable key
            declaration depth patterns (by
              intro leaf membership
              exact stable leaf (by
                simp [parallelLeavesList, membership]))
        rw [show canonicalizeListByAt key declaration depth
              (pattern :: patterns) =
            [canonicalizeByAt key declaration depth pattern] ++
              canonicalizeListByAt key declaration depth patterns by rfl,
          parallelContents_append]
        rw [parallelLeavesList]
        simpa [canonicalizeListByAt_eq_map, List.map_append] using
          head.append tail
end

/-! ## Naturality of the flattened frontier -/

/-- A representation-only singleton parallel around a bare parallel is
absorbed by keyed canonicalization.  Both normalizations select the same
visible depth; this hypothesis is essential because singleton absorption is
false when a Quote/Drop contraction changes the visible depth. -/
theorem canonicalizeByAt_parallel_singleton_parallel
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) (depth : Nat)
    (elements : List Pattern) :
    canonicalizeByAt key declaration depth
        (.collection declaration.parallelCollection
          [.collection declaration.parallelCollection elements none] none) =
      canonicalizeByAt key declaration depth
        (.collection declaration.parallelCollection elements none) := by
  let canonicalElements :=
    canonicalizeListByAt key declaration depth elements
  let normalized :=
    normalizeParallelElementsBy (key depth) declaration canonicalElements
  have normalizedNoUnit : ∀ element ∈ normalized,
      element ≠ .apply declaration.parallelUnitConstructor [] := by
    intro element membership
    have sourceMembership :=
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm (key depth)
        (parallelContents declaration canonicalElements)).mem_iff.mp membership
    exact keyedParallelFrontier_noUnit key declaration depth elements element
      (by simpa [canonicalElements, normalizeParallelElementsBy] using
        sourceMembership)
  have normalizedNoParallel : ∀ element ∈ normalized, ∀ nested,
      element ≠ .collection declaration.parallelCollection nested none := by
    intro element membership nested
    have sourceMembership :=
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm (key depth)
        (parallelContents declaration canonicalElements)).mem_iff.mp membership
    exact keyedParallelFrontier_noParallel key declaration depth elements
      element (by simpa [canonicalElements, normalizeParallelElementsBy] using
        sourceMembership) nested
  have exposed : parallelContents declaration
      [collapseParallel declaration normalized] = normalized := by
    generalize equality : normalized = patterns at *
    cases patterns with
    | nil => simp [parallelContents, collapseParallel, parallelSplice]
    | cons first remaining =>
        cases remaining with
        | nil =>
            have firstNotUnit := normalizedNoUnit first (by simp)
            have firstNotParallel := normalizedNoParallel first (by simp)
            have splice : parallelSplice declaration first = [first] :=
              parallelSplice_eq_singleton_of_not_parallel declaration first
                firstNotParallel
            simp [collapseParallel, parallelContents, splice, firstNotUnit]
        | cons second tail =>
            have filterFixed :
                (first :: second :: tail).filter
                    (fun element => element ≠
                      .apply declaration.parallelUnitConstructor []) =
                  first :: second :: tail :=
              List.filter_eq_self.mpr (fun element membership =>
                by simpa using normalizedNoUnit element membership)
            simp only [collapseParallel, parallelContents, List.flatMap_cons,
              List.flatMap_nil, parallelSplice, beq_self_eq_true, if_true,
              List.append_nil]
            exact filterFixed
  simp only [canonicalizeByAt, beq_self_eq_true, if_true,
    canonicalizeListByAt]
  change collapseParallel declaration
      (normalizeParallelElementsBy (key depth) declaration
        [collapseParallel declaration normalized]) =
    collapseParallel declaration normalized
  change collapseParallel declaration
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy (key depth)
        (parallelContents declaration [collapseParallel declaration normalized])) =
    collapseParallel declaration normalized
  rw [exposed]
  change collapseParallel declaration
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy (key depth)
        (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy (key depth)
          (parallelContents declaration canonicalElements))) =
    collapseParallel declaration normalized
  rw [Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_idempotent]
  rfl

/-- A process-typed static plan cannot retain authored Quote at the root of
its abstract pattern: rho's Quote constructor returns `Name`, whereas the
plan returns `Proc`. -/
theorem processPlan_abstractPattern_ne_quote_of_processType
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {payload : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload sourceType)
    (processType : sourceType = .base "Proc") :
    ∀ arguments, plan.abstractPattern ≠ .apply
      rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor
      arguments := by
  cases plan with
  | bvar | fvar | boundaryApplication | boundaryCollection | collection =>
      simp [CostStaticRegionPlan.abstractPattern]
  | @application _ _ _ _ _ wireName arguments declared rendered current
      preimage notBare children =>
      intro quoteArguments abstractQuote
      have labelQuote : preimage.sourceConstructor.1.label = "NQuote" :=
        (Pattern.apply.inj abstractQuote).1
      have categoryName := rhoCalc_category_eq_name_of_label_eq_quote
        preimage.sourceConstructor.2 labelQuote
      have categoryProc : preimage.sourceConstructor.1.category = "Proc" :=
        TypeExpr.base.inj processType
      rw [categoryProc] at categoryName
      exact (by decide : "Proc" ≠ "Name") categoryName
  | lambda | multiLambda => cases processType

/-- Keyed canonicalization absorbs the representation-only singleton
parallel around the common-semantic frame of any process-typed static plan.
The proof separates unit, bare-parallel, and rigid roots; the impossible
Quote root is excluded by the plan's source type. -/
theorem processPlan_commonFrame_parallelSingleton_absorbed
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      occurrences}
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      table values root}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {frameSourceBound frameTargetBound : List TypeExpr}
    (frameThinning : CostStaticBinderThinning rhoCIGSLT color
      frameSourceBound frameTargetBound)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {payload : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload (.base "Proc"))
    (scopeDepth depth : Nat) :
    let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation.toReflectivePresentationDecl
    let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
    let frame := fun pattern =>
      cospan.reifyWith environment.lookupAtom? leg
        (frameThinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (environment.reify pattern)))
    canonicalizeByAt key declaration depth
        (.collection declaration.parallelCollection
          [frame plan.abstractPattern] none) =
      canonicalizeByAt key declaration depth
        (frame plan.abstractPattern) := by
  dsimp only
  let sourceDeclaration :=
    rhoReflectivePresentation.toReflectivePresentationDecl
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
  let frame := fun pattern =>
    cospan.reifyWith environment.lookupAtom? leg
      (frameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (environment.reify pattern)))
  change canonicalizeByAt key declaration depth
      (.collection declaration.parallelCollection
        [frame plan.abstractPattern] none) =
    canonicalizeByAt key declaration depth (frame plan.abstractPattern)
  have notQuote := processPlan_abstractPattern_ne_quote_of_processType plan rfl
  by_cases unit : plan.abstractPattern =
      .apply sourceDeclaration.parallelUnitConstructor []
  · have frameEq : frame plan.abstractPattern =
        .apply declaration.parallelUnitConstructor [] := by
      rw [unit]
      simp only [frame]
      rw [cospan.reifyWith_eq_renameFVars,
        environment.reify_eq_renameFVars]
      simp [sourceDeclaration, declaration, Pattern.renameFVars, mapPattern,
        CostStaticBinderThinning.thickenAmbientBVars]
      cases color <;> rfl
    rw [frameEq]
    apply canonicalizeByAt_parallel_singleton_of_not_parallel
    intro elements equality
    have unitCanonical : canonicalizeByAt key declaration depth
        (.apply declaration.parallelUnitConstructor []) =
          .apply declaration.parallelUnitConstructor [] := by
      simp [canonicalizeByAt, canonicalizeListByAt,
        Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]
    rw [unitCanonical] at equality
    cases equality
  · by_cases parallel : ∃ elements, plan.abstractPattern =
        .collection sourceDeclaration.parallelCollection elements none
    · obtain ⟨elements, abstractEq⟩ := parallel
      have frameEq : ∃ framedElements, frame plan.abstractPattern =
          .collection declaration.parallelCollection framedElements none := by
        rw [abstractEq]
        simp only [frame]
        rw [cospan.reifyWith_eq_renameFVars,
          environment.reify_eq_renameFVars]
        simp only [Pattern.renameFVars, mapPattern,
          mapPatternList_eq_map,
          CostStaticBinderThinning.thickenAmbientBVars]
        cases color <;> refine ⟨_, rfl⟩
      obtain ⟨framedElements, frameEq⟩ := frameEq
      rw [frameEq]
      exact canonicalizeByAt_parallel_singleton_parallel key declaration depth
        framedElements
    · have stable : plan.abstractPattern ≠
            .apply sourceDeclaration.parallelUnitConstructor [] ∧
          (∀ elements, plan.abstractPattern ≠
            .collection sourceDeclaration.parallelCollection elements none) ∧
          ∀ arguments, plan.abstractPattern ≠
            .apply sourceDeclaration.quoteConstructor arguments :=
        ⟨unit, fun elements equality => parallel ⟨elements, equality⟩,
          notQuote⟩
      have framedStable := commonReifiedMappedThickened_root_stable
        environment frameThinning cospan leg scopeDepth plan.abstractPattern
          stable
      apply canonicalizeByAt_parallel_singleton_of_not_parallel
      exact (canonicalizeByAt_leaf_stable_of_root_stable key declaration depth
        (frame plan.abstractPattern) framedStable.1 framedStable.2.1
          framedStable.2.2).2

mutual
  /-- Renaming ordinary free variables commutes with parallel-frontier
  flattening.  Collection-tail variables remain schema metadata on both
  sides. -/
  theorem parallelLeaves_renameFVars
      (declaration : ReflectivePresentationDecl) (rename : String → String) :
      ∀ pattern,
      parallelLeaves declaration (Pattern.renameFVars rename pattern) =
        (parallelLeaves declaration pattern).map
          (Pattern.renameFVars rename)
    | .bvar index => by simp [parallelLeaves, Pattern.renameFVars]
    | .fvar name => by simp [parallelLeaves, Pattern.renameFVars]
    | .apply constructor arguments => by
        by_cases unit : constructor = declaration.parallelUnitConstructor ∧
          arguments = []
        · rcases unit with ⟨rfl, rfl⟩
          simp [parallelLeaves, Pattern.renameFVars]
        · simp [parallelLeaves, Pattern.renameFVars, unit]
    | .lambda binder body => by
        simp [parallelLeaves, Pattern.renameFVars]
    | .multiLambda arity binders body => by
        simp [parallelLeaves, Pattern.renameFVars]
    | .subst body replacement => by
        simp [parallelLeaves, Pattern.renameFVars]
    | .collection collectionType elements rest => by
        by_cases parallel : collectionType = declaration.parallelCollection ∧
          rest = none
        · rcases parallel with ⟨rfl, rfl⟩
          simp only [Pattern.renameFVars, parallelLeaves, and_self, if_true]
          exact parallelLeavesList_renameFVars declaration rename elements
        · simp only [Pattern.renameFVars, parallelLeaves,
            if_neg parallel, List.map_singleton]

  /-- List companion of `parallelLeaves_renameFVars`. -/
  theorem parallelLeavesList_renameFVars
      (declaration : ReflectivePresentationDecl) (rename : String → String) :
      ∀ patterns,
      parallelLeavesList declaration
          (patterns.map (Pattern.renameFVars rename)) =
        (parallelLeavesList declaration patterns).map
          (Pattern.renameFVars rename)
    | [] => rfl
    | pattern :: patterns => by
        simp only [List.map_cons, parallelLeavesList, List.map_append]
        rw [parallelLeaves_renameFVars, parallelLeavesList_renameFVars]
end

mutual
  /-- Mapping authored constructors into one Cost colour commutes with
  parallel-frontier flattening, using the mapped reflective declaration. -/
  theorem parallelLeaves_mapCostStatic
      (color : CostStaticColor) (declaration : ReflectivePresentationDecl) :
      ∀ pattern,
      parallelLeaves
          (costStaticReflectivePresentationDecl rhoCIGSLT color declaration)
          (mapPattern (color.symbols rhoCIGSLT) pattern) =
        (parallelLeaves declaration pattern).map
          (mapPattern (color.symbols rhoCIGSLT))
    | .bvar index => rfl
    | .fvar name => rfl
    | .apply constructor arguments => by
        let targetDeclaration := costStaticReflectivePresentationDecl
          rhoCIGSLT color declaration
        have unitMap : targetDeclaration.parallelUnitConstructor =
            (color.symbols rhoCIGSLT).constructor
              declaration.parallelUnitConstructor := by
          cases color <;> rfl
        by_cases unit : constructor = declaration.parallelUnitConstructor ∧
          arguments = []
        · rcases unit with ⟨rfl, rfl⟩
          have mappedUnit :
              (color.symbols rhoCIGSLT).constructor
                    declaration.parallelUnitConstructor =
                  targetDeclaration.parallelUnitConstructor ∧
                mapPatternList (color.symbols rhoCIGSLT) [] = [] :=
            ⟨unitMap.symm, rfl⟩
          simp only [mapPattern, parallelLeaves]
          rw [if_pos mappedUnit]
          simp
        · have mappedNotUnit : ¬
            ((color.symbols rhoCIGSLT).constructor constructor =
                targetDeclaration.parallelUnitConstructor ∧
              mapPatternList (color.symbols rhoCIGSLT) arguments = []) := by
            rintro ⟨constructorEq, argumentsEq⟩
            apply unit
            constructor
            · apply CostStaticColor.symbols_constructor_injective
                rhoCIGSLT color
              simpa [unitMap] using constructorEq
            · simpa [mapPatternList_eq_map] using argumentsEq
          simp only [mapPattern, parallelLeaves]
          rw [if_neg mappedNotUnit, if_neg unit]
          rfl
    | .lambda binder body => by simp [parallelLeaves, mapPattern]
    | .multiLambda arity binders body => by simp [parallelLeaves, mapPattern]
    | .subst body replacement => by simp [parallelLeaves, mapPattern]
    | .collection collectionType elements rest => by
        let targetDeclaration := costStaticReflectivePresentationDecl
          rhoCIGSLT color declaration
        have parallelMap : targetDeclaration.parallelCollection =
            declaration.parallelCollection := by
          cases color <;> rfl
        by_cases parallel : collectionType = declaration.parallelCollection ∧
          rest = none
        · rcases parallel with ⟨rfl, rfl⟩
          simp only [mapPattern, parallelLeaves, mapPatternList_eq_map]
          rw [parallelMap]
          simp only [and_self, if_true]
          exact parallelLeavesList_mapCostStatic color declaration elements
        · have mappedNotParallel : ¬
            (collectionType = targetDeclaration.parallelCollection ∧
              rest = none) := by
            simpa [parallelMap] using parallel
          simp only [mapPattern, parallelLeaves, mapPatternList_eq_map]
          rw [if_neg parallel, if_neg mappedNotParallel]
          simp [mapPattern, mapPatternList_eq_map]

  /-- List companion of `parallelLeaves_mapCostStatic`. -/
  theorem parallelLeavesList_mapCostStatic
      (color : CostStaticColor) (declaration : ReflectivePresentationDecl) :
      ∀ patterns,
      parallelLeavesList
          (costStaticReflectivePresentationDecl rhoCIGSLT color declaration)
          (patterns.map (mapPattern (color.symbols rhoCIGSLT))) =
        (parallelLeavesList declaration patterns).map
          (mapPattern (color.symbols rhoCIGSLT))
    | [] => rfl
    | pattern :: patterns => by
        simp only [List.map_cons, parallelLeavesList, List.map_append]
        rw [parallelLeaves_mapCostStatic,
          parallelLeavesList_mapCostStatic]
end

mutual
  /-- Ambient-binder reinsertion commutes with parallel-frontier
  flattening.  The operation changes only bound indices, so unit filtering
  and parallel splicing retain the same occurrence structure. -/
  theorem parallelLeaves_thickenAmbientBVars
      {color : CostStaticColor}
      {sourceBound targetBound : List TypeExpr}
      (thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound)
      (declaration : ReflectivePresentationDecl) (depth : Nat) :
      ∀ pattern,
      parallelLeaves declaration
          (thinning.thickenAmbientBVars depth pattern) =
        (parallelLeaves declaration pattern).map
          (thinning.thickenAmbientBVars depth)
    | .bvar index => by
        simp [parallelLeaves, CostStaticBinderThinning.thickenAmbientBVars]
    | .fvar name => by
        simp [parallelLeaves, CostStaticBinderThinning.thickenAmbientBVars]
    | .apply constructor arguments => by
        by_cases unit : constructor = declaration.parallelUnitConstructor ∧
            arguments = []
        · rcases unit with ⟨rfl, rfl⟩
          simp [parallelLeaves, CostStaticBinderThinning.thickenAmbientBVars]
        · simp [parallelLeaves, CostStaticBinderThinning.thickenAmbientBVars,
            unit]
    | .lambda binder body => by
        simp [parallelLeaves, CostStaticBinderThinning.thickenAmbientBVars]
    | .multiLambda arity binders body => by
        simp [parallelLeaves, CostStaticBinderThinning.thickenAmbientBVars]
    | .subst body replacement => by
        simp [parallelLeaves, CostStaticBinderThinning.thickenAmbientBVars]
    | .collection collectionType elements rest => by
        by_cases parallel : collectionType = declaration.parallelCollection ∧
            rest = none
        · rcases parallel with ⟨rfl, rfl⟩
          simp only [CostStaticBinderThinning.thickenAmbientBVars,
            parallelLeaves, and_self, if_true]
          exact parallelLeavesList_thickenAmbientBVars thinning declaration
            depth elements
        · simp only [CostStaticBinderThinning.thickenAmbientBVars,
            parallelLeaves, if_neg parallel, List.map_singleton]

  /-- List companion of `parallelLeaves_thickenAmbientBVars`. -/
  theorem parallelLeavesList_thickenAmbientBVars
      {color : CostStaticColor}
      {sourceBound targetBound : List TypeExpr}
      (thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound)
      (declaration : ReflectivePresentationDecl) (depth : Nat) :
      ∀ patterns,
      parallelLeavesList declaration
          (patterns.map (thinning.thickenAmbientBVars depth)) =
        (parallelLeavesList declaration patterns).map
          (thinning.thickenAmbientBVars depth)
    | [] => rfl
    | pattern :: patterns => by
        simp only [List.map_cons, parallelLeavesList, List.map_append]
        rw [parallelLeaves_thickenAmbientBVars,
          parallelLeavesList_thickenAmbientBVars]
end

/-- Reifying an authored frame through an endpoint environment and then into
the common semantic namespace commutes with its flattened parallel frontier.
The statement retains the complete mapped-and-thickened endpoint action used
by restoration-apex consumers. -/
theorem parallelLeaves_commonReifiedMappedThickened
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      occurrences}
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      table values root}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    (declaration : ReflectivePresentationDecl) (depth : Nat)
    (pattern : Pattern) :
    parallelLeaves
        (costStaticReflectivePresentationDecl rhoCIGSLT color declaration)
        (cospan.reifyWith environment.lookupAtom? leg
          (thinning.thickenAmbientBVars depth
            (mapPattern (color.symbols rhoCIGSLT)
              (environment.reify pattern)))) =
      (parallelLeaves declaration pattern).map (fun leaf =>
        cospan.reifyWith environment.lookupAtom? leg
          (thinning.thickenAmbientBVars depth
            (mapPattern (color.symbols rhoCIGSLT)
              (environment.reify leaf)))) := by
  rw [cospan.reifyWith_mappedThickened]
  rw [parallelLeaves_thickenAmbientBVars]
  rw [parallelLeaves_mapCostStatic]
  rw [cospan.reifyWith_eq_renameFVars]
  rw [parallelLeaves_renameFVars]
  rw [environment.reify_eq_renameFVars]
  rw [parallelLeaves_renameFVars]
  simp only [List.map_map]
  apply List.map_congr_left
  intro leaf _membership
  rw [cospan.reifyWith_mappedThickened]
  rw [environment.reify_eq_renameFVars,
    cospan.reifyWith_eq_renameFVars]
  rfl

/-- Keyed canonicalization of a common-reified endpoint frontier is the
pointwise keyed image of the authored frontier. -/
theorem canonicalizeListByAt_parallelLeaves_commonReifiedMappedThickened
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      occurrences}
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      table values root}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    (declaration : ReflectivePresentationDecl) (scopeDepth keyDepth : Nat)
    (pattern : Pattern) :
    canonicalizeListByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color declaration)
        keyDepth
        (parallelLeaves
          (costStaticReflectivePresentationDecl rhoCIGSLT color declaration)
          (cospan.reifyWith environment.lookupAtom? leg
            (thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (environment.reify pattern))))) =
      (parallelLeaves declaration pattern).map (fun leaf =>
        canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
          (costStaticReflectivePresentationDecl rhoCIGSLT color declaration)
          keyDepth
          (cospan.reifyWith environment.lookupAtom? leg
            (thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (environment.reify leaf))))) := by
  rw [parallelLeaves_commonReifiedMappedThickened]
  simp only [canonicalizeListByAt_eq_map, List.map_map]
  rfl

/-! ## Frontier size bounds -/

mutual
  /-- Flattening a parallel frontier never increases the size of an
  individual process occurrence. -/
  theorem sizeOf_le_of_mem_parallelLeaves
      (declaration : ReflectivePresentationDecl) : ∀ pattern leaf,
      leaf ∈ parallelLeaves declaration pattern → sizeOf leaf ≤ sizeOf pattern
    | .bvar index, leaf, membership => by
        simp only [parallelLeaves, List.mem_singleton] at membership
        subst leaf
        exact Nat.le_refl _
    | .fvar name, leaf, membership => by
        simp only [parallelLeaves, List.mem_singleton] at membership
        subst leaf
        exact Nat.le_refl _
    | .apply constructor arguments, leaf, membership => by
        simp only [parallelLeaves] at membership
        split at membership
        · simp at membership
        · exact Nat.le_of_eq (congrArg sizeOf
            (List.mem_singleton.mp membership))
    | .lambda binder body, leaf, membership => by
        exact Nat.le_of_eq (congrArg sizeOf
          (List.mem_singleton.mp membership))
    | .multiLambda arity binders body, leaf, membership => by
        exact Nat.le_of_eq (congrArg sizeOf
          (List.mem_singleton.mp membership))
    | .subst body replacement, leaf, membership => by
        exact Nat.le_of_eq (congrArg sizeOf
          (List.mem_singleton.mp membership))
    | .collection collectionType elements rest, leaf, membership => by
        simp only [parallelLeaves] at membership
        split at membership
        · have smaller := sizeOf_lt_of_mem_parallelLeavesList declaration
            elements leaf membership
          simp_wf
          omega
        · exact Nat.le_of_eq (congrArg sizeOf
            (List.mem_singleton.mp membership))

  /-- Every occurrence in a flattened list of parallel operands is strictly
  smaller than the operand list itself. -/
  theorem sizeOf_lt_of_mem_parallelLeavesList
      (declaration : ReflectivePresentationDecl) : ∀ patterns leaf,
      leaf ∈ parallelLeavesList declaration patterns →
        sizeOf leaf < sizeOf patterns
    | [], leaf, membership => by simp [parallelLeavesList] at membership
    | pattern :: patterns, leaf, membership => by
        simp only [parallelLeavesList, List.mem_append] at membership
        rcases membership with head | tail
        · have bounded := sizeOf_le_of_mem_parallelLeaves declaration
            pattern leaf head
          simp_wf
          omega
        · have bounded := sizeOf_lt_of_mem_parallelLeavesList declaration
            patterns leaf tail
          simp_wf
          omega
end

/-- If at least one endpoint is a bare parallel, every paired pair of
frontier occurrences is strictly smaller than the endpoint pair.  The other
endpoint only needs the non-strict frontier bound. -/
theorem pair_sizeOf_lt_of_mem_parallelLeaves_of_bareParallel
    (declaration : ReflectivePresentationDecl)
    {left right leftLeaf rightLeaf : Pattern}
    (leftMembership : leftLeaf ∈ parallelLeaves declaration left)
    (rightMembership : rightLeaf ∈ parallelLeaves declaration right)
    (bareParallel :
      (∃ elements, left = .collection declaration.parallelCollection
        elements none) ∨
      ∃ elements, right = .collection declaration.parallelCollection
        elements none) :
    sizeOf leftLeaf + sizeOf rightLeaf < sizeOf left + sizeOf right := by
  rcases bareParallel with ⟨elements, rfl⟩ | ⟨elements, rfl⟩
  · have leftSmaller := sizeOf_lt_of_mem_parallelLeavesList declaration
      elements leftLeaf (by simpa [parallelLeaves] using leftMembership)
    have rightBounded := sizeOf_le_of_mem_parallelLeaves declaration right
      rightLeaf rightMembership
    simp_wf
    omega
  · have leftBounded := sizeOf_le_of_mem_parallelLeaves declaration left
      leftLeaf leftMembership
    have rightSmaller := sizeOf_lt_of_mem_parallelLeavesList declaration
      elements rightLeaf (by simpa [parallelLeaves] using rightMembership)
    simp_wf
    omega

/-! ## Parent-frame naturality through the common semantic cospan -/

/-- A reached plan's source-canonical frame maps into the common semantic
namespace as keyed canonicalization of its uncancelled target frame.  The
available and structural depths remain independent until the target key is
known to ignore structural depth. -/
theorem reached_parentCanonicalFrame_commonReify
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (parentNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      parentNode.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      parentNode.boundaryTable values parentNode.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    (commutes : ∀ slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key)
    {payload : Pattern}
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      parentNode.plan.abstractPattern)
    (availableDepth scopeDepth : Nat) :
    cospan.reifyWith environment.lookupAtom? leg
        (parentNode.thinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (canonicalizeByDepths
              (CostStaticRegionNode.sourceSemanticPatternKeyAt parentNode
                environment)
              rhoReflectivePresentation availableDepth scopeDepth
              (environment.reify reached.plan.abstractPattern)))) =
      canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation)
        availableDepth
        (cospan.reifyWith environment.lookupAtom? leg
          (parentNode.thinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (environment.reify reached.plan.abstractPattern)))) := by
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation
  let targetKey : Nat → Nat → Pattern → Nat :=
    fun current _ candidate =>
      CostStaticRegionNode.semanticPatternKeyAt environment current candidate
  let targetFrame := parentNode.thinning.thickenAmbientBVars scopeDepth
    (mapPattern (color.symbols rhoCIGSLT)
      (environment.reify reached.plan.abstractPattern))
  have sourceKeyEq :
      CostStaticRegionNode.sourceSemanticPatternKeyAt parentNode environment =
        fun availableDepth scopeDepth pattern =>
          CostStaticRegionNode.semanticPatternKeyAt environment availableDepth
            (parentNode.thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT) pattern)) := rfl
  have targetFrameCovered : environment.Covers targetFrame := by
    intro name membership
    have canonicalMembership : name ∈
        (canonicalizeByDepths targetKey targetDeclaration availableDepth
          scopeDepth targetFrame).freeFvarNames :=
      (CostStaticAtomKeyCospan.mem_freeFvarNames_canonicalizeByDepths_iff
        targetKey targetDeclaration name availableDepth scopeDepth
        targetFrame).mpr membership
    have canonicalFrameEq :
        canonicalizeByDepths targetKey targetDeclaration availableDepth
            scopeDepth targetFrame =
          parentNode.thinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (canonicalizeByDepths
                (CostStaticRegionNode.sourceSemanticPatternKeyAt parentNode
                  environment)
                rhoReflectivePresentation availableDepth scopeDepth
                (environment.reify reached.plan.abstractPattern))) := by
      rw [sourceKeyEq]
      simpa [targetKey, targetDeclaration, targetFrame] using
        (Mettapedia.GSLT.LanguageDef.CostHereditaryCanonical.mapThicken_canonicalizeByDepths
          parentNode.thinning targetKey rhoReflectivePresentation
          availableDepth scopeDepth
          (environment.reify reached.plan.abstractPattern)).symm
    rw [canonicalFrameEq] at canonicalMembership
    exact
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.parentCanonicalFrame_atomCovered
        parentNode environment reached availableDepth scopeDepth name
          canonicalMembership
  have targetNaturality :
      parentNode.thinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (canonicalizeByDepths
              (CostStaticRegionNode.sourceSemanticPatternKeyAt parentNode
                environment)
              rhoReflectivePresentation availableDepth scopeDepth
              (environment.reify reached.plan.abstractPattern))) =
        canonicalizeByDepths targetKey targetDeclaration availableDepth
          scopeDepth targetFrame := by
    rw [sourceKeyEq]
    simpa [targetKey, targetDeclaration, targetFrame] using
      Mettapedia.GSLT.LanguageDef.CostHereditaryCanonical.mapThicken_canonicalizeByDepths
        parentNode.thinning targetKey rhoReflectivePresentation
        availableDepth scopeDepth
        (environment.reify reached.plan.abstractPattern)
  rw [targetNaturality]
  rw [environment.reifyWith_canonicalizeByDepths_semanticPatternKeyAt
    cospan leg commutes targetDeclaration availableDepth scopeDepth targetFrame
    targetFrameCovered]
  simpa [targetKey, targetDeclaration, targetFrame] using
    canonicalizeByDepths_ignoreScope
      (cospan.commonSemanticPatternKeyAt rhoCIGSLT) targetDeclaration
      availableDepth scopeDepth
      (cospan.reifyWith environment.lookupAtom? leg targetFrame)

/-- The authored declarations' two parallel spellings. -/
theorem authUnitConstructor :
    (rhoReflectivePresentation.toReflectivePresentationDecl).parallelUnitConstructor =
      "PZero" := rfl


/-! ## The frontier correspondence -/

theorem forall₂_singleton {α β : Type _} {R : α → β → Prop}
    {la : List α} {lb : List β} {a : α} {b : β}
    (ha : la = [a]) (hb : lb = [b]) (related : R a b) :
    List.Forall₂ R la lb := by
  subst ha; subst hb; exact .cons related .nil

theorem forall₂_nil {α β : Type _} {R : α → β → Prop}
    {la : List α} {lb : List β}
    (ha : la = []) (hb : lb = []) : List.Forall₂ R la lb := by
  subst ha; subst hb; exact .nil

/-- One matched process-frontier pair.  The exact binder fibre and visible
availability are retained, rather than existentially forgotten, because the
recursive semantic action consumes those indices when two frontiers are
paired. -/
def LeafWitness {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (sourceBound targetBound : List TypeExpr)
    (thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound)
    (sourceAvailable : List TypeExpr)
    (rootAbstract : Pattern)
    (rootEntries : List (TypedCostRegionBoundary rhoCIGSLT color targetFree))
    (leaf abstractLeaf : Pattern) : Prop :=
  ∃ outer : OneHoleContext,
  ∃ plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer leaf (.base "Proc"),
  ∃ skeletonContext : OneHoleContext,
    rootAbstract = skeletonContext.fill plan.abstractPattern ∧
    plan.abstractPattern = abstractLeaf ∧
    plan.RawAdmission ∧
    Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      plan.boundaryTable.entries rootEntries)

/-- Recover the standard reached-plan package without losing the retained
process fibre. -/
theorem LeafWitness.exists_reached {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {rootAbstract : Pattern}
    {rootEntries : List (TypedCostRegionBoundary rhoCIGSLT color targetFree)}
    {leaf abstractLeaf : Pattern}
    (witness : LeafWitness sourceBound targetBound thinning sourceAvailable
      rootAbstract rootEntries leaf abstractLeaf) :
    ∃ reached : CostStaticPlanReached rhoCIGSLT color targetFree leaf
        rootAbstract,
      reached.sourceBound = sourceBound ∧
      reached.targetBound = targetBound ∧
      HEq reached.thinning thinning ∧
      reached.sourceAvailable = sourceAvailable ∧
      reached.sourceType = .base "Proc" ∧
      reached.plan.abstractPattern = abstractLeaf ∧
      reached.plan.RawAdmission ∧
      Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
        reached.plan.boundaryTable.entries rootEntries) := by
  rcases witness with
    ⟨outer, plan, skeletonContext, abstractEq, abstractPatternEq, admission,
      embedding⟩
  let reached : CostStaticPlanReached rhoCIGSLT color targetFree leaf
      rootAbstract :=
    { sourceBound := sourceBound
      targetBound := targetBound
      thinning := thinning
      sourceAvailable := sourceAvailable
      outer := outer
      sourceType := .base "Proc"
      plan := plan
      skeletonContext := skeletonContext
      abstract_eq := abstractEq }
  exact ⟨reached, rfl, rfl, HEq.rfl, rfl, rfl, abstractPatternEq, admission,
    embedding⟩

/-- A certified-boundary process leaf becomes its selected semantic atom after
parent reification, constructor mapping, ambient-binder reinsertion, and keyed
canonicalization.  The selected slot is recovered from the retained reached
occurrence, not by comparing boundary values. -/
theorem boundaryPlan_commonReifiedMappedThickened_eq_atom
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      occurrences}
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      table}
    {rootAbstract : Pattern}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      table values rootAbstract}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {frameSourceBound frameTargetBound : List TypeExpr}
    (frameThinning : CostStaticBinderThinning rhoCIGSLT color
      frameSourceBound frameTargetBound)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer skeletonContext : OneHoleContext}
    {payload : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload (.base "Proc"))
    (rootEq : rootAbstract = skeletonContext.fill plan.abstractPattern)
    (boundaryClass : plan.rootClass.IsCertifiedBoundary)
    (scopeDepth keyDepth : Nat) :
    let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
      color rhoReflectivePresentation.toReflectivePresentationDecl
    let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
    ∃ slot : Fin environment.atomCount,
      canonicalizeByAt key targetDeclaration keyDepth
          (cospan.reifyWith environment.lookupAtom? leg
            (frameThinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (environment.reify plan.abstractPattern)))) =
        cospan.reifyWith environment.lookupAtom? leg
          (.fvar (environment.atomName slot)) := by
  dsimp only
  let reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract :=
    { sourceBound := sourceBound
      targetBound := targetBound
      thinning := thinning
      sourceAvailable := sourceAvailable
      outer := outer
      sourceType := .base "Proc"
      plan := plan
      skeletonContext := skeletonContext
      abstract_eq := rootEq }
  obtain ⟨boundary⟩ :=
    reached.nonempty_boundaryView_of_boundaryClass boundaryClass
  obtain ⟨slot, selected⟩ := Option.isSome_iff_exists.mp
    (environment.slotOfName?_isSome_of_occurrence
      boundary.stopped.boundaryOccurrence)
  refine ⟨slot, ?_⟩
  rw [boundary.abstract_eq]
  simp only [CostStaticAtomEnvironment.reify,
    CostStaticBinderThinning.thickenAmbientBVars, mapPattern]
  unfold CostStaticAtomEnvironment.reifyName
  have selected' : environment.slotOfName?
      (costRegionBoundaryVariableName boundary.stopped.certified.typed.boundary) =
        some slot := by
    simpa only [boundary.stopped.boundaryOccurrence_name] using selected
  rw [selected']
  simp [Pattern.renameFVars, canonicalizeByAt]

/-- Equal semantic keys for two certified-boundary process leaves give an
arbitrary-depth common restoration apex.  Each endpoint is first identified
with its exact parent semantic atom; the atom support dichotomy then upgrades
the one-depth key equality without identifying boundary values or slots. -/
theorem boundaryPlans_commonRestorationApex_of_keyEq
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightTable}
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightTable rightValues rightRoot}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    {leftFrameSourceBound leftFrameTargetBound : List TypeExpr}
    {rightFrameSourceBound rightFrameTargetBound : List TypeExpr}
    (leftFrameThinning : CostStaticBinderThinning rhoCIGSLT color
      leftFrameSourceBound leftFrameTargetBound)
    (rightFrameThinning : CostStaticBinderThinning rhoCIGSLT color
      rightFrameSourceBound rightFrameTargetBound)
    {leftSourceBound leftTargetBound rightSourceBound rightTargetBound :
      List TypeExpr}
    {leftThinning : CostStaticBinderThinning rhoCIGSLT color leftSourceBound
      leftTargetBound}
    {rightThinning : CostStaticBinderThinning rhoCIGSLT color rightSourceBound
      rightTargetBound}
    {leftAvailable rightAvailable : List TypeExpr}
    {leftOuter rightOuter leftContext rightContext : OneHoleContext}
    {leftPayload rightPayload : Pattern}
    (leftPlan : CostStaticRegionPlan rhoCIGSLT color targetFree leftSourceBound
      leftTargetBound leftThinning leftAvailable leftOuter leftPayload
      (.base "Proc"))
    (rightPlan : CostStaticRegionPlan rhoCIGSLT color targetFree
      rightSourceBound rightTargetBound rightThinning rightAvailable rightOuter
      rightPayload (.base "Proc"))
    (leftRootEq : leftRoot = leftContext.fill leftPlan.abstractPattern)
    (rightRootEq : rightRoot = rightContext.fill rightPlan.abstractPattern)
    (leftBoundary : leftPlan.rootClass.IsCertifiedBoundary)
    (rightBoundary : rightPlan.rootClass.IsCertifiedBoundary)
    {exposedSupport : List TypeExpr}
    (leftSupport : ∀ slot,
      (leftEnvironment.atomValue slot).key.targetSupport = exposedSupport ∨
        (leftEnvironment.atomValue slot).key.targetSupport = [])
    (rightSupport : ∀ slot,
      (rightEnvironment.atomValue slot).key.targetSupport = exposedSupport ∨
        (rightEnvironment.atomValue slot).key.targetSupport = [])
    (scopeDepth keyDepth restorationDepth : Nat)
    (keyEq :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
        color rhoReflectivePresentation.toReflectivePresentationDecl
      let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
      key keyDepth
          (canonicalizeByAt key targetDeclaration keyDepth
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (leftFrameThinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols rhoCIGSLT)
                  (leftEnvironment.reify leftPlan.abstractPattern))))) =
        key keyDepth
          (canonicalizeByAt key targetDeclaration keyDepth
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (rightFrameThinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols rhoCIGSLT)
                  (rightEnvironment.reify rightPlan.abstractPattern)))))) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
      color rhoReflectivePresentation.toReflectivePresentationDecl
    let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
      targetDeclaration restorationDepth
      (canonicalizeByAt key targetDeclaration keyDepth
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (leftFrameThinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (leftEnvironment.reify leftPlan.abstractPattern)))))
      (canonicalizeByAt key targetDeclaration keyDepth
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rightFrameThinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (rightEnvironment.reify rightPlan.abstractPattern))))) := by
  dsimp only at keyEq ⊢
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation.toReflectivePresentationDecl
  let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
  obtain ⟨leftSlot, leftShape⟩ :=
    boundaryPlan_commonReifiedMappedThickened_eq_atom leftEnvironment
      leftFrameThinning cospan cospan.leftSlot leftPlan leftRootEq leftBoundary
      scopeDepth keyDepth
  obtain ⟨rightSlot, rightShape⟩ :=
    boundaryPlan_commonReifiedMappedThickened_eq_atom rightEnvironment
      rightFrameThinning cospan cospan.rightSlot rightPlan rightRootEq
      rightBoundary scopeDepth keyDepth
  have atomKeyEq :
      key keyDepth
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (.fvar (leftEnvironment.atomName leftSlot))) =
        key keyDepth
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (.fvar (rightEnvironment.atomName rightSlot))) := by
    rw [← leftShape, ← rightShape]
    exact keyEq
  have atomApex :=
    RhoMatchedStaticFramesApex.atom_of_keyEqAt_of_support_eq_or_nil
      leftEnvironment rightEnvironment leftSlot rightSlot
      (leftSupport leftSlot) (rightSupport rightSlot) keyDepth atomKeyEq
      targetDeclaration restorationDepth
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    leftShape.symm rightShape.symm atomApex

/-- A structural application tree retains its outer application head under
hereditary normalization; only the argument spine is normalized. -/
theorem CostRegionTree.exists_normalize_pattern_eq_apply_of_structural
    {targetFree : WellSorted.FreeTypeContext} {available outer : List TypeExpr}
    {wire : String} {arguments : List Pattern} {type : TypeExpr}
    (tree : CostRegionTree rhoCIGSLT targetFree available outer
      (.apply wire arguments) type)
    (structural : tree.rootIsStatic = false) :
    ∃ normalizedArguments,
      (tree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
          .apply wire normalizedArguments := by
  cases tree.structuralRootView structural with
  | neutralApplicationOrdinary _ _ _ _ _ _ children =>
      exact ⟨(children.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).patterns, by
        simp [CostRegionTree.normalize]⟩
  | neutralApplicationQuote _ _ _ _ _ _ children =>
      exact ⟨(children.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).patterns, by
        simp [CostRegionTree.normalize]⟩

/-- A certified process boundary retains the rendered head of its
outside-current declared constructor through hereditary normalization.

The proof uses the reached boundary view instead of eliminating the indexed
plan.  A hypothetical static tree at the same raw payload must have the plan
colour by the generated `Proc` fibre; render injectivity would then identify
an outside-current boundary constructor with a current constructor. -/
theorem processBoundaryPlan_exists_normalized_application
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {payload : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload (.base "Proc"))
    (boundaryClass : plan.rootClass.IsCertifiedBoundary)
    (tree : CostRegionTree rhoCIGSLT targetFree sourceAvailable [] payload
      (mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc"))) :
    ∃ constructor : rhoCIGSLT.DeclaredCostConstructor,
    ∃ wire normalizedArguments,
      rhoCIGSLT.renderDeclaredCostConstructor constructor = wire ∧
      rhoCIGSLT.declaredCostConstructorRole constructor ≠ .static color ∧
      (tree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
          .apply wire normalizedArguments := by
  let reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      plan.abstractPattern :=
    { sourceBound := sourceBound
      targetBound := targetBound
      thinning := thinning
      sourceAvailable := sourceAvailable
      outer := outer
      sourceType := .base "Proc"
      plan := plan
      skeletonContext := .hole
      abstract_eq := rfl }
  obtain ⟨boundary⟩ :=
    reached.nonempty_boundaryView_of_boundaryClass boundaryClass
  have member : boundary.stopped.certified.typed ∈
      plan.boundaryTable.entries := by
    rw [boundary.entries_eq]
    simp
  have kind := plan.boundaryKind_of_mem_entries
    boundary.stopped.certified.typed member
  cases kind with
  | application constructor rendered outsideCurrent content =>
      rename_i wire arguments
      have payloadShape : payload = .apply wire arguments :=
        boundary.content_eq.symm.trans content
      subst payload
      have structural : tree.rootIsStatic = false := by
        by_contra notStructural
        have static : tree.rootIsStatic = true :=
          Bool.eq_true_of_not_eq_false notStructural
        obtain ⟨treeColor, view⟩ :=
          tree.staticRootView_of_rootIsStatic static
        have colorEq : treeColor = color := by
          by_contra different
          have flipEq : treeColor = color.flip :=
            CostStaticColor.eq_flip_of_ne (Ne.symm different)
          subst treeColor
          apply mapTypeExpr_flipProc_ne color.flip
            (.base view.node.sourceSort.1)
          simpa [CostStaticColor.mapLangSort_name, mapTypeExpr] using
            view.typeEq.symm
        subst treeColor
        obtain ⟨currentConstructor, decoded, current⟩ :=
          view.node.plan.application_dispatch_of_isStaticRoot
            view.node.rootStatic view.patternEq
        have currentRendered :
            rhoCIGSLT.renderDeclaredCostConstructor currentConstructor = wire :=
          rhoCIGSLT.renderDeclaredCostConstructor_eq_of_decode wire
            currentConstructor decoded
        have constructorEq : constructor = currentConstructor :=
          rhoCIGSLT.renderDeclaredCostConstructor_injective
            (rendered.trans currentRendered.symm)
        subst currentConstructor
        exact outsideCurrent current
      obtain ⟨normalizedArguments, normalized⟩ :=
        CostRegionTree.exists_normalize_pattern_eq_apply_of_structural tree
          structural
      exact ⟨constructor, wire, normalizedArguments, rendered,
        outsideCurrent, normalized⟩
  | collection currentRejected oppositeChoice oppositeSelected content =>
      exact absurd oppositeSelected (fun selected =>
        rho_boundaryCollection_choices_absurd color targetFree _ _ _ _
          selected currentRejected)

theorem boundaryPlan_commonAtom_normalized_application
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (trees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.finiteBoundaryTable
      (trees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      node.plan.abstractPattern}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {frameSourceBound frameTargetBound : List TypeExpr}
    (frameThinning : CostStaticBinderThinning rhoCIGSLT color
      frameSourceBound frameTargetBound)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer skeletonContext : OneHoleContext}
    {payload : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload (.base "Proc"))
    (rootEq : node.plan.abstractPattern =
      skeletonContext.fill plan.abstractPattern)
    (embedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      plan.boundaryTable.entries node.plan.boundaryTable.entries)
    (boundaryClass : plan.rootClass.IsCertifiedBoundary)
    (scopeDepth keyDepth : Nat) :
    let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
      color rhoReflectivePresentation.toReflectivePresentationDecl
    let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
    ∃ slot : Fin environment.atomCount,
    ∃ constructor : rhoCIGSLT.DeclaredCostConstructor,
    ∃ wire normalizedArguments,
      canonicalizeByAt key targetDeclaration keyDepth
          (cospan.reifyWith environment.lookupAtom? leg
            (frameThinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (environment.reify plan.abstractPattern)))) =
        cospan.reifyWith environment.lookupAtom? leg
          (.fvar (environment.atomName slot)) ∧
      rhoCIGSLT.renderDeclaredCostConstructor constructor = wire ∧
      rhoCIGSLT.declaredCostConstructorRole constructor ≠ .static color ∧
      (environment.atomValue slot).key.normal =
        .apply wire normalizedArguments := by
  dsimp only
  let reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      node.plan.abstractPattern :=
    { sourceBound := sourceBound
      targetBound := targetBound
      thinning := thinning
      sourceAvailable := sourceAvailable
      outer := outer
      sourceType := .base "Proc"
      plan := plan
      skeletonContext := skeletonContext
      abstract_eq := rootEq }
  obtain ⟨boundary⟩ :=
    reached.nonempty_boundaryView_of_boundaryClass boundaryClass
  have singletonEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [boundary.stopped.certified.typed]
        node.plan.boundaryTable.entries := by
    rw [← boundary.entries_eq]
    exact embedding
  obtain ⟨slot, selected⟩ := Option.isSome_iff_exists.mp
    (environment.slotOfName?_isSome_of_occurrence
      boundary.stopped.boundaryOccurrence)
  let selectedTree :=
    boundary.stopped.selectedTreeFromForest singletonEmbedding trees
  let processTree :=
    (((selectedTree.reindexAvailable boundary.targetSupport_eq).reindexPattern
      boundary.content_eq).reindexType boundary.targetType_eq)
  obtain ⟨constructor, wire, normalizedArguments, rendered, outsideCurrent,
      processNormal⟩ :=
    processBoundaryPlan_exists_normalized_application plan boundaryClass processTree
  have processTreeNormal :
      (processTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (selectedTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    simp [processTree, CostRegionTree.reindexType_normalize,
      CostRegionTree.reindexPattern_normalize,
      CostRegionTree.reindexAvailable_normalize]
  have selectedNormal :
      (selectedTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        .apply wire normalizedArguments :=
    processTreeNormal.symm.trans processNormal
  have atomEq := boundary.stopped.environmentAtom_eq_selectedTree
    (kernel := rhoHereditaryNormalizationKernel)
    CostCanonicalLaws.rho_unambiguousStaticDecomposition singletonEmbedding
      trees (environment := environment) (slot := slot) selected
  have atomNormal := congrArg (fun atom => atom.key.normal) atomEq
  have atomNormalEq : (environment.atomValue slot).key.normal =
      (selectedTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    simpa only [TypedCostStaticAtom.ofBoundaryValue,
      CostRegionTree.normalizedBoundaryValue_pattern,
      rhoHereditaryNormalizationKernel] using atomNormal
  have frameShape :
      canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          keyDepth
          (cospan.reifyWith environment.lookupAtom? leg
            (frameThinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (environment.reify plan.abstractPattern)))) =
        cospan.reifyWith environment.lookupAtom? leg
          (.fvar (environment.atomName slot)) := by
    rw [boundary.abstract_eq]
    simp only [CostStaticAtomEnvironment.reify,
      CostStaticBinderThinning.thickenAmbientBVars, mapPattern]
    unfold CostStaticAtomEnvironment.reifyName
    have selected' : environment.slotOfName?
        (costRegionBoundaryVariableName
          boundary.stopped.certified.typed.boundary) = some slot := by
      simpa only [boundary.stopped.boundaryOccurrence_name] using selected
    rw [selected']
    simp [Pattern.renameFVars, canonicalizeByAt]
  exact ⟨slot, constructor, wire, normalizedArguments, frameShape, rendered,
    outsideCurrent, atomNormalEq.trans selectedNormal⟩

theorem processPlan_abstract_root_cases
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {payload : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload (.base "Proc"))
    (notBoundary : ¬ plan.rootClass.IsCertifiedBoundary) :
    (∃ index, plan.abstractPattern = .bvar index) ∨
    (∃ name, plan.abstractPattern =
      .fvar (costRegionSourceVariableName name)) ∨
    (∃ constructor : rhoCIGSLT.DeclaredCostConstructor,
      ∃ sourceWire targetWire arguments,
        rhoCIGSLT.renderDeclaredCostConstructor constructor = targetWire ∧
        rhoCIGSLT.declaredCostConstructorRole constructor = .static color ∧
        targetWire = (color.symbols rhoCIGSLT).constructor sourceWire ∧
        plan.abstractPattern = .apply sourceWire arguments) ∨
    ∃ collectionType elements rest,
      plan.abstractPattern = .collection collectionType elements rest := by
  generalize sourceTypeEq : (TypeExpr.base "Proc") = sourceType at plan
  cases plan with
  | bvar sourceIndex lookup correspondence availableScope =>
      exact Or.inl ⟨sourceIndex, rfl⟩
  | fvar lookup =>
      rename_i name
      exact Or.inr (Or.inl ⟨name, rfl⟩)
  | boundaryApplication constructor rendered outsideCurrent certified
      certifies =>
      exact (notBoundary (by
        simp [CostStaticRegionPlan.rootClass,
          CostStaticPlanRootClass.IsCertifiedBoundary])).elim
  | application constructor rendered current preimage notBare children =>
      have targetWire :
          rhoCIGSLT.renderDeclaredCostConstructor constructor =
            (color.symbols rhoCIGSLT).constructor
              preimage.sourceConstructor.1.label := by
        exact (rhoCIGSLT.materializeDeclaredCostConstructor_label
          constructor).symm.trans preimage.labelMap
      exact Or.inr (Or.inr (Or.inl ⟨constructor,
        preimage.sourceConstructor.1.label,
        (color.symbols rhoCIGSLT).constructor
          preimage.sourceConstructor.1.label,
        children.abstractPatterns, targetWire, current, rfl, rfl⟩))
  | lambda bodyPlan => cases sourceTypeEq
  | multiLambda bodyPlan => cases sourceTypeEq
  | collection choice selected children =>
      exact Or.inr (Or.inr (Or.inr ⟨_, children.abstractPatterns,
        Option.map costRegionSourceVariableName _, rfl⟩))
  | boundaryCollection currentRejected oppositeChoice oppositeSelected
      certified certifies =>
      exact (notBoundary (by
        simp [CostStaticRegionPlan.rootClass,
          CostStaticPlanRootClass.IsCertifiedBoundary])).elim

/-- After parent reification and keyed canonicalization, a non-boundary
process leaf still restores with one of the four possible non-boundary root
shapes.  In the application case the retained head is rendered by a
constructor declared static at the current colour. -/
theorem nonBoundaryPlan_commonFrame_restored_root_cases
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      occurrences}
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      table values root}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {frameSourceBound frameTargetBound : List TypeExpr}
    (frameThinning : CostStaticBinderThinning rhoCIGSLT color
      frameSourceBound frameTargetBound)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    (legCommutes : ∀ slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key)
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer skeletonContext : OneHoleContext}
    {payload : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload (.base "Proc"))
    (rootEq : root = skeletonContext.fill plan.abstractPattern)
    (notBoundary : ¬ plan.rootClass.IsCertifiedBoundary)
    (stable : plan.abstractPattern ≠
        .apply rhoReflectivePresentation.toReflectivePresentationDecl.parallelUnitConstructor [] ∧
      (∀ elements, plan.abstractPattern ≠
        .collection rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
          elements none) ∧
      ∀ arguments, plan.abstractPattern ≠
        .apply rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor
          arguments)
    (scopeDepth keyDepth : Nat) :
    let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
      color rhoReflectivePresentation.toReflectivePresentationDecl
    let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
    let endpoint := canonicalizeByAt key targetDeclaration keyDepth
      (cospan.reifyWith environment.lookupAtom? leg
        (frameThinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (environment.reify plan.abstractPattern))))
    let restored := ReflectiveContextSupport.substituteAt
      rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
        cospan.commonAssignment keyDepth endpoint
    (∃ index, restored = .bvar index) ∨
    (∃ name, restored = .fvar name) ∨
    (∃ constructor : rhoCIGSLT.DeclaredCostConstructor,
      ∃ wire arguments,
        rhoCIGSLT.renderDeclaredCostConstructor constructor = wire ∧
        rhoCIGSLT.declaredCostConstructorRole constructor = .static color ∧
        restored = .apply wire arguments) ∨
    ∃ collectionType elements rest,
      restored = .collection collectionType elements rest := by
  dsimp only
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation.toReflectivePresentationDecl
  let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
  let frame := fun pattern =>
    cospan.reifyWith environment.lookupAtom? leg
      (frameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (environment.reify pattern)))
  let endpoint := canonicalizeByAt key targetDeclaration keyDepth
    (frame plan.abstractPattern)
  let restored := ReflectiveContextSupport.substituteAt
    rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
      cospan.commonAssignment keyDepth endpoint
  change (∃ index, restored = .bvar index) ∨
    (∃ name, restored = .fvar name) ∨
    (∃ constructor : rhoCIGSLT.DeclaredCostConstructor,
      ∃ wire arguments,
        rhoCIGSLT.renderDeclaredCostConstructor constructor = wire ∧
        rhoCIGSLT.declaredCostConstructorRole constructor = .static color ∧
        restored = .apply wire arguments) ∨
    ∃ collectionType elements rest,
      restored = .collection collectionType elements rest
  have framedStable := commonReifiedMappedThickened_root_stable environment
    frameThinning cospan leg scopeDepth plan.abstractPattern stable
  change frame plan.abstractPattern ≠
        .apply targetDeclaration.parallelUnitConstructor [] ∧
      (∀ elements, frame plan.abstractPattern ≠
        .collection targetDeclaration.parallelCollection elements none) ∧
      ∀ arguments, frame plan.abstractPattern ≠
        .apply targetDeclaration.quoteConstructor arguments at framedStable
  rcases processPlan_abstract_root_cases plan notBoundary with
      ⟨index, abstractEq⟩ | ⟨name, abstractEq⟩ |
      ⟨constructor, sourceWire, targetWire, arguments, rendered, current,
        targetWireEq, abstractEq⟩ |
      ⟨collectionType, elements, rest, abstractEq⟩
  · left
    refine ⟨frameThinning.embedIndexAt scopeDepth index, ?_⟩
    have frameShape : frame plan.abstractPattern =
        .bvar (frameThinning.embedIndexAt scopeDepth index) := by
      rw [abstractEq]
      simp only [frame, cospan.reifyWith_eq_renameFVars,
        environment.reify_eq_renameFVars, Pattern.renameFVars, mapPattern,
        CostStaticBinderThinning.thickenAmbientBVars]
    dsimp only [restored, endpoint]
    rw [frameShape]
    simp only [canonicalizeByAt,
      ReflectiveContextSupport.substituteAt]
  · right; left
    have rootFill : root = skeletonContext.fill
        (.fvar (costRegionSourceVariableName name)) := by
      rw [← abstractEq]
      exact rootEq
    let occurrence : CostStaticFVarOccurrence root :=
      { name := costRegionSourceVariableName name
        context := skeletonContext
        selected := by
          rw [rootFill]
          exact Selects.of_fill _ _ }
    obtain ⟨slot, selected⟩ := Option.isSome_iff_exists.mp
      (environment.slotOfName?_isSome_of_occurrence occurrence)
    have selectedAtName : environment.slotOfName?
        (costRegionSourceVariableName name) = some slot := by
      simpa only [occurrence] using selected
    have frameShape : frame plan.abstractPattern =
        .fvar (cospan.commonAtomName (leg slot)) := by
      rw [abstractEq]
      simp [frame,
        Pattern.renameFVars, mapPattern,
        CostStaticBinderThinning.thickenAmbientBVars,
        CostStaticAtomEnvironment.reifyName, selectedAtName,
        CostStaticAtomKeyCospan.reifyNameWith,
        CostStaticAtomEnvironment.lookupAtom?_atomName]
    refine ⟨name, ?_⟩
    dsimp only [restored, endpoint]
    rw [frameShape]
    simp only [canonicalizeByAt,
      ReflectiveContextSupport.substituteAt,
      CostStaticAtomKeyCospan.commonAssignment_commonAtomName,
      CostStaticAtomKeyCospan.commonSupport_commonAtomName]
    rw [legCommutes slot]
    rw [environment.atomValue_normal_eq_of_slotOfName?_eq_some
      occurrence slot selected]
    have assignmentEq : values.assignment table occurrence.name =
        .fvar name := by
      simpa only [occurrence] using values.assignment_sourceVariable name
    rw [assignmentEq]
    simp [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]
  · right; right; left
    obtain ⟨framedArguments, frameShape⟩ : ∃ framedArguments,
        frame plan.abstractPattern = .apply targetWire framedArguments := by
      rw [abstractEq]
      rw [show targetWire = (color.symbols rhoCIGSLT).constructor sourceWire
        from targetWireEq]
      simp [frame, Pattern.renameFVars, mapPattern,
        mapPatternList_eq_map,
        CostStaticBinderThinning.thickenAmbientBVars]
    have notQuote : targetWire ≠ targetDeclaration.quoteConstructor := by
      intro equality
      apply framedStable.2.2 framedArguments
      rw [frameShape, equality]
    let childDepth := if ReflectiveContextSupport.isQuoteConstructor
        rhoCIGSLT.costWholeReflectionProfile targetWire then 0 else keyDepth
    let normalizedArguments := canonicalizeListByAt key targetDeclaration
      keyDepth framedArguments
    let restoredArguments := normalizedArguments.map
      (ReflectiveContextSupport.substituteAt
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment childDepth)
    refine ⟨constructor, targetWire, restoredArguments, rendered, current, ?_⟩
    dsimp only [restored, endpoint]
    rw [frameShape]
    simp [canonicalizeByAt,
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
      notQuote,
      restoredArguments, normalizedArguments, childDepth,
      ReflectiveContextSupport.substituteAt]
  · right; right; right
    obtain ⟨framedElements, frameShape⟩ : ∃ framedElements,
        frame plan.abstractPattern =
          .collection collectionType framedElements rest := by
      rw [abstractEq]
      simp [frame, Pattern.renameFVars, mapPattern,
        mapPatternList_eq_map,
        CostStaticBinderThinning.thickenAmbientBVars]
    dsimp only [restored, endpoint]
    rw [frameShape]
    by_cases restNone : rest = none
    · subst rest
      have notParallel : collectionType ≠ targetDeclaration.parallelCollection := by
        intro equality
        apply framedStable.2.1 framedElements
        rw [frameShape, equality]
      let normalizedElements := canonicalizeListByAt key targetDeclaration
        keyDepth framedElements
      let restoredElements := normalizedElements.map
        (ReflectiveContextSupport.substituteAt
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment keyDepth)
      refine ⟨collectionType, restoredElements, none, ?_⟩
      simp [canonicalizeByAt, notParallel,
        restoredElements, normalizedElements,
        ReflectiveContextSupport.substituteAt]
    · let normalizedElements := canonicalizeListByAt key targetDeclaration
        keyDepth framedElements
      let restoredElements := normalizedElements.map
        (ReflectiveContextSupport.substituteAt
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment keyDepth)
      refine ⟨collectionType, restoredElements, rest, ?_⟩
      simp [canonicalizeByAt,
        restoredElements, normalizedElements,
        ReflectiveContextSupport.substituteAt]

/-- A certified process boundary and a non-boundary process leaf cannot tie
under the common semantic ordering key.  The boundary restores to an
application headed by an outside-current declared constructor, whereas every
non-boundary root is rigid, an authored source variable, a current
application, or a collection. -/
theorem boundaryPlan_commonSemanticKey_ne_nonBoundaryPlan
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (leftNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.finiteBoundaryTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftNode.plan.abstractPattern}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    {rightOccurrences : List CostRegionOccurrence}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightTable}
    {rightRoot : Pattern}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightTable rightValues rightRoot}
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    {leftFrameSourceBound leftFrameTargetBound : List TypeExpr}
    {rightFrameSourceBound rightFrameTargetBound : List TypeExpr}
    (leftFrameThinning : CostStaticBinderThinning rhoCIGSLT color
      leftFrameSourceBound leftFrameTargetBound)
    (rightFrameThinning : CostStaticBinderThinning rhoCIGSLT color
      rightFrameSourceBound rightFrameTargetBound)
    {leftSourceBound leftTargetBound rightSourceBound rightTargetBound :
      List TypeExpr}
    {leftThinning : CostStaticBinderThinning rhoCIGSLT color leftSourceBound
      leftTargetBound}
    {rightThinning : CostStaticBinderThinning rhoCIGSLT color rightSourceBound
      rightTargetBound}
    {leftAvailable rightAvailable : List TypeExpr}
    {leftOuter rightOuter leftContext rightContext : OneHoleContext}
    {leftPayload rightPayload : Pattern}
    (leftPlan : CostStaticRegionPlan rhoCIGSLT color targetFree leftSourceBound
      leftTargetBound leftThinning leftAvailable leftOuter leftPayload
      (.base "Proc"))
    (rightPlan : CostStaticRegionPlan rhoCIGSLT color targetFree
      rightSourceBound rightTargetBound rightThinning rightAvailable rightOuter
      rightPayload (.base "Proc"))
    (leftRootEq : leftNode.plan.abstractPattern =
      leftContext.fill leftPlan.abstractPattern)
    (rightRootEq : rightRoot = rightContext.fill rightPlan.abstractPattern)
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      leftPlan.boundaryTable.entries leftNode.plan.boundaryTable.entries)
    (leftBoundary : leftPlan.rootClass.IsCertifiedBoundary)
    (rightNotBoundary : ¬ rightPlan.rootClass.IsCertifiedBoundary)
    (rightStable : rightPlan.abstractPattern ≠
        .apply rhoReflectivePresentation.toReflectivePresentationDecl.parallelUnitConstructor [] ∧
      (∀ elements, rightPlan.abstractPattern ≠
        .collection rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
          elements none) ∧
      ∀ arguments, rightPlan.abstractPattern ≠
        .apply rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor
          arguments)
    (scopeDepth keyDepth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
      color rhoReflectivePresentation.toReflectivePresentationDecl
    let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
    let leftEndpoint := canonicalizeByAt key targetDeclaration keyDepth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (leftFrameThinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (leftEnvironment.reify leftPlan.abstractPattern))))
    let rightEndpoint := canonicalizeByAt key targetDeclaration keyDepth
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (rightFrameThinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (rightEnvironment.reify rightPlan.abstractPattern))))
    key keyDepth leftEndpoint ≠ key keyDepth rightEndpoint := by
  dsimp only
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation.toReflectivePresentationDecl
  let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
  let leftEndpoint := canonicalizeByAt key targetDeclaration keyDepth
    (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
      (leftFrameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (leftEnvironment.reify leftPlan.abstractPattern))))
  let rightEndpoint := canonicalizeByAt key targetDeclaration keyDepth
    (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
      (rightFrameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (rightEnvironment.reify rightPlan.abstractPattern))))
  change key keyDepth leftEndpoint ≠ key keyDepth rightEndpoint
  obtain ⟨leftSlot, boundaryConstructor, boundaryWire,
      boundaryArguments, leftShape, boundaryRendered, boundaryOutside,
      boundaryNormal⟩ :=
    boundaryPlan_commonAtom_normalized_application leftNode leftTrees
      leftEnvironment leftFrameThinning cospan cospan.leftSlot leftPlan
      leftRootEq leftEmbedding leftBoundary scopeDepth keyDepth
  have leftRestoredShape : ∃ restoredArguments,
      ReflectiveContextSupport.substituteAt
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment keyDepth leftEndpoint =
        .apply boundaryWire restoredArguments := by
    let shift := keyDepth -
      (leftEnvironment.atomValue leftSlot).key.targetSupport.length
    let restoredArguments := boundaryArguments.map
      (Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0 shift)
    refine ⟨restoredArguments, ?_⟩
    dsimp only [leftEndpoint]
    rw [leftShape]
    simp only [CostStaticAtomKeyCospan.reifyWith,
      CostStaticAtomEnvironment.lookupAtom?_atomName,
      ReflectiveContextSupport.substituteAt,
      CostStaticAtomKeyCospan.commonAssignment_commonAtomName,
      CostStaticAtomKeyCospan.commonSupport_commonAtomName]
    rw [cospan.leftCommutes leftSlot, boundaryNormal]
    simp [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars,
      restoredArguments, shift]
  have rightCases := nonBoundaryPlan_commonFrame_restored_root_cases
    rightEnvironment rightFrameThinning cospan cospan.rightSlot
      cospan.rightCommutes rightPlan rightRootEq rightNotBoundary rightStable
      scopeDepth keyDepth
  intro keyEq
  have restoredEq :=
    (cospan.commonSemanticPatternKeyAt_eq_iff rhoCIGSLT keyDepth
      leftEndpoint rightEndpoint).mp keyEq
  obtain ⟨leftRestoredArguments, leftRestored⟩ := leftRestoredShape
  rcases rightCases with ⟨index, rightRestored⟩ |
      ⟨name, rightRestored⟩ |
      ⟨rightConstructor, rightWire, rightArguments, rightRendered,
        rightCurrent, rightRestored⟩ |
      ⟨collectionType, elements, rest, rightRestored⟩
  · rw [leftRestored, rightRestored] at restoredEq
    cases restoredEq
  · rw [leftRestored, rightRestored] at restoredEq
    cases restoredEq
  · rw [leftRestored, rightRestored] at restoredEq
    have wireEq : boundaryWire = rightWire :=
      (Pattern.apply.inj restoredEq).1
    have constructorEq : boundaryConstructor = rightConstructor :=
      rhoCIGSLT.renderDeclaredCostConstructor_injective
        (boundaryRendered.trans (wireEq.trans rightRendered.symm))
    subst rightConstructor
    exact boundaryOutside rightCurrent
  · rw [leftRestored, rightRestored] at restoredEq
    cases restoredEq

/-- A frontier theorem available for every payload drawn from one collection.
This separates the structural list traversal from recursion on the enclosing
pattern. -/
structure PlanFrontierForElements
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (sourceBound targetBound : List TypeExpr)
    (thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound)
    (sourceAvailable : List TypeExpr)
    (rootAbstract : Pattern)
    (rootEntries : List (TypedCostRegionBoundary rhoCIGSLT color targetFree))
    (elements : List Pattern) : Prop where
  relates : ∀ {outer : OneHoleContext} {payload : Pattern},
    payload ∈ elements →
    ∀ (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer payload (.base "Proc")),
      plan.RawAdmission →
      ∀ (F : OneHoleContext),
        rootAbstract = F.fill plan.abstractPattern →
        Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
          plan.boundaryTable.entries rootEntries) →
        List.Forall₂ (LeafWitness sourceBound targetBound thinning
          sourceAvailable rootAbstract rootEntries)
          (parallelLeaves
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl) payload)
          (parallelLeaves rhoReflectivePresentation.toReflectivePresentationDecl
            plan.abstractPattern)

/-- Traverse an element plan once frontier correspondence is available for
each raw element of the collection. -/
theorem frontierForall2_spine_aux
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {rootAbstract : Pattern}
    {rootEntries : List (TypedCostRegionBoundary rhoCIGSLT color targetFree)}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {collectionType : CollType} {before elements : List Pattern}
    (spine : CostStaticElementPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer collectionType before
      elements none (.base "Proc"))
    (recur : PlanFrontierForElements sourceBound targetBound thinning
      sourceAvailable rootAbstract rootEntries elements)
    (elementsTyped : WellSorted.ElementsHaveType rhoCIGSLT.costWholeLanguage
      targetFree sourceAvailable elements
      (mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc")))
    (metaList : Pattern.hasCanonicalBinderMetadataList elements = true)
    (objectList : isObjectPatternList elements = true)
    (scopedList : Pattern.isWellScopedListAt sourceAvailable.length elements =
      true)
    (reflectiveList : ∀ presentation ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor sourceAvailable.length
        elements = true)
    (sealed : List TypeExpr)
    (split : targetBound = sourceAvailable ++ sealed)
    (F : OneHoleContext) (beforeAbstracts : List Pattern)
    (hF : rootAbstract = F.fill (.collection
      rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
      (beforeAbstracts ++ spine.abstractPatterns) none))
    (embF : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      spine.boundaryTable.entries rootEntries)) :
    List.Forall₂ (LeafWitness sourceBound targetBound thinning
      sourceAvailable rootAbstract rootEntries)
      (parallelLeavesList
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) elements)
      (parallelLeavesList rhoReflectivePresentation.toReflectivePresentationDecl
        spine.abstractPatterns) := by
  induction elements generalizing before beforeAbstracts with
  | nil =>
      cases spine
      exact .nil
  | cons element elements' tail_ih =>
      cases spine with
      | @cons _ _ _ _ _ _ _ _ _ _ _ head tail =>
      cases elementsTyped with
      | cons headTyped tailTyped =>
      simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true]
        at metaList
      simp only [isObjectPatternList, Bool.and_eq_true] at objectList
      simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at scopedList
      obtain ⟨embSpine⟩ := embF
      have embSpineAppend : CostStaticPlanEntryEmbedding rhoCIGSLT color
          targetFree
          (head.boundaryTable.entries ++ tail.boundaryTable.entries)
          rootEntries := by
        rw [← TypedCostRegionBoundaryTable.entries_append
          head.boundaryTable tail.boundaryTable]
        exact embSpine
      have headEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT
          color targetFree head.boundaryTable.entries rootEntries) :=
        ⟨(CostStaticPlanEntryEmbedding.appendLeft _ _).comp embSpineAppend⟩
      have tailEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT
          color targetFree tail.boundaryTable.entries rootEntries) :=
        ⟨(CostStaticPlanEntryEmbedding.appendRight _ _).comp embSpineAppend⟩
      have headAdmission : head.RawAdmission :=
        { wellSorted := ⟨⟨headTyped, metaList.1, objectList.1, scopedList.1⟩,
            fun presentation membership => by
              have safeCons := reflectiveList presentation membership
              simp only [binderSafeListAt, Bool.and_eq_true] at safeCons
              simpa [binderSafeAt] using safeCons.1⟩
          targetBound_split := ⟨sealed, split⟩ }
      have absCons : (CostStaticElementPlan.cons head tail).abstractPatterns =
          head.abstractPattern :: tail.abstractPatterns := rfl
      have hFhead : rootAbstract = (F.comp (.collection
          rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
          beforeAbstracts .hole tail.abstractPatterns none)).fill
            head.abstractPattern := by
        rw [OneHoleContext.fill_comp, hF]
        all_goals rfl
      have headCall := recur.relates (List.mem_cons_self) head headAdmission
        (F.comp (.collection
          rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
          beforeAbstracts .hole tail.abstractPatterns none))
        hFhead headEmbedding
      have tailRecur : PlanFrontierForElements sourceBound targetBound
          thinning sourceAvailable rootAbstract rootEntries elements' := by
        refine ⟨?_⟩
        intro childOuter childPayload childMem childPlan childAdmission
          childF childEq childEmbedding
        exact recur.relates (List.mem_cons_of_mem _ childMem) childPlan
          childAdmission childF childEq childEmbedding
      have tailCall := tail_ih tail tailRecur tailTyped
        metaList.2 objectList.2 scopedList.2
        (fun presentation membership => by
          have safeCons := reflectiveList presentation membership
          simp only [binderSafeListAt, Bool.and_eq_true] at safeCons
          exact safeCons.2)
        (beforeAbstracts ++ [head.abstractPattern])
        (by
          show rootAbstract = _
          rw [hF, absCons]
          simp [List.append_assoc])
        tailEmbedding
      show List.Forall₂ _
        (parallelLeaves _ element ++ parallelLeavesList _ elements')
        (parallelLeavesList _
          (CostStaticElementPlan.cons head tail).abstractPatterns)
      rw [absCons]
      show List.Forall₂ _
        (parallelLeaves _ element ++ parallelLeavesList _ elements')
        (parallelLeaves _ head.abstractPattern ++
          parallelLeavesList _ tail.abstractPatterns)
      exact forall₂_append headCall tailCall

theorem frontierForall2_plan_fuel
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {rootAbstract : Pattern}
    {rootEntries : List (TypedCostRegionBoundary rhoCIGSLT color targetFree)}
    (fuel : Nat)
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {payload : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload (.base "Proc"))
    (admission : plan.RawAdmission)
    (F : OneHoleContext)
    (hF : rootAbstract = F.fill plan.abstractPattern)
    (embF : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      plan.boundaryTable.entries rootEntries))
    (measure : sizeOf payload ≤ fuel) :
    List.Forall₂ (LeafWitness sourceBound targetBound thinning sourceAvailable
      rootAbstract rootEntries)
      (parallelLeaves
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) payload)
      (parallelLeaves rhoReflectivePresentation.toReflectivePresentationDecl
        plan.abstractPattern) := by
  have fuelPositive : 0 < fuel := by
    cases payload <;> simp at measure ⊢ <;> omega
  generalize sourceTypeEq : TypeExpr.base "Proc" = sourceType at plan
  let processPlan := castCostStaticRegionPlanSourceType sourceTypeEq.symm plan
  have processAdmission : processPlan.RawAdmission := by
    cases sourceTypeEq
    exact admission
  have processAbstractEq : rootAbstract =
      F.fill processPlan.abstractPattern := by
    simpa [processPlan] using hF
  have processEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT
      color targetFree processPlan.boundaryTable.entries rootEntries) := by
    simpa [processPlan] using embF
  have selfWitness : LeafWitness sourceBound targetBound thinning
      sourceAvailable rootAbstract rootEntries payload
      plan.abstractPattern :=
    ⟨outer, processPlan, F, processAbstractEq, by simp [processPlan],
      processAdmission, processEmbedding⟩
  cases plan with
  | bvar sourceIndex lookup correspondence availableScope =>
      exact .cons selfWitness .nil
  | fvar lookup =>
      exact .cons selfWitness .nil
  | lambda bodyPlan =>
      exact TypeExpr.noConfusion sourceTypeEq
  | multiLambda bodyPlan =>
      exact TypeExpr.noConfusion sourceTypeEq
  | boundaryApplication declared rendered outsideCurrent certified certifies =>
      rename_i wireName arguments
      refine forall₂_singleton ?_ rfl selfWitness
      refine parallelLeaves_apply_of_not_unit _ ?_
      rintro ⟨wireEq, -⟩
      have decodedNone :=
        decodeDeclaredCostStaticConstructor_render_of_role_ne rhoCIGSLT
          declared color outsideCurrent
      rw [rendered, wireEq] at decodedNone
      rw [show decodeDeclaredCostStaticConstructor rhoCIGSLT color
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).parallelUnitConstructor = some "PZero" from by
        cases color <;> decide] at decodedNone
      exact absurd decodedNone (by simp)
  | application declared rendered current preimage notBare children =>
      rename_i wireName arguments
      have wireForm : wireName =
          (color.symbols rhoCIGSLT).constructor
            preimage.sourceConstructor.1.label := by
        rw [← rendered, ← rhoCIGSLT.materializeDeclaredCostConstructor_label
          declared, preimage.labelMap]
      by_cases unitLabel : preimage.sourceConstructor.1.label = "PZero"
      · have paramsNil : preimage.sourceConstructor.1.params = [] :=
          rhoCalc_params_nil_of_label_pzero preimage.sourceConstructor.1
            preimage.sourceConstructor.2 unitLabel
        have lengths :=
          CostHereditaryCrossColorLeafHinge.CostStaticArgumentPlan.abstractPatterns_length
            children
        have paramsLen : preimage.sourceConstructor.1.params.length = 0 := by
          rw [paramsNil]
          rfl
        have argumentsNil : arguments = [] :=
          List.eq_nil_of_length_eq_zero (lengths.2.trans paramsLen)
        have abstractsNil : children.abstractPatterns = [] :=
          List.eq_nil_of_length_eq_zero
            (lengths.1.trans (lengths.2.trans paramsLen))
        refine forall₂_nil ?_ ?_
        · have wireUnit : wireName =
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl
                ).parallelUnitConstructor := by
            rw [wireForm, unitLabel, rhoDecl_unitConstructor]
          rw [argumentsNil, wireUnit]
          exact parallelLeaves_apply_unit _
        · show parallelLeaves _
            (.apply preimage.sourceConstructor.1.label
              children.abstractPatterns) = []
          rw [abstractsNil, unitLabel, ← authUnitConstructor]
          exact parallelLeaves_apply_unit _
      · refine forall₂_singleton ?_ ?_ selfWitness
        · refine parallelLeaves_apply_of_not_unit _ ?_
          rintro ⟨wireEq, -⟩
          rw [wireForm, rhoDecl_unitConstructor] at wireEq
          exact unitLabel (costStaticColor_constructor_inj wireEq)
        · show parallelLeaves _
            (.apply preimage.sourceConstructor.1.label
              children.abstractPatterns) = _
          refine parallelLeaves_apply_of_not_unit _ ?_
          rintro ⟨labelEq, -⟩
          rw [authUnitConstructor] at labelEq
          exact unitLabel labelEq
  | boundaryCollection currentRejected oppositeChoice oppositeSelected
      certified certifies =>
      exact absurd oppositeSelected (fun selected =>
        rho_boundaryCollection_choices_absurd color targetFree _ _ _ _
          selected currentRejected)
  | @collection _ _ _ _ _ collectionType elements rest _ choice selected
      children =>
      have selectedProc : choice ∈ costStaticCollectionTypingChoices
          rhoCIGSLT color targetFree targetBound collectionType elements
          (mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc")) := by
        rw [sourceTypeEq]
        exact selected
      have elementType := rho_process_collection_choice_sourceElementType
        color choice selectedProc
      let processChildren :=
        children.castSourceElementType elementType.symm
      have processAbstractPatterns : processChildren.abstractPatterns =
          children.abstractPatterns := by simp [processChildren]
      have processBoundaryEntries : processChildren.boundaryTable.entries =
          children.boundaryTable.entries := by simp [processChildren]
      by_cases parallelShape : collectionType =
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).parallelCollection ∧ rest = none
      · obtain ⟨ctEq, restEq⟩ := parallelShape
        subst ctEq
        subst restEq
        obtain ⟨sealed, split⟩ := admission.targetBound_split
        have elementScope :
            Pattern.isWellScopedListAt sourceAvailable.length elements =
              true := by
          simpa [WellSorted.ScopeSafeAt, Pattern.isWellScopedAt] using
            admission.wellSorted.1.2.2.2
        have elementsTyped : WellSorted.ElementsHaveType
            rhoCIGSLT.costWholeLanguage targetFree sourceAvailable elements
            (mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc")) := by
          have typedAtTarget := WellSorted.checkElementsHaveType_sound
            (checkElementsHaveType_of_mem_costStaticCollectionTypingChoices
              selectedProc)
          rw [split] at typedAtTarget
          simpa [elementType] using
            typedAtTarget.restrictOuterOfScoped elementScope
        have metaList :
            Pattern.hasCanonicalBinderMetadataList elements = true := by
          simpa [Pattern.hasCanonicalBinderMetadata] using
            admission.wellSorted.1.2.1
        have objectList : isObjectPatternList elements = true := by
          simpa [WellSorted.isObjectPattern] using
            admission.wellSorted.1.2.2.1
        have reflectiveList : ∀ presentation ∈
            rhoCIGSLT.costWholeReflectionProfile.presentations,
            binderSafeListAt presentation.quoteConstructor
              sourceAvailable.length elements = true := by
          intro presentation membership
          simpa [binderSafeAt] using
            admission.wellSorted.2 presentation membership
        have ctAuth : (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).parallelCollection =
            (rhoReflectivePresentation.toReflectivePresentationDecl
              ).parallelCollection := by
          cases color <;> rfl
        have leftEq := parallelLeaves_parallel
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl) elements
        have rightEq : parallelLeaves
            rhoReflectivePresentation.toReflectivePresentationDecl
            (CostStaticRegionPlan.collection (source := rhoCIGSLT)
              (rest := none) choice selected children).abstractPattern =
            parallelLeavesList
              rhoReflectivePresentation.toReflectivePresentationDecl
              processChildren.abstractPatterns :=
          by
            change parallelLeaves
                rhoReflectivePresentation.toReflectivePresentationDecl
                (.collection
                  (costStaticReflectivePresentationDecl rhoCIGSLT color
                    rhoReflectivePresentation.toReflectivePresentationDecl
                    ).parallelCollection children.abstractPatterns none) = _
            rw [processAbstractPatterns]
            exact parallelLeaves_parallel_of_eq
              rhoReflectivePresentation.toReflectivePresentationDecl ctAuth
              children.abstractPatterns
        rw [leftEq, rightEq]
        have recur : PlanFrontierForElements sourceBound targetBound thinning
            sourceAvailable rootAbstract rootEntries elements := by
          refine ⟨?_⟩
          intro childOuter childPayload childMem childPlan
            childAdmission childF childEq childEmbedding
          have childMeasure : sizeOf childPayload ≤ fuel - 1 := by
            have childBound := List.sizeOf_lt_of_mem childMem
            have collectionBound : sizeOf elements < sizeOf
                (Pattern.collection
                  (costStaticReflectivePresentationDecl rhoCIGSLT color
                    rhoReflectivePresentation.toReflectivePresentationDecl
                    ).parallelCollection elements none) := by
              simp_wf
            omega
          exact frontierForall2_plan_fuel (fuel - 1) childPlan childAdmission
            childF childEq childEmbedding childMeasure
        exact frontierForall2_spine_aux processChildren recur elementsTyped metaList
          objectList elementScope reflectiveList sealed split F []
          (by
            calc
              rootAbstract = F.fill
                  (CostStaticRegionPlan.collection (source := rhoCIGSLT)
                    (rest := none) choice selected children).abstractPattern :=
                hF
              _ = F.fill (.collection
                    (costStaticReflectivePresentationDecl rhoCIGSLT color
                      rhoReflectivePresentation.toReflectivePresentationDecl
                      ).parallelCollection children.abstractPatterns none) :=
                rfl
              _ = F.fill (.collection
                    rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
                    processChildren.abstractPatterns none) := by
                apply congrArg F.fill
                calc
                  Pattern.collection
                      (costStaticReflectivePresentationDecl rhoCIGSLT color
                        rhoReflectivePresentation.toReflectivePresentationDecl
                        ).parallelCollection children.abstractPatterns none =
                      Pattern.collection
                        rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
                        children.abstractPatterns none :=
                    congrArg
                      (fun collectionType =>
                        Pattern.collection collectionType
                          children.abstractPatterns none)
                      ctAuth
                  _ = Pattern.collection
                        rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
                        processChildren.abstractPatterns none :=
                    congrArg
                      (fun abstracts => Pattern.collection
                        rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
                        abstracts none)
                      processAbstractPatterns.symm)
          (by
            have processPlanEntries : processPlan.boundaryTable.entries =
                processChildren.boundaryTable.entries := by
              calc
                processPlan.boundaryTable.entries =
                    (CostStaticRegionPlan.collection (source := rhoCIGSLT)
                      choice selected children).boundaryTable.entries := by
                  exact castCostStaticRegionPlanSourceType_boundaryTable_entries
                    sourceTypeEq.symm
                      (CostStaticRegionPlan.collection (source := rhoCIGSLT)
                        choice selected children)
                _ = children.boundaryTable.entries := rfl
                _ = processChildren.boundaryTable.entries :=
                  processBoundaryEntries.symm
            rw [← processPlanEntries]
            exact processEmbedding)
      · refine forall₂_singleton
          (parallelLeaves_collection_of_not_parallel _ parallelShape) ?_
          selfWitness
        show parallelLeaves _
          (.collection collectionType children.abstractPatterns
            (rest.map costRegionSourceVariableName)) = _
        refine parallelLeaves_collection_of_not_parallel _ ?_
        rintro ⟨ctEq, restMapEq⟩
        refine parallelShape ⟨?_, ?_⟩
        · rw [ctEq]
          cases color <;> rfl
        · cases rest with
          | none => rfl
          | some r => simp at restMapEq
termination_by fuel
decreasing_by omega

theorem frontierForall2_plan
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {rootAbstract : Pattern}
    {rootEntries : List (TypedCostRegionBoundary rhoCIGSLT color targetFree)}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {payload : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload (.base "Proc"))
    (admission : plan.RawAdmission)
    (F : OneHoleContext)
    (hF : rootAbstract = F.fill plan.abstractPattern)
    (embF : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      plan.boundaryTable.entries rootEntries)) :
    List.Forall₂ (LeafWitness sourceBound targetBound thinning sourceAvailable
      rootAbstract rootEntries)
      (parallelLeaves
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) payload)
      (parallelLeaves rhoReflectivePresentation.toReflectivePresentationDecl
        plan.abstractPattern) :=
  frontierForall2_plan_fuel (sizeOf payload) plan admission F hF embF
    (Nat.le_refl _)

theorem frontierForall2_spine
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {rootAbstract : Pattern}
    {rootEntries : List (TypedCostRegionBoundary rhoCIGSLT color targetFree)}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {collectionType : CollType} {before elements : List Pattern}
    (spine : CostStaticElementPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer collectionType before
      elements none (.base "Proc"))
    (elementsTyped : WellSorted.ElementsHaveType rhoCIGSLT.costWholeLanguage
      targetFree sourceAvailable elements
      (mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc")))
    (metaList : Pattern.hasCanonicalBinderMetadataList elements = true)
    (objectList : isObjectPatternList elements = true)
    (scopedList : Pattern.isWellScopedListAt sourceAvailable.length elements =
      true)
    (reflectiveList : ∀ presentation ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations,
      binderSafeListAt presentation.quoteConstructor sourceAvailable.length
        elements = true)
    (sealed : List TypeExpr)
    (split : targetBound = sourceAvailable ++ sealed)
    (F : OneHoleContext) (beforeAbstracts : List Pattern)
    (hF : rootAbstract = F.fill (.collection
      (rhoReflectivePresentation.toReflectivePresentationDecl
        ).parallelCollection
      (beforeAbstracts ++ spine.abstractPatterns) none))
    (embF : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      spine.boundaryTable.entries rootEntries)) :
    List.Forall₂ (LeafWitness sourceBound targetBound thinning sourceAvailable
      rootAbstract rootEntries)
      (parallelLeavesList
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) elements)
      (parallelLeavesList
        rhoReflectivePresentation.toReflectivePresentationDecl
        spine.abstractPatterns) := by
  have recur : PlanFrontierForElements sourceBound targetBound thinning
      sourceAvailable rootAbstract rootEntries elements := by
    refine ⟨?_⟩
    intro childOuter childPayload childMem childPlan childAdmission
      childF childEq childEmbedding
    exact frontierForall2_plan childPlan childAdmission childF childEq
      childEmbedding
  exact frontierForall2_spine_aux spine recur elementsTyped metaList objectList
    scopedList reflectiveList sealed split F beforeAbstracts hF embF

/-- **The current/authored process parallel-frontier correspondence.**  Every
admitted process plan's raw frontier at the current colour corresponds
pointwise, in occurrence order, to its abstract frontier at the authored
declaration.  Each pair retains the enclosing binder fibre, raw admission,
and entry embedding required by recursive semantic closure. -/
theorem parallelLeaves_abstractPattern_forall2
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {payload : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload (.base "Proc"))
    (admission : plan.RawAdmission) :
    List.Forall₂
      (LeafWitness sourceBound targetBound thinning sourceAvailable
        plan.abstractPattern plan.boundaryTable.entries)
      (parallelLeaves
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) payload)
      (parallelLeaves rhoReflectivePresentation.toReflectivePresentationDecl
        plan.abstractPattern) :=
  frontierForall2_plan plan admission .hole rfl
    ⟨CostStaticPlanEntryEmbedding.refl _⟩

/-- Map the authored endpoint of the process-frontier traversal without
losing the raw occurrence witness.  This is the list naturality form used by
semantic cospan consumers: source classification remains attached to the raw
leaf, while the endpoint list is already expressed in its reified parent
frame. -/
theorem parallelLeaves_map_abstractPattern_forall2
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {payload : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload (.base "Proc"))
    (admission : plan.RawAdmission) (frame : Pattern → Pattern) :
    List.Forall₂
      (fun rawLeaf framedLeaf =>
        ∃ abstractLeaf,
          LeafWitness sourceBound targetBound thinning sourceAvailable
            plan.abstractPattern plan.boundaryTable.entries rawLeaf
              abstractLeaf ∧
          frame abstractLeaf = framedLeaf)
      (parallelLeaves
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) payload)
      ((parallelLeaves rhoReflectivePresentation.toReflectivePresentationDecl
        plan.abstractPattern).map frame) := by
  rw [List.forall₂_map_right_iff]
  exact (parallelLeaves_abstractPattern_forall2 plan admission).imp
    (fun _ _ witness => ⟨_, witness, rfl⟩)

/-- Membership-retaining companion of
`parallelLeaves_map_abstractPattern_forall2`.  The raw frontier membership is
kept alongside the reached subplan so recursive consumers can prove that a
paired leaf is strictly smaller than a bare-parallel parent. -/
theorem parallelLeaves_map_abstractPattern_forall2_with_membership
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {payload : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload (.base "Proc"))
    (admission : plan.RawAdmission) (frame : Pattern → Pattern) :
    List.Forall₂
      (fun rawLeaf framedLeaf =>
        ∃ abstractLeaf,
          rawLeaf ∈ parallelLeaves
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl)
              payload ∧
            LeafWitness sourceBound targetBound thinning sourceAvailable
              plan.abstractPattern plan.boundaryTable.entries rawLeaf
                abstractLeaf ∧
            frame abstractLeaf = framedLeaf)
      (parallelLeaves
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) payload)
      ((parallelLeaves rhoReflectivePresentation.toReflectivePresentationDecl
        plan.abstractPattern).map frame) := by
  exact (forall₂_with_left_membership
    (parallelLeaves_map_abstractPattern_forall2 plan admission frame)).imp
      fun _ _ related => by
        obtain ⟨membership, abstractLeaf, witness, framed⟩ := related
        exact ⟨abstractLeaf, membership, witness, framed⟩

/-- Every member on the right of a pointwise list relation retains a
corresponding member on the left. -/
theorem exists_left_of_forall₂_mem_right
    {Left Right : Type*} {relation : Left → Right → Prop}
    {left : List Left} {right : List Right}
    (aligned : List.Forall₂ relation left right)
    {item : Right} (membership : item ∈ right) :
    ∃ source ∈ left, relation source item := by
  induction aligned with
  | nil => cases membership
  | @cons source target left right head tail inductionHypothesis =>
      rcases List.mem_cons.mp membership with rfl | membership
      · exact ⟨source, by simp, head⟩
      · obtain ⟨source', sourceMembership, related⟩ :=
          inductionHypothesis membership
        exact ⟨source', by simp [sourceMembership], related⟩

/-- The keyed canonical frontier of an admitted process plan in a common
semantic namespace is exactly its occurrence-preserving authored frontier.
The result retains duplicate occurrences and permits arbitrary parent
reification and ambient-binder reinsertion. -/
theorem processPlan_commonReifiedMappedThickened_frontier_perm
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      occurrences}
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      table values root}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {frameSourceBound frameTargetBound : List TypeExpr}
    (frameThinning : CostStaticBinderThinning rhoCIGSLT color
      frameSourceBound frameTargetBound)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {payload : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload (.base "Proc"))
    (admission : plan.RawAdmission) (scopeDepth keyDepth : Nat) :
    let authoredDeclaration :=
      rhoReflectivePresentation.toReflectivePresentationDecl
    let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
      color rhoReflectivePresentation
    let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
    let frame := fun pattern =>
      cospan.reifyWith environment.lookupAtom? leg
        (frameThinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (environment.reify pattern)))
    List.Perm
      (parallelContents targetDeclaration
        [canonicalizeByAt key targetDeclaration keyDepth
          (frame plan.abstractPattern)])
      ((parallelLeaves authoredDeclaration plan.abstractPattern).map
        (fun leaf => canonicalizeByAt key targetDeclaration keyDepth
          (frame leaf))) := by
  dsimp only
  let authoredDeclaration :=
    rhoReflectivePresentation.toReflectivePresentationDecl
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation
  let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
  let frame := fun pattern =>
    cospan.reifyWith environment.lookupAtom? leg
      (frameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (environment.reify pattern)))
  have traversal := parallelLeaves_abstractPattern_forall2 plan admission
  have leafStable : ∀ leaf,
      leaf ∈ parallelLeaves targetDeclaration (frame plan.abstractPattern) →
        canonicalizeByAt key targetDeclaration keyDepth leaf ≠
            .apply targetDeclaration.parallelUnitConstructor [] ∧
          ∀ elements,
            canonicalizeByAt key targetDeclaration keyDepth leaf ≠
              .collection targetDeclaration.parallelCollection elements
                none := by
    intro leaf membership
    rw [parallelLeaves_commonReifiedMappedThickened environment frameThinning
      cospan leg authoredDeclaration scopeDepth plan.abstractPattern] at membership
    obtain ⟨abstractLeaf, abstractMembership, rfl⟩ :=
      List.mem_map.mp membership
    obtain ⟨rawLeaf, rawMembership, witness⟩ :=
      exists_left_of_forall₂_mem_right traversal abstractMembership
    rcases witness with
      ⟨childOuter, childPlan, skeletonContext, rootEquality,
        childAbstractEquality, childAdmission, childEmbedding⟩
    have rawStable := parallelLeaves_mem_root_stable
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      payload rawLeaf rawMembership
    have rawNotParallel : ∀ elements, rawLeaf ≠
        .collection authoredDeclaration.parallelCollection elements none := by
      intro elements equality
      apply rawStable.2 elements
      rw [equality]
      cases color <;> rfl
    have sourceStable := processPlan_abstractPattern_root_stable childPlan rfl
      rawStable.1 rawNotParallel
    have abstractStable : abstractLeaf ≠
          .apply authoredDeclaration.parallelUnitConstructor [] ∧
        (∀ elements, abstractLeaf ≠
          .collection authoredDeclaration.parallelCollection elements none) ∧
        ∀ arguments, abstractLeaf ≠
          .apply authoredDeclaration.quoteConstructor arguments := by
      simpa [authoredDeclaration, childAbstractEquality] using sourceStable
    have framedStable := commonReifiedMappedThickened_root_stable environment
      frameThinning cospan leg scopeDepth abstractLeaf abstractStable
    exact canonicalizeByAt_leaf_stable_of_root_stable key targetDeclaration
      keyDepth (frame abstractLeaf) framedStable.1 framedStable.2.1
        framedStable.2.2
  have reconstructed := parallelLeaves_keyed_frontier_perm_of_leaf_stable
    key targetDeclaration keyDepth (frame plan.abstractPattern) leafStable
  rw [parallelLeaves_commonReifiedMappedThickened environment frameThinning
    cospan leg authoredDeclaration scopeDepth plan.abstractPattern] at reconstructed
  rw [canonicalizeListByAt_eq_map, List.map_map] at reconstructed
  change List.Perm
    (parallelContents targetDeclaration
      [canonicalizeByAt key targetDeclaration keyDepth
        (frame plan.abstractPattern)])
    ((parallelLeaves authoredDeclaration plan.abstractPattern).map
      ((canonicalizeByAt key targetDeclaration keyDepth) ∘ frame))
  exact reconstructed

/-- Recover the raw and authored occurrences behind one member of the keyed
parent frontier.  The result retains the reached subplan admission and its
boundary-table embedding through `LeafWitness`; no membership is reconstructed
by equality search after canonicalization. -/
theorem exists_leafWitness_of_mem_commonReifiedMappedThickened_frontier
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      occurrences}
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      table values root}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {frameSourceBound frameTargetBound : List TypeExpr}
    (frameThinning : CostStaticBinderThinning rhoCIGSLT color
      frameSourceBound frameTargetBound)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {payload endpoint : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload (.base "Proc"))
    (admission : plan.RawAdmission) (scopeDepth keyDepth : Nat)
    (membership :
      let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
        color rhoReflectivePresentation
      let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
      let frame := fun pattern =>
        cospan.reifyWith environment.lookupAtom? leg
          (frameThinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (environment.reify pattern)))
      endpoint ∈ parallelContents targetDeclaration
        [canonicalizeByAt key targetDeclaration keyDepth
          (frame plan.abstractPattern)]) :
    let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
      color rhoReflectivePresentation
    let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
    let frame := fun pattern =>
      cospan.reifyWith environment.lookupAtom? leg
        (frameThinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (environment.reify pattern)))
    ∃ rawLeaf abstractLeaf,
      rawLeaf ∈ parallelLeaves
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          payload ∧
        LeafWitness sourceBound targetBound thinning sourceAvailable
          plan.abstractPattern plan.boundaryTable.entries rawLeaf
            abstractLeaf ∧
        canonicalizeByAt key targetDeclaration keyDepth
          (frame abstractLeaf) = endpoint := by
  dsimp only at membership ⊢
  let authoredDeclaration :=
    rhoReflectivePresentation.toReflectivePresentationDecl
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation
  let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
  let frame := fun pattern =>
    cospan.reifyWith environment.lookupAtom? leg
      (frameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (environment.reify pattern)))
  have frontierPermutation :=
    processPlan_commonReifiedMappedThickened_frontier_perm environment
      frameThinning cospan leg plan admission scopeDepth keyDepth
  have mappedMembership : endpoint ∈
      (parallelLeaves authoredDeclaration plan.abstractPattern).map
        (fun leaf => canonicalizeByAt key targetDeclaration keyDepth
          (frame leaf)) :=
    frontierPermutation.mem_iff.mp membership
  obtain ⟨abstractLeaf, abstractMembership, endpointEq⟩ :=
    List.mem_map.mp mappedMembership
  have traversal := parallelLeaves_abstractPattern_forall2 plan admission
  obtain ⟨rawLeaf, rawMembership, witness⟩ :=
    exists_left_of_forall₂_mem_right traversal abstractMembership
  exact ⟨rawLeaf, abstractLeaf, rawMembership, witness, endpointEq⟩

/-- Foreign canonical equality lifts through both occurrence-preserving plan
frontiers to an aligned endpoint permutation.  Raw leaves are classified by
the foreign canonicalizer, while the endpoint relations retain the exact
authored occurrence and may map it into any later semantic frame. -/
noncomputable def
    parallelLeaves_abstractPattern_permutation_of_foreign_canonical_eq
    {color declarationColor : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr}
    {leftOuter rightOuter : OneHoleContext}
    {leftPayload rightPayload : Pattern}
    (leftPlan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable leftOuter leftPayload (.base "Proc"))
    (rightPlan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable rightOuter rightPayload (.base "Proc"))
    (leftAdmission : leftPlan.RawAdmission)
    (rightAdmission : rightPlan.RawAdmission)
    (different : declarationColor ≠ color)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPayload =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPayload)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (targetDeclaration : ReflectivePresentationDecl) (depth : Nat)
    (leftFrame rightFrame : Pattern → Pattern)
    (close : ∀ {leftRaw leftEndpoint rightRaw rightEndpoint},
      (∃ leftAbstract,
          leftRaw ∈ parallelLeaves
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            leftPayload ∧
          LeafWitness sourceBound targetBound thinning sourceAvailable
            leftPlan.abstractPattern leftPlan.boundaryTable.entries leftRaw
              leftAbstract ∧
          leftFrame leftAbstract = leftEndpoint) →
      (∃ rightAbstract,
          rightRaw ∈ parallelLeaves
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            rightPayload ∧
          LeafWitness sourceBound targetBound thinning sourceAvailable
            rightPlan.abstractPattern rightPlan.boundaryTable.entries rightRaw
              rightAbstract ∧
          rightFrame rightAbstract = rightEndpoint) →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftRaw =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightRaw →
      CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
        targetDeclaration depth leftEndpoint rightEndpoint) :
    CostStaticAtomKeyCospan.CommonRestorationApex.Permutation
      (source := rhoCIGSLT) cospan targetDeclaration depth
      ((parallelLeaves rhoReflectivePresentation.toReflectivePresentationDecl
        leftPlan.abstractPattern).map leftFrame)
      ((parallelLeaves rhoReflectivePresentation.toReflectivePresentationDecl
        rightPlan.abstractPattern).map rightFrame) := by
  let rawDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation.toReflectivePresentationDecl
  have leftTraversal :=
    parallelLeaves_map_abstractPattern_forall2_with_membership leftPlan
      leftAdmission leftFrame
  have rightTraversal :=
    parallelLeaves_map_abstractPattern_forall2_with_membership rightPlan
      rightAdmission rightFrame
  have leftTyped : HasType rhoCIGSLT.costWholeLanguage targetFree
      sourceAvailable leftPayload
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort) := by
    cases color <;> exact leftAdmission.wellSorted.1.1
  have rightTyped : HasType rhoCIGSLT.costWholeLanguage targetFree
      sourceAvailable rightPayload
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort) := by
    cases color <;> exact rightAdmission.wellSorted.1.1
  have permutation :=
    rhoProc_parallelLeaves_map_perm_of_foreign_canonical_eq
      (fun _ pattern => Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode pattern)
      color declarationColor different leftTyped rightTyped canonical depth
  exact CostStaticAtomKeyCospan.CommonRestorationApex.Permutation.of_related_map_perm
    cospan targetDeclaration depth (canonicalize rawDeclaration)
      (canonicalize rawDeclaration) leftTraversal rightTraversal permutation
      close

/-- Reconstruct a whole process-plan pair from common-restoration evidence on
the paired authored parallel frontiers.  Endpoint occurrences are first
canonicalized in their respective parent semantic environments, then the two
finite frontier permutations are composed with the foreign canonical
matching.  The singleton parallel wrappers expose exactly the representation
consumed by `CommonRestorationApex.parallel`. -/
noncomputable def
    processPlans_commonRestorationApex_of_foreignCanonical
    {color declarationColor : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightTable}
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightTable rightValues rightRoot}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    {leftFrameSourceBound leftFrameTargetBound : List TypeExpr}
    {rightFrameSourceBound rightFrameTargetBound : List TypeExpr}
    (leftFrameThinning : CostStaticBinderThinning rhoCIGSLT color
      leftFrameSourceBound leftFrameTargetBound)
    (rightFrameThinning : CostStaticBinderThinning rhoCIGSLT color
      rightFrameSourceBound rightFrameTargetBound)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leftLeg : Fin leftEnvironment.atomCount → Fin cospan.commonKeys.length)
    (rightLeg : Fin rightEnvironment.atomCount → Fin cospan.commonKeys.length)
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr}
    {leftOuter rightOuter : OneHoleContext}
    {leftPayload rightPayload : Pattern}
    (leftPlan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable leftOuter leftPayload (.base "Proc"))
    (rightPlan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable rightOuter rightPayload (.base "Proc"))
    (leftAdmission : leftPlan.RawAdmission)
    (rightAdmission : rightPlan.RawAdmission)
    (different : declarationColor ≠ color)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPayload =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPayload)
    (targetDeclaration : ReflectivePresentationDecl)
    (targetDeclaration_eq : targetDeclaration =
      costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
    (scopeDepth depth : Nat)
    (close : ∀ {leftRaw leftEndpoint rightRaw rightEndpoint},
      (∃ leftAbstract,
          leftRaw ∈ parallelLeaves
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            leftPayload ∧
          LeafWitness sourceBound targetBound thinning sourceAvailable
            leftPlan.abstractPattern leftPlan.boundaryTable.entries leftRaw
              leftAbstract ∧
          canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            targetDeclaration depth
            (cospan.reifyWith leftEnvironment.lookupAtom? leftLeg
              (leftFrameThinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols rhoCIGSLT)
                  (leftEnvironment.reify leftAbstract)))) = leftEndpoint) →
      (∃ rightAbstract,
          rightRaw ∈ parallelLeaves
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            rightPayload ∧
          LeafWitness sourceBound targetBound thinning sourceAvailable
            rightPlan.abstractPattern rightPlan.boundaryTable.entries rightRaw
              rightAbstract ∧
          canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            targetDeclaration depth
            (cospan.reifyWith rightEnvironment.lookupAtom? rightLeg
              (rightFrameThinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols rhoCIGSLT)
                  (rightEnvironment.reify rightAbstract)))) = rightEndpoint) →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftRaw =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightRaw →
      CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
        targetDeclaration depth leftEndpoint rightEndpoint) :
    let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
    let leftFrame := fun pattern =>
      cospan.reifyWith leftEnvironment.lookupAtom? leftLeg
        (leftFrameThinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (leftEnvironment.reify pattern)))
    let rightFrame := fun pattern =>
      cospan.reifyWith rightEnvironment.lookupAtom? rightLeg
        (rightFrameThinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (rightEnvironment.reify pattern)))
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
      targetDeclaration depth
      (canonicalizeByAt key targetDeclaration depth
        (leftFrame leftPlan.abstractPattern))
      (canonicalizeByAt key targetDeclaration depth
        (rightFrame rightPlan.abstractPattern)) := by
  subst targetDeclaration
  dsimp only
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation.toReflectivePresentationDecl
  let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
  let leftFrame := fun pattern =>
    cospan.reifyWith leftEnvironment.lookupAtom? leftLeg
      (leftFrameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (leftEnvironment.reify pattern)))
  let rightFrame := fun pattern =>
    cospan.reifyWith rightEnvironment.lookupAtom? rightLeg
      (rightFrameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (rightEnvironment.reify pattern)))
  let leftEndpoint := fun pattern =>
    canonicalizeByAt key targetDeclaration depth (leftFrame pattern)
  let rightEndpoint := fun pattern =>
    canonicalizeByAt key targetDeclaration depth (rightFrame pattern)
  have aligned :=
    parallelLeaves_abstractPattern_permutation_of_foreign_canonical_eq
      leftPlan rightPlan leftAdmission rightAdmission different canonical
      cospan targetDeclaration depth leftEndpoint rightEndpoint close
  have leftPermutation :=
    processPlan_commonReifiedMappedThickened_frontier_perm leftEnvironment
      leftFrameThinning cospan leftLeg leftPlan leftAdmission scopeDepth depth
  have rightPermutation :=
    processPlan_commonReifiedMappedThickened_frontier_perm rightEnvironment
      rightFrameThinning cospan rightLeg rightPlan rightAdmission scopeDepth depth
  have wrapped : CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT
      cospan targetDeclaration depth
      (canonicalizeByAt key targetDeclaration depth
        (.collection targetDeclaration.parallelCollection
          [leftFrame leftPlan.abstractPattern] none))
      (canonicalizeByAt key targetDeclaration depth
        (.collection targetDeclaration.parallelCollection
          [rightFrame rightPlan.abstractPattern] none)) :=
    CostStaticAtomKeyCospan.CommonRestorationApex.parallel_of_permutation
      cospan targetDeclaration depth
        (CostStaticAtomKeyCospan.CommonRestorationApex.Permutation.of_endpoint_perms
          aligned
          (by simpa only [canonicalizeListByAt, leftEndpoint, leftFrame, key]
            using leftPermutation)
          (by simpa only [canonicalizeListByAt, rightEndpoint, rightFrame, key]
            using rightPermutation))
  apply CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    (processPlan_commonFrame_parallelSingleton_absorbed leftEnvironment
      leftFrameThinning cospan leftLeg leftPlan scopeDepth depth)
    (processPlan_commonFrame_parallelSingleton_absorbed rightEnvironment
      rightFrameThinning cospan rightLeg rightPlan scopeDepth depth)
    wrapped

/-- Reconstruct a process-plan pair when the semantic ordering depth and the
restoration depth are independent.  Canonically paired source occurrences
establish the key permutation; every equal-key cross-pair must additionally
restore uniformly, which is precisely the coherence required by stable
sorting in the presence of ties. -/
noncomputable def
    processPlans_commonRestorationApex_at_independentDepths_of_foreignCanonical
    {color declarationColor : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightTable}
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightTable rightValues rightRoot}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    {leftFrameSourceBound leftFrameTargetBound : List TypeExpr}
    {rightFrameSourceBound rightFrameTargetBound : List TypeExpr}
    (leftFrameThinning : CostStaticBinderThinning rhoCIGSLT color
      leftFrameSourceBound leftFrameTargetBound)
    (rightFrameThinning : CostStaticBinderThinning rhoCIGSLT color
      rightFrameSourceBound rightFrameTargetBound)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leftLeg : Fin leftEnvironment.atomCount → Fin cospan.commonKeys.length)
    (rightLeg : Fin rightEnvironment.atomCount → Fin cospan.commonKeys.length)
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr}
    {leftOuter rightOuter : OneHoleContext}
    {leftPayload rightPayload : Pattern}
    (leftPlan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable leftOuter leftPayload (.base "Proc"))
    (rightPlan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable rightOuter rightPayload (.base "Proc"))
    (leftAdmission : leftPlan.RawAdmission)
    (rightAdmission : rightPlan.RawAdmission)
    (different : declarationColor ≠ color)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPayload =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPayload)
    (targetDeclaration : ReflectivePresentationDecl)
    (targetDeclaration_eq : targetDeclaration =
      costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
    (scopeDepth keyDepth restorationDepth : Nat)
    (close : ∀ {leftRaw leftEndpoint rightRaw rightEndpoint},
      (∃ leftAbstract,
          leftRaw ∈ parallelLeaves
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            leftPayload ∧
          LeafWitness sourceBound targetBound thinning sourceAvailable
            leftPlan.abstractPattern leftPlan.boundaryTable.entries leftRaw
              leftAbstract ∧
          canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            targetDeclaration keyDepth
            (cospan.reifyWith leftEnvironment.lookupAtom? leftLeg
              (leftFrameThinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols rhoCIGSLT)
                  (leftEnvironment.reify leftAbstract)))) = leftEndpoint) →
      (∃ rightAbstract,
          rightRaw ∈ parallelLeaves
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            rightPayload ∧
          LeafWitness sourceBound targetBound thinning sourceAvailable
            rightPlan.abstractPattern rightPlan.boundaryTable.entries rightRaw
              rightAbstract ∧
          canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            targetDeclaration keyDepth
            (cospan.reifyWith rightEnvironment.lookupAtom? rightLeg
              (rightFrameThinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols rhoCIGSLT)
                  (rightEnvironment.reify rightAbstract)))) = rightEndpoint) →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftRaw =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightRaw →
      ∀ depth, CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT
        cospan targetDeclaration depth leftEndpoint rightEndpoint)
    (crossTies :
      let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
      let leftFrame := fun pattern =>
        cospan.reifyWith leftEnvironment.lookupAtom? leftLeg
          (leftFrameThinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (leftEnvironment.reify pattern)))
      let rightFrame := fun pattern =>
        cospan.reifyWith rightEnvironment.lookupAtom? rightLeg
          (rightFrameThinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (rightEnvironment.reify pattern)))
      ∀ {leftEndpoint rightEndpoint},
        leftEndpoint ∈ parallelContents targetDeclaration
          (canonicalizeListByAt key targetDeclaration keyDepth
            [leftFrame leftPlan.abstractPattern]) →
        rightEndpoint ∈ parallelContents targetDeclaration
          (canonicalizeListByAt key targetDeclaration keyDepth
            [rightFrame rightPlan.abstractPattern]) →
        key keyDepth leftEndpoint = key keyDepth rightEndpoint →
        ∀ depth, CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT
          cospan targetDeclaration depth leftEndpoint rightEndpoint) :
    let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
    let leftFrame := fun pattern =>
      cospan.reifyWith leftEnvironment.lookupAtom? leftLeg
        (leftFrameThinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (leftEnvironment.reify pattern)))
    let rightFrame := fun pattern =>
      cospan.reifyWith rightEnvironment.lookupAtom? rightLeg
        (rightFrameThinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (rightEnvironment.reify pattern)))
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
      targetDeclaration restorationDepth
      (canonicalizeByAt key targetDeclaration keyDepth
        (leftFrame leftPlan.abstractPattern))
      (canonicalizeByAt key targetDeclaration keyDepth
        (rightFrame rightPlan.abstractPattern)) := by
  subst targetDeclaration
  dsimp only
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation.toReflectivePresentationDecl
  let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
  let leftFrame := fun pattern =>
    cospan.reifyWith leftEnvironment.lookupAtom? leftLeg
      (leftFrameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (leftEnvironment.reify pattern)))
  let rightFrame := fun pattern =>
    cospan.reifyWith rightEnvironment.lookupAtom? rightLeg
      (rightFrameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (rightEnvironment.reify pattern)))
  let leftEndpoint := fun pattern =>
    canonicalizeByAt key targetDeclaration keyDepth (leftFrame pattern)
  let rightEndpoint := fun pattern =>
    canonicalizeByAt key targetDeclaration keyDepth (rightFrame pattern)
  have aligned :=
    parallelLeaves_abstractPattern_permutation_of_foreign_canonical_eq
      leftPlan rightPlan leftAdmission rightAdmission different canonical
      cospan targetDeclaration keyDepth leftEndpoint rightEndpoint (by
        intro leftRaw leftResult rightRaw rightResult leftWitness rightWitness
          rawCanonical
        exact close leftWitness rightWitness rawCanonical keyDepth)
  have leftPermutation :=
    processPlan_commonReifiedMappedThickened_frontier_perm leftEnvironment
      leftFrameThinning cospan leftLeg leftPlan leftAdmission scopeDepth keyDepth
  have rightPermutation :=
    processPlan_commonReifiedMappedThickened_frontier_perm rightEnvironment
      rightFrameThinning cospan rightLeg rightPlan rightAdmission scopeDepth
        keyDepth
  have frontierAlignment :=
    CostStaticAtomKeyCospan.CommonRestorationApex.Permutation.of_endpoint_perms
      aligned
      (by simpa only [canonicalizeListByAt, leftEndpoint, leftFrame, key]
        using leftPermutation)
      (by simpa only [canonicalizeListByAt, rightEndpoint, rightFrame, key]
        using rightPermutation)
  have wrapped :=
    CostStaticAtomKeyCospan.CommonRestorationApex.parallel_at_keyDepth_of_key_perm_of_cross_ties
      cospan targetDeclaration keyDepth restorationDepth
        frontierAlignment.semanticKey_perm (by
          intro leftResult rightResult leftMembership rightMembership keyEq
          exact CostStaticAtomKeyCospan.CommonRestorationApex.restoresTogether_of_forall_apex
            (crossTies leftMembership rightMembership keyEq))
  apply CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    (processPlan_commonFrame_parallelSingleton_absorbed leftEnvironment
      leftFrameThinning cospan leftLeg leftPlan scopeDepth keyDepth)
    (processPlan_commonFrame_parallelSingleton_absorbed rightEnvironment
      rightFrameThinning cospan rightLeg rightPlan scopeDepth keyDepth)
    wrapped

/-- The separated-depth form of the occurrence-preserving frontier
permutation.  Each paired occurrence must admit a common apex at every
restoration depth; that uniform family becomes the leaf case of the
two-depth relation, while the frontier key depth remains independent. -/
noncomputable def
    parallelLeaves_abstractPattern_twoDepthPermutation_of_foreign_canonical_eq
    {color declarationColor : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr}
    {leftOuter rightOuter : OneHoleContext}
    {leftPayload rightPayload : Pattern}
    (leftPlan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable leftOuter leftPayload (.base "Proc"))
    (rightPlan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable rightOuter rightPayload (.base "Proc"))
    (leftAdmission : leftPlan.RawAdmission)
    (rightAdmission : rightPlan.RawAdmission)
    (different : declarationColor ≠ color)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPayload =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPayload)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (targetDeclaration : ReflectivePresentationDecl)
    (restorationDepth keyDepth : Nat)
    (leftFrame rightFrame : Pattern → Pattern)
    (close : ∀ {leftRaw leftEndpoint rightRaw rightEndpoint},
      (∃ leftAbstract,
          LeafWitness sourceBound targetBound thinning sourceAvailable
            leftPlan.abstractPattern leftPlan.boundaryTable.entries leftRaw
              leftAbstract ∧
          leftFrame leftAbstract = leftEndpoint) →
      (∃ rightAbstract,
          LeafWitness sourceBound targetBound thinning sourceAvailable
            rightPlan.abstractPattern rightPlan.boundaryTable.entries rightRaw
              rightAbstract ∧
          rightFrame rightAbstract = rightEndpoint) →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftRaw =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightRaw →
      ∀ depth,
        CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
          targetDeclaration depth leftEndpoint rightEndpoint) :
    CostStaticAtomKeyCospan.TwoDepthPermutation
      (source := rhoCIGSLT) cospan targetDeclaration restorationDepth keyDepth
      ((parallelLeaves rhoReflectivePresentation.toReflectivePresentationDecl
        leftPlan.abstractPattern).map leftFrame)
      ((parallelLeaves rhoReflectivePresentation.toReflectivePresentationDecl
        rightPlan.abstractPattern).map rightFrame) := by
  let rawDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation.toReflectivePresentationDecl
  have leftTraversal := parallelLeaves_map_abstractPattern_forall2 leftPlan
    leftAdmission leftFrame
  have rightTraversal := parallelLeaves_map_abstractPattern_forall2 rightPlan
    rightAdmission rightFrame
  have leftTyped : HasType rhoCIGSLT.costWholeLanguage targetFree
      sourceAvailable leftPayload
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort) := by
    cases color <;> exact leftAdmission.wellSorted.1.1
  have rightTyped : HasType rhoCIGSLT.costWholeLanguage targetFree
      sourceAvailable rightPayload
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort) := by
    cases color <;> exact rightAdmission.wellSorted.1.1
  have permutation :=
    rhoProc_parallelLeaves_map_perm_of_foreign_canonical_eq
      (fun _ pattern => Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode pattern)
      color declarationColor different leftTyped rightTyped canonical keyDepth
  exact CostStaticAtomKeyCospan.TwoDepthPermutation.of_related_map_perm
    cospan targetDeclaration restorationDepth keyDepth
      (canonicalize rawDeclaration) (canonicalize rawDeclaration)
      leftTraversal rightTraversal permutation
      (fun leftRelated rightRelated related =>
        CostStaticAtomKeyCospan.TwoDepthApex.leafAligned (.leaf
          (CostStaticAtomKeyCospan.CommonRestorationApex.restoresTogether_of_forall_apex
            (close leftRelated rightRelated related))))

/-- Reconstruct a reached process-plan pair in its parent semantic cospan on
the diagonal where the restoration and available-depth indices agree.  This
is the exact parallel adapter used below an authored Quote, whose child
indices are all reset to zero. -/
noncomputable def
    parallelPlanStops_commonRestorationApex_of_frontiers_at_availableDepth
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern type}
    {color declarationColor : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (foreign : declarationColor ≠ color)
    (callbackAvailable callbackScope : Nat)
    {leftPayload rightPayload : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree rightPayload
      rightView.node.plan.abstractPattern)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
    (targetBoundEq : leftReached.targetBound = rightReached.targetBound)
    (thinningEq : HEq leftReached.thinning rightReached.thinning)
    (leftProcess : leftReached.sourceType = .base "Proc")
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPayload =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPayload)
    (close :
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory
        (leftView.node.semanticAtomEnvironment
          (leftView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1
      let rightEnvironment := CostStaticAtomEnvironment.ofInventory
        (rightView.node.semanticAtomEnvironment
          (rightView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      ∀ {leftRaw leftEndpoint rightRaw rightEndpoint},
      (∃ leftAbstract,
        leftRaw ∈ parallelLeaves
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPayload ∧
        LeafWitness leftReached.sourceBound leftReached.targetBound
          leftReached.thinning leftReached.sourceAvailable
          leftReached.plan.abstractPattern leftReached.plan.boundaryTable.entries
          leftRaw leftAbstract ∧
        canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          callbackAvailable
          (cospan.reifyLeft leftEnvironment.lookupAtom?
            (leftView.node.thinning.thickenAmbientBVars callbackScope
              (mapPattern (color.symbols rhoCIGSLT)
                (leftEnvironment.reify leftAbstract)))) = leftEndpoint) →
      (∃ rightAbstract,
        rightRaw ∈ parallelLeaves
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightPayload ∧
        LeafWitness rightReached.sourceBound rightReached.targetBound
          rightReached.thinning rightReached.sourceAvailable
          rightReached.plan.abstractPattern rightReached.plan.boundaryTable.entries
          rightRaw rightAbstract ∧
        canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          callbackAvailable
          (cospan.reifyRight rightEnvironment.lookupAtom?
            (rightView.node.thinning.thickenAmbientBVars callbackScope
              (mapPattern (color.symbols rhoCIGSLT)
                (rightEnvironment.reify rightAbstract)))) = rightEndpoint) →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl) leftRaw =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl) rightRaw →
      CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        callbackAvailable leftEndpoint rightEndpoint) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackAvailable leftReached.plan.abstractPattern
        rightReached.plan.abstractPattern := by
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory
    (leftView.node.semanticAtomEnvironment
      (leftView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory
    (rightView.node.semanticAtomEnvironment
      (rightView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  have leftNaturality := reached_parentCanonicalFrame_commonReify leftView.node
    leftEnvironment cospan cospan.leftSlot cospan.leftCommutes leftReached
      callbackAvailable callbackScope
  have rightNaturality := reached_parentCanonicalFrame_commonReify rightView.node
    rightEnvironment cospan cospan.rightSlot cospan.rightCommutes rightReached
      callbackAvailable callbackScope
  obtain ⟨lsb, ltb, lth, lsa, lo, lst, lp, lsc, lae⟩ := leftReached
  obtain ⟨rsb, rtb, rth, rsa, ro, rst, rp, rsc, rae⟩ := rightReached
  cases sourceBoundEq
  cases targetBoundEq
  cases sourceAvailableEq
  cases thinningEq
  have rightProcess : rst = .base "Proc" := sourceTypeEq.symm.trans leftProcess
  subst leftProcess
  subst rightProcess
  have apex := processPlans_commonRestorationApex_of_foreignCanonical
    leftEnvironment rightEnvironment leftView.node.thinning
      rightView.node.thinning cospan cospan.leftSlot cospan.rightSlot lp rp
      leftAdmission rightAdmission foreign canonical targetDeclaration rfl
      callbackScope callbackAvailable (by
        intro leftRaw leftEndpoint rightRaw rightEndpoint leftWitness
          rightWitness rawCanonical
        simpa only [leftEnvironment, rightEnvironment, cospan,
          targetDeclaration, CostStaticAtomKeyCospan.reifyLeft,
          CostStaticAtomKeyCospan.reifyRight] using
            (close (leftRaw := leftRaw) (leftEndpoint := leftEndpoint)
              (rightRaw := rightRaw) (rightEndpoint := rightEndpoint)
              leftWitness rightWitness rawCanonical))
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    leftNaturality.symm rightNaturality.symm apex

end ParallelFrontier
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
