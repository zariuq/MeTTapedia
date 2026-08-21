import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonicalOccurrenceAvailability
import Mettapedia.GSLT.LanguageDef.CostAvailabilityTransposedRestoration

/-!
# Exact planner availability at rho occurrences

For binder-free rho static plans, the availability stored at a selected
planner leaf is exactly the availability computed from its structural zipper.
Applications reset that availability precisely at authored quotation
constructors; collections merely preserve it.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace CostStaticRegionNode

@[simp]
theorem rhoAvailabilityRegime_atContext_sealed
    (context : OneHoleContext) :
    CostStaticAvailabilityRegime.atContext rhoCIGSLT.reflection.1
        .sealed context = .sealed := by
  induction context <;>
    simp_all [CostStaticAvailabilityRegime.atContext]

/-- Starting exposed, the regime tracker says `sealed` exactly where rho's
quote-local availability interpreter has discarded the ambient suffix. -/
theorem rhoCanonicalOccurrenceAvailable_eq_if_atContext
    (ambient : List TypeExpr) (context : OneHoleContext) :
    rhoCanonicalOccurrenceAvailable ambient context =
      if CostStaticAvailabilityRegime.atContext rhoCIGSLT.reflection.1
          .exposed context = .sealed then [] else ambient := by
  induction context generalizing ambient with
  | hole => rfl
  | apply constructor before inner after inductionHypothesis =>
      by_cases quote : ReflectiveContextSupport.isQuoteConstructor
          rhoCIGSLT.reflection.1 constructor = true
      · simp [rhoCanonicalOccurrenceAvailable,
          CostStaticAvailabilityRegime.atContext, quote]
      · simpa [rhoCanonicalOccurrenceAvailable,
          CostStaticAvailabilityRegime.atContext, quote] using
          inductionHypothesis ambient
  | lambda binder inner inductionHypothesis =>
      exact inductionHypothesis ambient
  | multiLambda arity binders inner inductionHypothesis =>
      exact inductionHypothesis ambient
  | substBody inner replacement inductionHypothesis =>
      exact inductionHypothesis ambient
  | substReplacement body inner inductionHypothesis =>
      exact inductionHypothesis ambient
  | collection collectionType before inner after rest inductionHypothesis =>
      exact inductionHypothesis ambient

theorem rhoCanonicalOccurrenceAvailable_eq_nil_of_atContext_sealed
    (ambient : List TypeExpr) (context : OneHoleContext)
    (sealed : CostStaticAvailabilityRegime.atContext rhoCIGSLT.reflection.1
      .exposed context = .sealed) :
    rhoCanonicalOccurrenceAvailable ambient context = [] := by
  rw [rhoCanonicalOccurrenceAvailable_eq_if_atContext, sealed]
  rfl

private theorem planOccurrence_application_split_context
    {source : CIGSLT}
    {sourceBound targetBound sourceAvailable : List TypeExpr}
    {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
    {boundaries : List CostRegionBoundary} {sourceLabel : String}
    {constructor : source.DeclaredCostConstructor}
    {children : List (CostStaticPlanDecoration source)}
    {name : String} {context : OneHoleContext} {available : List TypeExpr}
    (occurrence : CostStaticPlanAbstractOccurrence source name
      (.mk sourceBound targetBound sourceAvailable outer pattern sourceType
        boundaries (.application sourceLabel constructor children))
      context available) :
    ∃ before child after inner,
      children = before ++ child :: after ∧
        context = .apply sourceLabel
          (before.map CostStaticPlanDecoration.abstractPattern) inner
          (after.map CostStaticPlanDecoration.abstractPattern) ∧
        Nonempty (CostStaticPlanAbstractOccurrence source name child inner
          available) := by
  cases occurrence with
  | application nested => exact ⟨_, _, _, _, rfl, rfl, ⟨nested⟩⟩

private theorem planOccurrence_collection_split_context
    {source : CIGSLT}
    {sourceBound targetBound sourceAvailable : List TypeExpr}
    {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
    {boundaries : List CostRegionBoundary} {collectionType : CollType}
    {sourceRest : Option String} {choice : CostCollectionTypingChoice}
    {children : List (CostStaticPlanDecoration source)}
    {name : String} {context : OneHoleContext} {available : List TypeExpr}
    (occurrence : CostStaticPlanAbstractOccurrence source name
      (.mk sourceBound targetBound sourceAvailable outer pattern sourceType
        boundaries (.collection collectionType sourceRest choice children))
      context available) :
    ∃ before child after inner,
      children = before ++ child :: after ∧
        context = .collection collectionType
          (before.map CostStaticPlanDecoration.abstractPattern) inner
          (after.map CostStaticPlanDecoration.abstractPattern) sourceRest ∧
        Nonempty (CostStaticPlanAbstractOccurrence source name child inner
          available) := by
  cases occurrence with
  | collection nested => exact ⟨_, _, _, _, rfl, rfl, ⟨nested⟩⟩

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
mutual
  /-- In a binder-free rho static plan, a selected leaf stores precisely the
  availability obtained by following its exact zipper and resetting at quote
  constructors. -/
  theorem CostStaticRegionPlan.abstractOccurrence_available_eq_quoteLocal
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType)
      (frameFree : WellSorted.ReflectiveSubstitutionBinderFree
        plan.abstractPattern = true)
      {name : String} {context : OneHoleContext}
      {planAvailable : List TypeExpr}
      (occurrence : CostStaticPlanAbstractOccurrence rhoCIGSLT name
        plan.decoration context planAvailable) :
      planAvailable = rhoCanonicalOccurrenceAvailable sourceAvailable context := by
    cases plan with
    | bvar sourceIndex lookup correspondence availableScope =>
        cases occurrence
    | fvar lookup =>
        cases occurrence
        rfl
    | boundaryApplication constructor rendered outsideCurrent certified
        certifies =>
        cases occurrence
        rfl
    | application constructor rendered current preimage notBare children =>
        obtain ⟨before, child, after, inner, decomposition, contextEquality,
            ⟨nested⟩⟩ :=
          planOccurrence_application_split_context occurrence
        have childrenFree :
            WellSorted.ReflectiveSubstitutionBinderFreeList
              children.abstractPatterns = true := by
          simpa [CostStaticRegionPlan.abstractPattern,
            WellSorted.ReflectiveSubstitutionBinderFree] using frameFree
        have childEquality :=
          CostStaticArgumentPlan.abstractOccurrence_available_eq_quoteLocal
            (name := name) (planAvailable := planAvailable)
            children childrenFree decomposition nested
        rw [contextEquality]
        simpa [rhoCanonicalOccurrenceAvailable] using childEquality
    | lambda bodyPlan =>
        simp [CostStaticRegionPlan.abstractPattern] at frameFree
    | multiLambda bodyPlan =>
        simp [CostStaticRegionPlan.abstractPattern,
          WellSorted.ReflectiveSubstitutionBinderFree] at frameFree
    | collection choice selected children =>
        obtain ⟨before, child, after, inner, decomposition, contextEquality,
            ⟨nested⟩⟩ :=
          planOccurrence_collection_split_context occurrence
        have childrenFree :
            WellSorted.ReflectiveSubstitutionBinderFreeList
              children.abstractPatterns = true := by
          simpa [CostStaticRegionPlan.abstractPattern,
            WellSorted.ReflectiveSubstitutionBinderFree] using frameFree
        have childEquality :=
          CostStaticElementPlan.abstractOccurrence_available_eq_quoteLocal
            (name := name) (planAvailable := planAvailable)
            children childrenFree decomposition nested
        rw [contextEquality]
        simpa [rhoCanonicalOccurrenceAvailable] using childEquality
    | boundaryCollection currentRejected oppositeChoice oppositeSelected
        certified certifies =>
        cases occurrence
        rfl
  termination_by 3 * sizeOf pattern + 2

  /-- Ordered-argument companion of exact planner availability. -/
  theorem CostStaticArgumentPlan.abstractOccurrence_available_eq_quoteLocal
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {outer : OneHoleContext} {wireName : String}
      {before arguments : List Pattern} {parameters : List TermParam}
      (plan : CostStaticArgumentPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
          parameters)
      (frameFree : WellSorted.ReflectiveSubstitutionBinderFreeList
        plan.abstractPatterns = true)
      {selectedBefore selectedAfter : List
        (CostStaticPlanDecoration rhoCIGSLT)}
      {selectedDecoration : CostStaticPlanDecoration rhoCIGSLT}
      {name : String} {inner : OneHoleContext}
      {planAvailable : List TypeExpr}
      (decomposition : plan.decorations =
        selectedBefore ++ selectedDecoration :: selectedAfter)
      (nested : CostStaticPlanAbstractOccurrence rhoCIGSLT name
        selectedDecoration inner planAvailable) :
      planAvailable = rhoCanonicalOccurrenceAvailable sourceAvailable inner := by
    cases plan with
    | nil => simp [CostStaticArgumentPlan.decorations] at decomposition
    | cons representation parameterType head tail =>
        have freeParts :
            WellSorted.ReflectiveSubstitutionBinderFree
                head.abstractPattern = true ∧
              WellSorted.ReflectiveSubstitutionBinderFreeList
                tail.abstractPatterns = true := by
          simpa [CostStaticArgumentPlan.abstractPatterns,
            WellSorted.ReflectiveSubstitutionBinderFreeList] using frameFree
        cases selectedBefore with
        | nil =>
            simp only [CostStaticArgumentPlan.decorations,
              List.nil_append, List.cons.injEq] at decomposition
            let headOccurrence :=
              CostStaticPlanAbstractOccurrence.reindexDecoration
                decomposition.1.symm nested
            exact
              CostStaticRegionPlan.abstractOccurrence_available_eq_quoteLocal
                head freeParts.1 headOccurrence
        | cons skipped selectedBefore =>
            simp only [CostStaticArgumentPlan.decorations,
              List.cons_append, List.cons.injEq] at decomposition
            exact
              CostStaticArgumentPlan.abstractOccurrence_available_eq_quoteLocal
                tail freeParts.2 decomposition.2 nested
  termination_by 3 * sizeOf arguments + 1

  /-- Homogeneous-collection companion of exact planner availability. -/
  theorem CostStaticElementPlan.abstractOccurrence_available_eq_quoteLocal
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {outer : OneHoleContext} {collectionType : CollType}
      {before elements : List Pattern} {rest : Option String}
      {sourceElementType : TypeExpr}
      (plan : CostStaticElementPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
          elements rest sourceElementType)
      (frameFree : WellSorted.ReflectiveSubstitutionBinderFreeList
        plan.abstractPatterns = true)
      {selectedBefore selectedAfter : List
        (CostStaticPlanDecoration rhoCIGSLT)}
      {selectedDecoration : CostStaticPlanDecoration rhoCIGSLT}
      {name : String} {inner : OneHoleContext}
      {planAvailable : List TypeExpr}
      (decomposition : plan.decorations =
        selectedBefore ++ selectedDecoration :: selectedAfter)
      (nested : CostStaticPlanAbstractOccurrence rhoCIGSLT name
        selectedDecoration inner planAvailable) :
      planAvailable = rhoCanonicalOccurrenceAvailable sourceAvailable inner := by
    cases plan with
    | nil => simp [CostStaticElementPlan.decorations] at decomposition
    | cons head tail =>
        have freeParts :
            WellSorted.ReflectiveSubstitutionBinderFree
                head.abstractPattern = true ∧
              WellSorted.ReflectiveSubstitutionBinderFreeList
                tail.abstractPatterns = true := by
          simpa [CostStaticElementPlan.abstractPatterns,
            WellSorted.ReflectiveSubstitutionBinderFreeList] using frameFree
        cases selectedBefore with
        | nil =>
            simp only [CostStaticElementPlan.decorations,
              List.nil_append, List.cons.injEq] at decomposition
            let headOccurrence :=
              CostStaticPlanAbstractOccurrence.reindexDecoration
                decomposition.1.symm nested
            exact
              CostStaticRegionPlan.abstractOccurrence_available_eq_quoteLocal
                head freeParts.1 headOccurrence
        | cons skipped selectedBefore =>
            simp only [CostStaticElementPlan.decorations,
              List.cons_append, List.cons.injEq] at decomposition
            exact
              CostStaticElementPlan.abstractOccurrence_available_eq_quoteLocal
                tail freeParts.2 decomposition.2 nested
  termination_by 3 * sizeOf elements + 1
end

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
mutual
  /-- An exact occurrence bearing a collision-free boundary name stores that
  boundary's certified target support.  This complements the quote-local
  theorem above: the structural zipper determines where the support is
  visible, while the boundary key determines which certified support it is. -/
  theorem CostStaticRegionPlan.abstractOccurrence_available_eq_boundarySupport
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType)
      {name : String} {context : OneHoleContext}
      {planAvailable : List TypeExpr}
      (occurrence : CostStaticPlanAbstractOccurrence rhoCIGSLT name
        plan.decoration context planAvailable)
      (boundary : CostRegionBoundary)
      (nameEquality : name = costRegionBoundaryVariableName boundary) :
      planAvailable = boundary.targetSupport := by
    cases plan with
    | bvar sourceIndex lookup correspondence availableScope =>
        cases occurrence
    | @fvar sourceBound targetBound sourceAvailable thinning outer sourceName
        sourceType lookup =>
        cases occurrence with
        | sourceFVar =>
            exact (costRegionSourceVariableName_ne_boundary sourceName boundary
              nameEquality).elim
    | boundaryApplication constructor rendered outsideCurrent certified
        certifies =>
        cases occurrence with
        | boundaryApplication =>
            have boundaryEquality : certified.typed.boundary = boundary :=
              costRegionBoundaryVariableName_injective nameEquality
            subst boundary
            exact certified.targetSupport_eq.symm
    | application constructor rendered current preimage notBare children =>
        obtain ⟨before, child, after, inner, decomposition, _contextEquality,
            ⟨nested⟩⟩ :=
          planOccurrence_application_split_context occurrence
        exact
          CostStaticArgumentPlan.abstractOccurrence_available_eq_boundarySupport
            children decomposition nested boundary nameEquality
    | lambda bodyPlan =>
        cases occurrence with
        | lambda nested =>
            exact
              CostStaticRegionPlan.abstractOccurrence_available_eq_boundarySupport
                bodyPlan nested boundary nameEquality
    | multiLambda bodyPlan =>
        cases occurrence with
        | multiLambda nested =>
            exact
              CostStaticRegionPlan.abstractOccurrence_available_eq_boundarySupport
                bodyPlan nested boundary nameEquality
    | collection choice selected children =>
        obtain ⟨before, child, after, inner, decomposition, _contextEquality,
            ⟨nested⟩⟩ :=
          planOccurrence_collection_split_context occurrence
        exact
          CostStaticElementPlan.abstractOccurrence_available_eq_boundarySupport
            children decomposition nested boundary nameEquality
    | boundaryCollection currentRejected oppositeChoice oppositeSelected
        certified certifies =>
        cases occurrence with
        | boundaryCollection =>
            have boundaryEquality : certified.typed.boundary = boundary :=
              costRegionBoundaryVariableName_injective nameEquality
            subst boundary
            exact certified.targetSupport_eq.symm
  termination_by 3 * sizeOf pattern + 2

  /-- Ordered-argument companion of boundary-support identification. -/
  theorem CostStaticArgumentPlan.abstractOccurrence_available_eq_boundarySupport
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {outer : OneHoleContext} {wireName : String}
      {before arguments : List Pattern} {parameters : List TermParam}
      (plan : CostStaticArgumentPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
          parameters)
      {selectedBefore selectedAfter : List
        (CostStaticPlanDecoration rhoCIGSLT)}
      {selectedDecoration : CostStaticPlanDecoration rhoCIGSLT}
      {name : String} {inner : OneHoleContext}
      {planAvailable : List TypeExpr}
      (decomposition : plan.decorations =
        selectedBefore ++ selectedDecoration :: selectedAfter)
      (nested : CostStaticPlanAbstractOccurrence rhoCIGSLT name
        selectedDecoration inner planAvailable)
      (boundary : CostRegionBoundary)
      (nameEquality : name = costRegionBoundaryVariableName boundary) :
      planAvailable = boundary.targetSupport := by
    cases plan with
    | nil => simp [CostStaticArgumentPlan.decorations] at decomposition
    | cons representation parameterType head tail =>
        cases selectedBefore with
        | nil =>
            simp only [CostStaticArgumentPlan.decorations,
              List.nil_append, List.cons.injEq] at decomposition
            let headOccurrence :=
              CostStaticPlanAbstractOccurrence.reindexDecoration
                decomposition.1.symm nested
            exact
              CostStaticRegionPlan.abstractOccurrence_available_eq_boundarySupport
                head headOccurrence boundary nameEquality
        | cons skipped selectedBefore =>
            simp only [CostStaticArgumentPlan.decorations,
              List.cons_append, List.cons.injEq] at decomposition
            exact
              CostStaticArgumentPlan.abstractOccurrence_available_eq_boundarySupport
                tail decomposition.2 nested boundary nameEquality
  termination_by 3 * sizeOf arguments + 1

  /-- Homogeneous-collection companion of boundary-support identification. -/
  theorem CostStaticElementPlan.abstractOccurrence_available_eq_boundarySupport
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {outer : OneHoleContext} {collectionType : CollType}
      {before elements : List Pattern} {rest : Option String}
      {sourceElementType : TypeExpr}
      (plan : CostStaticElementPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
          elements rest sourceElementType)
      {selectedBefore selectedAfter : List
        (CostStaticPlanDecoration rhoCIGSLT)}
      {selectedDecoration : CostStaticPlanDecoration rhoCIGSLT}
      {name : String} {inner : OneHoleContext}
      {planAvailable : List TypeExpr}
      (decomposition : plan.decorations =
        selectedBefore ++ selectedDecoration :: selectedAfter)
      (nested : CostStaticPlanAbstractOccurrence rhoCIGSLT name
        selectedDecoration inner planAvailable)
      (boundary : CostRegionBoundary)
      (nameEquality : name = costRegionBoundaryVariableName boundary) :
      planAvailable = boundary.targetSupport := by
    cases plan with
    | nil => simp [CostStaticElementPlan.decorations] at decomposition
    | cons head tail =>
        cases selectedBefore with
        | nil =>
            simp only [CostStaticElementPlan.decorations,
              List.nil_append, List.cons.injEq] at decomposition
            let headOccurrence :=
              CostStaticPlanAbstractOccurrence.reindexDecoration
                decomposition.1.symm nested
            exact
              CostStaticRegionPlan.abstractOccurrence_available_eq_boundarySupport
                head headOccurrence boundary nameEquality
        | cons skipped selectedBefore =>
            simp only [CostStaticElementPlan.decorations,
              List.cons_append, List.cons.injEq] at decomposition
            exact
              CostStaticElementPlan.abstractOccurrence_available_eq_boundarySupport
                tail decomposition.2 nested boundary nameEquality
  termination_by 3 * sizeOf elements + 1
end

mutual
  /-- Every certified boundary in a binder-free rho plan is either exposed
  to the plan's current reflective availability or sealed below Quote. -/
  theorem CostStaticRegionPlan.boundaryTargetSupport_eq_sourceAvailable_or_nil
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType)
      (frameFree : WellSorted.ReflectiveSubstitutionBinderFree
        plan.abstractPattern = true)
      (boundary : TypedCostRegionBoundary rhoCIGSLT color targetFree)
      (membership : boundary ∈ plan.boundaryTable.entries) :
      boundary.boundary.targetSupport = sourceAvailable ∨
        boundary.boundary.targetSupport = [] := by
    cases plan with
    | bvar sourceIndex lookup correspondence availableScope =>
        change boundary ∈ ([] : List
          (TypedCostRegionBoundary rhoCIGSLT color targetFree)) at membership
        simp at membership
    | fvar lookup =>
        change boundary ∈ ([] : List
          (TypedCostRegionBoundary rhoCIGSLT color targetFree)) at membership
        simp at membership
    | boundaryApplication constructor rendered outsideCurrent certified
        certifies =>
        change boundary ∈ [certified.typed] at membership
        simp only [List.mem_singleton] at membership
        subst boundary
        exact Or.inl certified.targetSupport_eq
    | application constructor rendered current preimage notBare children =>
        have childrenFree :
            WellSorted.ReflectiveSubstitutionBinderFreeList
              children.abstractPatterns = true := by
          simpa [CostStaticRegionPlan.abstractPattern,
            WellSorted.ReflectiveSubstitutionBinderFree] using frameFree
        have childResult :=
          CostStaticArgumentPlan.boundaryTargetSupport_eq_sourceAvailable_or_nil
            children childrenFree boundary membership
        by_cases quote : ReflectiveContextSupport.isQuoteConstructor
            rhoCIGSLT.reflection.1 preimage.sourceConstructor.1.label = true
        · right
          rcases childResult with exposed | sealed
          · simpa [quote] using exposed
          · exact sealed
        · simpa [quote] using childResult
    | lambda bodyPlan =>
        simp [CostStaticRegionPlan.abstractPattern] at frameFree
    | multiLambda bodyPlan =>
        simp [CostStaticRegionPlan.abstractPattern,
          WellSorted.ReflectiveSubstitutionBinderFree] at frameFree
    | collection choice selected children =>
        have childrenFree :
            WellSorted.ReflectiveSubstitutionBinderFreeList
              children.abstractPatterns = true := by
          simpa [CostStaticRegionPlan.abstractPattern,
            WellSorted.ReflectiveSubstitutionBinderFree] using frameFree
        exact
          CostStaticElementPlan.boundaryTargetSupport_eq_sourceAvailable_or_nil
            children childrenFree boundary membership
    | boundaryCollection currentRejected oppositeChoice oppositeSelected
        certified certifies =>
        change boundary ∈ [certified.typed] at membership
        simp only [List.mem_singleton] at membership
        subst boundary
        exact Or.inl certified.targetSupport_eq
  termination_by 3 * sizeOf pattern + 2

  /-- Argument-spine companion of the boundary support dichotomy. -/
  theorem CostStaticArgumentPlan.boundaryTargetSupport_eq_sourceAvailable_or_nil
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {outer : OneHoleContext} {wireName : String}
      {before arguments : List Pattern} {parameters : List TermParam}
      (plan : CostStaticArgumentPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
        parameters)
      (frameFree : WellSorted.ReflectiveSubstitutionBinderFreeList
        plan.abstractPatterns = true)
      (boundary : TypedCostRegionBoundary rhoCIGSLT color targetFree)
      (membership : boundary ∈ plan.boundaryTable.entries) :
      boundary.boundary.targetSupport = sourceAvailable ∨
        boundary.boundary.targetSupport = [] := by
    cases plan with
    | nil =>
        change boundary ∈ ([] : List
          (TypedCostRegionBoundary rhoCIGSLT color targetFree)) at membership
        simp at membership
    | cons representation parameterType head tail =>
        have freeParts :
            WellSorted.ReflectiveSubstitutionBinderFree head.abstractPattern =
                true ∧
              WellSorted.ReflectiveSubstitutionBinderFreeList
                tail.abstractPatterns = true := by
          simpa [CostStaticArgumentPlan.abstractPatterns,
            WellSorted.ReflectiveSubstitutionBinderFreeList] using frameFree
        change boundary ∈
          (TypedCostRegionBoundaryTable.append head.boundaryTable
            tail.boundaryTable).entries at membership
        rw [TypedCostRegionBoundaryTable.entries_append] at membership
        rcases List.mem_append.mp membership with headMembership | tailMembership
        · exact
            CostStaticRegionPlan.boundaryTargetSupport_eq_sourceAvailable_or_nil
              head freeParts.1 boundary headMembership
        · exact
            CostStaticArgumentPlan.boundaryTargetSupport_eq_sourceAvailable_or_nil
              tail freeParts.2 boundary tailMembership
  termination_by 3 * sizeOf arguments + 1

  /-- Collection-spine companion of the boundary support dichotomy. -/
  theorem CostStaticElementPlan.boundaryTargetSupport_eq_sourceAvailable_or_nil
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {outer : OneHoleContext} {collectionType : CollType}
      {before elements : List Pattern} {rest : Option String}
      {sourceElementType : TypeExpr}
      (plan : CostStaticElementPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
        elements rest sourceElementType)
      (frameFree : WellSorted.ReflectiveSubstitutionBinderFreeList
        plan.abstractPatterns = true)
      (boundary : TypedCostRegionBoundary rhoCIGSLT color targetFree)
      (membership : boundary ∈ plan.boundaryTable.entries) :
      boundary.boundary.targetSupport = sourceAvailable ∨
        boundary.boundary.targetSupport = [] := by
    cases plan with
    | nil =>
        change boundary ∈ ([] : List
          (TypedCostRegionBoundary rhoCIGSLT color targetFree)) at membership
        simp at membership
    | cons head tail =>
        have freeParts :
            WellSorted.ReflectiveSubstitutionBinderFree head.abstractPattern =
                true ∧
              WellSorted.ReflectiveSubstitutionBinderFreeList
                tail.abstractPatterns = true := by
          simpa [CostStaticElementPlan.abstractPatterns,
            WellSorted.ReflectiveSubstitutionBinderFreeList] using frameFree
        change boundary ∈
          (TypedCostRegionBoundaryTable.append head.boundaryTable
            tail.boundaryTable).entries at membership
        rw [TypedCostRegionBoundaryTable.entries_append] at membership
        rcases List.mem_append.mp membership with headMembership | tailMembership
        · exact
            CostStaticRegionPlan.boundaryTargetSupport_eq_sourceAvailable_or_nil
              head freeParts.1 boundary headMembership
        · exact
            CostStaticElementPlan.boundaryTargetSupport_eq_sourceAvailable_or_nil
              tail freeParts.2 boundary tailMembership
  termination_by 3 * sizeOf elements + 1
end

end CostStaticRegionNode

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
