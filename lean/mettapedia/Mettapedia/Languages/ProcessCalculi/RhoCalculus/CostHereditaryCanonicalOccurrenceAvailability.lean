import Mettapedia.GSLT.LanguageDef.CostCanonicalOccurrenceInventoryBridge
import Mettapedia.GSLT.LanguageDef.CostReflectiveSupportTwoAvailabilitySubstitution
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonical
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryOccurrenceSupportProfile

/-!
# Quote-local availability for canonical rho occurrences

The canonical occurrence trace already retains a positional source occurrence.
This module gives its zipper the rho-specific availability interpretation used
by the support-preservation proof.  The only operation that changes that
availability is crossing an authored quote constructor.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace CostStaticRegionNode

private theorem rhoCIGSLT_reflection_eq_rhoReflectionProfile :
    rhoCIGSLT.reflection.1 = rhoReflectionProfile := rfl

theorem rhoCanonicalOccurrence_quoteBoundary :
    ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.reflection.1
      rhoReflectivePresentation.quoteConstructor = true := by
  rw [rhoCIGSLT_reflection_eq_rhoReflectionProfile]
  simp [ReflectiveContextSupport.isQuoteConstructor, rhoReflectionProfile]

/-- Reflective availability at the hole of a rho static context. -/
def rhoCanonicalOccurrenceAvailable (ambient : List TypeExpr) :
    OneHoleContext → List TypeExpr
  | .hole => ambient
  | .apply constructor _ inner _ =>
      rhoCanonicalOccurrenceAvailable
        (if ReflectiveContextSupport.isQuoteConstructor
            rhoCIGSLT.reflection.1 constructor then [] else ambient) inner
  | .lambda _ inner => rhoCanonicalOccurrenceAvailable ambient inner
  | .multiLambda _ _ inner => rhoCanonicalOccurrenceAvailable ambient inner
  | .substBody inner _ => rhoCanonicalOccurrenceAvailable ambient inner
  | .substReplacement _ inner => rhoCanonicalOccurrenceAvailable ambient inner
  | .collection _ _ inner _ _ => rhoCanonicalOccurrenceAvailable ambient inner

@[simp]
theorem rhoCanonicalOccurrenceAvailable_nil (context : OneHoleContext) :
    rhoCanonicalOccurrenceAvailable [] context = [] := by
  induction context with
  | hole => rfl
  | apply constructor before inner after inductionHypothesis =>
      simpa [rhoCanonicalOccurrenceAvailable] using inductionHypothesis
  | lambda binder inner inductionHypothesis => exact inductionHypothesis
  | multiLambda arity binders inner inductionHypothesis => exact inductionHypothesis
  | substBody inner replacement inductionHypothesis => exact inductionHypothesis
  | substReplacement body inner inductionHypothesis => exact inductionHypothesis
  | collection collectionType before inner after rest inductionHypothesis =>
      exact inductionHypothesis

theorem rhoCanonicalOccurrenceAvailable_castRoot
    {left right : Pattern} (equal : left = right)
    (occurrence : CostStaticFVarOccurrence left) (ambient : List TypeExpr) :
    rhoCanonicalOccurrenceAvailable ambient
        (CostStaticFVarOccurrence.castRoot equal occurrence).context =
      rhoCanonicalOccurrenceAvailable ambient occurrence.context := by
  cases equal
  rfl

theorem rhoCanonicalOccurrenceAvailable_castOccurrence
    {left right : Pattern} (equal : left = right)
    (occurrence : CostStaticFVarOccurrence right) (ambient : List TypeExpr) :
    rhoCanonicalOccurrenceAvailable ambient (equal.symm ▸ occurrence).context =
      rhoCanonicalOccurrenceAvailable ambient occurrence.context := by
  cases equal
  rfl

theorem rhoCanonicalOccurrenceAvailable_comp
    (ambient : List TypeExpr) (outer inner : OneHoleContext) :
    rhoCanonicalOccurrenceAvailable ambient (outer.comp inner) =
      rhoCanonicalOccurrenceAvailable
        (rhoCanonicalOccurrenceAvailable ambient outer) inner := by
  induction outer generalizing ambient with
  | hole => rfl
  | apply constructor before outer after inductionHypothesis =>
      exact inductionHypothesis _
  | lambda binder outer inductionHypothesis => exact inductionHypothesis _
  | multiLambda arity binders outer inductionHypothesis =>
      exact inductionHypothesis _
  | substBody outer replacement inductionHypothesis =>
      exact inductionHypothesis _
  | substReplacement body outer inductionHypothesis =>
      exact inductionHypothesis _
  | collection collectionType before outer after rest inductionHypothesis =>
      exact inductionHypothesis _

theorem rhoCanonicalOccurrenceAvailable_castPatterns
    {left right : List Pattern} (equal : left = right)
    (occurrence : CostStaticFVarListOccurrence left)
    (ambient : List TypeExpr) :
    rhoCanonicalOccurrenceAvailable ambient
        (CostStaticFVarListOccurrence.castPatterns equal occurrence
          ).occurrence.context =
      rhoCanonicalOccurrenceAvailable ambient occurrence.occurrence.context := by
  cases equal
  rfl

theorem rhoCanonicalOccurrenceAvailable_singletonListOccurrenceRoot
    {root : Pattern} (occurrence : CostStaticFVarListOccurrence [root])
    (ambient : List TypeExpr) :
    rhoCanonicalOccurrenceAvailable ambient
        (singletonListOccurrenceRoot occurrence).context =
      rhoCanonicalOccurrenceAvailable ambient occurrence.occurrence.context := by
  rcases occurrence with ⟨position, nested⟩
  have positionValue : position.val = 0 := by
    have bound := position.isLt
    change position.val < 1 at bound
    omega
  have positionEquality : position = ⟨0, by simp⟩ :=
    Fin.ext positionValue
  subst position
  rfl

theorem rhoCanonicalOccurrenceAvailable_pullbackPerm
    {source target : List Pattern} (permutation : target.Perm source)
    (occurrence : CostStaticFVarListOccurrence target)
    (ambient : List TypeExpr) :
    rhoCanonicalOccurrenceAvailable ambient
        (occurrence.pullbackPerm permutation).occurrence.context =
      rhoCanonicalOccurrenceAvailable ambient occurrence.occurrence.context := by
  unfold CostStaticFVarListOccurrence.pullbackPerm
  dsimp only
  exact rhoCanonicalOccurrenceAvailable_castOccurrence
    (permutation.getElem_idxBij_eq_getElem occurrence.position)
      occurrence.occurrence
      ambient

theorem rhoCanonicalOccurrenceAvailable_positionalPullback
    {source target : List Pattern}
    (embedding : CostStaticFVarListOccurrence.CostPositionalSublist target
      source)
    (occurrence : CostStaticFVarListOccurrence target)
    (ambient : List TypeExpr) :
    rhoCanonicalOccurrenceAvailable ambient
        (CostStaticFVarListOccurrence.CostPositionalSublist.pullback embedding
          occurrence).occurrence.context =
      rhoCanonicalOccurrenceAvailable ambient occurrence.occurrence.context := by
  unfold CostStaticFVarListOccurrence.CostPositionalSublist.pullback
  dsimp only
  exact rhoCanonicalOccurrenceAvailable_castOccurrence
    (CostStaticFVarListOccurrence.CostPositionalSublist.sourcePosition_get
      embedding occurrence.position) occurrence.occurrence ambient

theorem rhoCanonicalOccurrenceAvailable_filterOccurrenceSource
    (keep : Pattern → Bool) (patterns : List Pattern)
    (occurrence : CostStaticFVarListOccurrence (patterns.filter keep))
    (ambient : List TypeExpr) :
    rhoCanonicalOccurrenceAvailable ambient
        (filterOccurrenceSource keep patterns occurrence).occurrence.context =
      rhoCanonicalOccurrenceAvailable ambient occurrence.occurrence.context := by
  exact rhoCanonicalOccurrenceAvailable_positionalPullback
    (CostStaticFVarListOccurrence.filterPositionalSublist keep patterns)
      occurrence ambient

theorem rhoCanonicalOccurrenceAvailable_sortPatternsByOccurrenceSource
    {Key : Type} [LinearOrder Key] (key : Pattern → Key)
    (patterns : List Pattern)
    (occurrence : CostStaticFVarListOccurrence
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy key patterns))
    (ambient : List TypeExpr) :
    rhoCanonicalOccurrenceAvailable ambient
        (sortPatternsByOccurrenceSource key patterns occurrence
          ).occurrence.context =
      rhoCanonicalOccurrenceAvailable ambient occurrence.occurrence.context := by
  exact rhoCanonicalOccurrenceAvailable_pullbackPerm
    (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm key patterns)
      occurrence ambient

@[simp]
theorem rhoCanonicalOccurrenceAvailable_inApply
    (ambient : List TypeExpr) (constructor : String)
    {patterns : List Pattern}
    (occurrence : CostStaticFVarListOccurrence patterns) :
    rhoCanonicalOccurrenceAvailable ambient
        (occurrence.inApply constructor).context =
      rhoCanonicalOccurrenceAvailable
        (if ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.reflection.1
            constructor then [] else ambient)
        occurrence.occurrence.context := by
  rfl

@[simp]
theorem rhoCanonicalOccurrenceAvailable_inCollection
    (ambient : List TypeExpr) (collectionType : CollType)
    (rest : Option String) {patterns : List Pattern}
    (occurrence : CostStaticFVarListOccurrence patterns) :
    rhoCanonicalOccurrenceAvailable ambient
        (occurrence.inCollection collectionType rest).context =
      rhoCanonicalOccurrenceAvailable ambient occurrence.occurrence.context := by
  rfl

theorem rhoCanonicalOccurrenceAvailable_applyOccurrenceArgument
    (ambient : List TypeExpr) (constructor : String)
    (arguments : List Pattern)
    (occurrence : CostStaticFVarOccurrence (.apply constructor arguments)) :
    rhoCanonicalOccurrenceAvailable
        (if ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.reflection.1
            constructor then [] else ambient)
        (applyOccurrenceArgument constructor arguments occurrence
          ).occurrence.context =
      rhoCanonicalOccurrenceAvailable ambient occurrence.context := by
  unfold applyOccurrenceArgument
  let view := Classical.choice
    (CostApplyOccurrenceView.nonempty constructor arguments occurrence)
  change rhoCanonicalOccurrenceAvailable
      (if ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.reflection.1
          constructor then [] else ambient) view.inner =
    rhoCanonicalOccurrenceAvailable ambient occurrence.context
  rw [view.context_eq]
  rfl

theorem rhoCanonicalOccurrenceAvailable_collectionOccurrenceMember
    (ambient : List TypeExpr) (collectionType : CollType)
    (patterns : List Pattern) (rest : Option String)
    (occurrence : CostStaticFVarOccurrence
      (.collection collectionType patterns rest)) :
    rhoCanonicalOccurrenceAvailable ambient
        (collectionOccurrenceMember collectionType patterns rest occurrence
          ).occurrence.context =
      rhoCanonicalOccurrenceAvailable ambient occurrence.context := by
  unfold collectionOccurrenceMember
  let view := collectionOccurrenceView collectionType patterns rest occurrence
  change rhoCanonicalOccurrenceAvailable ambient view.inner =
    rhoCanonicalOccurrenceAvailable ambient occurrence.context
  rw [view.context_eq]
  rfl

/-- The final parallel collapse is position-preserving for local reflective
availability, including its singleton-elimination branch. -/
theorem rhoCanonicalOccurrenceAvailable_collapseParallelOccurrenceSource
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (occurrence : CostStaticFVarOccurrence
      (collapseParallel declaration patterns)) (ambient : List TypeExpr) :
    rhoCanonicalOccurrenceAvailable ambient
        (collapseParallelOccurrenceSource declaration patterns occurrence
          ).occurrence.context =
      rhoCanonicalOccurrenceAvailable ambient occurrence.context := by
  cases patterns with
  | nil =>
      have impossible := occurrence.name_mem_freeFvarNames
      simp [collapseParallel, Pattern.freeFvarNames] at impossible
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second tail =>
          exact rhoCanonicalOccurrenceAvailable_collectionOccurrenceMember
            ambient declaration.parallelCollection (first :: second :: tail)
              none occurrence

theorem rhoFinishNormalizeReflectiveApply_binderFree
    (constructor : String) (arguments : List Pattern)
    (argumentsFree :
      WellSorted.ReflectiveSubstitutionBinderFreeList arguments = true) :
    WellSorted.ReflectiveSubstitutionBinderFree
      (finishNormalizeReflectiveApply rhoReflectivePresentation constructor
        arguments) = true := by
  cases shape : finishApplyShape rhoReflectivePresentation constructor arguments with
  | retained resultEquality =>
      rw [resultEquality]
      simpa [WellSorted.ReflectiveSubstitutionBinderFree] using argumentsFree
  | exposed name constructorEquality argumentsEquality resultEquality =>
      rw [resultEquality]
      rw [argumentsEquality] at argumentsFree
      simpa [WellSorted.ReflectiveSubstitutionBinderFree,
        WellSorted.ReflectiveSubstitutionBinderFreeList] using argumentsFree

theorem rhoCollapseParallel_binderFree
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (patternsFree :
      WellSorted.ReflectiveSubstitutionBinderFreeList patterns = true) :
    WellSorted.ReflectiveSubstitutionBinderFree
      (collapseParallel declaration patterns) = true := by
  cases patterns with
  | nil =>
      simp [collapseParallel, WellSorted.ReflectiveSubstitutionBinderFree,
        WellSorted.ReflectiveSubstitutionBinderFreeList]
  | cons first rest =>
      cases rest with
      | nil =>
          simpa [collapseParallel,
            WellSorted.ReflectiveSubstitutionBinderFreeList] using patternsFree
      | cons second tail =>
          simpa [collapseParallel,
            WellSorted.ReflectiveSubstitutionBinderFree,
            WellSorted.ReflectiveSubstitutionBinderFreeList] using patternsFree

def RhoReflectiveBinderFreeAll (patterns : List Pattern) : Prop :=
  ∀ pattern ∈ patterns,
    WellSorted.ReflectiveSubstitutionBinderFree pattern = true

theorem rhoReflectiveSubstitutionBinderFreeList_iff_all
    (patterns : List Pattern) :
    WellSorted.ReflectiveSubstitutionBinderFreeList patterns = true ↔
      RhoReflectiveBinderFreeAll patterns := by
  induction patterns with
  | nil => simp [RhoReflectiveBinderFreeAll,
      WellSorted.ReflectiveSubstitutionBinderFreeList]
  | cons head tail inductionHypothesis =>
      simp [RhoReflectiveBinderFreeAll,
        WellSorted.ReflectiveSubstitutionBinderFreeList,
        inductionHypothesis]

theorem rhoParallelSplice_binderFree
    (declaration : ReflectivePresentationDecl) (pattern : Pattern)
    (patternFree : WellSorted.ReflectiveSubstitutionBinderFree pattern = true) :
    WellSorted.ReflectiveSubstitutionBinderFreeList
      (parallelSplice declaration pattern) = true := by
  cases pattern with
  | bvar | fvar | apply | lambda | multiLambda | subst =>
      simp [parallelSplice,
        WellSorted.ReflectiveSubstitutionBinderFree,
        WellSorted.ReflectiveSubstitutionBinderFreeList] at patternFree ⊢
      all_goals exact patternFree
  | collection collectionType elements rest =>
      cases rest with
      | some restName =>
          simpa [parallelSplice,
            WellSorted.ReflectiveSubstitutionBinderFree,
            WellSorted.ReflectiveSubstitutionBinderFreeList] using patternFree
      | none =>
          by_cases parallel : collectionType = declaration.parallelCollection
          · subst collectionType
            simpa [parallelSplice,
              WellSorted.ReflectiveSubstitutionBinderFree] using patternFree
          · simpa [parallelSplice, parallel,
              WellSorted.ReflectiveSubstitutionBinderFree,
              WellSorted.ReflectiveSubstitutionBinderFreeList] using patternFree

theorem rhoNormalizeParallelElementsBy_binderFree
    {Key : Type} [LinearOrder Key] (key : Pattern → Key)
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (patternsFree :
      WellSorted.ReflectiveSubstitutionBinderFreeList patterns = true) :
    WellSorted.ReflectiveSubstitutionBinderFreeList
      (normalizeParallelElementsBy key declaration patterns) = true := by
  apply (rhoReflectiveSubstitutionBinderFreeList_iff_all _).mpr
  let flattened := patterns.flatMap (parallelSplice declaration)
  let retained := flattened.filter fun pattern =>
    pattern ≠ .apply declaration.parallelUnitConstructor []
  have patternsAll : RhoReflectiveBinderFreeAll patterns :=
    (rhoReflectiveSubstitutionBinderFreeList_iff_all patterns).mp patternsFree
  have flattenedAll : RhoReflectiveBinderFreeAll flattened := by
    intro pattern membership
    simp only [flattened, List.mem_flatMap] at membership
    obtain ⟨sourcePattern, sourceMembership, expandedMembership⟩ := membership
    have sourceFree := patternsAll sourcePattern sourceMembership
    have expandedFree := rhoParallelSplice_binderFree declaration sourcePattern
      sourceFree
    exact (rhoReflectiveSubstitutionBinderFreeList_iff_all _).mp
      expandedFree pattern expandedMembership
  have retainedAll : RhoReflectiveBinderFreeAll retained := by
    intro pattern membership
    simp only [retained, List.mem_filter] at membership
    exact flattenedAll pattern membership.1
  have sortedAll : RhoReflectiveBinderFreeAll
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy key retained) := by
    intro pattern membership
    have retainedMembership : pattern ∈ retained :=
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm key retained
        ).mem_iff.mp membership
    exact retainedAll pattern retainedMembership
  exact sortedAll

mutual
  /-- Keyed rho canonicalization preserves the fragment whose substitutions
  contain no authored binders. -/
  theorem rhoReflectiveSubstitutionBinderFree_canonicalizeByDepths
      {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
      (availableDepth scopeDepth : Nat) :
      ∀ pattern,
        WellSorted.ReflectiveSubstitutionBinderFree pattern = true →
          WellSorted.ReflectiveSubstitutionBinderFree
            (canonicalizeByDepths key rhoReflectivePresentation
              availableDepth scopeDepth pattern) = true
    | .bvar _, _ => rfl
    | .fvar _, _ => rfl
    | .apply constructor arguments, free => by
        simp only [canonicalizeByDepths]
        apply rhoFinishNormalizeReflectiveApply_binderFree
        apply rhoReflectiveSubstitutionBinderFreeList_canonicalizeListByDepths
          key
          (if constructor == rhoReflectivePresentation.quoteConstructor then 0
            else availableDepth)
          scopeDepth
        exact free
    | .lambda _ _, free => by
        simp [WellSorted.ReflectiveSubstitutionBinderFree] at free
    | .multiLambda _ _ _, free => by
        simp [WellSorted.ReflectiveSubstitutionBinderFree] at free
    | .subst _ _, free => by
        simp [WellSorted.ReflectiveSubstitutionBinderFree] at free
    | .collection collectionType elements none, free => by
        simp only [canonicalizeByDepths]
        have normalizedFree :=
          rhoReflectiveSubstitutionBinderFreeList_canonicalizeListByDepths
            key availableDepth scopeDepth elements free
        split
        · apply rhoCollapseParallel_binderFree rhoReflectivePresentation
          exact rhoNormalizeParallelElementsBy_binderFree
            (key availableDepth scopeDepth) rhoReflectivePresentation _
              normalizedFree
        · exact normalizedFree
    | .collection collectionType elements (some rest), free => by
        simp only [canonicalizeByDepths,
          WellSorted.ReflectiveSubstitutionBinderFree]
        exact rhoReflectiveSubstitutionBinderFreeList_canonicalizeListByDepths
          key availableDepth scopeDepth elements free
  termination_by pattern => 3 * sizeOf pattern + 2

  /-- Pointwise companion to binder-free keyed rho canonicalization. -/
  theorem rhoReflectiveSubstitutionBinderFreeList_canonicalizeListByDepths
      {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
      (availableDepth scopeDepth : Nat) :
      ∀ patterns,
        WellSorted.ReflectiveSubstitutionBinderFreeList patterns = true →
          WellSorted.ReflectiveSubstitutionBinderFreeList
            (canonicalizeListByDepths key rhoReflectivePresentation
              availableDepth scopeDepth patterns) = true
    | [], _ => rfl
    | pattern :: patterns, free => by
        simp only [canonicalizeListByDepths,
          WellSorted.ReflectiveSubstitutionBinderFreeList,
          Bool.and_eq_true] at free ⊢
        exact ⟨
          rhoReflectiveSubstitutionBinderFree_canonicalizeByDepths key
            availableDepth scopeDepth pattern free.1,
          rhoReflectiveSubstitutionBinderFreeList_canonicalizeListByDepths key
            availableDepth scopeDepth patterns free.2⟩
  termination_by patterns => 3 * sizeOf patterns + 1

  decreasing_by
    all_goals simp_wf <;> omega
end

theorem rhoCanonicalizeListByDepths_isObjectPatternList
    {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat) :
    ∀ patterns,
      WellSorted.isObjectPatternList patterns = true →
        WellSorted.isObjectPatternList
          (canonicalizeListByDepths key rhoReflectivePresentation
            availableDepth scopeDepth patterns) = true
  | [], _ => rfl
  | pattern :: patterns, object => by
      simp only [canonicalizeListByDepths,
        WellSorted.isObjectPatternList, Bool.and_eq_true] at object ⊢
      exact ⟨
        canonicalizeByDepths_isObjectPattern key rhoReflectivePresentation
          availableDepth scopeDepth pattern object.1,
        rhoCanonicalizeListByDepths_isObjectPatternList key
          availableDepth scopeDepth patterns object.2⟩
  termination_by patterns => 3 * sizeOf patterns + 1

theorem rhoCanonicalOccurrenceAvailable_flatMapOccurrenceSource
    (expand : Pattern → List Pattern) (patterns : List Pattern)
    (occurrence : CostStaticFVarListOccurrence (patterns.flatMap expand))
    (ambient : List TypeExpr) :
    rhoCanonicalOccurrenceAvailable ambient
        (CostStaticFVarListOccurrence.flatMapOccurrenceSource expand patterns
          occurrence).expandedOccurrence.occurrence.context =
      rhoCanonicalOccurrenceAvailable ambient occurrence.occurrence.context := by
  induction patterns with
  | nil => exact Fin.elim0 occurrence.position
  | cons head tail inductionHypothesis =>
      rw [CostStaticFVarListOccurrence.flatMapOccurrenceSource]
      by_cases inHead : occurrence.position.val < (expand head).length
      · rw [dif_pos inHead]
        have elementEquality :
            (expand head).get ⟨occurrence.position.val, inHead⟩ =
              ((head :: tail).flatMap expand).get occurrence.position := by
          symm
          exact List.getElem_append_left inHead
        exact rhoCanonicalOccurrenceAvailable_castOccurrence
          elementEquality occurrence.occurrence ambient
      · rw [dif_neg inHead]
        let tailPosition : Fin (tail.flatMap expand).length :=
          ⟨occurrence.position.val - (expand head).length, by
            have bound : occurrence.position.val <
                (expand head).length + (tail.flatMap expand).length := by
              simpa [List.flatMap] using occurrence.position.isLt
            exact Nat.sub_lt_left_of_lt_add (Nat.le_of_not_gt inHead) bound⟩
        have elementEquality :
            (tail.flatMap expand).get tailPosition =
              ((head :: tail).flatMap expand).get occurrence.position := by
          symm
          exact List.getElem_append_right
            (by simpa using Nat.le_of_not_gt inHead)
        let tailOccurrence : CostStaticFVarListOccurrence
            (tail.flatMap expand) :=
          { position := tailPosition
            occurrence := elementEquality ▸ occurrence.occurrence }
        have tailAvailable :
            rhoCanonicalOccurrenceAvailable ambient
                tailOccurrence.occurrence.context =
              rhoCanonicalOccurrenceAvailable ambient
                occurrence.occurrence.context := by
          unfold tailOccurrence
          dsimp only
          exact rhoCanonicalOccurrenceAvailable_castOccurrence
            elementEquality occurrence.occurrence ambient
        exact (inductionHypothesis tailOccurrence).trans tailAvailable

theorem rhoCanonicalOccurrenceAvailable_parallelSpliceOccurrenceSource
    (declaration : ReflectivePresentationDecl) {pattern : Pattern}
    (occurrence : CostStaticFVarListOccurrence
      (parallelSplice declaration pattern)) (ambient : List TypeExpr) :
    rhoCanonicalOccurrenceAvailable ambient
        (parallelSpliceOccurrenceSource declaration occurrence).context =
      rhoCanonicalOccurrenceAvailable ambient occurrence.occurrence.context := by
  cases pattern with
  | collection collectionType elements rest =>
      cases rest with
      | some restName =>
          have spliceEquality :
              parallelSplice declaration
                  (.collection collectionType elements (some restName)) =
                [.collection collectionType elements (some restName)] := rfl
          simpa only [parallelSpliceOccurrenceSource] using
            (rhoCanonicalOccurrenceAvailable_singletonListOccurrenceRoot
              (occurrence.castPatterns spliceEquality) ambient).trans
            (rhoCanonicalOccurrenceAvailable_castPatterns spliceEquality
              occurrence ambient)
      | none =>
          by_cases parallel :
              collectionType = declaration.parallelCollection
          · subst collectionType
            have spliceEquality :
                parallelSplice declaration
                    (.collection declaration.parallelCollection elements none) =
                  elements := by
              simp [parallelSplice]
            simpa [parallelSpliceOccurrenceSource] using
              (rhoCanonicalOccurrenceAvailable_inCollection ambient
                declaration.parallelCollection none
                  (occurrence.castPatterns spliceEquality)).trans
              (rhoCanonicalOccurrenceAvailable_castPatterns spliceEquality
                occurrence ambient)
          · have spliceEquality :
                parallelSplice declaration
                    (.collection collectionType elements none) =
                  [.collection collectionType elements none] := by
              simp [parallelSplice, parallel]
            simpa only [parallelSpliceOccurrenceSource, dif_neg parallel] using
              (rhoCanonicalOccurrenceAvailable_singletonListOccurrenceRoot
                (occurrence.castPatterns spliceEquality) ambient).trans
              (rhoCanonicalOccurrenceAvailable_castPatterns spliceEquality
                occurrence ambient)
  | bvar index =>
      simpa only [parallelSpliceOccurrenceSource] using
        (rhoCanonicalOccurrenceAvailable_singletonListOccurrenceRoot
          occurrence ambient)
  | fvar name =>
      simpa only [parallelSpliceOccurrenceSource] using
        (rhoCanonicalOccurrenceAvailable_singletonListOccurrenceRoot
          occurrence ambient)
  | apply constructor arguments =>
      simpa only [parallelSpliceOccurrenceSource] using
        (rhoCanonicalOccurrenceAvailable_singletonListOccurrenceRoot
          occurrence ambient)
  | lambda binder body =>
      simpa only [parallelSpliceOccurrenceSource] using
        (rhoCanonicalOccurrenceAvailable_singletonListOccurrenceRoot
          occurrence ambient)
  | multiLambda arity binders body =>
      simpa only [parallelSpliceOccurrenceSource] using
        (rhoCanonicalOccurrenceAvailable_singletonListOccurrenceRoot
          occurrence ambient)
  | subst body replacement =>
      simpa only [parallelSpliceOccurrenceSource] using
        (rhoCanonicalOccurrenceAvailable_singletonListOccurrenceRoot
          occurrence ambient)

theorem rhoCanonicalOccurrenceAvailable_parallelFlatMapOccurrenceSource
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (occurrence : CostStaticFVarListOccurrence
      (patterns.flatMap (parallelSplice declaration)))
    (ambient : List TypeExpr) :
    rhoCanonicalOccurrenceAvailable ambient
        (parallelFlatMapOccurrenceSource declaration patterns occurrence
          ).occurrence.context =
      rhoCanonicalOccurrenceAvailable ambient occurrence.occurrence.context := by
  unfold parallelFlatMapOccurrenceSource
  let source := CostStaticFVarListOccurrence.flatMapOccurrenceSource
    (parallelSplice declaration) patterns occurrence
  exact
    (rhoCanonicalOccurrenceAvailable_parallelSpliceOccurrenceSource
      declaration source.expandedOccurrence ambient).trans
    (rhoCanonicalOccurrenceAvailable_flatMapOccurrenceSource
      (parallelSplice declaration) patterns occurrence ambient)

theorem rhoCanonicalOccurrenceAvailable_normalizeParallelOccurrenceSource
    {Key : Type} [LinearOrder Key] (key : Pattern → Key)
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (occurrence : CostStaticFVarListOccurrence
      (normalizeParallelElementsBy key declaration patterns))
    (ambient : List TypeExpr) :
    rhoCanonicalOccurrenceAvailable ambient
        (normalizeParallelElementsByOccurrenceSource key declaration patterns
          occurrence).occurrence.context =
      rhoCanonicalOccurrenceAvailable ambient occurrence.occurrence.context := by
  unfold normalizeParallelElementsByOccurrenceSource
  let flattened := patterns.flatMap (parallelSplice declaration)
  let retained := flattened.filter fun pattern =>
    pattern ≠ .apply declaration.parallelUnitConstructor []
  let phaseEquality : normalizeParallelElementsBy key declaration patterns =
      Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy key retained := by
    rfl
  let sortedOccurrence : CostStaticFVarListOccurrence
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy key retained) :=
    occurrence.castPatterns phaseEquality
  let retainedOccurrence :=
    sortPatternsByOccurrenceSource key retained sortedOccurrence
  let flattenedOccurrence := filterOccurrenceSource
    (fun pattern => pattern ≠ .apply declaration.parallelUnitConstructor [])
    flattened retainedOccurrence
  exact
    (rhoCanonicalOccurrenceAvailable_parallelFlatMapOccurrenceSource
      declaration patterns flattenedOccurrence ambient).trans
    ((rhoCanonicalOccurrenceAvailable_filterOccurrenceSource
      (fun pattern => pattern ≠ .apply declaration.parallelUnitConstructor [])
      flattened retainedOccurrence ambient).trans
    ((rhoCanonicalOccurrenceAvailable_sortPatternsByOccurrenceSource
      key retained sortedOccurrence ambient).trans
    (rhoCanonicalOccurrenceAvailable_castPatterns phaseEquality occurrence
      ambient)))

theorem rhoCanonicalOccurrenceAvailable_keyedParallelPhaseOccurrenceSource
    {Key : Type} [LinearOrder Key] (key : Pattern → Key)
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (occurrence : CostStaticFVarOccurrence
      (collapseParallel declaration
        (normalizeParallelElementsBy key declaration patterns)))
    (ambient : List TypeExpr) :
    rhoCanonicalOccurrenceAvailable ambient
        (keyedParallelPhaseOccurrenceSource key declaration patterns occurrence
          ).occurrence.context =
      rhoCanonicalOccurrenceAvailable ambient occurrence.context := by
  unfold keyedParallelPhaseOccurrenceSource
  let normalizedOccurrence := collapseParallelOccurrenceSource declaration
    (normalizeParallelElementsBy key declaration patterns) occurrence
  exact
    (rhoCanonicalOccurrenceAvailable_normalizeParallelOccurrenceSource
      key declaration patterns normalizedOccurrence ambient).trans
    (rhoCanonicalOccurrenceAvailable_collapseParallelOccurrenceSource
      declaration (normalizeParallelElementsBy key declaration patterns)
        occurrence ambient)

/-- Through the Quote/Drop finisher, a selected occurrence either retains its
exact local availability or comes from a quote-sealed source position. -/
theorem rhoCanonicalOccurrenceAvailable_finishApplyOccurrenceSource_eq_or_nil
    (constructor : String) (arguments : List Pattern)
    (occurrence : CostStaticFVarOccurrence
      (finishNormalizeReflectiveApply rhoReflectivePresentation constructor
        arguments)) (ambient : List TypeExpr) :
    rhoCanonicalOccurrenceAvailable
        (if ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.reflection.1
            constructor then [] else ambient)
        (finishApplyOccurrenceSource rhoReflectivePresentation constructor
          arguments occurrence).occurrence.context =
      rhoCanonicalOccurrenceAvailable ambient occurrence.context ∨
    rhoCanonicalOccurrenceAvailable
        (if ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.reflection.1
            constructor then [] else ambient)
        (finishApplyOccurrenceSource rhoReflectivePresentation constructor
          arguments occurrence).occurrence.context = [] := by
  unfold finishApplyOccurrenceSource
  cases shape : finishApplyShape rhoReflectivePresentation constructor arguments with
  | retained resultEquality =>
      left
      simpa using
        (rhoCanonicalOccurrenceAvailable_applyOccurrenceArgument ambient
          constructor arguments (occurrence.castRoot resultEquality)).trans
          (rhoCanonicalOccurrenceAvailable_castRoot resultEquality occurrence
            ambient)
  | exposed name constructorEquality argumentsEquality resultEquality =>
      subst constructor
      subst arguments
      right
      rw [rhoCanonicalOccurrence_quoteBoundary]
      exact rhoCanonicalOccurrenceAvailable_nil _

/-- Typing inversion for the authored rho Quote/Drop redex.  The exposed
payload lies in the exact `Name` fibre. -/
theorem rhoQuoteDrop_inner_typed
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {inner : Pattern} {type : TypeExpr}
    (typed : WellSorted.HasType rhoCalc free bound
      (.apply "NQuote" [.apply "PDrop" [inner]]) type) :
    WellSorted.HasType rhoCalc free bound inner TypeExpr.name := by
  obtain ⟨rule, membership, labelEquality, _notBare, _typeEquality,
      argumentsTyped⟩ := WellSorted.hasType_apply_inversion typed
  simp [rhoCalc] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
  · simp at labelEquality
  · simp at labelEquality
  · cases argumentsTyped with
    | @cons _ argument arguments parameter parameters expected
        representation parameterType argumentTyped tailTyped =>
        cases tailTyped
        have expectedEquality : expected = TypeExpr.proc := by
          simpa [WellSorted.parameterType?, TypeExpr.proc,
            TypeExpr.baseType] using parameterType.symm
        subst expected
        obtain ⟨innerTyped, _innerSafe⟩ :=
          CanonicalSupport.drop_argument_supportSafe argumentTyped
            (argumentTyped.reflectiveSupportSafeAt_empty bound)
        exact innerTyped
  · simp at labelEquality
  · simp at labelEquality
  · simp at labelEquality

/-- Pointwise rho canonicalization preserves a typed constructor-argument
spine at its explicit quote-visible depth. -/
theorem rhoCanonicalizeListByDepths_argumentsTyped
    {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {arguments : List Pattern} {parameters : List TermParam}
    (typed : WellSorted.ArgumentsHaveTypes rhoCalc free bound arguments
      parameters)
    (canonicalizable : CanonicalSupport.ParametersCanonicalizable parameters)
    (object : WellSorted.isObjectPatternList arguments = true) :
    WellSorted.ArgumentsHaveTypes rhoCalc free bound
      (canonicalizeListByDepths key rhoReflectivePresentation availableDepth
        scopeDepth arguments) parameters := by
  induction arguments generalizing parameters with
  | nil =>
      cases parameters with
      | nil =>
          cases typed
          simpa [canonicalizeListByDepths] using
            (WellSorted.ArgumentsHaveTypes.nil
              (language := rhoCalc) (free := free) (bound := bound))
      | cons parameter parameters =>
          cases typed
  | cons argument arguments inductionHypothesis =>
      cases parameters with
      | nil =>
          cases typed
      | cons parameter parameters =>
          cases typed with
          | @cons _ _ _ _ _ expected representation parameterType argumentTyped
              argumentsTyped =>
              have objectParts : WellSorted.isObjectPattern argument = true ∧
                  WellSorted.isObjectPatternList arguments = true := by
                simpa [WellSorted.isObjectPatternList] using object
              have argumentCanonicalizable :
                  CanonicalSupport.CanonicalizableRhoType expected :=
                canonicalizable parameter (by simp) expected parameterType
              obtain ⟨normalizedArgumentTyped, _normalizedArgumentSafe⟩ :=
                CanonicalSupport.canonicalizeByDepths_supportSafe key scopeDepth
                  argumentTyped
                  (argumentTyped.reflectiveSupportSafeAt_empty
                    (List.replicate availableDepth TypeExpr.name))
                  argumentCanonicalizable objectParts.1
              have normalizedArgumentTyped' : WellSorted.HasType rhoCalc free bound
                  (canonicalizeByDepths key rhoReflectivePresentation
                    availableDepth scopeDepth argument) expected := by
                simpa using normalizedArgumentTyped
              have tailCanonicalizable :
                  CanonicalSupport.ParametersCanonicalizable parameters := by
                intro tailParameter membership tailExpected tailType
                exact canonicalizable tailParameter (by simp [membership])
                  tailExpected tailType
              have normalizedArgumentsTyped := inductionHypothesis argumentsTyped
                tailCanonicalizable objectParts.2
              have normalizedRepresentation :=
                CanonicalSupport.matchesParameterRepresentation_canonicalizeByDepths
                  key availableDepth scopeDepth parameter argument representation
              simpa [canonicalizeListByDepths] using
                WellSorted.ArgumentsHaveTypes.cons normalizedRepresentation
                  parameterType normalizedArgumentTyped' normalizedArgumentsTyped

/-- The exact occurrence trace only needs elementwise typing.  Both typed
constructor spines and homogeneous collection fibres provide it. -/
def RhoPatternListHasType (free : WellSorted.FreeTypeContext)
    (bound : List TypeExpr) (patterns : List Pattern) : Prop :=
  ∀ pattern ∈ patterns, ∃ type,
    WellSorted.HasType rhoCalc free bound pattern type

theorem RhoPatternListHasType.ofArguments
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {arguments : List Pattern} {parameters : List TermParam}
    (typed : WellSorted.ArgumentsHaveTypes rhoCalc free bound arguments
      parameters) :
    RhoPatternListHasType free bound arguments := by
  induction arguments generalizing parameters with
  | nil =>
      cases parameters with
      | nil => simp [RhoPatternListHasType]
      | cons parameter parameters => cases typed
  | cons argument arguments inductionHypothesis =>
      cases parameters with
      | nil => cases typed
      | cons parameter parameters =>
          cases typed with
          | @cons _ _ _ _ _ expected representation parameterType argumentTyped
              argumentsTyped =>
              intro pattern membership
              simp only [List.mem_cons] at membership
              rcases membership with rfl | membership
              · exact ⟨expected, argumentTyped⟩
              · exact inductionHypothesis argumentsTyped pattern membership

theorem RhoPatternListHasType.ofElements
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern} {elementType : TypeExpr}
    (typed : WellSorted.ElementsHaveType rhoCalc free bound elements
      elementType) :
    RhoPatternListHasType free bound elements := by
  induction elements generalizing elementType with
  | nil =>
      cases typed
      simp [RhoPatternListHasType]
  | cons element elements inductionHypothesis =>
      cases typed with
      | @cons _ _ _ _ elementTyped elementsTyped =>
          intro pattern membership
          simp only [List.mem_cons] at membership
          rcases membership with rfl | membership
          · exact ⟨_, elementTyped⟩
          · exact inductionHypothesis elementsTyped pattern membership

/-- A visible free-variable occurrence in a binder-free rho object of Name
sort is itself a Name-sorted source variable.  Quote-headed Name objects are
sealed, so they cannot contain such a visible occurrence. -/
theorem rhoTypedNameFVar_lookup_of_available_ne_nil
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {pattern : Pattern}
    (typed : WellSorted.HasType rhoCalc free bound pattern TypeExpr.name)
    (object : WellSorted.isObjectPattern pattern = true)
    (frameFree : WellSorted.ReflectiveSubstitutionBinderFree pattern = true)
    (occurrence : CostStaticFVarOccurrence pattern)
    (ambient : List TypeExpr)
    (available_ne_nil :
      rhoCanonicalOccurrenceAvailable ambient occurrence.context ≠ []) :
    free occurrence.name = some TypeExpr.name := by
  cases pattern with
  | bvar index =>
      have impossible := occurrence.name_mem_freeFvarNames
      simp [Pattern.freeFvarNames] at impossible
  | fvar name =>
      cases typed with
      | fvar lookup =>
          have nameEquality : occurrence.name = name := by
            simpa [Pattern.freeFvarNames] using occurrence.name_mem_freeFvarNames
          simpa [nameEquality] using lookup
  | apply constructor arguments =>
      obtain ⟨rule, membership, labelEquality, _notBare, typeEquality,
          _argumentsTyped⟩ := WellSorted.hasType_apply_inversion typed
      have categoryEquality : rule.category = "Name" :=
        (TypeExpr.base.inj typeEquality).symm
      have sealed :=
        EquationSubstitution.rho_reflectiveNameResultSealed
          rhoReflectivePresentation.toReflectivePresentationDecl
          (by simp [rhoReflectionProfile]) rule membership categoryEquality
      let view := Classical.choice
        (CostApplyOccurrenceView.nonempty constructor arguments occurrence)
      have constructorEquality :
          constructor = rhoReflectivePresentation.quoteConstructor :=
        labelEquality.trans sealed.1
      have localNil : rhoCanonicalOccurrenceAvailable ambient
          occurrence.context = [] := by
        rw [view.context_eq]
        change rhoCanonicalOccurrenceAvailable
            (if ReflectiveContextSupport.isQuoteConstructor
                rhoCIGSLT.reflection.1 constructor then [] else ambient)
            view.inner = []
        have quoteBoundary :
            ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.reflection.1
              constructor = true := by
          rw [constructorEquality]
          exact rhoCanonicalOccurrence_quoteBoundary
        rw [quoteBoundary]
        exact rhoCanonicalOccurrenceAvailable_nil _
      exact (available_ne_nil localNil).elim
  | lambda binder body =>
      simp [WellSorted.ReflectiveSubstitutionBinderFree] at frameFree
  | multiLambda arity binders body =>
      simp [WellSorted.ReflectiveSubstitutionBinderFree] at frameFree
  | subst body replacement =>
      simp [WellSorted.ReflectiveSubstitutionBinderFree] at frameFree
  | collection collectionType elements rest =>
      rcases WellSorted.hasType_collection_inversion typed with
        ⟨elementType, typeEquality, _elementsTyped⟩ |
          ⟨rule, parameterName, elementType, membership, parameterShape,
            typeEquality, _elementsTyped⟩
      · cases typeEquality
      · have categoryEquality : rule.category = "Name" :=
          (TypeExpr.base.inj typeEquality).symm
        have sealed :=
          EquationSubstitution.rho_reflectiveNameResultSealed
            rhoReflectivePresentation.toReflectivePresentationDecl
            (by simp [rhoReflectionProfile]) rule membership categoryEquality
        exact (sealed.2 ⟨parameterName, collectionType, elementType,
          parameterShape⟩).elim

/-- The typed Quote/Drop finisher gives the local ancestry dichotomy needed
by rho support transport: an exact availability match, or a sealed source
occurrence whose source variable has Name sort. -/
theorem rhoCanonicalOccurrenceAvailable_finishApplyOccurrenceSource_eq_or_name
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    (constructor : String) (arguments : List Pattern) {type : TypeExpr}
    (typed : WellSorted.HasType rhoCalc free bound
      (.apply constructor arguments) type)
    (object : WellSorted.isObjectPattern
      (.apply constructor arguments) = true)
    (frameFree : WellSorted.ReflectiveSubstitutionBinderFree
      (.apply constructor arguments) = true)
    (occurrence : CostStaticFVarOccurrence
      (finishNormalizeReflectiveApply rhoReflectivePresentation constructor
        arguments)) (ambient : List TypeExpr) :
    rhoCanonicalOccurrenceAvailable
        (if ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.reflection.1
            constructor then [] else ambient)
        (finishApplyOccurrenceSource rhoReflectivePresentation constructor
          arguments occurrence).occurrence.context =
      rhoCanonicalOccurrenceAvailable ambient occurrence.context ∨
    (rhoCanonicalOccurrenceAvailable
        (if ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.reflection.1
            constructor then [] else ambient)
        (finishApplyOccurrenceSource rhoReflectivePresentation constructor
          arguments occurrence).occurrence.context = [] ∧
      free (finishApplyOccurrenceSource rhoReflectivePresentation constructor
        arguments occurrence).occurrence.name = some TypeExpr.name) := by
  unfold finishApplyOccurrenceSource
  cases shape : finishApplyShape rhoReflectivePresentation constructor arguments with
  | retained resultEquality =>
      left
      simpa using
        (rhoCanonicalOccurrenceAvailable_applyOccurrenceArgument ambient
          constructor arguments (occurrence.castRoot resultEquality)).trans
          (rhoCanonicalOccurrenceAvailable_castRoot resultEquality occurrence
            ambient)
  | exposed name constructorEquality argumentsEquality resultEquality =>
      subst constructor
      subst arguments
      let exposedOccurrence := occurrence.castRoot resultEquality
      by_cases targetNil :
          rhoCanonicalOccurrenceAvailable ambient occurrence.context = []
      · left
        rw [rhoCanonicalOccurrence_quoteBoundary]
        exact (rhoCanonicalOccurrenceAvailable_nil _).trans targetNil.symm
      · right
        constructor
        · rw [rhoCanonicalOccurrence_quoteBoundary]
          exact rhoCanonicalOccurrenceAvailable_nil _
        · have payloadTyped : WellSorted.HasType rhoCalc free bound name
              TypeExpr.name := by
            simpa [rhoReflectivePresentation] using rhoQuoteDrop_inner_typed typed
          have payloadObject : WellSorted.isObjectPattern name = true := by
            simpa [WellSorted.isObjectPattern,
              WellSorted.isObjectPatternList] using object
          have payloadFree : WellSorted.ReflectiveSubstitutionBinderFree
              name = true := by
            simpa [WellSorted.ReflectiveSubstitutionBinderFree,
              WellSorted.ReflectiveSubstitutionBinderFreeList] using frameFree
          have exposedAvailableNe :
              rhoCanonicalOccurrenceAvailable ambient
                exposedOccurrence.context ≠ [] := by
            intro exposedNil
            apply targetNil
            exact
              (rhoCanonicalOccurrenceAvailable_castRoot resultEquality
                occurrence ambient).symm.trans exposedNil
          have exposedName : free exposedOccurrence.name = some TypeExpr.name :=
            rhoTypedNameFVar_lookup_of_available_ne_nil payloadTyped
              payloadObject payloadFree exposedOccurrence ambient
                exposedAvailableNe
          simpa [exposedOccurrence] using exposedName

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
mutual
  /-- Typed exact ancestry through full rho canonicalization.  A selected
  occurrence either keeps its quote-local availability or traces to a sealed
  Name-sorted source variable. -/
  theorem rhoCanonicalOccurrenceAvailable_canonicalizeByDepthsOccurrenceSource_eq_or_name
      {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
      (availableDepth scopeDepth : Nat) :
      ∀ (pattern : Pattern) (free : WellSorted.FreeTypeContext)
        (bound : List TypeExpr) (type : TypeExpr)
        (_typed : WellSorted.HasType rhoCalc free bound pattern type)
        (occurrence : CostStaticFVarOccurrence
          (canonicalizeByDepths key rhoReflectivePresentation availableDepth
            scopeDepth pattern))
        (ambient : List TypeExpr),
        WellSorted.ReflectiveSubstitutionBinderFree pattern = true →
        WellSorted.isObjectPattern pattern = true →
          rhoCanonicalOccurrenceAvailable ambient
              (canonicalizeByDepthsOccurrenceSource key
                rhoReflectivePresentation availableDepth scopeDepth pattern
                  occurrence).context =
            rhoCanonicalOccurrenceAvailable ambient occurrence.context ∨
          (rhoCanonicalOccurrenceAvailable ambient
              (canonicalizeByDepthsOccurrenceSource key
                rhoReflectivePresentation availableDepth scopeDepth pattern
                  occurrence).context = [] ∧
            free (canonicalizeByDepthsOccurrenceSource key
              rhoReflectivePresentation availableDepth scopeDepth pattern
                occurrence).name = some TypeExpr.name)
    | .bvar index, free, bound, type, typed, occurrence, _, _, _ => by
        have impossible := occurrence.name_mem_freeFvarNames
        simp [canonicalizeByDepths, Pattern.freeFvarNames] at impossible
    | .fvar name, free, bound, type, typed, occurrence, _, _, _ => by
        left
        rw [canonicalizeByDepthsOccurrenceSource]
    | .apply constructor arguments, free, bound, type, typed, occurrence,
        ambient, frameFree, object => by
        obtain ⟨rule, membership, labelEquality, notBare, typeEquality,
            argumentsTyped⟩ := WellSorted.hasType_apply_inversion typed
        subst constructor
        let childAvailableDepth :=
          if rule.label == rhoReflectivePresentation.quoteConstructor then 0
          else availableDepth
        let childAmbient :=
          if ReflectiveContextSupport.isQuoteConstructor
              rhoCIGSLT.reflection.1 rule.label then [] else ambient
        let normalizedArguments :=
          canonicalizeListByDepths key rhoReflectivePresentation
            childAvailableDepth scopeDepth arguments
        let normalizedArgument := finishApplyOccurrenceSource
          rhoReflectivePresentation rule.label normalizedArguments occurrence
        let sourceArgument := canonicalizeListByDepthsOccurrenceSource key
          rhoReflectivePresentation childAvailableDepth scopeDepth arguments
            normalizedArgument
        have argumentsObject :
            WellSorted.isObjectPatternList arguments = true := by
          simpa [WellSorted.isObjectPattern] using object
        have argumentsFree :
            WellSorted.ReflectiveSubstitutionBinderFreeList arguments = true := by
          simpa [WellSorted.ReflectiveSubstitutionBinderFree] using frameFree
        have parametersCanonicalizable :=
          CanonicalSupport.rhoRule_parametersCanonicalizable membership notBare
        have normalizedArgumentsTyped :
            WellSorted.ArgumentsHaveTypes rhoCalc free bound
              normalizedArguments rule.params := by
          exact rhoCanonicalizeListByDepths_argumentsTyped key
            childAvailableDepth scopeDepth argumentsTyped
              parametersCanonicalizable argumentsObject
        let preFinishTyped : WellSorted.HasType rhoCalc free bound
            (.apply rule.label normalizedArguments) (.base rule.category) :=
          .constructor membership notBare normalizedArgumentsTyped
        have normalizedArgumentsObject :
            WellSorted.isObjectPatternList normalizedArguments = true := by
          exact rhoCanonicalizeListByDepths_isObjectPatternList key
            childAvailableDepth scopeDepth arguments argumentsObject
        have preFinishObject : WellSorted.isObjectPattern
            (.apply rule.label normalizedArguments) = true := by
          simpa [WellSorted.isObjectPattern] using normalizedArgumentsObject
        have normalizedArgumentsFree :
            WellSorted.ReflectiveSubstitutionBinderFreeList
              normalizedArguments = true := by
          dsimp [normalizedArguments]
          exact
            rhoReflectiveSubstitutionBinderFreeList_canonicalizeListByDepths
              key childAvailableDepth scopeDepth arguments argumentsFree
        have preFinishFree : WellSorted.ReflectiveSubstitutionBinderFree
            (.apply rule.label normalizedArguments) = true := by
          simpa [WellSorted.ReflectiveSubstitutionBinderFree] using
            normalizedArgumentsFree
        have nested :=
          rhoCanonicalOccurrenceAvailable_canonicalizeListByDepthsOccurrenceSource_eq_or_name
            key childAvailableDepth scopeDepth arguments free bound
              (RhoPatternListHasType.ofArguments argumentsTyped)
                normalizedArgument childAmbient argumentsFree argumentsObject
        have finished :=
          rhoCanonicalOccurrenceAvailable_finishApplyOccurrenceSource_eq_or_name
            rule.label normalizedArguments preFinishTyped preFinishObject
              preFinishFree occurrence ambient
        rw [canonicalizeByDepthsOccurrenceSource]
        change rhoCanonicalOccurrenceAvailable ambient
            (sourceArgument.inApply rule.label).context =
              rhoCanonicalOccurrenceAvailable ambient occurrence.context ∨
            (rhoCanonicalOccurrenceAvailable childAmbient
                sourceArgument.occurrence.context = [] ∧
              free (sourceArgument.inApply rule.label).name =
                some TypeExpr.name)
        rw [rhoCanonicalOccurrenceAvailable_inApply]
        rcases nested with nestedEq | nestedExposure
        · rcases finished with finishedEq | finishedName
          · exact Or.inl (nestedEq.trans finishedEq)
          · right
            constructor
            · exact nestedEq.trans finishedName.1
            have sourceName :=
              canonicalizeListByDepthsOccurrenceSource_name key
                rhoReflectivePresentation childAvailableDepth scopeDepth
                  arguments normalizedArgument
            have normalizedArgumentName :
                free normalizedArgument.occurrence.name =
                  some TypeExpr.name := by
              simpa [normalizedArgument] using finishedName.2
            have sourceArgumentName :
                free sourceArgument.occurrence.name = some TypeExpr.name := by
              rw [sourceName]
              exact normalizedArgumentName
            simpa [sourceArgument] using sourceArgumentName
        · exact Or.inr nestedExposure
    | .lambda binder body, free, bound, type, typed, occurrence, ambient,
        frameFree, object => by
        simp [WellSorted.ReflectiveSubstitutionBinderFree] at frameFree
    | .multiLambda arity binders body, free, bound, type, typed, occurrence,
        ambient, frameFree, object => by
        simp [WellSorted.ReflectiveSubstitutionBinderFree] at frameFree
    | .subst body replacement, free, bound, type, typed, occurrence, ambient,
        frameFree, object => by
        simp [WellSorted.ReflectiveSubstitutionBinderFree] at frameFree
    | .collection collectionType elements rest, free, bound, type, typed,
        occurrence, ambient, frameFree, object => by
        obtain ⟨elementType, elementsTyped⟩ : ∃ elementType,
            WellSorted.ElementsHaveType rhoCalc free bound elements
              elementType := by
          rcases WellSorted.hasType_collection_inversion typed with
            ⟨elementType, _typeEquality, elementsTyped⟩ |
              ⟨rule, parameterName, elementType, membership, parameterShape,
                _typeEquality, elementsTyped⟩
          · exact ⟨elementType, elementsTyped⟩
          · exact ⟨elementType, elementsTyped⟩
        have elementsFree :
            WellSorted.ReflectiveSubstitutionBinderFreeList elements = true := by
          simpa [WellSorted.ReflectiveSubstitutionBinderFree] using frameFree
        have elementsObject :
            WellSorted.isObjectPatternList elements = true := by
          cases rest with
          | none =>
              simpa [WellSorted.isObjectPattern] using object
          | some restName =>
              simp [WellSorted.isObjectPattern] at object
        let normalizedElements := canonicalizeListByDepths key
          rhoReflectivePresentation availableDepth scopeDepth elements
        cases rest with
        | none =>
            by_cases parallel :
                collectionType = rhoReflectivePresentation.parallelCollection
            · subst collectionType
              rw [canonicalizeByDepthsOccurrenceSource, dif_pos rfl]
              let phaseEquality :
                  canonicalizeByDepths key rhoReflectivePresentation
                      availableDepth scopeDepth
                      (.collection rhoReflectivePresentation.parallelCollection
                        elements none) =
                    collapseParallel rhoReflectivePresentation
                      (normalizeParallelElementsBy
                        (key availableDepth scopeDepth) rhoReflectivePresentation
                          normalizedElements) := by
                simp [canonicalizeByDepths, normalizedElements]
              let finalOccurrence := occurrence.castRoot phaseEquality
              let normalizedOccurrence := keyedParallelPhaseOccurrenceSource
                (key availableDepth scopeDepth) rhoReflectivePresentation
                  normalizedElements finalOccurrence
              let sourceOccurrence :=
                canonicalizeListByDepthsOccurrenceSource key
                  rhoReflectivePresentation availableDepth scopeDepth elements
                    normalizedOccurrence
              have nested :=
                rhoCanonicalOccurrenceAvailable_canonicalizeListByDepthsOccurrenceSource_eq_or_name
                  key availableDepth scopeDepth elements free bound
                    (RhoPatternListHasType.ofElements elementsTyped)
                      normalizedOccurrence ambient elementsFree elementsObject
              change rhoCanonicalOccurrenceAvailable ambient
                  (sourceOccurrence.inCollection
                    rhoReflectivePresentation.parallelCollection none).context =
                    rhoCanonicalOccurrenceAvailable ambient occurrence.context ∨
                  (rhoCanonicalOccurrenceAvailable ambient
                      sourceOccurrence.occurrence.context = [] ∧
                    free (sourceOccurrence.inCollection
                      rhoReflectivePresentation.parallelCollection none).name =
                        some TypeExpr.name)
              rw [rhoCanonicalOccurrenceAvailable_inCollection]
              rcases nested with nestedEq | nestedName
              · left
                exact nestedEq.trans
                  ((rhoCanonicalOccurrenceAvailable_keyedParallelPhaseOccurrenceSource
                    (key availableDepth scopeDepth) rhoReflectivePresentation
                      normalizedElements finalOccurrence ambient).trans
                  (rhoCanonicalOccurrenceAvailable_castRoot phaseEquality
                    occurrence ambient))
              · exact Or.inr nestedName
            · rw [canonicalizeByDepthsOccurrenceSource, dif_neg parallel]
              let phaseEquality :
                  canonicalizeByDepths key rhoReflectivePresentation
                      availableDepth scopeDepth
                      (.collection collectionType elements none) =
                    .collection collectionType normalizedElements none := by
                simp [canonicalizeByDepths, normalizedElements, parallel]
              let finalOccurrence := occurrence.castRoot phaseEquality
              let normalizedOccurrence := collectionOccurrenceMember
                collectionType normalizedElements none finalOccurrence
              let sourceOccurrence :=
                canonicalizeListByDepthsOccurrenceSource key
                  rhoReflectivePresentation availableDepth scopeDepth elements
                    normalizedOccurrence
              have nested :=
                rhoCanonicalOccurrenceAvailable_canonicalizeListByDepthsOccurrenceSource_eq_or_name
                  key availableDepth scopeDepth elements free bound
                    (RhoPatternListHasType.ofElements elementsTyped)
                      normalizedOccurrence ambient elementsFree elementsObject
              change rhoCanonicalOccurrenceAvailable ambient
                  (sourceOccurrence.inCollection collectionType none).context =
                    rhoCanonicalOccurrenceAvailable ambient occurrence.context ∨
                  (rhoCanonicalOccurrenceAvailable ambient
                      sourceOccurrence.occurrence.context = [] ∧
                    free (sourceOccurrence.inCollection collectionType none).name =
                      some TypeExpr.name)
              rw [rhoCanonicalOccurrenceAvailable_inCollection]
              rcases nested with nestedEq | nestedName
              · left
                exact nestedEq.trans
                  ((rhoCanonicalOccurrenceAvailable_collectionOccurrenceMember
                    ambient collectionType normalizedElements none
                      finalOccurrence).trans
                  (rhoCanonicalOccurrenceAvailable_castRoot phaseEquality
                    occurrence ambient))
              · exact Or.inr nestedName
        | some collectionRest =>
            rw [canonicalizeByDepthsOccurrenceSource]
            let phaseEquality :
                canonicalizeByDepths key rhoReflectivePresentation
                    availableDepth scopeDepth
                    (.collection collectionType elements
                      (some collectionRest)) =
                  .collection collectionType normalizedElements
                    (some collectionRest) := by
              simp [canonicalizeByDepths, normalizedElements]
            let finalOccurrence := occurrence.castRoot phaseEquality
            let normalizedOccurrence := collectionOccurrenceMember
              collectionType normalizedElements (some collectionRest)
                finalOccurrence
            let sourceOccurrence :=
              canonicalizeListByDepthsOccurrenceSource key
                rhoReflectivePresentation availableDepth scopeDepth elements
                  normalizedOccurrence
            have nested :=
              rhoCanonicalOccurrenceAvailable_canonicalizeListByDepthsOccurrenceSource_eq_or_name
                key availableDepth scopeDepth elements free bound
                  (RhoPatternListHasType.ofElements elementsTyped)
                    normalizedOccurrence ambient elementsFree elementsObject
            change rhoCanonicalOccurrenceAvailable ambient
                (sourceOccurrence.inCollection collectionType
                  (some collectionRest)).context =
                    rhoCanonicalOccurrenceAvailable ambient occurrence.context ∨
                (rhoCanonicalOccurrenceAvailable ambient
                    sourceOccurrence.occurrence.context = [] ∧
                  free (sourceOccurrence.inCollection collectionType
                    (some collectionRest)).name = some TypeExpr.name)
            rw [rhoCanonicalOccurrenceAvailable_inCollection]
            rcases nested with nestedEq | nestedName
            · left
              exact nestedEq.trans
                ((rhoCanonicalOccurrenceAvailable_collectionOccurrenceMember
                  ambient collectionType normalizedElements
                    (some collectionRest) finalOccurrence).trans
                (rhoCanonicalOccurrenceAvailable_castRoot phaseEquality
                  occurrence ambient))
            · exact Or.inr nestedName
  termination_by pattern => 3 * sizeOf pattern + 2

  /-- Elementwise-typed list companion to the full rho ancestry dichotomy. -/
  theorem rhoCanonicalOccurrenceAvailable_canonicalizeListByDepthsOccurrenceSource_eq_or_name
      {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
      (availableDepth scopeDepth : Nat) :
      ∀ (patterns : List Pattern) (free : WellSorted.FreeTypeContext)
        (bound : List TypeExpr)
        (_typed : RhoPatternListHasType free bound patterns)
        (occurrence : CostStaticFVarListOccurrence
          (canonicalizeListByDepths key rhoReflectivePresentation
            availableDepth scopeDepth patterns))
        (ambient : List TypeExpr),
        WellSorted.ReflectiveSubstitutionBinderFreeList patterns = true →
        WellSorted.isObjectPatternList patterns = true →
          rhoCanonicalOccurrenceAvailable ambient
              (canonicalizeListByDepthsOccurrenceSource key
                rhoReflectivePresentation availableDepth scopeDepth patterns
                  occurrence).occurrence.context =
            rhoCanonicalOccurrenceAvailable ambient occurrence.occurrence.context ∨
          (rhoCanonicalOccurrenceAvailable ambient
              (canonicalizeListByDepthsOccurrenceSource key
                rhoReflectivePresentation availableDepth scopeDepth patterns
                  occurrence).occurrence.context = [] ∧
            free (canonicalizeListByDepthsOccurrenceSource key
              rhoReflectivePresentation availableDepth scopeDepth patterns
                occurrence).occurrence.name = some TypeExpr.name)
    | [], free, bound, typed, occurrence, ambient, frameFree, object =>
        Fin.elim0 occurrence.position
    | head :: tail, free, bound, typed, occurrence, ambient, frameFree,
        object => by
        have headTyped : ∃ type,
            WellSorted.HasType rhoCalc free bound head type :=
          typed head (by simp)
        have tailTyped : RhoPatternListHasType free bound tail := by
          intro pattern membership
          exact typed pattern (by simp [membership])
        have freeParts :
            WellSorted.ReflectiveSubstitutionBinderFree head = true ∧
              WellSorted.ReflectiveSubstitutionBinderFreeList tail = true := by
          simpa [WellSorted.ReflectiveSubstitutionBinderFreeList] using
            frameFree
        have objectParts : WellSorted.isObjectPattern head = true ∧
            WellSorted.isObjectPatternList tail = true := by
          simpa [WellSorted.isObjectPatternList] using object
        rcases occurrence with ⟨position, nested⟩
        cases position using Fin.cases with
        | zero =>
            rw [canonicalizeListByDepthsOccurrenceSource]
            obtain ⟨type, headTyped⟩ := headTyped
            exact
              rhoCanonicalOccurrenceAvailable_canonicalizeByDepthsOccurrenceSource_eq_or_name
                key availableDepth scopeDepth head free bound type headTyped
                  nested ambient freeParts.1 objectParts.1
        | succ tailPosition =>
            rw [canonicalizeListByDepthsOccurrenceSource]
            let tailOccurrence : CostStaticFVarListOccurrence
                (canonicalizeListByDepths key rhoReflectivePresentation
                  availableDepth scopeDepth tail) :=
              { position := tailPosition
                occurrence := nested }
            exact
              rhoCanonicalOccurrenceAvailable_canonicalizeListByDepthsOccurrenceSource_eq_or_name
                key availableDepth scopeDepth tail free bound tailTyped
                  tailOccurrence ambient freeParts.2 objectParts.2
  termination_by patterns => 3 * sizeOf patterns + 1

  decreasing_by
    all_goals simp_wf <;> omega
end

/-- Exact source-inventory ancestry for one occurrence in rho's hereditary
canonical representative. -/
abbrev RhoCanonicalInventoryOccurrenceCertificate
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (targetOccurrence : CostStaticFVarOccurrence
      (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
        rhoReflectivePresentation node.targetBound.length 0
        (node.reifiedSourceFrame environment).1)) :=
  CostCanonicalInventoryOccurrenceCertificate environment
    (sourceSemanticPatternKeyAt node environment) rhoReflectivePresentation
      node.targetBound.length 0 targetOccurrence

noncomputable def rhoCanonicalInventoryOccurrenceCertificate
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (targetOccurrence : CostStaticFVarOccurrence
      (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
        rhoReflectivePresentation node.targetBound.length 0
        (node.reifiedSourceFrame environment).1)) :
    RhoCanonicalInventoryOccurrenceCertificate node environment
      targetOccurrence := by
  simpa only [node.reifiedSourceFrame_pattern] using
    costCanonicalInventoryOccurrenceCertificate environment
      (sourceSemanticPatternKeyAt node environment) rhoReflectivePresentation
        node.targetBound.length 0 targetOccurrence

/-- Reifying semantic atoms changes only free-variable names, not quote
boundaries in the surrounding occurrence zipper. -/
theorem rhoCanonicalOccurrenceAvailable_reifyContext
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (ambient : List TypeExpr) (context : OneHoleContext) :
    rhoCanonicalOccurrenceAvailable ambient
        (environment.reifyContext context) =
      rhoCanonicalOccurrenceAvailable ambient context := by
  rw [environment.reifyContext_eq_renameFVarsContext]
  induction context generalizing ambient with
  | hole => rfl
  | apply constructor before inner after inductionHypothesis =>
      simpa [StructuralPatternAction.renameFVarsContext,
        rhoCanonicalOccurrenceAvailable] using
        inductionHypothesis
          (if ReflectiveContextSupport.isQuoteConstructor
              rhoCIGSLT.reflection.1 constructor then [] else ambient)
  | lambda binder inner inductionHypothesis => exact inductionHypothesis ambient
  | multiLambda arity binders inner inductionHypothesis =>
      exact inductionHypothesis ambient
  | substBody inner replacement inductionHypothesis =>
      exact inductionHypothesis ambient
  | substReplacement body inner inductionHypothesis =>
      exact inductionHypothesis ambient
  | collection collectionType before inner after rest inductionHypothesis =>
      exact inductionHypothesis ambient

/-- Specialize typed canonical ancestry to the inventory selected by a rho
static node.  Binder-freedom is retained as an explicit premise here; its
plan-level proof is independent of this occurrence transport. -/
theorem rhoCanonicalInventoryOccurrence_sourceAvailable_eq_targetAvailable_or_sourceName_of_binderFree
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (targetOccurrence : CostStaticFVarOccurrence
      (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
        rhoReflectivePresentation node.targetBound.length 0
        (node.reifiedSourceFrame environment).1))
    (ambient : List TypeExpr)
    (frameFree : WellSorted.ReflectiveSubstitutionBinderFree
      (node.reifiedSourceFrame environment).1 = true) :
    let ancestry := rhoCanonicalInventoryOccurrenceCertificate node
      environment targetOccurrence
    rhoCanonicalOccurrenceAvailable ambient
        (planDecorationOccurrenceAt node inventory
          ancestry.sourcePosition).context =
        rhoCanonicalOccurrenceAvailable ambient targetOccurrence.context ∨
      (rhoCanonicalOccurrenceAvailable ambient
          (planDecorationOccurrenceAt node inventory
            ancestry.sourcePosition).context = [] ∧
        (environment.atomValue
          (environment.occurrenceSlot ancestry.sourcePosition)
            ).key.sourceType = TypeExpr.name) := by
  let ancestry := rhoCanonicalInventoryOccurrenceCertificate node environment
    targetOccurrence
  let sourceSupported := node.reifiedSourceFrame_supported environment
  have traced :=
    rhoCanonicalOccurrenceAvailable_canonicalizeByDepthsOccurrenceSource_eq_or_name
      (sourceSemanticPatternKeyAt node environment) node.targetBound.length 0
        (node.reifiedSourceFrame environment).1 environment.sourceAtomFreeContext
          node.sourceBound (.base node.sourceSort.1) sourceSupported.toHasType
            targetOccurrence ambient frameFree
              (node.reifiedSourceFrame environment).2.1.2.2.1
  have tracedAtCertificate :
      rhoCanonicalOccurrenceAvailable ambient
          ancestry.reifiedOccurrence.context =
            rhoCanonicalOccurrenceAvailable ambient
              targetOccurrence.context ∨
        (rhoCanonicalOccurrenceAvailable ambient
            ancestry.reifiedOccurrence.context = [] ∧
          environment.sourceAtomFreeContext ancestry.reifiedOccurrence.name =
            some TypeExpr.name) := by
    rw [ancestry.canonical_source_eq]
    exact traced
  have planToReified :
      rhoCanonicalOccurrenceAvailable ambient
          (planDecorationOccurrenceAt node inventory
            ancestry.sourcePosition).context =
        rhoCanonicalOccurrenceAvailable ambient
          ancestry.reifiedOccurrence.context := by
    calc
      rhoCanonicalOccurrenceAvailable ambient
          (planDecorationOccurrenceAt node inventory
            ancestry.sourcePosition).context =
          rhoCanonicalOccurrenceAvailable ambient
            (inventory.occurrenceAt ancestry.sourcePosition
              ).fvarOccurrence.context := by
            rw [planDecorationOccurrenceAt_context]
      _ = rhoCanonicalOccurrenceAvailable ambient
            ancestry.sourceOccurrence.context := by
          rw [ancestry.position_eq]
      _ = rhoCanonicalOccurrenceAvailable ambient
            (environment.reifyOccurrence ancestry.sourceOccurrence
              ).context := by
          symm
          simpa using rhoCanonicalOccurrenceAvailable_reifyContext
            environment ambient ancestry.sourceOccurrence.context
      _ = rhoCanonicalOccurrenceAvailable ambient
            ancestry.reifiedOccurrence.context := by
          rw [ancestry.reified_eq]
  rcases tracedAtCertificate with sameAvailable | exposure
  · exact Or.inl (planToReified.trans sameAvailable)
  · right
    constructor
    · exact planToReified.trans exposure.1
    · have reifiedName : ancestry.reifiedOccurrence.name =
          environment.atomName
            (environment.occurrenceSlot ancestry.sourcePosition) :=
        ancestry.canonical_name_eq.trans ancestry.target_name_eq_atomName
      rw [reifiedName, environment.sourceAtomFreeContext_atomName] at exposure
      exact Option.some.inj exposure.2

/-- Static rho plans use only the non-principal zero, drop, quote, and
parallel declarations. -/
theorem rhoStaticPreimage_sourceConstructor_cases
    {color : CostStaticColor}
    {constructor : rhoCIGSLT.DeclaredCostConstructor}
    (preimage : CostStaticConstructorPreimage rhoCIGSLT color constructor) :
    preimage.sourceConstructor.1 = rhoCalc.terms[0] ∨
      preimage.sourceConstructor.1 = rhoCalc.terms[1] ∨
      preimage.sourceConstructor.1 = rhoCalc.terms[2] ∨
      preimage.sourceConstructor.1 = rhoCalc.terms[3] := by
  have membership := preimage.sourceConstructor.2
  change preimage.sourceConstructor.1 ∈
    [rhoCalc.terms[0], rhoCalc.terms[1], rhoCalc.terms[2],
      rhoCalc.terms[3], rhoCalc.terms[4], rhoCalc.terms[5]] at membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with first | second | third | fourth | input | output
  · exact Or.inl first
  · exact Or.inr (Or.inl second)
  · exact Or.inr (Or.inr (Or.inl third))
  · exact Or.inr (Or.inr (Or.inr fourth))
  · have notPrincipal :=
      (rhoContinuationRetyping.mem_wrappedConstructors_iff
        preimage.sourceConstructor).mp preimage.wrapped
    apply (notPrincipal.2 ?_).elim
    apply Subtype.ext
    exact input.trans rhoInteractionCut_environment_constructor_value.symm
  · have notPrincipal :=
      (rhoContinuationRetyping.mem_wrappedConstructors_iff
        preimage.sourceConstructor).mp preimage.wrapped
    apply (notPrincipal.1 ?_).elim
    apply Subtype.ext
    exact output.trans rhoInteractionCut_program_constructor_value.symm

mutual
  /-- Semantic atom reification changes free-variable spelling only, so it
  preserves the binder-free syntax predicate. -/
  theorem rhoReflectiveSubstitutionBinderFree_reify
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {occurrences : List CostRegionOccurrence}
      {table : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
        occurrences}
      {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
        table}
      {root pattern : Pattern}
      {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
        table values root}
      (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
        inventory) :
      WellSorted.ReflectiveSubstitutionBinderFree (environment.reify pattern) =
        WellSorted.ReflectiveSubstitutionBinderFree pattern := by
    cases pattern with
    | bvar | fvar =>
        simp [Pattern.renameFVars,
          WellSorted.ReflectiveSubstitutionBinderFree]
    | apply constructor arguments =>
        simp only [CostStaticAtomEnvironment.reify,
          WellSorted.ReflectiveSubstitutionBinderFree]
        exact rhoReflectiveSubstitutionBinderFreeList_reify environment arguments
    | lambda | multiLambda | subst =>
        simp [Pattern.renameFVars,
          WellSorted.ReflectiveSubstitutionBinderFree]
    | collection collectionType elements rest =>
        simp only [CostStaticAtomEnvironment.reify,
          WellSorted.ReflectiveSubstitutionBinderFree]
        exact rhoReflectiveSubstitutionBinderFreeList_reify environment elements
  termination_by 3 * sizeOf pattern + 2

  /-- List companion to binder-free preservation under atom reification. -/
  theorem rhoReflectiveSubstitutionBinderFreeList_reify
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
        inventory) :
      ∀ patterns,
        WellSorted.ReflectiveSubstitutionBinderFreeList
            (patterns.map environment.reify) =
          WellSorted.ReflectiveSubstitutionBinderFreeList patterns
    | [] => rfl
    | pattern :: patterns => by
        simp only [List.map_cons,
          WellSorted.ReflectiveSubstitutionBinderFreeList]
        rw [rhoReflectiveSubstitutionBinderFree_reify
              (pattern := pattern) environment,
          rhoReflectiveSubstitutionBinderFreeList_reify environment patterns]
  termination_by patterns => 3 * sizeOf patterns + 1

  decreasing_by
    all_goals simp_wf <;> omega
end

/-- A non-bare rho static declaration has only base-sorted parameters. -/
theorem rhoStaticPreimage_nonBare_parameters_base
    {color : CostStaticColor}
    {constructor : rhoCIGSLT.DeclaredCostConstructor}
    (preimage : CostStaticConstructorPreimage rhoCIGSLT color constructor)
    (notBare : ¬ WellSorted.UsesBareCollection
      preimage.sourceConstructor.1) :
    ∀ parameter ∈ preimage.sourceConstructor.1.params,
      ∃ category, WellSorted.parameterType? parameter =
        some (.base category) := by
  intro parameter membership
  rcases rhoStaticPreimage_sourceConstructor_cases preimage with
    zero | drop | quote | parallel
  · rw [zero] at membership
    simp [rhoCalc] at membership
  · rw [drop] at membership
    simp [rhoCalc] at membership
    subst parameter
    exact ⟨"Name", rfl⟩
  · rw [quote] at membership
    simp [rhoCalc] at membership
    subst parameter
    exact ⟨"Proc", rfl⟩
  · apply (notBare ?_).elim
    rw [parallel]
    exact ⟨"ps", .hashBag, TypeExpr.proc, by rfl⟩

mutual
  /-- A rho static plan in a base-sort fibre erases to a binder-free atom
  frame.  Non-static subterms have already become boundary variables. -/
  theorem CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType)
      (base : ∃ category, sourceType = .base category) :
      WellSorted.ReflectiveSubstitutionBinderFree plan.abstractPattern = true := by
    cases plan with
    | bvar | fvar | boundaryApplication | boundaryCollection => rfl
    | @application sourceBound targetBound sourceAvailable thinning outer
        wireName arguments constructor rendered current preimage notBare
        children =>
        simpa [CostStaticRegionPlan.abstractPattern,
          WellSorted.ReflectiveSubstitutionBinderFree] using
          CostStaticArgumentPlan.rhoAbstractPatterns_binderFree_of_base
            children
            (rhoStaticPreimage_nonBare_parameters_base preimage notBare)
    | @lambda sourceBound targetBound sourceAvailable thinning outer binder
        body domain codomain bodyPlan =>
        obtain ⟨category, impossible⟩ := base
        cases impossible
    | @multiLambda sourceBound targetBound sourceAvailable thinning outer arity
        binders body domain codomain bodyPlan =>
        obtain ⟨category, impossible⟩ := base
        cases impossible
    | @collection sourceBound targetBound sourceAvailable thinning outer
        collectionType elements rest sourceType choice selected children =>
        obtain ⟨category, sourceTypeEquality⟩ := base
        cases sourceTypeEquality
        rcases mem_costStaticCollectionTypingChoices_sound rhoCIGSLT color
            targetFree targetBound collectionType elements
            (mapTypeExpr (color.symbols rhoCIGSLT) (.base category)) choice
            selected with direct | bare
        · obtain ⟨sourceElementType, choiceEquality, expectedEquality,
              _checked⟩ := direct
          have impossible : (.base category : TypeExpr) =
              .collection collectionType sourceElementType :=
            mapTypeExpr_costStatic_injective rhoCIGSLT color expectedEquality
          cases impossible
        · obtain ⟨rule, sourceElementType, choiceEquality, membership,
              _wrapped, _expectedEquality, parameterName, parameterShape,
              _checked⟩ := bare
          have ruleEquality : rule = rhoCalc.terms[3] :=
            CostCanonicalLaws.rho_rule_eq_parallel_of_bare_shape membership
              parameterShape
          subst rule
          simp [rhoCalc, TypeExpr.bag, TypeExpr.proc,
            TypeExpr.baseType] at parameterShape
          have sourceElementEquality : sourceElementType = TypeExpr.proc := by
            exact parameterShape.2.2.symm
          cases sourceElementEquality
          cases choiceEquality
          simpa [CostStaticRegionPlan.abstractPattern,
            WellSorted.ReflectiveSubstitutionBinderFree] using
            CostStaticElementPlan.rhoAbstractPatterns_binderFree_of_base
              children ⟨"Proc", rfl⟩
  termination_by 3 * sizeOf pattern + 2

  /-- Ordered arguments of a rho static application remain binder-free when
  every authored parameter has a base result type. -/
  theorem CostStaticArgumentPlan.rhoAbstractPatterns_binderFree_of_base
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {outer : OneHoleContext} {wireName : String}
      {before arguments : List Pattern} {parameters : List TermParam}
      (plan : CostStaticArgumentPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
          parameters)
      (parametersBase : ∀ parameter ∈ parameters,
        ∃ category, WellSorted.parameterType? parameter =
          some (.base category)) :
      WellSorted.ReflectiveSubstitutionBinderFreeList
        plan.abstractPatterns = true := by
    cases plan with
    | nil => rfl
    | @cons sourceBound targetBound sourceAvailable thinning outer wireName
        before argument arguments parameter parameters sourceExpected
        representation parameterType head tail =>
        obtain ⟨category, expectedBase⟩ :=
          parametersBase parameter (by simp)
        have sourceExpectedEquality : sourceExpected = .base category :=
          Option.some.inj (parameterType.symm.trans expectedBase)
        subst sourceExpected
        have tailBase : ∀ tailParameter ∈ parameters,
            ∃ tailCategory, WellSorted.parameterType? tailParameter =
              some (.base tailCategory) := by
          intro tailParameter membership
          exact parametersBase tailParameter (by simp [membership])
        simp [CostStaticArgumentPlan.abstractPatterns,
          WellSorted.ReflectiveSubstitutionBinderFreeList,
          CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base head
            ⟨category, rfl⟩,
          CostStaticArgumentPlan.rhoAbstractPatterns_binderFree_of_base tail
            tailBase]
  termination_by 3 * sizeOf arguments + 1

  /-- Homogeneous elements of a rho static parallel frame remain binder-free
  when their authored element type is a base sort. -/
  theorem CostStaticElementPlan.rhoAbstractPatterns_binderFree_of_base
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
      (base : ∃ category, sourceElementType = .base category) :
      WellSorted.ReflectiveSubstitutionBinderFreeList
        plan.abstractPatterns = true := by
    cases plan with
    | nil => rfl
    | cons head tail =>
        simp [CostStaticElementPlan.abstractPatterns,
          WellSorted.ReflectiveSubstitutionBinderFreeList,
          CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base head base,
          CostStaticElementPlan.rhoAbstractPatterns_binderFree_of_base tail
            base]
  termination_by 3 * sizeOf elements + 1
  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega
end

/-- The source skeleton selected by a rho static node is binder-free.  This
uses the static plan itself as authority, rather than a post-hoc check. -/
theorem skeleton_binderFree
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree) :
    WellSorted.ReflectiveSubstitutionBinderFree node.skeleton.1 = true := by
  rw [node.skeleton_pattern]
  exact CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base node.plan
    ⟨node.sourceSort.1, rfl⟩

/-- Reifying semantic atom names cannot introduce a binder into the source
frame supplied to hereditary canonicalization. -/
theorem reifiedSourceFrame_binderFree
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory) :
    WellSorted.ReflectiveSubstitutionBinderFree
      (node.reifiedSourceFrame environment).1 = true := by
  rw [node.reifiedSourceFrame_pattern,
    rhoReflectiveSubstitutionBinderFree_reify environment]
  exact skeleton_binderFree node

/-- The typed inventory occurrence dichotomy has no residual binder-free
premise for a genuine rho static node. -/
theorem rhoCanonicalInventoryOccurrence_sourceAvailable_eq_targetAvailable_or_sourceName
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (targetOccurrence : CostStaticFVarOccurrence
      (canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
        rhoReflectivePresentation node.targetBound.length 0
        (node.reifiedSourceFrame environment).1))
    (ambient : List TypeExpr) :
    let ancestry := rhoCanonicalInventoryOccurrenceCertificate node
      environment targetOccurrence
    rhoCanonicalOccurrenceAvailable ambient
        (planDecorationOccurrenceAt node inventory
          ancestry.sourcePosition).context =
        rhoCanonicalOccurrenceAvailable ambient targetOccurrence.context ∨
      (rhoCanonicalOccurrenceAvailable ambient
          (planDecorationOccurrenceAt node inventory
            ancestry.sourcePosition).context = [] ∧
        (environment.atomValue
          (environment.occurrenceSlot ancestry.sourcePosition)
            ).key.sourceType = TypeExpr.name) := by
  exact rhoCanonicalInventoryOccurrence_sourceAvailable_eq_targetAvailable_or_sourceName_of_binderFree
    node environment targetOccurrence ambient
      (reifiedSourceFrame_binderFree node environment)

end CostStaticRegionNode

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
