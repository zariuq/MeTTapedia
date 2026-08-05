import Mettapedia.GSLT.LanguageDef.CostHereditaryFrameNormalization

/-!
# Naturality of hereditary Cost canonicalization

Semantic-atom normalization compares child meanings while retaining the
finite atoms in the frame being normalized.  This file establishes the exact
structural naturality laws needed to transport such a keyed canonicalizer
from an authored frame into either generated Cost colour and through its
certified ambient-binder insertion.

The two depths are intentionally distinct: reflective quotation resets the
quote-visible depth used by the semantic key, whereas ambient-binder insertion
continues to count the structural depth below the quote.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

namespace CostHereditaryCanonical

/-- The Cost constructor embedding commutes exactly with the post-order
quote/drop contraction selected by a mapped reflective declaration. -/
theorem mapPattern_finishNormalizeReflectiveApply
    (source : CIGSLT) (color : CostStaticColor)
    (declaration : ReflectivePresentationDecl)
    (constructor : String) (arguments : List Pattern) :
    mapPattern (color.symbols source)
        (finishNormalizeReflectiveApply declaration constructor arguments) =
      finishNormalizeReflectiveApply
        (costStaticReflectivePresentationDecl source color declaration)
        ((color.symbols source).constructor constructor)
        (arguments.map (mapPattern (color.symbols source))) := by
  by_cases isQuote : constructor = declaration.quoteConstructor
  · subst constructor
    cases arguments with
    | nil =>
        simp [finishNormalizeReflectiveApply, mapPattern,
          costStaticReflectivePresentationDecl_eq_map,
          mapReflectivePresentation]
    | cons argument arguments =>
        cases arguments with
        | cons second remainder =>
            simp [finishNormalizeReflectiveApply, mapPattern,
              costStaticReflectivePresentationDecl_eq_map,
              mapReflectivePresentation]
        | nil =>
            cases argument with
            | apply nestedConstructor nestedArguments =>
                cases nestedArguments with
                | nil =>
                    simp [finishNormalizeReflectiveApply, mapPattern,
                      costStaticReflectivePresentationDecl_eq_map,
                      mapReflectivePresentation]
                | cons name tail =>
                    cases tail with
                    | cons second remainder =>
                        simp [finishNormalizeReflectiveApply, mapPattern,
                          costStaticReflectivePresentationDecl_eq_map,
                          mapReflectivePresentation]
                    | nil =>
                        by_cases isDrop :
                            nestedConstructor = declaration.dropConstructor
                        · subst nestedConstructor
                          simp [finishNormalizeReflectiveApply, mapPattern,
                            costStaticReflectivePresentationDecl_eq_map,
                            mapReflectivePresentation]
                        · simp [finishNormalizeReflectiveApply, mapPattern,
                            costStaticReflectivePresentationDecl_eq_map,
                            mapReflectivePresentation, isDrop]
            | _ =>
                simp [finishNormalizeReflectiveApply, mapPattern,
                  costStaticReflectivePresentationDecl_eq_map,
                  mapReflectivePresentation]
  · simp [finishNormalizeReflectiveApply, mapPattern, isQuote,
      costStaticReflectivePresentationDecl_eq_map,
      mapReflectivePresentation]

/-- Mapping a normalized occurrence into a Cost colour commutes with the
one-layer parallel splice. -/
theorem mapPattern_parallelSplice
    (source : CIGSLT) (color : CostStaticColor)
    (declaration : ReflectivePresentationDecl) (pattern : Pattern) :
    (parallelSplice declaration pattern).map
        (mapPattern (color.symbols source)) =
      parallelSplice
        (costStaticReflectivePresentationDecl source color declaration)
        (mapPattern (color.symbols source) pattern) := by
  rw [costStaticReflectivePresentationDecl_eq_map]
  cases pattern with
  | bvar index => rfl
  | fvar name => rfl
  | apply constructor arguments => rfl
  | lambda binder body => rfl
  | multiLambda arity binders body => rfl
  | subst body replacement => rfl
  | collection collectionType elements rest =>
      cases rest with
      | some restName => rfl
      | none =>
          simp only [parallelSplice, mapPattern, mapPatternList_eq_map,
            mapReflectivePresentation]
          by_cases isParallel :
              collectionType = declaration.parallelCollection
          · subst collectionType
            simp
          · have notParallelBool :
                (collectionType == declaration.parallelCollection) = false :=
              beq_eq_false_iff_ne.mpr isParallel
            simp [notParallelBool, mapPattern, mapPatternList_eq_map]

/-- The Cost constructor embedding commutes with deleting occurrences of the
selected parallel unit. -/
theorem mapPattern_filter_ne_parallelUnit
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
            .apply ((color.symbols source).constructor
              declaration.parallelUnitConstructor) [] := by
        simp [mapPattern]
      by_cases isUnit :
          pattern = .apply declaration.parallelUnitConstructor []
      · subst pattern
        have sourceDecision :
            decide
                (Pattern.apply declaration.parallelUnitConstructor [] ≠
                  Pattern.apply declaration.parallelUnitConstructor []) =
              false := by
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
          (mapPattern_filter_ne_parallelUnit source color declaration patterns)
      · have mappedNotUnit :
            mapPattern (color.symbols source) pattern ≠
              .apply ((color.symbols source).constructor
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
          (mapPattern_filter_ne_parallelUnit source color declaration patterns)

/-- The unsorted parallel contents commute exactly with the Cost constructor
embedding. -/
theorem mapPattern_parallelContents
    (source : CIGSLT) (color : CostStaticColor)
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern) :
    (parallelContents declaration patterns).map
        (mapPattern (color.symbols source)) =
      parallelContents
        (costStaticReflectivePresentationDecl source color declaration)
        (patterns.map (mapPattern (color.symbols source))) := by
  unfold parallelContents
  simp only [costStaticReflectivePresentationDecl_eq_map,
    mapReflectivePresentation]
  rw [mapPattern_filter_ne_parallelUnit]
  rw [List.map_flatMap, List.flatMap_map]
  apply congrArg
  apply List.flatMap_congr
  intro pattern membership
  simpa [costStaticReflectivePresentationDecl_eq_map,
    mapReflectivePresentation] using
      (mapPattern_parallelSplice source color declaration pattern)

/-- Stable key sorting commutes with a map when the source comparator is the
pullback of the target key. -/
theorem map_sortPatternsBy
    {Key : Type} [LinearOrder Key] {f : Pattern → Pattern}
    (key : Pattern → Key) (patterns : List Pattern) :
    (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy
        (fun pattern => key (f pattern)) patterns).map f =
      Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy key
        (patterns.map f) := by
  unfold Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy
  apply List.map_mergeSort
  intro left leftMembership right rightMembership
  rfl

/-- Keyed parallel normalization commutes exactly with the Cost embedding
when the authored key is the pullback of the generated key. -/
theorem mapPattern_normalizeParallelElementsBy
    {Key : Type} [LinearOrder Key]
    (source : CIGSLT) (color : CostStaticColor)
    (key : Pattern → Key) (declaration : ReflectivePresentationDecl)
    (patterns : List Pattern) :
    (normalizeParallelElementsBy
        (fun pattern => key (mapPattern (color.symbols source) pattern))
        declaration patterns).map (mapPattern (color.symbols source)) =
      normalizeParallelElementsBy key
        (costStaticReflectivePresentationDecl source color declaration)
        (patterns.map (mapPattern (color.symbols source))) := by
  unfold normalizeParallelElementsBy
  rw [map_sortPatternsBy]
  exact congrArg
    (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy key)
    (mapPattern_parallelContents source color declaration patterns)

/-- Rebuilding zero, one, or many parallel occurrences commutes exactly with
the Cost embedding. -/
theorem mapPattern_collapseParallel
    (source : CIGSLT) (color : CostStaticColor)
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern) :
    mapPattern (color.symbols source)
        (collapseParallel declaration patterns) =
      collapseParallel
        (costStaticReflectivePresentationDecl source color declaration)
        (patterns.map (mapPattern (color.symbols source))) := by
  cases patterns with
  | nil =>
      simp [collapseParallel, mapPattern,
        costStaticReflectivePresentationDecl_eq_map,
        mapReflectivePresentation]
  | cons first remaining =>
      cases remaining with
      | nil => rfl
      | cons second tail =>
          simp [collapseParallel, mapPattern,
            costStaticReflectivePresentationDecl_eq_map,
            mapReflectivePresentation]

/-- Two-depth keyed canonicalization is strictly natural under either Cost
colour when the authored key is the pullback of the generated key. -/
theorem mapPattern_canonicalizeByDepths
    {Key : Type} [LinearOrder Key]
    (source : CIGSLT) (color : CostStaticColor)
    (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) :
    ∀ availableDepth scopeDepth pattern,
      mapPattern (color.symbols source)
          (canonicalizeByDepths
            (fun availableDepth scopeDepth pattern =>
              key availableDepth scopeDepth
                (mapPattern (color.symbols source) pattern))
            declaration availableDepth scopeDepth pattern) =
        canonicalizeByDepths key
          (costStaticReflectivePresentationDecl source color declaration)
          availableDepth scopeDepth
          (mapPattern (color.symbols source) pattern) := by
  intro availableDepth scopeDepth pattern
  induction pattern using Pattern.inductionOn generalizing availableDepth
      scopeDepth with
  | hbvar index => simp [canonicalizeByDepths, mapPattern]
  | hfvar name => simp [canonicalizeByDepths, mapPattern]
  | happly constructor arguments inductionHypothesis =>
      let childAvailableDepth :=
        if constructor == declaration.quoteConstructor then 0
        else availableDepth
      have mappedQuoteDecision :
          ((color.symbols source).constructor constructor ==
            (costStaticReflectivePresentationDecl source color declaration).quoteConstructor) =
          (constructor == declaration.quoteConstructor) := by
        simp [costStaticReflectivePresentationDecl_eq_map,
          mapReflectivePresentation, CostStaticColor.symbols_constructor]
      have listFactor :
          (canonicalizeListByDepths
              (fun availableDepth scopeDepth pattern =>
                key availableDepth scopeDepth
                  (mapPattern (color.symbols source) pattern))
              declaration childAvailableDepth scopeDepth arguments).map
              (mapPattern (color.symbols source)) =
            canonicalizeListByDepths key
              (costStaticReflectivePresentationDecl source color declaration)
              childAvailableDepth scopeDepth
              (arguments.map (mapPattern (color.symbols source))) := by
        rw [canonicalizeListByDepths_eq_map,
          canonicalizeListByDepths_eq_map]
        simp only [List.map_map]
        apply List.map_congr_left
        intro argument membership
        exact inductionHypothesis argument membership childAvailableDepth
          scopeDepth
      simp only [canonicalizeByDepths, mapPattern, mapPatternList_eq_map]
      rw [mappedQuoteDecision]
      change mapPattern (color.symbols source)
          (finishNormalizeReflectiveApply declaration constructor
            (canonicalizeListByDepths
              (fun availableDepth scopeDepth pattern =>
                key availableDepth scopeDepth
                  (mapPattern (color.symbols source) pattern))
              declaration childAvailableDepth scopeDepth arguments)) = _
      rw [mapPattern_finishNormalizeReflectiveApply, listFactor]
  | hlambda binder body inductionHypothesis =>
      simp only [canonicalizeByDepths, mapPattern,
        Pattern.lambda.injEq, true_and]
      exact inductionHypothesis (availableDepth + 1) (scopeDepth + 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [canonicalizeByDepths, mapPattern,
        Pattern.multiLambda.injEq, true_and]
      exact inductionHypothesis (availableDepth + arity)
        (scopeDepth + arity)
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [canonicalizeByDepths, mapPattern, Pattern.subst.injEq]
      exact ⟨bodyInduction (availableDepth + 1) (scopeDepth + 1),
        replacementInduction availableDepth scopeDepth⟩
  | hcollection collectionType elements rest inductionHypothesis =>
      have listFactor :
          (canonicalizeListByDepths
              (fun availableDepth scopeDepth pattern =>
                key availableDepth scopeDepth
                  (mapPattern (color.symbols source) pattern))
              declaration availableDepth scopeDepth elements).map
              (mapPattern (color.symbols source)) =
            canonicalizeListByDepths key
              (costStaticReflectivePresentationDecl source color declaration)
              availableDepth scopeDepth
              (elements.map (mapPattern (color.symbols source))) := by
        rw [canonicalizeListByDepths_eq_map,
          canonicalizeListByDepths_eq_map]
        simp only [List.map_map]
        apply List.map_congr_left
        intro element membership
        exact inductionHypothesis element membership availableDepth scopeDepth
      cases rest with
      | some restName =>
          simp only [canonicalizeByDepths, mapPattern, mapPatternList_eq_map,
            Pattern.collection.injEq, true_and]
          exact ⟨listFactor, trivial⟩
      | none =>
          by_cases isParallel :
              collectionType = declaration.parallelCollection
          · subst collectionType
            have targetParallelDecision :
                (declaration.parallelCollection ==
                  (costStaticReflectivePresentationDecl source color
                    declaration).parallelCollection) = true := by
              simp [costStaticReflectivePresentationDecl_eq_map,
                mapReflectivePresentation]
            simp only [canonicalizeByDepths, mapPattern,
              mapPatternList_eq_map, beq_self_eq_true,
              targetParallelDecision, if_true]
            rw [mapPattern_collapseParallel]
            rw [mapPattern_normalizeParallelElementsBy, listFactor]
          · have sourceNotParallel :
                (collectionType == declaration.parallelCollection) = false :=
              beq_eq_false_iff_ne.mpr isParallel
            have targetNotParallel :
                (collectionType ==
                  (costStaticReflectivePresentationDecl source color
                    declaration).parallelCollection) = false := by
              simpa [costStaticReflectivePresentationDecl_eq_map,
                mapReflectivePresentation] using sourceNotParallel
            have targetDifferent : collectionType ≠
                (costStaticReflectivePresentationDecl source color
                  declaration).parallelCollection := by
              simpa [costStaticReflectivePresentationDecl_eq_map,
                mapReflectivePresentation] using isParallel
            have mappedTargetDifferent : collectionType ≠
                (mapReflectivePresentation (color.symbols source)
                  declaration).parallelCollection := by
              simpa [mapReflectivePresentation] using isParallel
            simpa [canonicalizeByDepths, sourceNotParallel,
              targetNotParallel, isParallel, targetDifferent,
              mappedTargetDifferent, mapPattern, mapPatternList_eq_map] using
              congrArg
                (fun normalizedElements =>
                  Pattern.collection collectionType normalizedElements none)
                listFactor

/-! ## Ambient-binder naturality -/

/-- Ambient-binder insertion commutes with the post-order quote/drop
contraction at the same structural depth. -/
theorem thickenAmbientBVars_finishNormalizeReflectiveApply
    {source : CIGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning source color sourceBound targetBound)
    (depth : Nat) (declaration : ReflectivePresentationDecl)
    (constructor : String) (arguments : List Pattern) :
    thinning.thickenAmbientBVars depth
        (finishNormalizeReflectiveApply declaration constructor arguments) =
      finishNormalizeReflectiveApply declaration constructor
        (arguments.map (thinning.thickenAmbientBVars depth)) := by
  by_cases isQuote : constructor = declaration.quoteConstructor
  · subst constructor
    cases arguments with
    | nil =>
        simp [finishNormalizeReflectiveApply,
          CostStaticBinderThinning.thickenAmbientBVars]
    | cons argument arguments =>
        cases arguments with
        | cons second remainder =>
            simp [finishNormalizeReflectiveApply,
              CostStaticBinderThinning.thickenAmbientBVars]
        | nil =>
            cases argument with
            | apply nestedConstructor nestedArguments =>
                cases nestedArguments with
                | nil =>
                    simp [finishNormalizeReflectiveApply,
                      CostStaticBinderThinning.thickenAmbientBVars]
                | cons name tail =>
                    cases tail with
                    | cons second remainder =>
                        simp [finishNormalizeReflectiveApply,
                          CostStaticBinderThinning.thickenAmbientBVars]
                    | nil =>
                        by_cases isDrop :
                            nestedConstructor = declaration.dropConstructor
                        · subst nestedConstructor
                          simp [finishNormalizeReflectiveApply,
                            CostStaticBinderThinning.thickenAmbientBVars]
                        · simp [finishNormalizeReflectiveApply,
                            CostStaticBinderThinning.thickenAmbientBVars,
                            isDrop]
            | _ =>
                simp [finishNormalizeReflectiveApply,
                  CostStaticBinderThinning.thickenAmbientBVars]
  · simp [finishNormalizeReflectiveApply,
      CostStaticBinderThinning.thickenAmbientBVars, isQuote]

/-- Ambient-binder insertion preserves and reflects the selected parallel
unit shape. -/
theorem thickenAmbientBVars_eq_parallelUnit_iff
    {source : CIGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning source color sourceBound targetBound)
    (depth : Nat) (unitConstructor : String) (pattern : Pattern) :
    thinning.thickenAmbientBVars depth pattern =
        .apply unitConstructor [] ↔
      pattern = .apply unitConstructor [] := by
  cases pattern <;>
    simp [CostStaticBinderThinning.thickenAmbientBVars]

/-- Ambient-binder insertion commutes with the one-layer parallel splice. -/
theorem thickenAmbientBVars_parallelSplice
    {source : CIGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning source color sourceBound targetBound)
    (depth : Nat) (declaration : ReflectivePresentationDecl)
    (pattern : Pattern) :
    (parallelSplice declaration pattern).map
        (thinning.thickenAmbientBVars depth) =
      parallelSplice declaration
        (thinning.thickenAmbientBVars depth pattern) := by
  cases pattern with
  | bvar index =>
      simp [parallelSplice, CostStaticBinderThinning.thickenAmbientBVars]
  | fvar name =>
      simp [parallelSplice, CostStaticBinderThinning.thickenAmbientBVars]
  | apply constructor arguments =>
      simp [parallelSplice, CostStaticBinderThinning.thickenAmbientBVars]
  | lambda binder body =>
      simp [parallelSplice, CostStaticBinderThinning.thickenAmbientBVars]
  | multiLambda arity binders body =>
      simp [parallelSplice, CostStaticBinderThinning.thickenAmbientBVars]
  | subst body replacement =>
      simp [parallelSplice, CostStaticBinderThinning.thickenAmbientBVars]
  | collection collectionType elements rest =>
      cases rest with
      | some restName =>
          simp [parallelSplice,
            CostStaticBinderThinning.thickenAmbientBVars]
      | none =>
          simp only [parallelSplice,
            CostStaticBinderThinning.thickenAmbientBVars]
          by_cases isParallel :
              collectionType = declaration.parallelCollection
          · subst collectionType
            simp
          · have notParallelBool :
                (collectionType == declaration.parallelCollection) = false :=
              beq_eq_false_iff_ne.mpr isParallel
            simp [notParallelBool,
              CostStaticBinderThinning.thickenAmbientBVars]

/-- Ambient-binder insertion commutes with deleting the selected parallel
unit. -/
theorem thickenAmbientBVars_filter_ne_parallelUnit
    {source : CIGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning source color sourceBound targetBound)
    (depth : Nat) (declaration : ReflectivePresentationDecl) :
    ∀ patterns : List Pattern,
    (patterns.filter fun pattern =>
        pattern ≠ .apply declaration.parallelUnitConstructor []).map
        (thinning.thickenAmbientBVars depth) =
      (patterns.map (thinning.thickenAmbientBVars depth)).filter fun pattern =>
        pattern ≠ .apply declaration.parallelUnitConstructor []
  | [] => rfl
  | pattern :: patterns => by
      by_cases isUnit :
          pattern = .apply declaration.parallelUnitConstructor []
      · subst pattern
        have sourceDecision :
            decide
                (Pattern.apply declaration.parallelUnitConstructor [] ≠
                  Pattern.apply declaration.parallelUnitConstructor []) =
              false := by
          simp
        have targetDecision :
            decide
                (thinning.thickenAmbientBVars depth
                    (.apply declaration.parallelUnitConstructor []) ≠
                  .apply declaration.parallelUnitConstructor []) = false := by
          simp [CostStaticBinderThinning.thickenAmbientBVars]
        simp only [List.filter_cons, List.map_cons]
        rw [sourceDecision, targetDecision]
        simpa using
          (thickenAmbientBVars_filter_ne_parallelUnit thinning depth
            declaration patterns)
      · have thickenedNotUnit :
            thinning.thickenAmbientBVars depth pattern ≠
              .apply declaration.parallelUnitConstructor [] := by
          exact (thickenAmbientBVars_eq_parallelUnit_iff thinning depth
            declaration.parallelUnitConstructor pattern).not.mpr isUnit
        have sourceDecision :
            decide
                (pattern ≠
                  .apply declaration.parallelUnitConstructor []) = true := by
          simp [isUnit]
        have targetDecision :
            decide
                (thinning.thickenAmbientBVars depth pattern ≠
                  .apply declaration.parallelUnitConstructor []) = true := by
          simpa using thickenedNotUnit
        simp only [List.filter_cons, List.map_cons]
        rw [sourceDecision, targetDecision]
        exact congrArg
          (List.cons (thinning.thickenAmbientBVars depth pattern))
          (thickenAmbientBVars_filter_ne_parallelUnit thinning depth
            declaration patterns)

/-- The unsorted parallel contents commute exactly with ambient-binder
insertion at one structural depth. -/
theorem thickenAmbientBVars_parallelContents
    {source : CIGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning source color sourceBound targetBound)
    (depth : Nat) (declaration : ReflectivePresentationDecl)
    (patterns : List Pattern) :
    (parallelContents declaration patterns).map
        (thinning.thickenAmbientBVars depth) =
      parallelContents declaration
        (patterns.map (thinning.thickenAmbientBVars depth)) := by
  unfold parallelContents
  rw [thickenAmbientBVars_filter_ne_parallelUnit]
  rw [List.map_flatMap, List.flatMap_map]
  apply congrArg
  apply List.flatMap_congr
  intro pattern membership
  exact thickenAmbientBVars_parallelSplice thinning depth declaration pattern

/-- Keyed parallel normalization commutes exactly with ambient-binder
insertion when its input key is pulled back along that insertion. -/
theorem thickenAmbientBVars_normalizeParallelElementsBy
    {Key : Type} [LinearOrder Key]
    {source : CIGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning source color sourceBound targetBound)
    (depth : Nat) (key : Pattern → Key)
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern) :
    (normalizeParallelElementsBy
        (fun pattern => key (thinning.thickenAmbientBVars depth pattern))
        declaration patterns).map
        (thinning.thickenAmbientBVars depth) =
      normalizeParallelElementsBy key declaration
        (patterns.map (thinning.thickenAmbientBVars depth)) := by
  unfold normalizeParallelElementsBy
  rw [map_sortPatternsBy]
  exact congrArg
    (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy key)
    (thickenAmbientBVars_parallelContents thinning depth declaration patterns)

/-- Rebuilding zero, one, or many parallel occurrences commutes exactly with
ambient-binder insertion. -/
theorem thickenAmbientBVars_collapseParallel
    {source : CIGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning source color sourceBound targetBound)
    (depth : Nat) (declaration : ReflectivePresentationDecl)
    (patterns : List Pattern) :
    thinning.thickenAmbientBVars depth
        (collapseParallel declaration patterns) =
      collapseParallel declaration
        (patterns.map (thinning.thickenAmbientBVars depth)) := by
  cases patterns with
  | nil =>
      simp [collapseParallel,
        CostStaticBinderThinning.thickenAmbientBVars]
  | cons first remaining =>
      cases remaining with
      | nil => rfl
      | cons second tail =>
          simp [collapseParallel,
            CostStaticBinderThinning.thickenAmbientBVars]

/-- Two-depth keyed canonicalization is strictly natural under a certified
ambient-binder insertion when the input key is pulled back along insertion at
the current structural depth. -/
theorem thickenAmbientBVars_canonicalizeByDepths
    {Key : Type} [LinearOrder Key]
    {source : CIGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning source color sourceBound targetBound)
    (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) :
    ∀ availableDepth scopeDepth pattern,
      thinning.thickenAmbientBVars scopeDepth
          (canonicalizeByDepths
            (fun availableDepth scopeDepth pattern =>
              key availableDepth scopeDepth
                (thinning.thickenAmbientBVars scopeDepth pattern))
            declaration availableDepth scopeDepth pattern) =
        canonicalizeByDepths key declaration availableDepth scopeDepth
          (thinning.thickenAmbientBVars scopeDepth pattern) := by
  intro availableDepth scopeDepth pattern
  induction pattern using Pattern.inductionOn generalizing availableDepth
      scopeDepth with
  | hbvar index =>
      simp [canonicalizeByDepths,
        CostStaticBinderThinning.thickenAmbientBVars]
  | hfvar name =>
      simp [canonicalizeByDepths,
        CostStaticBinderThinning.thickenAmbientBVars]
  | happly constructor arguments inductionHypothesis =>
      let childAvailableDepth :=
        if constructor == declaration.quoteConstructor then 0
        else availableDepth
      have listFactor :
          (canonicalizeListByDepths
              (fun availableDepth scopeDepth pattern =>
                key availableDepth scopeDepth
                  (thinning.thickenAmbientBVars scopeDepth pattern))
              declaration childAvailableDepth scopeDepth arguments).map
              (thinning.thickenAmbientBVars scopeDepth) =
            canonicalizeListByDepths key declaration childAvailableDepth
              scopeDepth
              (arguments.map (thinning.thickenAmbientBVars scopeDepth)) := by
        rw [canonicalizeListByDepths_eq_map,
          canonicalizeListByDepths_eq_map]
        simp only [List.map_map]
        apply List.map_congr_left
        intro argument membership
        exact inductionHypothesis argument membership childAvailableDepth
          scopeDepth
      simp only [canonicalizeByDepths,
        CostStaticBinderThinning.thickenAmbientBVars]
      change thinning.thickenAmbientBVars scopeDepth
          (finishNormalizeReflectiveApply declaration constructor
            (canonicalizeListByDepths
              (fun availableDepth scopeDepth pattern =>
                key availableDepth scopeDepth
                  (thinning.thickenAmbientBVars scopeDepth pattern))
              declaration childAvailableDepth scopeDepth arguments)) = _
      rw [thickenAmbientBVars_finishNormalizeReflectiveApply, listFactor]
  | hlambda binder body inductionHypothesis =>
      simp only [canonicalizeByDepths,
        CostStaticBinderThinning.thickenAmbientBVars,
        Pattern.lambda.injEq, true_and]
      exact inductionHypothesis (availableDepth + 1) (scopeDepth + 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [canonicalizeByDepths,
        CostStaticBinderThinning.thickenAmbientBVars,
        Pattern.multiLambda.injEq, true_and]
      exact inductionHypothesis (availableDepth + arity)
        (scopeDepth + arity)
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [canonicalizeByDepths,
        CostStaticBinderThinning.thickenAmbientBVars,
        Pattern.subst.injEq]
      exact ⟨bodyInduction (availableDepth + 1) (scopeDepth + 1),
        replacementInduction availableDepth scopeDepth⟩
  | hcollection collectionType elements rest inductionHypothesis =>
      have listFactor :
          (canonicalizeListByDepths
              (fun availableDepth scopeDepth pattern =>
                key availableDepth scopeDepth
                  (thinning.thickenAmbientBVars scopeDepth pattern))
              declaration availableDepth scopeDepth elements).map
              (thinning.thickenAmbientBVars scopeDepth) =
            canonicalizeListByDepths key declaration availableDepth
              scopeDepth
              (elements.map (thinning.thickenAmbientBVars scopeDepth)) := by
        rw [canonicalizeListByDepths_eq_map,
          canonicalizeListByDepths_eq_map]
        simp only [List.map_map]
        apply List.map_congr_left
        intro element membership
        exact inductionHypothesis element membership availableDepth scopeDepth
      cases rest with
      | some restName =>
          simp only [canonicalizeByDepths,
            CostStaticBinderThinning.thickenAmbientBVars,
            Pattern.collection.injEq, true_and]
          exact ⟨listFactor, trivial⟩
      | none =>
          by_cases isParallel :
              collectionType = declaration.parallelCollection
          · subst collectionType
            simp only [canonicalizeByDepths,
              CostStaticBinderThinning.thickenAmbientBVars,
              beq_self_eq_true, if_true]
            rw [thickenAmbientBVars_collapseParallel]
            rw [thickenAmbientBVars_normalizeParallelElementsBy, listFactor]
          · have notParallel :
                (collectionType == declaration.parallelCollection) = false :=
              beq_eq_false_iff_ne.mpr isParallel
            simpa [canonicalizeByDepths, notParallel, isParallel,
              CostStaticBinderThinning.thickenAmbientBVars] using
              congrArg
                (fun normalizedElements =>
                  Pattern.collection collectionType normalizedElements none)
                listFactor

/-- Mapping into a Cost colour and reinserting target-only ambient binders
forms one exact naturality square for two-depth keyed canonicalization. -/
theorem mapThicken_canonicalizeByDepths
    {Key : Type} [LinearOrder Key]
    {source : CIGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning source color sourceBound targetBound)
    (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (availableDepth scopeDepth : Nat) (pattern : Pattern) :
    thinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols source)
          (canonicalizeByDepths
            (fun availableDepth scopeDepth pattern =>
              key availableDepth scopeDepth
                (thinning.thickenAmbientBVars scopeDepth
                  (mapPattern (color.symbols source) pattern)))
            declaration availableDepth scopeDepth pattern)) =
      canonicalizeByDepths key
        (costStaticReflectivePresentationDecl source color declaration)
        availableDepth scopeDepth
        (thinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols source) pattern)) := by
  let mappedKey : Nat → Nat → Pattern → Key :=
    fun availableDepth scopeDepth pattern =>
      key availableDepth scopeDepth
        (thinning.thickenAmbientBVars scopeDepth pattern)
  calc
    thinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols source)
            (canonicalizeByDepths
              (fun availableDepth scopeDepth pattern =>
                key availableDepth scopeDepth
                  (thinning.thickenAmbientBVars scopeDepth
                    (mapPattern (color.symbols source) pattern)))
              declaration availableDepth scopeDepth pattern)) =
        thinning.thickenAmbientBVars scopeDepth
          (canonicalizeByDepths mappedKey
            (costStaticReflectivePresentationDecl source color declaration)
            availableDepth scopeDepth
            (mapPattern (color.symbols source) pattern)) := by
      apply congrArg (thinning.thickenAmbientBVars scopeDepth)
      exact mapPattern_canonicalizeByDepths source color mappedKey declaration
        availableDepth scopeDepth pattern
    _ = canonicalizeByDepths key
          (costStaticReflectivePresentationDecl source color declaration)
          availableDepth scopeDepth
          (thinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols source) pattern)) := by
      exact thickenAmbientBVars_canonicalizeByDepths thinning key
        (costStaticReflectivePresentationDecl source color declaration)
        availableDepth scopeDepth (mapPattern (color.symbols source) pattern)

/-- Key sorting, parallel flattening, and unit removal preserve exactly the
constructor support of the input spine. -/
theorem constructorListWithin_normalizeParallelElementsBy_iff
    {Key : Type} [LinearOrder Key]
    {allowed : String → Prop} (key : Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (unitAllowed : allowed declaration.parallelUnitConstructor)
    (patterns : List Pattern) :
    ConstructorListWithin allowed
        (normalizeParallelElementsBy key declaration patterns) ↔
      ConstructorListWithin allowed patterns :=
  (ConstructorListWithin.perm
      (normalizeParallelElementsBy_perm key declaration patterns)).trans
    (constructorListWithin_normalizeParallelElements_iff declaration
      unitAllowed patterns)

/-- Two-depth keyed canonicalization preserves and reflects membership in any
constructor fragment containing the three reflective constructors.  The key
may depend on both depths and on the complete subpattern: it changes only the
permutation of parallel occurrences, never their constructor support. -/
theorem constructorsWithin_canonicalizeByDepths_iff
    {Key : Type} [LinearOrder Key]
    {allowed : String → Prop}
    (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (reflectiveAllowed : ReflectiveConstructorsAllowed allowed declaration) :
    ∀ availableDepth scopeDepth pattern,
      ConstructorsWithin allowed
          (canonicalizeByDepths key declaration availableDepth scopeDepth
            pattern) ↔
        ConstructorsWithin allowed pattern
  | _, _, .bvar _ => by simp [canonicalizeByDepths, ConstructorsWithin]
  | _, _, .fvar _ => by simp [canonicalizeByDepths, ConstructorsWithin]
  | availableDepth, scopeDepth, .apply constructor arguments => by
      simp only [canonicalizeByDepths]
      rw [constructorsWithin_finishNormalizeReflectiveApply_iff declaration
        reflectiveAllowed]
      apply and_congr Iff.rfl
      simp only [constructorListWithin_iff_forall,
        canonicalizeListByDepths_eq_map, List.mem_map]
      constructor
      · intro supported argument membership
        exact
          (constructorsWithin_canonicalizeByDepths_iff key declaration
              reflectiveAllowed
              (if constructor == declaration.quoteConstructor then 0
                else availableDepth)
              scopeDepth argument).mp
            (supported
              (canonicalizeByDepths key declaration
                (if constructor == declaration.quoteConstructor then 0
                  else availableDepth)
                scopeDepth argument) ⟨argument, membership, rfl⟩)
      · rintro supported normalized ⟨argument, membership, rfl⟩
        exact
          (constructorsWithin_canonicalizeByDepths_iff key declaration
              reflectiveAllowed
              (if constructor == declaration.quoteConstructor then 0
                else availableDepth)
              scopeDepth argument).mpr
            (supported argument membership)
  | availableDepth, scopeDepth, .lambda binder body => by
      simpa [canonicalizeByDepths, ConstructorsWithin] using
        constructorsWithin_canonicalizeByDepths_iff key declaration
          reflectiveAllowed (availableDepth + 1) (scopeDepth + 1) body
  | availableDepth, scopeDepth,
      .multiLambda arity binders body => by
      simpa [canonicalizeByDepths, ConstructorsWithin] using
        constructorsWithin_canonicalizeByDepths_iff key declaration
          reflectiveAllowed (availableDepth + arity) (scopeDepth + arity) body
  | availableDepth, scopeDepth, .subst body replacement => by
      simp only [canonicalizeByDepths, ConstructorsWithin]
      exact and_congr
        (constructorsWithin_canonicalizeByDepths_iff key declaration
          reflectiveAllowed (availableDepth + 1) (scopeDepth + 1) body)
        (constructorsWithin_canonicalizeByDepths_iff key declaration
          reflectiveAllowed availableDepth scopeDepth replacement)
  | availableDepth, scopeDepth,
      .collection collectionType elements none => by
      have listFactor :
          ConstructorListWithin allowed
              (canonicalizeListByDepths key declaration availableDepth
                scopeDepth elements) ↔
            ConstructorListWithin allowed elements := by
        simp only [constructorListWithin_iff_forall,
          canonicalizeListByDepths_eq_map, List.mem_map]
        constructor
        · intro supported element membership
          exact
            (constructorsWithin_canonicalizeByDepths_iff key declaration
                reflectiveAllowed availableDepth scopeDepth element).mp
              (supported
                (canonicalizeByDepths key declaration availableDepth
                  scopeDepth element) ⟨element, membership, rfl⟩)
        · rintro supported normalized ⟨element, membership, rfl⟩
          exact
            (constructorsWithin_canonicalizeByDepths_iff key declaration
                reflectiveAllowed availableDepth scopeDepth element).mpr
              (supported element membership)
      by_cases selected : collectionType = declaration.parallelCollection
      · subst collectionType
        simp only [canonicalizeByDepths, beq_self_eq_true, if_true]
        rw [constructorsWithin_collapseParallel_iff declaration
          reflectiveAllowed.parallelUnit]
        rw [constructorListWithin_normalizeParallelElementsBy_iff
          (key availableDepth scopeDepth) declaration
          reflectiveAllowed.parallelUnit]
        exact listFactor
      · have selectedBoolean :
            (collectionType == declaration.parallelCollection) = false :=
          beq_eq_false_iff_ne.mpr selected
        simp [canonicalizeByDepths, selectedBoolean, ConstructorsWithin,
          listFactor]
  | availableDepth, scopeDepth,
      .collection collectionType elements (some rest) => by
      simp only [canonicalizeByDepths, ConstructorsWithin,
        constructorListWithin_iff_forall,
        canonicalizeListByDepths_eq_map, List.mem_map]
      constructor
      · intro supported element membership
        exact
          (constructorsWithin_canonicalizeByDepths_iff key declaration
              reflectiveAllowed availableDepth scopeDepth element).mp
            (supported
              (canonicalizeByDepths key declaration availableDepth scopeDepth
                element) ⟨element, membership, rfl⟩)
      · rintro supported normalized ⟨element, membership, rfl⟩
        exact
          (constructorsWithin_canonicalizeByDepths_iff key declaration
              reflectiveAllowed availableDepth scopeDepth element).mpr
            (supported element membership)

end CostHereditaryCanonical

end Mettapedia.GSLT.LanguageDef
