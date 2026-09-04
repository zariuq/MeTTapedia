import Mettapedia.GSLT.LanguageDef.CostSemanticAtomReifyCongruence
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalKeyed

/-!
# Free-variable alignment through keyed canonicalization

`PatternLeafAligned` deliberately permits a semantic leaf to stand for an
arbitrary pattern.  That flexibility is needed after a boundary has been
restored, but it is too broad before reflective canonicalization: an opaque
leaf may itself hide a Quote/Drop or parallel redex.

Source atom frames have the stronger shape recorded by `FvarAligned`—their
only flexible leaves are free variables.  This file proves that exact relation
is preserved by two endpoint-local keyed canonicalizers when aligned subterms
receive equal keys.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-- An arbitrary semantic leaf can hide a reflective redex, so key agreement
alone cannot make `PatternLeafAligned` a canonicalization congruence. -/
theorem patternLeafAligned_canonicalizeByDepths_not_unconditional
    (declaration : ReflectivePresentationDecl)
    (quote_ne_drop : declaration.quoteConstructor ≠
      declaration.dropConstructor)
    (leftName rightName : String) :
    let left := Pattern.apply declaration.quoteConstructor
      [.apply declaration.dropConstructor [.fvar leftName]]
    let right := Pattern.fvar rightName
    let relation : Pattern → Pattern → Prop := fun candidateLeft
      candidateRight => candidateLeft = left ∧ candidateRight = right
    PatternLeafAligned relation left right ∧
      (∀ (_availableDepth _scopeDepth : Nat) {candidateLeft candidateRight},
        PatternLeafAligned relation candidateLeft candidateRight →
          (0 : Nat) = 0) ∧
      ¬ PatternLeafAligned relation
        (canonicalizeByDepths (fun _ _ _ => (0 : Nat)) declaration 0 0 left)
        (canonicalizeByDepths (fun _ _ _ => (0 : Nat)) declaration 0 0 right) := by
  dsimp
  refine ⟨.leaf ⟨rfl, rfl⟩, ?_, ?_⟩
  · intro _ _ _ _ _
    rfl
  · rw [canonicalizeByDepths_quote_drop _ _ quote_ne_drop]
    simp only [canonicalizeByDepths]
    intro aligned
    cases aligned with
    | leaf related => simp at related

namespace FvarAlignedList

/-- Forget the project-specific list wrapper to `List.Forall₂`. -/
def toForall₂ {relation : String → String → Prop} :
    ∀ {left right : List Pattern}, FvarAlignedList relation left right →
      List.Forall₂ (FvarAligned relation) left right
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons head (toForall₂ tail)

/-- Rebuild the project-specific list wrapper from `List.Forall₂`. -/
def ofForall₂ {relation : String → String → Prop} :
    ∀ {left right : List Pattern},
      List.Forall₂ (FvarAligned relation) left right →
        FvarAlignedList relation left right
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons head (ofForall₂ tail)

/-- Aligned lists are empty at exactly the same endpoint. -/
theorem eq_nil_iff {relation : String → String → Prop}
    {left right : List Pattern} (aligned : FvarAlignedList relation left right) :
    left = [] ↔ right = [] := by
  cases aligned <;> simp

end FvarAlignedList

namespace FvarAligned

mutual
  /-- Mapping one presentation on both endpoints preserves free-variable
  alignment; presentation maps leave free-variable spellings unchanged. -/
  def mapPattern (symbols : LanguageDefSymbolMap)
      {relation : String → String → Prop} :
      ∀ {left right}, FvarAligned relation left right →
        FvarAligned relation
          (Mettapedia.GSLT.LanguageDef.mapPattern symbols left)
          (Mettapedia.GSLT.LanguageDef.mapPattern symbols right)
    | _, _, .bvar index => .bvar index
    | _, _, .fvar related => .fvar related
    | _, _, .apply constructor arguments =>
        .apply (symbols.constructor constructor)
          (FvarAlignedList.mapPattern symbols arguments)
    | _, _, .lambda binder body => .lambda binder (body.mapPattern symbols)
    | _, _, .multiLambda arity binders body =>
        .multiLambda arity binders (body.mapPattern symbols)
    | _, _, .subst body replacement =>
        .subst (body.mapPattern symbols) (replacement.mapPattern symbols)
    | _, _, .collection collectionType rest elements =>
        .collection collectionType rest
          (FvarAlignedList.mapPattern symbols elements)

  /-- Listwise companion of `FvarAligned.mapPattern`. -/
  def FvarAlignedList.mapPattern (symbols : LanguageDefSymbolMap)
      {relation : String → String → Prop} :
      ∀ {left right}, FvarAlignedList relation left right →
        FvarAlignedList relation (mapPatternList symbols left)
          (mapPatternList symbols right)
    | _, _, .nil => .nil
    | _, _, .cons head tail =>
        .cons (head.mapPattern symbols)
          (FvarAlignedList.mapPattern symbols tail)
end

mutual
  /-- Restoring ambient bound-variable positions with one thinning preserves
  free-variable alignment. -/
  def thickenAmbientBVars
      {source : CIGSLT} {color : CostStaticColor}
      {sourceBound targetBound : List TypeExpr}
      (thinning : CostStaticBinderThinning source color sourceBound targetBound)
      {relation : String → String → Prop} :
      ∀ depth {left right}, FvarAligned relation left right →
        FvarAligned relation
          (thinning.thickenAmbientBVars depth left)
          (thinning.thickenAmbientBVars depth right)
    | depth, _, _, .bvar index => by
        simpa only [CostStaticBinderThinning.thickenAmbientBVars] using
          (FvarAligned.bvar (relation := relation)
            (thinning.embedIndexAt depth index))
    | depth, _, _, .fvar related => by
        simpa only [CostStaticBinderThinning.thickenAmbientBVars] using
          (FvarAligned.fvar related)
    | depth, _, _, .apply constructor arguments => by
        simpa only [CostStaticBinderThinning.thickenAmbientBVars] using
          (FvarAligned.apply constructor
            (FvarAlignedList.thickenAmbientBVars thinning depth arguments))
    | depth, _, _, .lambda binder body => by
        simpa only [CostStaticBinderThinning.thickenAmbientBVars] using
          (FvarAligned.lambda binder
            (body.thickenAmbientBVars thinning (depth + 1)))
    | depth, _, _, .multiLambda arity binders body => by
        simpa only [CostStaticBinderThinning.thickenAmbientBVars] using
          (FvarAligned.multiLambda arity binders
            (body.thickenAmbientBVars thinning (depth + arity)))
    | depth, _, _, .subst body replacement => by
        simpa only [CostStaticBinderThinning.thickenAmbientBVars] using
          (FvarAligned.subst
            (body.thickenAmbientBVars thinning (depth + 1))
            (replacement.thickenAmbientBVars thinning depth))
    | depth, _, _, .collection collectionType rest elements => by
        simpa only [CostStaticBinderThinning.thickenAmbientBVars] using
          (FvarAligned.collection collectionType rest
            (FvarAlignedList.thickenAmbientBVars thinning depth elements))

  /-- Listwise companion of `FvarAligned.thickenAmbientBVars`. -/
  def FvarAlignedList.thickenAmbientBVars
      {source : CIGSLT} {color : CostStaticColor}
      {sourceBound targetBound : List TypeExpr}
      (thinning : CostStaticBinderThinning source color sourceBound targetBound)
      {relation : String → String → Prop} :
      ∀ depth {left right}, FvarAlignedList relation left right →
        FvarAlignedList relation
          (left.map (thinning.thickenAmbientBVars depth))
          (right.map (thinning.thickenAmbientBVars depth))
    | _, _, _, .nil => .nil
    | depth, _, _, .cons head tail =>
        .cons (head.thickenAmbientBVars thinning depth)
          (FvarAlignedList.thickenAmbientBVars thinning depth tail)
end

mutual
  /-- Free-variable alignment is a congruence for two endpoint-local
  reflective substitutions when each paired variable restores equally at
  every quote-visible depth. -/
  theorem substituteAt_eq
      (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
      (leftSupport rightSupport : ContextSupport.Support)
      (leftAssignment rightAssignment : ContextSupport.Assignment)
      {relation : String → String → Prop}
      (restores : ∀ {leftName rightName}, relation leftName rightName →
        ∀ depth,
          ReflectiveContextSupport.substituteAt profile leftSupport
              leftAssignment depth (.fvar leftName) =
            ReflectiveContextSupport.substituteAt profile rightSupport
              rightAssignment depth (.fvar rightName)) :
      ∀ {left right}, FvarAligned relation left right → ∀ depth,
        ReflectiveContextSupport.substituteAt profile leftSupport
            leftAssignment depth left =
          ReflectiveContextSupport.substituteAt profile rightSupport
            rightAssignment depth right
    | _, _, .bvar index, depth => by
        simp [ReflectiveContextSupport.substituteAt]
    | _, _, .fvar related, depth => restores related depth
    | _, _, .apply constructor arguments, depth => by
        simp only [ReflectiveContextSupport.substituteAt, Pattern.apply.injEq,
          true_and]
        exact FvarAlignedList.substituteAt_eq profile leftSupport rightSupport
          leftAssignment rightAssignment restores arguments
          (if ReflectiveContextSupport.isQuoteConstructor profile constructor
            then 0 else depth)
    | _, _, .lambda binder body, depth => by
        simp only [ReflectiveContextSupport.substituteAt,
          Pattern.lambda.injEq, true_and]
        exact body.substituteAt_eq profile leftSupport rightSupport
          leftAssignment rightAssignment restores (depth + 1)
    | _, _, .multiLambda arity binders body, depth => by
        simp only [ReflectiveContextSupport.substituteAt,
          Pattern.multiLambda.injEq, true_and]
        exact body.substituteAt_eq profile leftSupport rightSupport
          leftAssignment rightAssignment restores (depth + arity)
    | _, _, .subst body replacement, depth => by
        simp only [ReflectiveContextSupport.substituteAt, Pattern.subst.injEq]
        exact ⟨body.substituteAt_eq profile leftSupport rightSupport
            leftAssignment rightAssignment restores (depth + 1),
          replacement.substituteAt_eq profile leftSupport rightSupport
            leftAssignment rightAssignment restores depth⟩
    | _, _, .collection collectionType rest elements, depth => by
        simp only [ReflectiveContextSupport.substituteAt,
          Pattern.collection.injEq, true_and, and_true]
        exact FvarAlignedList.substituteAt_eq profile leftSupport rightSupport
          leftAssignment rightAssignment restores elements depth

  /-- Listwise companion of `FvarAligned.substituteAt_eq`. -/
  theorem FvarAlignedList.substituteAt_eq
      (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
      (leftSupport rightSupport : ContextSupport.Support)
      (leftAssignment rightAssignment : ContextSupport.Assignment)
      {relation : String → String → Prop}
      (restores : ∀ {leftName rightName}, relation leftName rightName →
        ∀ depth,
          ReflectiveContextSupport.substituteAt profile leftSupport
              leftAssignment depth (.fvar leftName) =
            ReflectiveContextSupport.substituteAt profile rightSupport
              rightAssignment depth (.fvar rightName)) :
      ∀ {left right}, FvarAlignedList relation left right → ∀ depth,
        left.map (ReflectiveContextSupport.substituteAt profile leftSupport
            leftAssignment depth) =
          right.map (ReflectiveContextSupport.substituteAt profile rightSupport
            rightAssignment depth)
    | _, _, .nil, _ => rfl
    | _, _, .cons head tail, depth => by
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨head.substituteAt_eq profile leftSupport rightSupport
            leftAssignment rightAssignment restores depth,
          FvarAlignedList.substituteAt_eq profile leftSupport rightSupport
            leftAssignment rightAssignment restores tail depth⟩
end

/-- Structurally aligned patterns agree on whether they are the selected
parallel unit. -/
theorem parallelUnit_iff {relation : String → String → Prop}
    {left right : Pattern} (aligned : FvarAligned relation left right)
    (declaration : ReflectivePresentationDecl) :
    left = .apply declaration.parallelUnitConstructor [] ↔
      right = .apply declaration.parallelUnitConstructor [] := by
  cases aligned with
  | apply constructor arguments =>
      simp only [Pattern.apply.injEq]
      constructor
      · rintro ⟨constructorEq, leftNil⟩
        exact ⟨constructorEq, arguments.eq_nil_iff.mp leftNil⟩
      · rintro ⟨constructorEq, rightNil⟩
        exact ⟨constructorEq, arguments.eq_nil_iff.mpr rightNil⟩
  | bvar => simp
  | fvar => simp
  | lambda => simp
  | multiLambda => simp
  | subst => simp
  | collection => simp

/-- One parallel-splice step preserves exact free-variable alignment. -/
theorem parallelSplice {relation : String → String → Prop}
    {left right : Pattern} (aligned : FvarAligned relation left right)
    (declaration : ReflectivePresentationDecl) :
    List.Forall₂ (FvarAligned relation)
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice declaration
        left)
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice declaration
        right) := by
  cases aligned with
  | bvar index => exact .cons (.bvar index) .nil
  | fvar related => exact .cons (.fvar related) .nil
  | apply constructor arguments =>
      exact .cons (.apply constructor arguments) .nil
  | lambda binder body => exact .cons (.lambda binder body) .nil
  | multiLambda arity binders body =>
      exact .cons (.multiLambda arity binders body) .nil
  | subst body replacement => exact .cons (.subst body replacement) .nil
  | @collection collectionType rest leftElements rightElements elements =>
      cases rest with
      | some restName =>
          exact .cons (.collection collectionType (some restName) elements) .nil
      | none =>
          by_cases selected : collectionType = declaration.parallelCollection
          · subst collectionType
            simpa only [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
              beq_self_eq_true, if_true] using
              elements.toForall₂
          · have selectedFalse :
                (collectionType == declaration.parallelCollection) = false :=
              beq_eq_false_iff_ne.mpr selected
            simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
              selectedFalse] using
              (List.Forall₂.cons
                (FvarAligned.collection collectionType none elements) .nil)

end FvarAligned

namespace FvarAlignedList

/-- Parallel flattening and unit deletion preserve positional alignment. -/
theorem parallelContents {relation : String → String → Prop}
    {left right : List Pattern} (aligned : FvarAlignedList relation left right)
    (declaration : ReflectivePresentationDecl) :
    FvarAlignedList relation
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents declaration
        left)
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents declaration
        right) := by
  apply ofForall₂
  unfold Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelContents
  have flattened : List.Forall₂ (FvarAligned relation)
      (left.flatMap
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice declaration))
      (right.flatMap
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice declaration)) := by
    apply List.rel_flatMap aligned.toForall₂
    intro leftPattern rightPattern related
    exact related.parallelSplice declaration
  apply List.rel_filter _ flattened
  intro leftPattern rightPattern related
  change
    (decide (leftPattern ≠
      .apply declaration.parallelUnitConstructor []) = true) ↔
    (decide (rightPattern ≠
      .apply declaration.parallelUnitConstructor []) = true)
  rw [decide_eq_true_iff, decide_eq_true_iff]
  exact not_congr (related.parallelUnit_iff declaration)

/-- Stable sorting retains each paired occurrence when paired subterms receive
equal endpoint-local keys. -/
theorem sortPatternsBy {Key : Type} [LinearOrder Key]
    {relation : String → String → Prop}
    (leftKey rightKey : Pattern → Key) {left right : List Pattern}
    (aligned : FvarAlignedList relation left right)
    (keys : ∀ {leftPattern rightPattern},
      FvarAligned relation leftPattern rightPattern →
        leftKey leftPattern = rightKey rightPattern) :
    FvarAlignedList relation
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy leftKey left)
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy rightKey right) := by
  apply ofForall₂
  exact Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_forall₂
    leftKey rightKey aligned.toForall₂ keys

/-- The whole flatten/filter/sort frontier preserves alignment. -/
theorem normalizeParallelElementsBy {Key : Type} [LinearOrder Key]
    {relation : String → String → Prop}
    (leftKey rightKey : Pattern → Key) {left right : List Pattern}
    (aligned : FvarAlignedList relation left right)
    (keys : ∀ {leftPattern rightPattern},
      FvarAligned relation leftPattern rightPattern →
        leftKey leftPattern = rightKey rightPattern)
    (declaration : ReflectivePresentationDecl) :
    FvarAlignedList relation
      (normalizeParallelElementsBy leftKey declaration left)
      (normalizeParallelElementsBy rightKey declaration right) := by
  unfold Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy
  exact (aligned.parallelContents declaration).sortPatternsBy
    leftKey rightKey keys

/-- Rebuilding the empty, singleton, or proper parallel frontier preserves
alignment. -/
theorem collapseParallel {relation : String → String → Prop}
    {left right : List Pattern} (aligned : FvarAlignedList relation left right)
    (declaration : ReflectivePresentationDecl) :
    FvarAligned relation
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel declaration
        left)
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel declaration
        right) := by
  cases aligned with
  | nil =>
      exact .apply declaration.parallelUnitConstructor .nil
  | cons head tail =>
      cases tail with
      | nil =>
          simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel]
            using head
      | cons second rest =>
          simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel]
            using
            (.collection declaration.parallelCollection none
              (.cons head (.cons second rest)))

/-- Quote/Drop finishing preserves free-variable alignment because both
endpoints expose the same rigid redex shape. -/
theorem finishNormalizeReflectiveApply
    {relation : String → String → Prop}
    (declaration : ReflectivePresentationDecl) (constructor : String)
    {left right : List Pattern} (aligned : FvarAlignedList relation left right) :
    FvarAligned relation
      (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
        declaration constructor left)
      (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
        declaration constructor right) := by
  by_cases quoteHead :
      (constructor == declaration.quoteConstructor) = true
  · cases aligned with
    | nil =>
        simp only [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
          quoteHead, if_true]
        exact .apply constructor .nil
    | cons head tail =>
        cases tail with
        | cons second rest =>
            simp only [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
              quoteHead, if_true]
            exact .apply constructor (.cons head (.cons second rest))
        | nil =>
            cases head with
            | bvar index =>
                simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                  quoteHead] using (.apply constructor
                    (.cons (.bvar index) .nil))
            | fvar related =>
                simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                  quoteHead] using (.apply constructor
                    (.cons (.fvar related) .nil))
            | lambda binder body =>
                simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                  quoteHead] using (.apply constructor
                    (.cons (.lambda binder body) .nil))
            | multiLambda arity binders body =>
                simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                  quoteHead] using (.apply constructor
                    (.cons (.multiLambda arity binders body) .nil))
            | subst body replacement =>
                simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                  quoteHead] using (.apply constructor
                    (.cons (.subst body replacement) .nil))
            | collection collectionType rest elements =>
                simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                  quoteHead] using (.apply constructor
                    (.cons (.collection collectionType rest elements) .nil))
            | @apply innerConstructor leftArguments rightArguments arguments =>
                cases arguments with
                | nil =>
                    simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                      quoteHead] using (.apply constructor
                        (.cons (.apply innerConstructor .nil) .nil))
                | cons payload payloadTail =>
                    cases payloadTail with
                    | cons secondPayload restPayload =>
                        simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                          quoteHead] using (.apply constructor
                            (.cons (.apply innerConstructor
                              (.cons payload (.cons secondPayload restPayload)))
                                .nil))
                    | nil =>
                        by_cases dropHead :
                            (innerConstructor == declaration.dropConstructor) =
                              true
                        · simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                            quoteHead, dropHead] using payload
                        · have dropHeadFalse :
                              (innerConstructor == declaration.dropConstructor) =
                                false := Bool.eq_false_of_not_eq_true dropHead
                          simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
                            quoteHead, dropHeadFalse] using (.apply constructor
                              (.cons (.apply innerConstructor
                                (.cons payload .nil)) .nil))
  · have quoteHeadFalse :
        (constructor == declaration.quoteConstructor) = false :=
      Bool.eq_false_of_not_eq_true quoteHead
    simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
      quoteHeadFalse] using (.apply constructor aligned)

end FvarAlignedList

mutual
  /-- Two-depth keyed canonicalization preserves exact structural alignment
  when every aligned subterm receives equal endpoint-local keys. -/
  def FvarAligned.canonicalizeByDepths
      {Key : Type} [LinearOrder Key]
      {relation : String → String → Prop}
      (leftKey rightKey : Nat → Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      (keys : ∀ availableDepth scopeDepth {left right},
        FvarAligned relation left right →
          leftKey availableDepth scopeDepth left =
            rightKey availableDepth scopeDepth right) :
      ∀ {left right}, FvarAligned relation left right →
        ∀ availableDepth scopeDepth,
          FvarAligned relation
            (canonicalizeByDepths leftKey declaration availableDepth
              scopeDepth left)
            (canonicalizeByDepths rightKey declaration availableDepth
              scopeDepth right)
    | _, _, .bvar index, _, _ => .bvar index
    | _, _, .fvar related, _, _ => .fvar related
    | _, _, .apply constructor arguments, availableDepth, scopeDepth => by
        let childAvailableDepth :=
          if constructor == declaration.quoteConstructor then 0
          else availableDepth
        have normalizedArguments :=
          FvarAlignedList.canonicalizeByDepths leftKey rightKey declaration
            keys arguments childAvailableDepth scopeDepth
        simpa [canonicalizeByDepths, childAvailableDepth] using
          normalizedArguments.finishNormalizeReflectiveApply declaration
            constructor
    | _, _, .lambda binder body, availableDepth, scopeDepth =>
        .lambda binder (body.canonicalizeByDepths leftKey rightKey declaration
          keys (availableDepth + 1) (scopeDepth + 1))
    | _, _, .multiLambda arity binders body, availableDepth, scopeDepth =>
        .multiLambda arity binders
          (body.canonicalizeByDepths leftKey rightKey declaration keys
            (availableDepth + arity) (scopeDepth + arity))
    | _, _, .subst body replacement, availableDepth, scopeDepth =>
        .subst
          (body.canonicalizeByDepths leftKey rightKey declaration keys
            (availableDepth + 1) (scopeDepth + 1))
          (replacement.canonicalizeByDepths leftKey rightKey declaration keys
            availableDepth scopeDepth)
    | _, _, .collection collectionType rest elements, availableDepth,
        scopeDepth => by
        have normalizedElements :=
          FvarAlignedList.canonicalizeByDepths leftKey rightKey declaration
            keys elements availableDepth scopeDepth
        cases rest with
        | some restName =>
            simpa [canonicalizeByDepths] using
              (FvarAligned.collection collectionType (some restName)
                normalizedElements)
        | none =>
            by_cases selected :
                collectionType = declaration.parallelCollection
            · subst collectionType
              have sorted := normalizedElements.normalizeParallelElementsBy
                (leftKey availableDepth scopeDepth)
                (rightKey availableDepth scopeDepth)
                (keys availableDepth scopeDepth) declaration
              simpa [canonicalizeByDepths] using
                sorted.collapseParallel declaration
            · have selectedFalse :
                  (collectionType == declaration.parallelCollection) = false :=
                beq_eq_false_iff_ne.mpr selected
              simpa [canonicalizeByDepths, selectedFalse] using
                (FvarAligned.collection collectionType none normalizedElements)

  /-- Listwise companion of `FvarAligned.canonicalizeByDepths`. -/
  def FvarAlignedList.canonicalizeByDepths
      {Key : Type} [LinearOrder Key]
      {relation : String → String → Prop}
      (leftKey rightKey : Nat → Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      (keys : ∀ availableDepth scopeDepth {left right},
        FvarAligned relation left right →
          leftKey availableDepth scopeDepth left =
            rightKey availableDepth scopeDepth right) :
      ∀ {left right}, FvarAlignedList relation left right →
        ∀ availableDepth scopeDepth,
          FvarAlignedList relation
            (canonicalizeListByDepths leftKey declaration availableDepth
              scopeDepth left)
            (canonicalizeListByDepths rightKey declaration availableDepth
              scopeDepth right)
    | _, _, .nil, _, _ => .nil
    | _, _, .cons head tail, availableDepth, scopeDepth =>
        .cons
          (head.canonicalizeByDepths leftKey rightKey declaration keys
            availableDepth scopeDepth)
          (tail.canonicalizeByDepths leftKey rightKey declaration keys
            availableDepth scopeDepth)
end

/-- Positive canary: the corrected relation follows a paired Quote/Drop redex
through two endpoint-local canonicalizers and retains the related variable
spellings exposed by the contraction. -/
theorem fvarAligned_canonicalizeByDepths_quoteDrop_canary
    (declaration : ReflectivePresentationDecl)
    (leftName rightName : String) :
    let relation : String → String → Prop := fun left right =>
      left = leftName ∧ right = rightName
    FvarAligned relation
      (canonicalizeByDepths (fun _ _ _ => (0 : Nat)) declaration 3 5
        (.apply declaration.quoteConstructor
          [.apply declaration.dropConstructor [.fvar leftName]]))
      (canonicalizeByDepths (fun _ _ _ => (0 : Nat)) declaration 3 5
        (.apply declaration.quoteConstructor
          [.apply declaration.dropConstructor [.fvar rightName]])) := by
  dsimp
  let input : FvarAligned
      (fun left right => left = leftName ∧ right = rightName)
      (.apply declaration.quoteConstructor
        [.apply declaration.dropConstructor [.fvar leftName]])
      (.apply declaration.quoteConstructor
        [.apply declaration.dropConstructor [.fvar rightName]]) :=
    .apply declaration.quoteConstructor
      (.cons (.apply declaration.dropConstructor
        (.cons (.fvar ⟨rfl, rfl⟩) .nil)) .nil)
  exact input.canonicalizeByDepths (fun _ _ _ => (0 : Nat))
    (fun _ _ _ => (0 : Nat)) declaration (by intros; rfl) 3 5

end Mettapedia.GSLT.LanguageDef
